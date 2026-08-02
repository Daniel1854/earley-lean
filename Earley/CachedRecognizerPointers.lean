/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Proofs.Model
public import Earley.Slice
public import Earley.Filter
public import Earley.Proofs.Finiteness
public import Earley.Recognizer
public import Earley.Proofs.Recognizer
public import Std.Data.HashMap.Lemmas
public import Mathlib.Data.Set.Card

/-!

This module represents an optimized implementation of the Earley algorithm.
For more details on the general algorithm, see `Recognizer`.

In comparison to the naive implementation in `Recognizer`:
- it caches if an item already exists in a bin: HashMap (EarleyItem T N) Nat
- it caches the indices for the items that can be completed: HashMap N (List (EarleyItem T N × Nat))

These optimizations do make it such that maintaining only one origin information per binitem
would be way more convenient, and since the implementation for `build_tree` only uses
the first pointer of the reduction pointer anyway, this doesn't affect the algorithms currently.
This could be a more appropriate next step instead of the current implementation?

TODO: CachedParser would use `Array.findIdx?` instead of filterWithIdx?
TODO: clean some proofs up after completionCache.WF has been introduced as part of CachedEarleyBin
-/

@[expose] public section

namespace Earley
namespace CachedRecognizerPointers

open Model
open EarleyItem
open Utils
open Recognizer

@[grind]
def itemsA {T N : Type} (bin : Array (BinItem T N)) : Array (EarleyItem T N) :=
  bin.map (fun x => x.item)

/--
A cache for checking if an items resides within a single bin.
Maps an EarleyItem to its index within the bin.
-/
abbrev ItemCache (T N : Type) [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)] : Type :=
  Std.HashMap (EarleyItem T N) Nat

/--
A raw array is well-formed in relation to an ItemCache,
if each entry of the array got an entry in the item cache with the corresponding index stored.
-/
@[grind]
public def ItemCache.RawWF {T N : Type} [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)]
    (raw : Array (BinItem T N)) (items : ItemCache T N) : Prop :=
  ∀ i, (hi : i < raw.size) → items.contains raw[i].item
    ∧ ∃ (h : items.contains raw[i].item), items[raw[i].item] = i

/--
An ItemCache is well-formed in relation to a raw array,
if all entries `{item: i}` of the cache correspond in a way,
that the item at index `i` of the raw array is actually the item `item`.
-/
@[grind]
public def ItemCache.EntriesWF {T N : Type} [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)]
    (raw : Array (BinItem T N)) (items : ItemCache T N) : Prop :=
  ∀ x, (hx : x ∈ items) → items[x] < raw.size
    ∧ ∃ (h : items[x] < raw.size), raw[items[x]].item = x

/--
An ItemCache is well-formed, if both
- the raw array is well-formed in relation to the item cache
- the item cache is well-formed in relation to raw array
-/
@[grind]
public def ItemCache.WF {T N : Type} [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)]
    (raw : Array (BinItem T N)) (items : ItemCache T N) : Prop :=
  ItemCache.RawWF raw items ∧ ItemCache.EntriesWF raw items

/--
A cache for accessing the possible rules for a completion within a single bin.
Maps a non-terminal to all the EarleyItems that the bin contains for it and
their index within the bin.
-/
abbrev CompletionCache (T N : Type) [BEq N] [Hashable N] : Type :=
  Std.HashMap N (List (EarleyItem T N × Nat))

/--
A raw array is well-formed in relation to a CompletionCache,
if each entry of the array that has a non-terminal as the next symbol got an entry
in the completion cache for that non-terminal with the corresponding item and index stored.
-/
@[grind]
public def CompletionCache.RawWF {T N : Type} [BEq T] [BEq N] [Hashable N]
    (raw : Array (BinItem T N)) (completions : CompletionCache T N) : Prop :=
  ∀ i, (hi : i < raw.size) → (A : N) →
    (hnext : nextSymbol raw[i].item == some (Symbol.nonterminal A)) →
    ∃ (h : A ∈ completions), (raw[i].item, i) ∈ completions[A]

/--
A CompletionCache is well-formed in relation to a raw array,
if the list stored for each non-terminal `List (item, i)` corresponds to the raw array in a way,
such that all items that got that non-terminal as their next symbol are recorded
together with their index in the raw array.

TODO: this last half-sentence is too wiggly and wont suffice for proofs I think.
      Maybe I need a relation on the Nat within the possible completions for one NT as well
      since it is strictly increasing?
-/
@[grind]
public def CompletionCache.EntriesWF {T N : Type} [BEq T] [BEq N] [Hashable N]
    (raw : Array (BinItem T N)) (completions : CompletionCache T N) : Prop :=
  ∀ A, (hx : A ∈ completions) → ∀ x ∈ completions[A],
    x.2 < raw.size ∧ ∃ (hx : x.2 < raw.size), raw[x.2].item = x.1

/--
A CompletionCache is well-formed, if both
- the raw array is well-formed in relation to the completion cache
- the completion cache is well-formed in relation to raw array

TODO: An inductive predicate definition would be really nice, but then the structure of my proofs
doesnt work at all since I am unable to remove elements from my linked list entries?
A bit unclear how that would interact.
-/
@[grind]
public def CompletionCache.WF {T N : Type} [BEq T] [BEq N] [Hashable N]
    (raw : Array (BinItem T N)) (completions : CompletionCache T N) : Prop :=
  CompletionCache.RawWF raw completions ∧ CompletionCache.EntriesWF raw completions

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : Array (BinItem T N)
  items : ItemCache T N
  invItems : ItemCache.WF raw items
  completions : CompletionCache T N
  invCompletions : CompletionCache.WF raw completions

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq T] [LawfulBEq N] [LawfulBEq (EarleyItem T N)]
  [Hashable N] [Hashable (EarleyItem T N)]

@[grind]
def rawList {n : Nat} (bins : CachedEarleyBins T N n) : EarleyBins T N n :=
  bins.map (fun x => x.raw.toList)

/--
A combination of an EarleyBins with its cache and a well-formedness Invariant about it.
-/
public structure WfEarleyBinsCached (G : ContextFreeGrammarList T N) (wlen : Nat) where
  bins : CachedEarleyBins T N (wlen + 1)
  inv : EarleyBins.WF G (rawList bins)

section WellFormedBin

@[grind →]
public lemma memNT_of_completionCacheWF {bin : CachedEarleyBin T N} {A : N}
    {x : BinItem T N} (hnext : x.item.nextSymbol = some (Symbol.nonterminal A))
    (hmemx : x ∈ bin.raw) : A ∈ bin.completions := by
  have := bin.invCompletions.left
  grind [Array.getElem_of_mem]

omit [LawfulBEq T] [LawfulBEq N] in
public lemma itemCacheWF_of_eq_Items {bin : CachedEarleyBin T N} {raw' : Array (BinItem T N)}
    (heq : ∀ i, (hi : i < bin.raw.size ∧ i < raw'.size) → bin.raw[i].item = raw'[i].item)
    (h : bin.raw.size = raw'.size) : ItemCache.WF raw' bin.items := by
  constructor
  · have := bin.invItems.left
    grind
  · have := bin.invItems.right
    grind

public lemma completionCacheWF_of_eq_Items {bin : CachedEarleyBin T N} {raw' : Array (BinItem T N)}
    (heq : ∀ i, (hi : i < bin.raw.size ∧ i < raw'.size) → bin.raw[i].item = raw'[i].item)
    (h : bin.raw.size = raw'.size) : CompletionCache.WF raw' bin.completions := by
  constructor
  · have := bin.invCompletions.left
    grind
  · have := bin.invCompletions.right
    grind

omit [LawfulBEq T] [LawfulBEq N] in
public lemma itemCacheWF_of_push {bin : CachedEarleyBin T N} {y : BinItem T N}
    (h : ¬ bin.items.contains y.item = true) {raw' : Array (BinItem T N)}
    (hR : raw' = bin.raw.push y) {items' : ItemCache T N}
    (hI : items' = bin.items.insert y.item bin.raw.size) : ItemCache.WF raw' items' := by
  constructor
  · have := bin.invItems.left
    grind
  · have := bin.invItems.right
    grind

public lemma completionCacheWF_of_push_of_nextA (bin : CachedEarleyBin T N) {A : N}
    {y : BinItem T N} (hnext : y.item.nextSymbol = some (Symbol.nonterminal A))
    {raw' : Array (BinItem T N)} (hR : raw' = bin.raw.push y)
    {completions' : CompletionCache T N} (hC : completions' = bin.completions.alter A
      (fun zs => match zs with
      | some zs => zs.append [⟨y.item, bin.raw.size⟩]
      | none => ([⟨y.item, bin.raw.size⟩] : List (EarleyItem T N × Nat)))) :
    CompletionCache.WF raw' completions' := by
  if h : A ∈ bin.completions then
    refine ⟨?_, ?_⟩
    · have : A ∈ completions' := by grind
      have : bin.completions[A] ⊆ completions'[A] := by
        simp only [hC, List.append_eq, Std.HashMap.getElem_alter_self]
        grind
      have : ⟨y.item, bin.raw.size⟩ ∈ completions'[A] := by
        simp only [hC, List.append_eq, Std.HashMap.getElem_alter_self]
        grind
      have := bin.invCompletions.left
      grind
    · have := bin.invCompletions.right
      simp only [hC, List.append_eq]
      intro B hmem x hmemx
      grind
  else
    refine ⟨?_, ?_⟩
    · have := bin.invCompletions.left
      grind
    · have := bin.invCompletions.right
      grind

public lemma completionCacheWF_of_push_of_nextNotA {bin : CachedEarleyBin T N}
    {y : BinItem T N} (hnext : ∀ A, y.item.nextSymbol ≠ some (Symbol.nonterminal A)) :
    CompletionCache.WF (bin.raw.push y) bin.completions := by
  constructor
  · have := bin.invCompletions.left
    grind
  · have := bin.invCompletions.right
    grind

omit [LawfulBEq T] [LawfulBEq N] in
public lemma itemCacheWF_of_erase (bin : CachedEarleyBin T N) (x : BinItem T N)
    (xs : BinItems T N) (heq : bin.raw.toList = x :: xs) (hN : (items (x :: xs)).Nodup)
    (items' : ItemCache T N) (hitems : items' = (bin.items.erase x.item).map (fun _ y => y - 1)) :
    ItemCache.WF xs.toArray items' := by
  simp only [ItemCache.WF, ItemCache.RawWF, List.size_toArray, hitems, List.getElem_toArray,
    Std.HashMap.contains_map, Std.HashMap.contains_erase, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, beq_eq_false_iff_ne, ne_eq, Std.HashMap.contains_iff_mem,
    Std.HashMap.getElem_map, Std.HashMap.getElem_erase, and_exists_self, ItemCache.EntriesWF,
    Std.HashMap.mem_map, Std.HashMap.mem_erase, forall_and_index]
  have : bin.raw.toList.length = bin.raw.size := by grind
  have : 0 < bin.raw.size := by grind
  have hzs : xs.length = bin.raw.size - 1 := by grind
  refine ⟨?_, ?_⟩
  · intro i hi
    have := bin.invItems.left (i+1) (by lia)
    rcases this with ⟨w, hw⟩
    have h1 : ¬x.item = xs[i].item := by
      simp only [items, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hN
      grind
    have h2 : xs[i].item = bin.raw[i+1].item := by
      have : i + 1 < (x :: xs).length := by lia
      have : (x ::xs)[i+1].item = bin.raw[i+1].item := by grind
      grind
    have h3 : xs[i].item ∈ bin.items := by grind
    use ⟨h1, h3⟩
    grind
  · intro x' hx' hmemx
    have := bin.invItems.right x' hmemx
    rcases this with ⟨w, hw⟩
    use (by grind)
    let idx := bin.items[x']
    have : idx < (x :: xs).length := by lia
    have : (x ::xs)[idx].item = bin.raw[idx].item := by grind
    grind

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.

TODO: I could merge scanList with scanCached by reasoning about some getElem instance?
      But there is not much merit to it currently since the proof is trivial.
-/
public def scanCached (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.size)
    (pre : Nat) : BinItems T N :=
  if w[k] == a then
    [⟨incItem x (x.endIdx+1), Pointer.predecessor pre⟩]
  else
    []

omit [BEq N] [LawfulBEq T] [LawfulBEq N] [LawfulBEq (EarleyItem T N)] [Hashable N]
  [Hashable (EarleyItem T N)] in
lemma scanCached_eq_scanList (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (hk : k < w.size)
    (pre : Nat) : scanCached w x a k hk pre = scanList w.toList x a k hk pre := by
  grind [scanList, scanCached]

/--
Cached implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
`j` is the index of y in its bin.
-/
public def completeCached (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : BinItems T N :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := bins[y.startIdx].completions.getD y.rule.input []
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ => ⟨incItem x y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

-- TODO: this one is unused
lemma memCache_of_getElem {x : EarleyItem T N} {bin : CachedEarleyBin T N} {A : N}
    (hnext : nextSymbol x == some (Symbol.nonterminal A)) (hA : A ∈ bin.completions)
    (k : Nat) (hk : k < bin.raw.size)
    (hmem : x = bin.raw[k].item) : (x, k) ∈ bin.completions[A] := by
  have := bin.invCompletions
  grind

-- Very likely requires induction on i.
-- TODO: this is a pain since I need to restrict the completion Cache then,
-- BUT to maintain the symmetric part of the completion invariant,
-- this would mean that I also have to erase the first item from bin.
-- Maybe I dont need the full invariant?
-- TODO: Requires some inv about bin? nodup on bin seems very likely
lemma getCompletionCache_eq_filterWithIdxAux (bin : BinItems T N)
    (binCached : CachedEarleyBin T N) (i : Nat) (A : N)
    (heq : slice bin i bin.length = binCached.raw.toList) :
    Std.HashMap.getD binCached.completions A [] =
    filterWithIdxAux (fun x => nextSymbol x == some (Symbol.nonterminal A)) 0 (items bin) := by
  let P := fun x : EarleyItem T N => nextSymbol x == some (Symbol.nonterminal A)
  -- I would enjoy doing fun_induction but some hypothesis go missing so I cant.
  -- Need to recurse manually I guess? unless I do do a proof over i
  match h : bin with
  | [] =>
    simp [items, filterWithIdxAux]
    sorry
  | x :: xs =>
    have := binCached.invCompletions
    if hP : P x.item then
      simp only [items, List.map_cons, filterWithIdxAux, hP, ↓reduceIte, zero_add, P]
      sorry
    else
      simp only [items, List.map_cons, filterWithIdxAux, hP, Bool.false_eq_true, ↓reduceIte,
        zero_add, P]
      sorry
  --simp only [CompletionCache.WF, Prod.forall] at this
  -- do I want to to induct on i? then I have to map the completions list to an increment /o\
  --have := memFilterWithIdx_of_mem  P

lemma completeCached_eq_completeList {n : Nat} (bins : EarleyBins T N n)
    (binsCached : CachedEarleyBins T N n) (y : EarleyItem T N) (hS : y.startIdx < n)
    (heq : bins = rawList binsCached) (j : Nat) :
    completeCached y binsCached hS j = completeList y bins hS j := by
  rw [completeList_eq_completeListI]
  let P := fun x : EarleyItem T N => nextSymbol x == some (Symbol.nonterminal y.rule.input)
  have : binsCached[y.startIdx].completions.getD y.rule.input []
      = filterWithIdx (items bins[y.startIdx]) P := by
    apply getCompletionCache_eq_filterWithIdxAux (i := 0)
    grind
  grind [completeListI, completeCached]

/--
Add given list one by one into `bin`, if they are not already part of `bin`.
-/
@[inline, grind]
public def updateBinCached (bin : CachedEarleyBin T N) : BinItems T N → CachedEarleyBin T N
  | [] => bin
  | y::ys =>
    if h : bin.items.contains y.item then
      let idx := bin.items[y.item]
      have hidx : idx < bin.raw.size := by
        have := bin.invItems
        grind
      match (bin.raw[idx].pointer, y.pointer) with
      | (Pointer.reduction xp xP, Pointer.reduction yp yP) =>
        let updItem : BinItem T N := ⟨y.item, Pointer.reduction xp (yp::yP.append xP)⟩
        have hS : bin.raw.size = (bin.raw.swapAt idx updItem hidx).2.size := by grind
        have hI : ∀ (i : ℕ) (hi : i < bin.raw.size ∧ i < (bin.raw.swapAt idx updItem hidx).2.size),
            bin.raw[i].item = (bin.raw.swapAt idx updItem hidx).2[i].item := by
          have := bin.invItems
          grind
        have invItems' := itemCacheWF_of_eq_Items hI hS
        have invCompletions' := completionCacheWF_of_eq_Items hI hS
        let newBin := ⟨(bin.raw.swapAt idx updItem hidx).snd, bin.items, invItems',
          bin.completions, invCompletions'⟩
        updateBinCached newBin ys
      | _ => updateBinCached bin ys
    else
      let raw' := bin.raw.push y
      let items' :=  bin.items.insert y.item bin.raw.size
      have invItems' : ItemCache.WF raw' items' := itemCacheWF_of_push h
        (by simp [raw']) (by simp [items'])
      match hnext : y.item.nextSymbol with
      | some (Symbol.nonterminal n) =>
        let completions' := bin.completions.alter n (fun zs => match zs with
          | some zs => zs.append [⟨y.item, bin.raw.size⟩]
          | none => ([⟨y.item, bin.raw.size⟩] : List (EarleyItem T N × Nat)))
        have invCompletions' : CompletionCache.WF raw' completions' :=
          completionCacheWF_of_push_of_nextA bin hnext (by simp [raw']) (by simp [completions'])
        updateBinCached ⟨raw', items', invItems', completions', invCompletions'⟩ ys
      | some (Symbol.terminal t) | none =>
        -- If the next symbol isn't a non-terminal, the completion cache doesn't need to be touched.
        have invCompletions' : CompletionCache.WF raw' bin.completions :=
          completionCacheWF_of_push_of_nextNotA (by grind)
        updateBinCached ⟨raw', items', invItems', bin.completions, invCompletions'⟩ ys

/--
Append `bins` at index `k` with non-duplicate items from `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : CachedEarleyBins T N n) (k : Nat)
    (newBin : BinItems T N) : CachedEarleyBins T N n :=
  Vector.modify bins k (fun x => updateBinCached x newBin)

@[simp, grind =]
public lemma updateBin_nil (bin : CachedEarleyBin T N) : updateBinCached bin [] = bin := by
  simp [updateBinCached]

public lemma updateBinCached_new (bin : CachedEarleyBin T N) (newBin : BinItems T N)
    (h : ∀ x ∈ items newBin, bin.items.contains x = false) (hN : (items newBin).Nodup) :
    (updateBinCached bin newBin).raw.toList = bin.raw.toList ++ newBin := by
  fun_induction updateBinCached bin newBin <;> grind

-- A very mechanical proof, but thats to be expected since it is such an unnatural thing.
public lemma updateBinCached_eq_updateBinCached_of_erase {bin bin' : CachedEarleyBin T N}
    (x y : BinItem T N) (xs : BinItems T N) (heq : bin.raw.toList = x :: xs)
    (hneq : x.item ≠ y.item) (items' : ItemCache T N)
    (hitems : items' = (bin.items.erase x.item).map (fun _ y => y - 1))
    (itemInv : ItemCache.WF xs.toArray items')
    (completions' : CompletionCache T N) (compInv : CompletionCache.WF xs.toArray completions')
    (heq : bin' = ⟨xs.toArray, items', itemInv, completions', compInv⟩) :
    (updateBinCached bin [y]).raw.toList = x :: (updateBinCached bin' [y]).raw.toList := by
  if hcont : bin.items.contains y.item = true then
    have : bin.raw.toList.length = bin.raw.size := by grind
    have : 0 < bin.raw.size := by grind
    have : bin'.items.contains y.item = true := by grind
    simp only [updateBinCached, hcont, this, ↓reduceDIte, List.append_eq, Array.swapAt_def]
    have : bin.raw[0] = x := by
      have : bin.raw.toList[0] = x := by grind
      grind
    have : bin.items[y.item] ≠ 0 := by
      have := bin.invItems.right
      grind
    have : bin.items[y.item] = bin'.items[y.item] + 1 := by grind
    have : bin.items[y.item] < bin.raw.size := by grind
    have : bin'.items[y.item] < bin'.raw.size := by grind
    have hp : bin.raw[bin.items[y.item]].pointer = bin'.raw[bin'.items[y.item]].pointer := by
      have : bin.raw[bin.items[y.item]].pointer = bin.raw.toList[bin.items[y.item]].pointer := by
        grind
      simp only [this, Array.getElem_toList]
      grind
    split
    · rename_i heq
      simp only [hp, Prod.mk.injEq] at heq
      grind [Array.toList_set]
    · rename_i heq
      simp only [hp, Prod.mk.injEq, imp_false, not_and] at heq
      grind
  else
    grind [updateBinCached_new]

public theorem updateBinCached_eq_updateBinAux (bin : BinItems T N) (y : BinItem T N)
    (binCached : CachedEarleyBin T N) (heq : binCached.raw.toList = bin) (hN : (items bin).Nodup) :
    (updateBinCached binCached [y]).raw.toList = updateBinAux y bin := by
  fun_induction updateBinAux y bin generalizing binCached with
  | case1 y =>
    have := binCached.invItems.right
    simp only [Array.toList_eq_nil_iff] at heq
    grind
  -- Matching raw items: merge pointer
  | case2 y x xs heqI xp xP yp yP heqP =>
    have := binCached.invItems.left
    have : 0 < binCached.raw.size := by grind
    have hx : binCached.raw[0] = x := by
      have : binCached.raw.toList[0] = x := by grind
      grind
    grind [Array.toList_set]
  -- Matching no-raw items: no-op
  | case3 y x xs heqI hneqP =>
    have := binCached.invItems.left
    have : 0 < binCached.raw.size := by grind
    have hx : binCached.raw[0] = x := by
      have : binCached.raw.toList[0] = x := by grind
      grind
    grind
   -- This is the fun case, that requires the IH:
   -- Adjusting CachedEarleyBin for the induction step is rather cumbersome since we need to
   -- - cut the first element off (x)
   -- - remove x from the items cache, while also decrementing all indices in the items cache
   -- - remove x from the completions cache, while also decrementing
   --   all indices in all lists of the completion cache
   -- TODO: this is the same that is required for reasoning with filterWithIdxAux right?
  | case4 y x xs hneqI ih =>
    let raw' := xs.toArray
    let items' := binCached.items.erase x.item
    let items'' := items'.map (fun item idx => idx - 1)
    have invItems'' : ItemCache.WF raw' items'' := by grind [itemCacheWF_of_erase]
    let completions' := binCached.completions.map (fun A xs => xs.map (fun x idx => (x, idx-1)))
    match hnext : x.item.nextSymbol with
    | some (Symbol.nonterminal A) =>
      -- I can simply pop the first element since I know the list to be sorted.
      -- But this doesnt make the proof easier.
      let completions'' := binCached.completions.alter A
        (fun zs => match zs with
        | some zs => match zs with
          | [] => ([] : List (EarleyItem T N × Nat))
          | z :: zs => zs
        | none => ([] : List (EarleyItem T N × Nat)))
      have invCompletions'' : CompletionCache.WF raw' completions'' := by
        -- TODO: stub this
        sorry
      let binCached' : CachedEarleyBin T N :=
        ⟨raw', items'', invItems'', completions'', invCompletions''⟩
      specialize ih binCached' (by grind) (by grind)
      rw [← ih]
      grind [updateBinCached_eq_updateBinCached_of_erase]
    | none | some (Symbol.terminal t) =>
      have invCompletions' : CompletionCache.WF raw' binCached.completions := by
        -- TODO: stub this
        sorry
      let binCached' : CachedEarleyBin T N :=
        ⟨raw', items'', invItems'', binCached.completions, invCompletions'⟩
      specialize ih binCached' (by grind) (by grind)
      rw [← ih]
      grind [updateBinCached_eq_updateBinCached_of_erase]

theorem updateBinCached_cons (bin : CachedEarleyBin T N) (y : BinItem T N) (ys : BinItems T N) :
    updateBinCached bin (y :: ys) = updateBinCached (updateBinCached bin [y]) ys := by
  rw [updateBinCached]
  rw (occs := .pos [1]) [updateBinCached]
  if h : bin.items.contains y.item then
    simp only [h, ↓reduceDIte, List.append_eq, Array.swapAt_def, updateBin_nil]
    split <;> simp
  else
    simp only [h, Bool.false_eq_true, ↓reduceDIte, List.append_eq, updateBin_nil]
    split <;> simp

lemma updateBinCached_eq_updateBin (bin : BinItems T N) (newBin : BinItems T N)
    (binCached : CachedEarleyBin T N) (heq : binCached.raw.toList = bin) (hN : (items bin).Nodup) :
    (updateBinCached binCached newBin).raw.toList = updateBin bin newBin := by
  fun_induction updateBin bin newBin generalizing binCached with
  | case1 bin => grind
  | case2 bin y ys ih =>
    have := updateBinCached_eq_updateBinAux bin y binCached heq hN
    specialize ih (updateBinCached binCached [y]) this (by grind [noDup_of_updateBinAux])
    grind [updateBinCached_cons]

lemma updateBinsCached_eq_updateBins {G : ContextFreeGrammarList T N} {w : Array T}
    (bins : EarleyBins T N (w.size + 1)) (k : Nat)
    (newBin : BinItems T N) (binsCached : CachedEarleyBins T N (w.size + 1))
    (hbins : EarleyBins.WF G (rawList binsCached)) (heq : rawList binsCached = bins) :
    rawList (updateBinsCached binsCached k newBin) = updateBins bins k newBin := by
  grind [updateBinCached_eq_updateBin]

lemma wfBins_of_earleyBinCached {G : ContextFreeGrammarList T N} {w : Array T} (j k : Nat)
    (bins bins' : CachedEarleyBins T N (w.size + 1)) (hbins : EarleyBins.WF G (rawList bins))
    (hk : k < bins.size) (hj : ¬ (j ≥ bins[k].raw.size))
    (h : bins' =
      match nextSymbol bins[k].raw[j].item with
      | some s => match s with
        | Symbol.nonterminal A =>
          -- Add all potential .predict operations on the current item to the current bin
          let newItems := predictList G A k
          updateBinsCached bins k newItems
        | Symbol.terminal a =>
          -- If we are the final bin then don't try to progress via consuming another terminal
          if hk : k ≥ w.size then
            bins
          else
            -- Add a potential .scan operations on the current item to the next bin
            let newItem := scanCached w bins[k].raw[j].item a k (by omega) j
            updateBinsCached bins (k + 1) newItem
      | none =>
        -- Add all potential .complete operations on the current item to the current bin
        let newItems := completeCached bins[k].raw[j].item bins (by grind) j
        updateBinsCached bins k newItems) : EarleyBins.WF G (rawList bins') := by
  simp only [ge_iff_le, h]
  match hnext : nextSymbol bins[k].raw[j].item with
  | some s => match s with
    | Symbol.nonterminal A =>
      have : ∀ k, (hk : k < w.size + 1) → (items (rawList bins)[k]).Nodup := by grind
      simp only [updateBinsCached_eq_updateBins (hbins := hbins)]
      apply wfBins_of_predictList hbins hk
    | Symbol.terminal a =>
      if hk : k ≥ w.size then
        simp [hk, hbins]
      else
        simp only [hk, ↓reduceDIte, scanCached_eq_scanList,
          updateBinsCached_eq_updateBins (hbins := hbins)]
        apply wfBins_of_scanList hbins
        · simp [rawList]
        · grind
        · grind
  | none =>
      simp only [completeCached_eq_completeList, updateBinsCached_eq_updateBins (hbins := hbins)]
      apply wfBins_of_completeList hbins
      · simp [rawList]
      · grind
      · grind

end WellFormedBin

/--
Computes the k-th bin starting from index j and returns the updated bins.
-/
public def earleyBinCached {G : ContextFreeGrammarList T N} {w : Array T}
    (bins : CachedEarleyBins T N (w.size + 1)) (k : Nat) (hk : k < bins.size) (j : Nat)
    (hbins : EarleyBins.WF G (rawList bins)) : WfEarleyBinsCached G w.size :=
  -- Return the bins if we are the end of the list of the current bin
  if hj : j ≥ bins[k].raw.size then
    ⟨bins, hbins⟩
  else
    let x := bins[k].raw[j]
    let bins' := match nextSymbol x.item with
    | some s => match s with
      | Symbol.nonterminal A =>
        -- Add all potential .predict operations on the current item to the current bin
        let newItems := predictList G A k
        updateBinsCached bins k newItems
      | Symbol.terminal a =>
        -- If we are the final bin then don't try to progress via consuming another terminal
        if hk : k ≥ w.size then
          bins
        else
          -- Add a potential .scan operations on the current item to the next bin
          let newItem := scanCached w x.item a k (by omega) j
          updateBinsCached bins (k + 1) newItem
    | none =>
      -- Add all potential .complete operations on the current item to the current bin
      let newItems := completeCached x.item bins (by grind) j
      updateBinsCached bins k newItems
    have : EarleyBins.WF G (rawList bins') := by grind [wfBins_of_earleyBinCached]
    earleyBinCached bins' k (by omega) (j+1) this
termination_by { x | isWellFormed G.rules w.size x }.ncard + 1 - j
decreasing_by exact decreasingAux hbins j k (by lia) (by grind)

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
-/
@[grind]
public def initCachedBins (G : ContextFreeGrammarList T N) (w : Array T) :
    WfEarleyBinsCached G w.size :=
  -- Starting with some capacity can be lucrative depending on the benchmark.
  have invItems : ItemCache.WF #[] ∅ := by grind
  have invCompletions : CompletionCache.WF #[] ∅ := by grind
  let bins := Vector.replicate (w.size + 1) ⟨.empty,  {},  invItems, {}, invCompletions⟩
  let bins' := updateBinsCached bins 0 (initList G)
  have : EarleyBins.WF G (rawList bins') := by
    simp only [EarleyBins.WF, Order.lt_add_one_iff]
    intro k hk
    have : bins[k].raw = #[] := by
      simp only [Vector.getElem_replicate, bins]
      rfl
    if hk : k = 0 then
      simp only [hk]
      have ⟨hN, _⟩ := wfBinItems_of_initList G w.size
      have hsub : (rawList bins')[0] = initList G := by
        have := updateBinCached_new bins[0] (initList G) (by grind) hN
        grind
      grind [initList]
    else
      grind
  ⟨bins', this⟩

/--
Computes up to the k-th bin.
Creates the callstack, such that we can compute the bins in order from 0 to n.
-/
@[grind]
public def earleyBinsCached (G : ContextFreeGrammarList T N) (w : Array T) (k : Nat)
    (h : k < w.size + 1) : WfEarleyBinsCached G w.size :=
  match h : k with
  | 0 =>
    let ⟨bins, inv⟩ := initCachedBins G w
    earleyBinCached bins 0 (by simp) 0 inv
  | i+1 =>
    -- Given the first i-th bins being computed, we can compute i+1
    let ⟨bins, inv⟩ := earleyBinsCached G w i (by lia)
    earleyBinCached bins k (by lia) 0 inv

/--
Returns the bins after trying to recognize `w` by using `G`.
-/
@[grind]
public def earleyCached (G : ContextFreeGrammarList T N) (w : Array T) :
    WfEarleyBinsCached G w.size :=
  earleyBinsCached G w w.size (by simp)

/--
Returns if a given word gets recognized by the Grammar by using a variant of the Earley algorithm.

TODO: what code gets compiled from `∃ x ∈ List ?
-/
@[grind]
public def recognizeCached (G : ContextFreeGrammarList T N) (w : Array T) : Bool :=
  let bins := earleyCached G w |>.bins
  let finalItems := itemsA bins[w.size].raw
  ∃ x ∈ finalItems, isFinished G.initial w.size x

end CachedRecognizerPointers
end Earley
