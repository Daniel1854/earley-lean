/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Filter
public import Earley.Recognizer
public import Earley.Proofs.Recognizer

/-!

This module represents an optimized implementation of the Earley algorithm.
For more details on the general algorithm, see `Recognizer`.

In comparison to the naive implementation in `Recognizer`:
- it caches if an item already exists in a bin: HashMap (EarleyItem T N) Nat
- it caches the indices for the items that can be completed: HashMap N (List (EarleyItem T N × Nat))
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
A CompletionCache is well-formed, if the list stored for each non-terminal `List (item, i)`
corresponds exactly to the result `filterWithIdx` computes for that non-terminal for the raw array.
-/
@[grind]
public def CompletionCache.WF {T N : Type} [BEq T] [BEq N] [Hashable N]
    (raw : Array (BinItem T N)) (completions : CompletionCache T N) : Prop :=
  ∀ A, completions.getD A [] =
    filterWithIdx (items raw.toList) (fun x => nextSymbol x == some (Symbol.nonterminal A))

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

omit [LawfulBEq T] [LawfulBEq N] in
lemma itemCacheWF_of_eq_Items {bin : CachedEarleyBin T N} {raw' : Array (BinItem T N)}
    (heq : ∀ i, (hi : i < bin.raw.size ∧ i < raw'.size) → bin.raw[i].item = raw'[i].item)
    (h : bin.raw.size = raw'.size) : ItemCache.WF raw' bin.items := by
  constructor
  · have := bin.invItems.left
    grind
  · have := bin.invItems.right
    grind

omit [LawfulBEq T] [LawfulBEq N] in
lemma completionCacheWF_of_eq_Items {bin : CachedEarleyBin T N} {raw' : Array (BinItem T N)}
    (heq : ∀ i, (hi : i < bin.raw.size ∧ i < raw'.size) → bin.raw[i].item = raw'[i].item)
    (h : bin.raw.size = raw'.size) : CompletionCache.WF raw' bin.completions := by
  have := bin.invCompletions
  have : itemsA bin.raw = itemsA raw' := by
    grind
  grind [Array.toList_map]

omit [LawfulBEq T] [LawfulBEq N] in
lemma itemCacheWF_of_push {bin : CachedEarleyBin T N} {y : BinItem T N}
    (h : ¬ bin.items.contains y.item = true) {raw' : Array (BinItem T N)}
    (hR : raw' = bin.raw.push y) {items' : ItemCache T N}
    (hI : items' = bin.items.insert y.item bin.raw.size) : ItemCache.WF raw' items' := by
  constructor
  · have := bin.invItems.left
    grind
  · have := bin.invItems.right
    grind

lemma completionCacheWF_of_push_of_nextA (bin : CachedEarleyBin T N) {A : N}
    {y : BinItem T N} (hnext : y.item.nextSymbol = some (Symbol.nonterminal A))
    {raw' : Array (BinItem T N)} (hR : raw' = bin.raw.push y)
    {completions' : CompletionCache T N} (hC : completions' = bin.completions.alter A
      (fun zs => match zs with
      | some zs => zs.append [⟨y.item, bin.raw.size⟩]
      | none => ([⟨y.item, bin.raw.size⟩] : List (EarleyItem T N × Nat)))) :
    CompletionCache.WF raw' completions' := by
  intro B
  simp only [hR, hC, List.append_eq, Array.toList_push]
  have inv := bin.invCompletions
  specialize inv B
  if hab : B = A then
    simp only [List.append_eq, hab, Std.HashMap.getD_alter_self] at *
    have : (match bin.completions[A]? with
      | some zs => some (zs ++ [(y.item, bin.raw.size)])
      | none => some [(y.item, bin.raw.size)]).getD [] =
        (bin.completions.getD A []) ++ [(y.item, bin.raw.size)] := by
      if h : A ∈ bin.completions then
        have := Std.HashMap.getElem?_eq_some_getD_of_contains h (fallback := [])
        simp only [h, getElem?_pos, Option.some.injEq] at this
        simp [h, this]
      else
        simp [h, Std.HashMap.getD_eq_fallback_of_contains_eq_false]
    rw [this]
    rw [inv]
    grind [filterWithIdx_cons_of_P]
  else
    have : (A == B) = false := by grind
    simp only [Std.HashMap.getD_alter, this, Bool.false_eq_true, ↓reduceIte]
    rw [inv]
    simp only [items, List.map_append, List.map_cons, List.map_nil]
    grind [filterWithIdx_cons_of_notP]

lemma completionCacheWF_of_push_of_nextNotA {bin : CachedEarleyBin T N}
    {y : BinItem T N} (hnext : ∀ A, y.item.nextSymbol ≠ some (Symbol.nonterminal A)) :
    CompletionCache.WF (bin.raw.push y) bin.completions := by
  have := bin.invCompletions
  intro A
  specialize this A
  simp only [this, Array.toList_push]
  have : (fun x => nextSymbol x == some (Symbol.nonterminal A)) y.item = false := by grind
  grind [filterWithIdx_cons_of_notP]

omit [LawfulBEq T] [LawfulBEq N] in
lemma itemCacheWF_of_erase (bin : CachedEarleyBin T N) (x : BinItem T N)
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

lemma completionCacheWF_of_erase_of_nextA {bin : CachedEarleyBin T N} {x : BinItem T N}
    {xs : BinItems T N} (heq : bin.raw.toList = x :: xs)
    (A : N) (hnext : x.item.nextSymbol = some (Symbol.nonterminal A))
    {completions' completions'' : CompletionCache T N}
    (hC' : completions' = bin.completions.map (fun _ xs => xs.map (fun (x, idx) => (x, idx - 1))))
    (hC'' : completions'' = completions'.alter A (fun zs => match zs with
      | some zs => match zs with
        | [] => some []
        | _ :: zs => zs
      | none => none)) :
    CompletionCache.WF xs.toArray completions'' := by
  intro B
  have inv := bin.invCompletions
  specialize inv B
  if hab : B = A then
    -- P holds for X, so we have to extract (x.item, 0) from both sides.
    let P := fun x : EarleyItem T N => nextSymbol x == some (Symbol.nonterminal A)
    have hFstep := filterWithIdx_erase_of_P x.item (items xs) P (by grind)
    have : (filterWithIdx (x.item :: items xs) P).map (fun (x, i) => (x, i - 1))
        = (bin.completions.getD A []).map (fun (x, i) => (x, i - 1)) := by
      grind
    simp only [this] at hFstep
    have : (bin.completions.getD A []).map (fun x => (x.1, x.2 - 1))
        = completions'.getD A [] := by
      grind [Std.HashMap.getD_of_map]
    have : (bin.completions.getD A []).map (fun x => (x.1, x.2 - 1))
        = (x.item, 0) :: completions''.getD A [] := by
      grind
    grind
  else
    -- P doesnt hold for x, so the removal doesn't change the output
    have : (A == B) = false := by grind
    simp only [hC'', hC', Std.HashMap.getD_alter, this, Bool.false_eq_true, ↓reduceIte]
    have : (Std.HashMap.map (fun A xs => List.map (fun x => (x.1, x.2 - 1)) xs)
        bin.completions).getD B [] =
        (bin.completions.getD B []).map (fun x => (x.1, x.2 - 1)) := by
      grind [Std.HashMap.getD_of_map]
    rw [this]
    rw [inv]
    grind [filterWithIdx_erase_of_not_P]

lemma completionCacheWF_of_erase_of_nextNotA {bin : CachedEarleyBin T N} {x : BinItem T N}
    {xs : BinItems T N} (heq : bin.raw.toList = x :: xs)
    (hnext : ∀ A, x.item.nextSymbol ≠ some (Symbol.nonterminal A))
    {completions' : CompletionCache T N}
    (hC' : completions' = bin.completions.map (fun _ xs => xs.map (fun (x, idx) => (x, idx - 1)))) :
    CompletionCache.WF xs.toArray completions' := by
  intro A
  have inv := bin.invCompletions
  specialize inv A
  specialize hnext A
  have : (Std.HashMap.map (fun A xs => List.map (fun x => (x.1, x.2 - 1)) xs)
      bin.completions).getD A [] =
      (bin.completions.getD A []).map (fun x => (x.1, x.2 - 1)) := by
    grind [Std.HashMap.getD_of_map]
  grind [filterWithIdx_erase_of_not_P]

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

omit [LawfulBEq T] [LawfulBEq N] in
public theorem completeCached_eq_completeList {wlen : Nat}
    (bins : EarleyBins T N (wlen + 1)) (y : EarleyItem T N) (hS : y.startIdx < (wlen + 1))
    (binsCached : CachedEarleyBins T N (wlen + 1)) (heq : bins = rawList binsCached) (j : Nat) :
    completeCached y binsCached hS j = completeList y bins hS j := by
  rw [completeList_eq_completeListI]
  let P := fun x : EarleyItem T N => nextSymbol x == some (Symbol.nonterminal y.rule.input)
  have : binsCached[y.startIdx].completions.getD y.rule.input []
      = filterWithIdx (items bins[y.startIdx]) P := by
    have := binsCached[y.startIdx].invCompletions
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
lemma updateBinCached_eq_updateBinCached_of_erase {bin bin' : CachedEarleyBin T N}
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
  | case4 y x xs hneqI ih =>
    let raw' := xs.toArray
    let items' := binCached.items.erase x.item
    let items'' := items'.map (fun item idx => idx - 1)
    have invItems'' : ItemCache.WF raw' items'' := by grind [itemCacheWF_of_erase]
    let completions' : CompletionCache T N :=
      binCached.completions.map (fun A xs => xs.map (fun (x, idx) => (x, idx - 1)))
    match hnext : x.item.nextSymbol with
    | some (Symbol.nonterminal A) =>
      let completions'' := completions'.alter A
        (fun zs => match zs with
        | some zs => match zs with
          | [] => some []
          | z :: zs => zs
        | none => none)
      have invCompletions'' : CompletionCache.WF raw' completions'' :=
        completionCacheWF_of_erase_of_nextA heq A hnext (completions' := completions')
          (by simp [completions']) (by simp [completions''])
      let binCached' : CachedEarleyBin T N :=
        ⟨raw', items'', invItems'', completions'', invCompletions''⟩
      specialize ih binCached' (by grind) (by grind)
      rw [← ih]
      grind [updateBinCached_eq_updateBinCached_of_erase]
    | none | some (Symbol.terminal t) =>
      have invCompletions' : CompletionCache.WF raw' completions' := by
        apply completionCacheWF_of_erase_of_nextNotA heq (completions' := completions')
        · grind
        · simp [completions']
      let binCached' : CachedEarleyBin T N :=
        ⟨raw', items'', invItems'', completions', invCompletions'⟩
      specialize ih binCached' (by grind) (by grind)
      rw [← ih]
      grind [updateBinCached_eq_updateBinCached_of_erase]

lemma updateBinCached_cons (bin : CachedEarleyBin T N) (y : BinItem T N) (ys : BinItems T N) :
    updateBinCached bin (y :: ys) = updateBinCached (updateBinCached bin [y]) ys := by
  rw [updateBinCached]
  rw (occs := .pos [1]) [updateBinCached]
  if h : bin.items.contains y.item then
    simp only [h, ↓reduceDIte, List.append_eq, Array.swapAt_def, updateBin_nil]
    split <;> simp
  else
    simp only [h, Bool.false_eq_true, ↓reduceDIte, List.append_eq, updateBin_nil]
    split <;> simp

public theorem updateBinCached_eq_updateBin (bin : BinItems T N) (newBin : BinItems T N)
    (binCached : CachedEarleyBin T N) (heq : binCached.raw.toList = bin) (hN : (items bin).Nodup) :
    (updateBinCached binCached newBin).raw.toList = updateBin bin newBin := by
  fun_induction updateBin bin newBin generalizing binCached with
  | case1 bin => grind
  | case2 bin y ys ih =>
    have := updateBinCached_eq_updateBinAux bin y binCached heq hN
    specialize ih (updateBinCached binCached [y]) this (by grind [noDup_of_updateBinAux])
    grind [updateBinCached_cons]

public theorem updateBinsCached_eq_updateBins {G : ContextFreeGrammarList T N} {w : Array T}
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
            let newItem := scanList w bins[k].raw[j].item a k (by omega) j
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
        simp only [hk, ↓reduceDIte, updateBinsCached_eq_updateBins (hbins := hbins)]
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
          let newItem := scanList w x.item a k (by omega) j
          updateBinsCached bins (k+1) newItem
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
-/
@[grind]
public def recognizeCached (G : ContextFreeGrammarList T N) (w : Array T) : Bool :=
  let bins := earleyCached G w |>.bins
  let finalItems := itemsA bins[w.size].raw
  ∃ x ∈ finalItems, isFinished G.initial w.size x

end CachedRecognizerPointers
end Earley
