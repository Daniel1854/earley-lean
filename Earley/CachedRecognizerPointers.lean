/-
Copyright (c) 2026 Daniel Soukup. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Soukup
-/
module
public import Earley.Model
public import Earley.Proofs.Model
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
An ItemCache is well-formed, if it contains exclusively all elements of the raw array and
the saved index corresponds to the index within the raw array.

TODO: Unclear if this can be stated in a way that I dont require it both ways
      items.size = raw.size
      this would be easier to prove and entails the same thing in combination with Nodup?
      (∀ x, (hx : x ∈ raw) → items.contains x.item) hm
TODO: lemma x ∈ itemsA raw or can grind do this efficiently??
-/
@[grind]
public def ItemCache.WF {T N : Type} [BEq (EarleyItem T N)] [Hashable (EarleyItem T N)]
    (raw : Array (BinItem T N)) (items : ItemCache T N) : Prop :=
  (∀ x, (hx : x ∈ items) →  items[x] < raw.size
    ∧ ∃ (h : items[x] < raw.size), raw[items[x]].item = x)
  ∧ (∀ i, (hi : i < raw.size) → items.contains raw[i].item
    ∧ ∃ (h : items.contains raw[i].item), items[raw[i].item] = i)

/--
A cache for accessing the possible rules for a completion within a single bin.
Maps a non-terminal to all the EarleyItems that the bin contains for it and
their index within the bin.
-/
abbrev CompletionCache (T N : Type) [BEq N] [Hashable N] : Type :=
  Std.HashMap N (List (EarleyItem T N × Nat))

/--
A CompletionCache is well-formed, if all elements of the raw array with their index are
members of the stored completionList for their input symbol of their rule.

TODO: there should be a more functional way to state this.
-/
@[grind]
public def CompletionCache.WF {T N : Type} [BEq N] [Hashable N]
    (raw : Array (BinItem T N)) (completions : CompletionCache T N) : Prop :=
  ∀ i, (hi : i < raw.size) → completions.contains raw[i].item.rule.input
    ∧ ∃ (h : completions.contains raw[i].item.rule.input),
      (raw[i].item, i) ∈ completions[raw[i].item.rule.input]

public structure CachedEarleyBin (T N : Type) [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] where
  raw : Array (BinItem T N)
  items : ItemCache T N
  invItems : ItemCache.WF raw items
  completions : CompletionCache T N
  -- TODO: when the time is ripe.
  --invCompletions : CompletionCache.WF raw completions

abbrev CachedEarleyBins (T N : Type) [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]
    [Hashable N] [Hashable (EarleyItem T N)] (n : Nat) : Type :=
  Vector (CachedEarleyBin T N) n

variable {T N : Type} [BEq T] [BEq N] [LawfulBEq (EarleyItem T N)]
  [Hashable N] [Hashable (EarleyItem T N)]

/--
The caches are well-formed, if both of them are well-formed.
FIXME: maybe its better to have the invs at the bins and not even use this?
-/
@[grind]
public def Cache.WF {wlen : Nat} (bins : CachedEarleyBins T N (wlen + 1)) : Prop :=
  ∀ k, (hk : k < bins.size) → ItemCache.WF bins[k].raw bins[k].items
    ∧ CompletionCache.WF bins[k].raw bins[k].completions

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

/--
List-based implementation of the .scan operation.

Gets called with the next symbol being the terminal `a` of the item `x` and returns a new item
if `a` matches the word for given index `k`.
-/
public def scanCached (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (h : k < w.size)
    (pre : Nat) : List (BinItem T N) :=
  if w[k] == a then
    [⟨incItem x (x.endIdx+1), Pointer.predecessor pre⟩]
  else
    []


omit [BEq N] [LawfulBEq (EarleyItem T N)] [Hashable N] [Hashable (EarleyItem T N)] in
lemma scanCached_eq_scanList (w : Array T) (x : EarleyItem T N) (a : T) (k : Nat) (hk : k < w.size)
    (pre : Nat) : scanCached w x a k hk pre = scanList w.toList x a k hk pre := by
  grind [scanList, scanCached]

/--
List-based implementation of the .complete operation.

Returns items for each successful completion of item `y` using its startIdx for bins.
`j` is the index of y in its bin.
-/
public def completeCached (y : EarleyItem T N) {n : Nat} (bins : CachedEarleyBins T N n)
    (h : y.startIdx < n) (j : Nat) : List (BinItem T N) :=
  -- The origin bin filtered for matchings with y
  let xMatches : List (EarleyItem T N × Nat) := bins[y.startIdx].completions.getD y.rule.input []
  -- Matchings mapped onto a new item with the index recorded within the reduction pointer
  xMatches.map (fun ⟨x,i⟩ => ⟨incItem x y.endIdx, Pointer.reduction ⟨y.startIdx,i,j⟩ []⟩)

lemma completeCached_eq_completeList {n : Nat} (bins : EarleyBins T N n)
    (binsCached : CachedEarleyBins T N n) (y : EarleyItem T N) (hS : y.startIdx < n)
    (heq : bins = rawList binsCached) (j : Nat) :
    completeCached y binsCached hS j = completeList y bins hS j := by
  rw [completeList_eq_completeListI]
  let P := fun x : EarleyItem T N => nextSymbol x == some (Symbol.nonterminal y.rule.input)
  have : binsCached[y.startIdx].completions.getD y.rule.input []
      = filterWithIdx (items bins[y.startIdx]) P := by
    have : CompletionCache.WF binsCached[y.startIdx].raw binsCached[y.startIdx].completions := by
      sorry -- this will be injected through CachedEarleyBin most likely
    -- TODO: this seems to be one of the main usages of the inv of CompletionCache
    simp only [CompletionCache.WF, Std.HashMap.contains_iff_mem, and_exists_self] at this
    sorry
  grind [completeListI, completeCached]

/--
Add given list one by one into `bin`, if they are not already part of `bin`.
-/
@[inline, grind]
public def updateBinCached (bin : CachedEarleyBin T N) : List (BinItem T N) → CachedEarleyBin T N
  | [] => bin
  | y::ys =>
    if h : bin.items.contains y.item then
      let idx := bin.items[y.item]
      have hidx : idx < bin.raw.size := by
        have := bin.invItems
        grind
      match (bin.raw[idx].pointer, y.pointer) with
      | (Pointer.reduction xp xP, Pointer.reduction yp yP) =>
        let updItem := ⟨y.item, Pointer.reduction xp (yp::yP.append xP)⟩
        have inv : ItemCache.WF (bin.raw.swapAt idx updItem hidx).2 bin.items := by
          have := bin.invItems
          grind
        let newBin := ⟨(bin.raw.swapAt idx updItem hidx).snd, bin.items, inv, bin.completions⟩
        updateBinCached newBin ys
      | _ => updateBinCached bin ys
    else
      let raw' := bin.raw.push y
      let items' :=  bin.items.insert y.item bin.raw.size
      have inv : ItemCache.WF raw' items' := by
        have := bin.invItems
        grind
      match y.item.nextSymbol with
      | some (Symbol.nonterminal n) =>
        let completions' := bin.completions.alter n (fun zs => match zs with
          | some zs => zs.append [⟨y.item, bin.raw.size⟩]
          | none => ([⟨y.item, bin.raw.size⟩] : List (EarleyItem T N × Nat)))
        updateBinCached ⟨raw', items', inv, completions'⟩ ys
      | _ =>
        -- If the next symbol isn't a non-terminal, the completion cache doesn't need to be touched.
        updateBinCached ⟨raw', items', inv, bin.completions⟩ ys

/--
Append `bins` at index `k` with non-duplicate items from `newBin` and return the updated bins.
-/
@[grind]
public def updateBinsCached {n : Nat} (bins : CachedEarleyBins T N n) (k : Nat)
    (newBin : BinItems T N) : CachedEarleyBins T N n :=
  Vector.modify bins k (fun x => updateBinCached x newBin)

@[simp, grind =]
lemma updateBin_nil (bin : CachedEarleyBin T N) : updateBinCached bin [] = bin := by
  simp [updateBinCached]

lemma updateBinCached_eq_updateBinAux (bin : BinItems T N) (y : BinItem T N)
    (binCached : CachedEarleyBin T N) (heq : binCached.raw.toList = bin) :
    (updateBinCached binCached [y]).raw.toList = updateBinAux y bin := by
  fun_induction updateBinAux y bin generalizing binCached with
  | case1 y =>
    have := binCached.invItems
    simp only [Array.toList_eq_nil_iff] at heq
    grind
  -- Matching raw items: merge pointer
  | case2 y x xs heqI xp xP yp yP heqP =>
    have := binCached.invItems
    have : 0 < binCached.raw.size := by grind
    have hx : binCached.raw[0] = x := by
      have : binCached.raw.toList[0] = x := by grind
      grind
    grind [Array.toList_set]
  -- Matching no-raw items: no-op
  | case3 y x xs heqI hneqP =>
    have := binCached.invItems
    have : 0 < binCached.raw.size := by grind
    have hx : binCached.raw[0] = x := by
      have : binCached.raw.toList[0] = x := by grind
      grind
    grind
  -- Non-matching item: check the next item
  | case4 y x xs hneqI ih =>
    have := binCached.invItems
    have : 0 < binCached.raw.size := by grind
    have hx : binCached.raw[0] = x := by
      have : binCached.raw.toList[0] = x := by grind
      grind
    -- FIXME: this is wrong, I need to remove x from binCached.items for the inv to be provable
    -- oh. and all the entries need to be decremented by one. thats rather bad.
    -- but these seems provable at least.
    let binCached' : CachedEarleyBin T N :=
      ⟨binCached.raw[1:], binCached.items, sorry, binCached.completions⟩
    specialize ih binCached' (by sorry)
    rw [← ih]
    sorry

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
    (binCached : CachedEarleyBin T N) (heq : binCached.raw.toList = bin) :
    (updateBinCached binCached newBin).raw.toList = updateBin bin newBin := by
  fun_induction updateBin bin newBin generalizing binCached with
  | case1 bin => grind
  | case2 bin y ys ih =>
    have := updateBinCached_eq_updateBinAux bin y binCached heq
    specialize ih (updateBinCached binCached [y]) this
    grind [updateBinCached_cons]

lemma updateBinsCached_eq_updateBins {n : Nat} (bins : EarleyBins T N n) (k : Nat)
    (newBin : BinItems T N) (binsCached : CachedEarleyBins T N n)
    (heq : rawList binsCached = bins) :
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
      simp only [updateBinsCached_eq_updateBins]
      apply wfBins_of_predictList hbins hk
    | Symbol.terminal a =>
      if hk : k ≥ w.size then
        simp [hk, hbins]
      else
        simp only [hk, ↓reduceDIte, scanCached_eq_scanList, updateBinsCached_eq_updateBins]
        apply wfBins_of_scanList hbins
        · simp [rawList]
        · grind
        · grind
  | none =>
      simp only [completeCached_eq_completeList, updateBinsCached_eq_updateBins]
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
decreasing_by
  apply Nat.sub_lt_sub_left
  · specialize hbins k (by lia)
    let wfItemsBin := { x | isWellFormed G.rules w.size x }
    have : (items (rawList bins)[k]).length ≤ wfItemsBin.ncard := by
      have hF := Earley.Proofs.Finiteness.finiteEarleyWF G w.size
      have ⟨hNoDup, _, _, _⟩ := hbins
      let P := (fun x => isWellFormed G.rules w.size x)
      apply length_lte_ncard_of_superset (items (rawList bins)[k]) wfItemsBin P
        (by grind) (by grind) hNoDup
    grind
  · simp

public lemma updateBinCached_of_unclear (bin : CachedEarleyBin T N) (newBin : List (BinItem T N))
    (h : ∀ x ∈ items newBin, x ∉ items bin.raw.toList) (hN : (items newBin).Nodup) :
    (updateBinCached bin newBin).raw.toList = bin.raw.toList ++ newBin := by
  fun_induction updateBinCached bin newBin with
  | case1 bin => grind
  | case2 bin y ys hcont =>
    have := bin.invItems
    have : Std.HashMap.contains bin.items y.item = false := by sorry
    grind
  | case3 bin y ys hcont idx hidx x ih=>
    have := bin.invItems
    have : Std.HashMap.contains bin.items y.item = false := by sorry
    grind
  | case4 bin y ys hncont raw' items' inv A hnexty completions' ih =>
    have := bin.invItems
    sorry
  | case5 bin y ys hncont raw' items' inv hnexty ih =>
    have := bin.invItems
    sorry

/--
Initialize bins by constructing the first bin through using .init for all G.rules.
-/
@[grind]
public def initCachedBins (G : ContextFreeGrammarList T N) (w : Array T) :
    WfEarleyBinsCached G w.size :=
  -- Starting with some capacity can be lucrative depending on the benchmark.
  have : ItemCache.WF #[] ∅ := by grind
  let bins := Vector.replicate (w.size + 1) ⟨.empty,  {},  this, {}⟩
  let bins' := updateBinsCached bins 0 (initList G)
  have : EarleyBins.WF G (rawList bins') := by
    simp only [EarleyBins.WF, Order.lt_add_one_iff]
    intro k hk
    have : bins[k].raw = #[] := by
      simp only [Vector.getElem_replicate, bins]
      rfl
    if hk : k = 0 then
      simp only [hk]
      have hsub : (rawList bins')[0] = initList G := by
        have := G.nodup
        have := updateBinCached_of_unclear bins[0] (initList G) (by grind) (by grind [initList])
        grind
      have ⟨hN, _⟩ := wfBinItems_of_initList G w.size
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
public def recognizeCached (G : ContextFreeGrammarList T N) (w : Array T) [LawfulBEq T] : Bool :=
  let bins := earleyCached G w |>.bins
  let finalItems := itemsA bins[w.size].raw
  ∃ x ∈ finalItems, isFinished G.initial w.size x

end CachedRecognizerPointers
end Earley
