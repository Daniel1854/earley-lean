import Earley.Recognizer

open Earley.Recognizer

-- TODO: is matching less performant if there are more elements within the inductive type?
--       test it out with grammars 1-4
inductive N1 where
| S : N1
deriving BEq, ReflBEq, LawfulBEq

inductive N2 where
| S : N2
| X : N2
| Y : N2
| Z : N2
deriving BEq, ReflBEq, LawfulBEq

inductive T where
| a : T
deriving BEq, ReflBEq, LawfulBEq

def rule0 : ContextFreeRule T N1 :=
  ⟨N1.S, [Symbol.terminal T.a]⟩

def rule1 : ContextFreeRule T N1 :=
  ⟨N1.S, [Symbol.nonterminal N1.S, Symbol.nonterminal N1.S]⟩

def rule2 : ContextFreeRule T N1 :=
  ⟨N1.S, [Symbol.terminal T.a, Symbol.nonterminal N1.S]⟩

def rule3 : ContextFreeRule T N1 :=
  ⟨N1.S, [Symbol.terminal T.a, Symbol.nonterminal N1.S, Symbol.terminal T.a]⟩

def rule4 : ContextFreeRule T N1 :=
  ⟨N1.S, [Symbol.nonterminal N1.S, Symbol.terminal T.a]⟩

def fetchGrammar (grammarIdx : UInt32) : Option (ContextFreeGrammarList T N1) :=
  match grammarIdx with
  --S -> SS | a
  | 1 => some ⟨N1.S, [rule0, rule1], by simp [rule0, rule1]⟩
  --S -> aS | a
  | 2 => some ⟨N1.S, [rule0, rule2], by simp [rule0, rule2]⟩
  --S -> aSa | a
  | 3 => some ⟨N1.S, [rule0, rule3], by simp [rule0, rule3]⟩
  --S -> Sa | a
  | 4 => some ⟨N1.S, [rule0, rule4], by simp [rule0, rule4]⟩
  --S -> SX | a, X -> Y | Z, Y -> a, Z -> a
  | 5 => none
  | _ => none

def sizeBins {n : Nat} (bins : EarleyBins T N1 n) : Nat :=
  bins.map (fun bin => bin.length) |>.sum

def sizePointer (p : Pointer) : Nat :=
  match p with
  | .null | .predecessor _ => 1
  | .reduction _ ps => 1 + ps.length

def sizePointers {n : Nat} (bins : EarleyBins T N1 n) : Nat :=
  bins.map (fun bin => bin.map (fun item => sizePointer item.pointer) |>.sum) |>.sum

def benchRecognizer (G : ContextFreeGrammarList T N1) (numChars : UInt32) : IO Unit := do
  -- FIXME: check if I can simply swap w to Array instead of List
  let t0 ← IO.monoNanosNow
  let w := List.replicate numChars.toNat T.a
  let t1 ← IO.monoNanosNow
  let ⟨bins, _⟩ := earleyList G w
  let t2 ← IO.monoNanosNow
  let binSize := sizeBins bins
  let pointerSize := sizePointers bins
  IO.println s!"num_pointers: {sizePointers bins}"
  IO.println s!"Time to create w '{t1 - t0}' ns"
  IO.println s!"Time to create bins '{t2 - t1}' ns"
  IO.println s!"{numChars},{t2-t1},{binSize},{pointerSize},{binSize + pointerSize}"

def main (args : List String) : IO UInt32 := do
  if args.length < 2 then
    IO.println "Usage: Bench <grammarIdx> <numChars>"
    IO.println ""
    IO.println "Valid values for grammarIdx range from 1-5:"
    IO.println "(1) S -> SS  | a"
    IO.println "(2) S -> aS  | a"
    IO.println "(3) S -> aSa | a"
    IO.println "(4) S -> Sa  | a"
    IO.println "(5) S -> SX  | a, X -> Y | Z, Y -> a, Z -> a"
    return 1
  let grammarIdx := String.toNat! args[0]! |>.toUInt32
  let numChars := String.toNat! args[1]! |>.toUInt32
  IO.println s!"Trying to parse grammar {grammarIdx} for an input length of {numChars}"
  if let some grammar := fetchGrammar grammarIdx then
    benchRecognizer grammar numChars
  else
    IO.println s!"No controlflow for grammarIdx={grammarIdx}"
  return 0
