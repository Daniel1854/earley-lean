import Earley.Recognizer

open Earley.Recognizer

-- Matching is indeed less performant if there are more elements within the inductive type.
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

def rule5 : ContextFreeRule T N2 :=
  ⟨N2.S, [Symbol.terminal T.a]⟩

def rule6 : ContextFreeRule T N2 :=
  ⟨N2.S, [Symbol.nonterminal N2.S, Symbol.nonterminal N2.X]⟩

def rule7 : ContextFreeRule T N2 :=
  ⟨N2.X, [Symbol.nonterminal N2.Y]⟩

def rule8 : ContextFreeRule T N2 :=
  ⟨N2.X, [Symbol.nonterminal N2.Z]⟩

def rule9 : ContextFreeRule T N2 :=
  ⟨N2.Y, [Symbol.terminal T.a]⟩

def rule10 : ContextFreeRule T N2 :=
  ⟨N2.Z, [Symbol.terminal T.a]⟩

def sizeBins {N : Type} {n : Nat} (bins : EarleyBins T N n) : Nat :=
  bins.map (fun bin => bin.length) |>.sum

def sizePointer (p : Pointer) : Nat :=
  match p with
  | .null | .predecessor _ => 1
  | .reduction _ ps => 1 + ps.length

def sizePointers {N : Type} {n : Nat} (bins : EarleyBins T N n) : Nat :=
  bins.map (fun bin => bin.map (fun item => sizePointer item.pointer) |>.sum) |>.sum

def benchRecognizer {N : Type} [BEq N] [LawfulBEq (Earley.Model.EarleyItem T N)]
    (G : ContextFreeGrammarList T N) (numChars : UInt32) : IO Unit := do
  let w ← IO.lazyPure (fun () => List.replicate numChars.toNat T.a)
  let t1 ← IO.monoMsNow
  let ⟨bins, _⟩ ← IO.lazyPure (fun () => earleyList G w)
  let t2 ← IO.monoMsNow
  let binSize ← IO.lazyPure (fun () => sizeBins bins)
  let pointerSize ← IO.lazyPure (fun () => sizePointers bins)
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
  match grammarIdx with
  --S -> SS | a
  | 1 => benchRecognizer ⟨N1.S, [rule0, rule1], by simp [rule0, rule1]⟩ numChars
  --S -> aS | a
  | 2 => benchRecognizer ⟨N1.S, [rule0, rule2], by simp [rule0, rule2]⟩ numChars
  --S -> aSa | a
  | 3 => benchRecognizer ⟨N1.S, [rule0, rule3], by simp [rule0, rule3]⟩ numChars
  --S -> Sa | a
  | 4 => benchRecognizer ⟨N1.S, [rule0, rule4], by simp [rule0, rule4]⟩ numChars
  --S -> SX | a, X -> Y | Z, Y -> a, Z -> a
  | 5 =>
    let G := {
      initial := N2.S,
      rules := [rule5, rule6, rule7, rule8, rule9, rule10],
      nodup := by simp [rule5, rule6, rule7, rule8, rule9, rule10]
    }
    benchRecognizer G numChars
  | _ => IO.println s!"No controlflow for grammarIdx={grammarIdx}"
  return 0
