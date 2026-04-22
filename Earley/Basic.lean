import Earley.ContextFreeGrammars
import Mathlib.Computability.ContextFreeGrammar

/-!
This module contains the API for the Earley Recognizer
together with basic operations on top of it.
Maybe separate the Recognizer from the Parser Implementation actually. No need to have it
Unclear what this library wants to do yet. TODO
-/
namespace Earley

/--
An EarleyItem

I want to be able to see the dotted (maybe use @?) notation in my repr for an EarleyItem
prob should have some sanity check tests for that though
-/
structure EarleyItem (N T : Type) where
  rule : ContextFreeRule N T


/--
tail recursive helper
-/
def reconize_aux : Bool := sorry

/--
Checks whether the input is in the language defined by the grammar
-/
def earley_recognize {N T : Type} (w : Symbol T N) (cfg : ContextFreeGrammar T) : Bool := sorry


end Earley
