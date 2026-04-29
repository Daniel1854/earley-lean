module
public import Mathlib.Computability.ContextFreeGrammar

namespace Earley
namespace EarleyRecognizer
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


end EarleyRecognizer
end Earley
