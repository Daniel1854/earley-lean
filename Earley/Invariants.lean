module
/-!
This module houses the correctness proofs for the Earley Recognizer and Parser

Something like the following?

parser accepts word w given grammar G
<-> word can be generated through a sequence of derivations of Grammar G
    ^apparently this is not something we are interested
(this seems to be implicitly given through the parser anyway since we reconstruct the derivation?)

Rau et Nipkow do it like the following:

input w gets accepted <-> S(|w|) contains a certain final state

So they reason about the soundness of the states huh
-/
namespace Earley
namespace Invariants

end Invariants
end Earley
