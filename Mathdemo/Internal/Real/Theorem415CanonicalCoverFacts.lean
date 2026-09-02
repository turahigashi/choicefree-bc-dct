import Mathdemo.Internal.Real.Theorem415LocalFullSetValueBridges
import Mathdemo.Internal.Sec4.CoverChiTelescopeBridge

set_option linter.style.longLine false

/-!
# G247: theorem 4.15 from canonical cover facts

G246 made the theorem-4.15 endpoint consume only local full-set value bridges
for the abs-error sequence.  This file traces that local bridge one definition
layer lower: the public bridge input can now be replaced by the concrete
canonical-cover facts, or by the still lower `χ` telescope data already used
in the chapter-4 `I_B` construction.

The direction is deliberately one-way:

* canonical cover/χ data -> value bridge -> local bridge -> theorem 4.15;
* no attempt is made to recover cover data from a propositional value bridge.

This preserves the Bishop-style discipline: carry the witnesses that the
construction actually uses, and do not extract them from bare membership or
fullness propositions.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route














end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
