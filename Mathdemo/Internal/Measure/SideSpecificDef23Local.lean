import Mathdemo.Internal.Measure.Definition23LocalWitnessesProposition

set_option linter.style.longLine false

/-!
# G285: side-specific Def.2.3 local outer surface

G284 connected the Def.2.3/Def.1.6 local witnesses to the flat-value lemmas
under a general local outer provider.  This file narrows that frontier to the
source-shaped side-specific form actually used in the printed Proposition 4.2
argument:

* on `A.S1`, use the positive-side membership together with the local
  Definition-1.6 witness for `f`;
* on `A.S2`, use the negative-side membership together with the same kind of
  local `f` witness.

Thus the remaining analytic theorem is not an arbitrary
membership-to-witness selector.  It is precisely the f-cut/standard-lambda-row
outer absolute convergence for the explicit local witnesses.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Side-specific local outer frontier -/



/-! ## 2. Side-specific abs packages -/





/-! ## 3. Side-specific flat abs and value statements -/









/-! ## 4. Audit -/




end BishopC

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
