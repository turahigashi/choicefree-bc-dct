import Mathdemo.Internal.Measure.SequenceSurfacesFiniteProposition210

set_option linter.style.longLine false

/-!
# G297: base Proposition-2.10 wrappers from Def23 input

G296 prepared strong Definition-2.3 data for the finite increment families.
The existing Proposition 2.10 constructors in Chapter 2 still return the older
`IntegrableSet1` API.  This node adds thin wrappers that accept
`IntegrableSet1WithDef23` hypotheses and pass their `.base` fields to the
existing countable union/intersection constructions.

This is intentionally a base-output bridge.  It does not claim a strong
`IntegrableSet1WithDef23` result for `BSet.bigOr A` or `BSet.bigAnd A`; that
would still require the countable-side domain and absolute-convergence
witnesses for the final representative.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Countable union base wrapper -/







/-! ## 2. Countable intersection base wrapper -/





/-! ## 3. Audit -/




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
