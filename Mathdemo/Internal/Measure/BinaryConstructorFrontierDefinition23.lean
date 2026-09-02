import Mathdemo.Internal.Measure.ForwardDomainAbsoluteConvergenceTransportConstructor

set_option linter.style.longLine false

/-!
# G290: binary constructor frontier for Definition-2.3 local data

G288 introduced the strong local API `IntegrableSet1WithDef23`, whose
absolute-convergence fields return actual `RSeq.SeriesSum` data.  G289 added
the forward transport lemmas needed by the Chapter-2 binary constructors.

Attempting to build `IntegrableSet1WithDef23 (BSet.or A B)` directly exposes a
constructive boundary: membership in `(A or B).S1` is a Prop-valued disjunction,
whereas `RSeq.SeriesSum` is Type-valued data with a modulus.  Eliminating that
disjunction into `SeriesSum` would be a Prop-to-Type extraction.  This node
therefore records the conservative, choice-free repair: keep domain fields as
ordinary Prop-valued data, and lower the absolute-convergence fields to
`Nonempty (RSeq.SeriesSum ...)`.  The resulting Prop-level API is closed under
the binary constructors without adding choice.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Prop-level Definition-2.3 absolute-convergence API -/



namespace IntegrableSet1WithDef23PropAbs



/-! ## 2. Side extraction for `or` -/









/-! ## 3. Prop-level strengthened `or` constructor -/





/-! ## 4. Side extraction for `and` -/









/-! ## 5. Prop-level strengthened `and` constructor -/





/-! ## 6. Side extraction for relative `sub` -/









/-! ## 7. Prop-level strengthened relative subtraction constructor -/





end IntegrableSet1WithDef23PropAbs

/-! ## 8. Audit -/




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
