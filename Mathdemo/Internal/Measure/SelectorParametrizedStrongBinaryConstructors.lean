import Mathdemo.Internal.Measure.TypeCodedSideCertificatesBinaryDefinition

set_option linter.style.longLine false

/-!
# G292: selector-parametrized strong binary constructors

G290 established the choice-free `Nonempty`/Prop-level constructor API.  G291
added Type-coded side certificates that recover actual `SeriesSum` data when a
specific side case is available.

This node puts those pieces together.  It gives strong
`IntegrableSet1WithDef23` constructors for `or`, `and`, and relative `sub`,
but only when the missing disjunctive side case is supplied as explicit Type
data by a selector argument.  The selector is not constructed here; this node
therefore does not perform raw Prop-to-Type extraction and does not add choice.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

namespace IntegrableSet1WithDef23

/-! ## 1. Strong `or` from an explicit positive-side selector -/





/-! ## 2. Strong `and` from an explicit negative-side selector -/





/-! ## 3. Strong relative `sub` from an explicit negative-side selector -/





end IntegrableSet1WithDef23

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
