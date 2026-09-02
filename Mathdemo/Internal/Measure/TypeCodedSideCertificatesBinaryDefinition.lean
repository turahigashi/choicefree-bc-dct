import Mathdemo.Internal.Measure.BinaryConstructorFrontierDefinition23

set_option linter.style.longLine false

/-!
# G291: Type-coded side certificates for binary Definition-2.3 data

G290 showed the obstruction: a raw proof `x in (A or B).S1` is Prop-valued and
cannot be case-split to produce concrete `RSeq.SeriesSum` data.  This node adds
the constructive replacement for places that truly need Type data: explicit
Type-coded side certificates for the disjunctive sides of the binary
constructors.

With these certificates, actual domain and absolute-convergence data can be
transported without choice.  This does not yet rewrite the broad
`IntegrableSet1` structure; it records the source-faithful interface needed for
the next refactor.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Type-coded side certificates -/







namespace OrS1Case















end OrS1Case

namespace AndS2Case















end AndS2Case

namespace SubS2Case















end SubS2Case

/-! ## 2. Audit -/




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
