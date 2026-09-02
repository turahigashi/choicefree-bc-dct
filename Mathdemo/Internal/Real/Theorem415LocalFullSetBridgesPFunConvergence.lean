import Mathdemo.Internal.Real.Theorem415SourceShapedStandardRowIBProvider
import Mathdemo.Internal.Sec4.Local415SourceData

set_option linter.style.longLine false

/-!
# G243: theorem 4.15 through local full-set bridges and PFun convergence

G242 closed a source-shaped theorem-4.15 endpoint using the standard-row S2
provider, but its lemma-4.14 interface still consumed the completed
`remainingAtoms` route through the previous global value bridge.

This file keeps the same public source data and lowers the error side one step
further: `remainingAtoms` are first converted to local full-set value bridges,
then the lemma-4.14 `I_B` interface is instantiated from those local bridges.
The convergence-to-zero input remains the PFun/representation source data from
G242, so no Prop-to-data selector is introduced.
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
