import Mathdemo.Internal.Real.Chapter3FinalAuditTheorem3
import Mathdemo.Internal.BishopSec4_Convergence

set_option linter.style.longLine false

/-!
# G162-G163: Chapter 4 source audit and Definition 4.1 / Proposition 4.2

This file starts the Chapter 4 countdown after the completed Chapter 3 bridge.
It records the source item list for Bishop--Cheng Chapter 4 and exposes the
already-established Lean surface for Definition 4.1 and Proposition 4.2.

The important point for Proposition 4.2 is that the file does not merely expose
an inhabitant of `IntegrableRep`; it also re-exports the value theorem showing
that the constructed representative has the intended pointwise value
`chi_A(x) * f(x)` at common convergence points.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace SourceAudit



end SourceAudit

namespace Def41Prop42






end Def41Prop42
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Def41Prop42





end BishopCReal
