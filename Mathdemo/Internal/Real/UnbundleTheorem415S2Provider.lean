import Mathdemo.Internal.Real.DirectLocalSplitDataTheorem4
import Mathdemo.Internal.Sec4.S2StandardOuterBridge

set_option linter.style.longLine false

/-!
# G245: unbundle the theorem-4.15 S2 provider frontier

G244 gives the preferred endpoint for theorem 4.15: source-shaped S2 data,
direct local split data, local full-set `I_B`, and PFun convergence.

This file does not prove new lower mathematics.  It makes the remaining
source-shaped provider frontier explicit by replacing the bundled
`Sec4GeneralIBSourceS2StandardOuterProvider` input with its five concrete
source components: row-to-flat, characteristic-domain witnesses, standard S1
outer data, S2 rows, and S2 outer data.
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
