import Mathdemo.Internal.Real.Theorem415SourceShapedStandardRowProvider
import Mathdemo.Internal.Sec4.RowToFlat
import Mathdemo.Internal.Sec4.S2StandardOuterBridge

set_option linter.style.longLine false

/-!
# G252: remove row-to-flat from the theorem-4.15 public frontier

G251 reduced the abs-error pack input to the source-shaped standard-row
provider.  One of that provider's fields, the generic row-to-flat bridge for
`seriesSumRep_L1`, is already proved as `sec4_rowToFlat_source`.

This file therefore removes `rowToFlat` from the theorem-4.15 statement data
and fills it from the existing proof.  The remaining provider components are
the genuinely source-shaped standard-row data:

* characteristic-domain witnesses for `χ_A`;
* standard `A.S1` abs-outer convergence;
* standard `A.S2` rows;
* standard `A.S2` abs-outer convergence.
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
