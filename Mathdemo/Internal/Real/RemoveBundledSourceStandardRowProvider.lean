import Mathdemo.Internal.Real.DeriveGeneralLocalBridgeProviderSource
import Mathdemo.Internal.Sec4.RowToFlat

set_option linter.style.longLine false

/-!
# G271: remove the bundled source standard-row provider from the local route

G270 replaced theorem-specific local bridge data by the existing
`Sec4GeneralIBSourceS2StandardOuterProvider`.  That provider still bundled one
component already proved in the development: the generic `rowToFlat` bridge.

This file fills `rowToFlat` with `sec4_rowToFlat_source` and exposes only the
four source-shaped Proposition-4.2 components still relevant to the direct
measurable representative:

* characteristic-domain witnesses for `χ_A`;
* standard positive-side outer convergence;
* standard negative-side rows;
* standard negative-side outer convergence for those rows.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Rebuild the G270 route from global standard-row components -/



/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
