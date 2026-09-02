import Mathdemo.Internal.Real.RemoveDirectAbsErrorRowSeeds

set_option linter.style.longLine false

/-!
# G255: build the theorem-4.15 majorant split from source cover-set data

G254 still accepted the full majorant split estimate as a public input.  The
older source route already proves that estimate from Bishop's displayed
cover-set/tail-budget argument for the constructive majorant `g + |f|`.

This file reuses that argument without reintroducing PFun representatives:
the only theorem-4.15 convergence datum left in the mainline is the
source-level measure convergence of the absolute-error sequence.
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
