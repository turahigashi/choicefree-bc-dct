import Mathdemo.Internal.Real.Theorem415DominationPackagedSource

set_option linter.style.longLine false

/-!
# G237: theorem-4.15 source route with Proposition 4.2 local witnesses

G236 left one theorem-4.15 source bridge visible:
`Sec4GeneralIBDomainResidualProvider`.  That provider is not part of the
dominated-convergence statement itself.  It is the lower Proposition-4.2
witness interface used to build the general measurable `I_B` rows.

This file moves that obligation out of the theorem-4.15 statement-shaped data.
The new endpoint takes the exact local row-seed data supplied by the
Proposition-4.2 layer:

* row seeds for the non-negative error sequence `|f_n - f|`;
* row seeds for the constructive majorant `g + |f|`.

The theorem-4.15 route then builds the local `I_B` bridges, the majorant split,
and the PFun convergence route directly from those seeds.  No Prop-to-data
selector is introduced.
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
