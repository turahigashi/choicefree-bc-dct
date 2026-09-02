import Mathdemo.Internal.Real.Theorem415DomainResidualIB

set_option linter.style.longLine false

/-!
# G242: theorem 4.15 through the source-shaped standard-row `I_B` provider

G241 routed theorem 4.15 through the domain-residual provider.  That provider
is useful as a row-seed bridge, but it still packages obligations for arbitrary
row witnesses.

This file adds a more source-shaped theorem-4.15 endpoint.  The error side of
lemma 4.14 is lowered to the completed `remainingAtoms` interface supplied by
`Sec4GeneralIBSourceS2StandardOuterProvider`, whose `A.S1` and `A.S2` outer
obligations are attached to the standard Proposition 4.2 rows.  The majorant
tail is kept on the ordinary relative/complement-integral side, so no row-seed
data for the constructive majorant `g + |f|` is reintroduced.
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
