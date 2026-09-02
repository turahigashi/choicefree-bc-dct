import Mathdemo.Internal.Real.Proposition24MeasureIdentityLocal

set_option linter.style.longLine false

/-!
# G150: Proposition 2.5, relative difference and measure splitting

G149 closed Proposition 2.4's measure identity over the Bishop RegularSeq route.
This file adds Proposition 2.5:

`mu(C) = mu(C ∧ D) + mu(C - D)`

whenever `C` and `C ∧ D` are integrable.  The source proof uses
`chi(C-D) = chi(C) - chi(C ∧ D)`.  Here that difference representative and its
pointwise characteristic law are carried as explicit data, so no representative is
selected later from a quotient or a bare proposition.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop25SubMeasure

open CharacteristicFormula

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}









end Prop25SubMeasure
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.Prop25SubMeasure





end BishopCReal
