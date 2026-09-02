import Mathdemo.Internal.Real.SplittingScalarLawsValueIdentificationCore

/-!
# G72: reducing value identification to PFun-level pointwise order

G71 split the final property-(4) scalar laws into value-identification and
core scalar order.  Definition 1.6 already records that `valueAt` agrees with
the first partial-function component.  This file proves and uses that generic
identification.

The remaining frontier is now PFun-level pointwise order:

* large line 735:
  the PFun value of `|min(f,n)-min(g_N,n)|` is bounded by the PFun value of
  `|f-g_N|`;
* small line 743:
  the PFun value of `min(|f|,1/n)` is bounded by the PFun value of the old
  small truncation plus the absolute tail.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqPFun

variable {X : Type}












end BishopRegularSeqPFun

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}









end BishopRegularSeqIntegrableRep


namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}














end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
