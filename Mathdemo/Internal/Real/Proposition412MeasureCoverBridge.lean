import Mathdemo.Internal.Real.Proposition412MeasureDefectArithmetic

set_option linter.style.longLine false

/-!
# G170: Proposition 4.12 measure cover bridge

G169 reduced the measure-defect estimate in Proposition 4.12 to the exact
cover-monotonicity bridge

`μ(A - (B ∧ C)) ≤ μ((A - B) ∨ (A - C))`.

This file closes that bridge in the representation-carrying style:

* first prove the concrete `S1` cover
  `(A - (B ∧ C)).S1 ⊆ ((A - B) ∨ (A - C)).S1`;
* then prove a `measure1` monotonicity lemma from `S1` inclusion, using the
  `IntegrableSet1.valid` data and `prop_1_11`;
* finally combine the cover with G169's additive half-epsilon estimate.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace MeasureDefectBridge







end MeasureDefectBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.MeasureDefectBridge





end BishopCReal
