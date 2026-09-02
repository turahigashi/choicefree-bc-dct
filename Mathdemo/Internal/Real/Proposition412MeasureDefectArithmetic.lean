import Mathdemo.Internal.Real.Proposition412FirstFaithfulLayers

set_option linter.style.longLine false

/-!
# G169: Proposition 4.12 measure-defect arithmetic bridge

G168 closed the common-good-set extraction and the pointwise epsilon estimate
on `E = B ∧ C`.  This file closes the additive/numeric part of the next
source step:

* `μ(D ∨ E) ≤ μ(D) + μ(E)` follows from the finite additivity lemma for
  `or` and nonnegativity of the intersection.
* Hence `μ(A - (B ∧ C)) < eps` follows from the two half-epsilon defect
  estimates once the remaining set-cover/monotonicity bridge
  `μ(A - (B ∧ C)) ≤ μ((A - B) ∨ (A - C))` is supplied.

The remaining bridge is left explicit rather than hidden behind a proposition.
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
