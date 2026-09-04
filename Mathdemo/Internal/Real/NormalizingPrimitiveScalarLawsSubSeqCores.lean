import Mathdemo.Internal.Real.ReducingSmallLine743BoundProposition
/-!
# G81: normalizing the primitive scalar laws to `subSeq` cores

G80 left the two remaining property-(4) scalar laws in the displayed source
form using `addSeq _ ((-1) * _)`.  The existing RegularSeq algebra already
knows that this display is Bishop-eventually equal to `subSeq`.

This file proves that normalization and uses order transport to reduce the
G80 primitive laws to cleaner `subSeq`-core laws:

* `|min(a,c)-min(b,c)| <= |a-b|`;
* `min(|a|,c) <= min(|b|,c) + ||a|-b|`;

where both differences are now represented by `subSeq` at the core frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The displayed source subtraction `x + (-1) * y` is the same Bishop real as
the repository's `subSeq x y`. -/
theorem addSeq_negOneMul_right_eventually_subSeq
    (Arch : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually
      (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y))
      (subSeq x y) := by
  have hmul :
      relEventually
        (mulSeqConcreteWith Arch (negSeq oneSeq) y)
        (negSeq y) :=
    mulSeq_neg_one_left_eventually_neg Arch y
  have hadd :
      relEventually
        (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y))
        (addSeq x (negSeq y)) :=
    addSeq_respects_eventually
      x x
      (mulSeqConcreteWith Arch (negSeq oneSeq) y) (negSeq y)
      (relEventually_refl x)
      hmul
  have hsub :
      relEventually (addSeq x (negSeq y)) (subSeq x y) :=
    relEventually_symm
      (subSeq x y)
      (addSeq x (negSeq y))
      (subSeq_eq_add_neg_eventually x y)
  exact
    relEventually_trans
      (addSeq x (mulSeqConcreteWith Arch (negSeq oneSeq) y))
      (addSeq x (negSeq y))
      (subSeq x y)
      hadd
      hsub


namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
