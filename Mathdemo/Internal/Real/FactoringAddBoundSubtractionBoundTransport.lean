import Mathdemo.Internal.Real.GeneratingLargeAddBoundMinLaws

set_option linter.style.longLine false

/-!
# G89: factoring add-bound to subtraction-bound transport

G88 still kept the bridge

`x <= y + z -> x - y <= z`

as a primitive order input.  This file factors that bridge into:

* monotonicity of `subSeq · y` in the left argument;
* the algebraic cancellation `(y+z)-y = z` over `relEventually`.

The cancellation lemma is proved here from the existing RegularSeq
`relEventually` algebra laws, leaving only the left-subtraction monotonicity
as the new primitive frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Algebraic cancellation over the RegularSeq implementation equality:
subtracting the first summand from `y+z` leaves `z`. -/
theorem subSeq_add_left_cancel_eventually
    (y z : RegularSeq) :
    relEventually (subSeq (addSeq y z) y) z := by
  have h0 :
      relEventually
        (subSeq (addSeq y z) y)
        (addSeq (addSeq y z) (negSeq y)) :=
    subSeq_eq_add_neg_eventually (addSeq y z) y
  have h1 :
      relEventually
        (addSeq (addSeq y z) (negSeq y))
        (addSeq y (addSeq z (negSeq y))) :=
    addSeq_assoc_eventually y z (negSeq y)
  have hcomm_inner :
      relEventually
        (addSeq z (negSeq y))
        (addSeq (negSeq y) z) :=
    addSeq_comm_eventually z (negSeq y)
  have h2 :
      relEventually
        (addSeq y (addSeq z (negSeq y)))
        (addSeq y (addSeq (negSeq y) z)) :=
    addSeq_respects_eventually
      y y
      (addSeq z (negSeq y)) (addSeq (negSeq y) z)
      (relEventually_refl y)
      hcomm_inner
  have h3 :
      relEventually
        (addSeq y (addSeq (negSeq y) z))
        (addSeq (addSeq y (negSeq y)) z) :=
    relEventually_symm
      (addSeq (addSeq y (negSeq y)) z)
      (addSeq y (addSeq (negSeq y) z))
      (addSeq_assoc_eventually y (negSeq y) z)
  have hcancel :
      relEventually (addSeq y (negSeq y)) zeroSeq :=
    addSeq_neg_right_eventually y
  have h4 :
      relEventually
        (addSeq (addSeq y (negSeq y)) z)
        (addSeq zeroSeq z) :=
    addSeq_respects_eventually
      (addSeq y (negSeq y)) zeroSeq
      z z
      hcancel
      (relEventually_refl z)
  have h5 :
      relEventually (addSeq zeroSeq z) z :=
    addSeq_zero_left_eventually z
  exact
    relEventually_trans
      (subSeq (addSeq y z) y)
      (addSeq (addSeq y z) (negSeq y))
      z
      h0
      (relEventually_trans
        (addSeq (addSeq y z) (negSeq y))
        (addSeq y (addSeq z (negSeq y)))
        z
        h1
        (relEventually_trans
          (addSeq y (addSeq z (negSeq y)))
          (addSeq y (addSeq (negSeq y) z))
          z
          h2
          (relEventually_trans
            (addSeq y (addSeq (negSeq y) z))
            (addSeq (addSeq y (negSeq y)) z)
            z
            h3
            (relEventually_trans
              (addSeq (addSeq y (negSeq y)) z)
              (addSeq zeroSeq z)
              z
              h4
              h5))))

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
