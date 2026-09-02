import Mathdemo.Internal.Real.PeelingOffHalfFactorShiftedMin

set_option linter.style.longLine false

/-!
# G117: reducing the shifted-min body identity to a sum identity

G116 left line 743 with the pre-half body identity

`body(x+d,c) ~ body(x,c-d) + d + d`.

This file closes the subtraction/absolute-value transport around that body.
The remaining content is the additive-sum translation

`(x+d)+c ~ (x+(c-d))+(d+d)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Shifting the left input of a subtraction by `s` shifts the result by `s`:
`(a+s)-b = (a-b)+s` over eventual equality. -/
theorem subSeq_add_left_shift_eventually
    (a s b : RegularSeq) :
    relEventually
      (subSeq (addSeq a s) b)
      (addSeq (subSeq a b) s) := by
  have h0 :
      relEventually
        (subSeq (addSeq a s) b)
        (addSeq (addSeq a s) (negSeq b)) :=
    subSeq_eq_add_neg_eventually (addSeq a s) b
  have h1 :
      relEventually
        (addSeq (addSeq a s) (negSeq b))
        (addSeq a (addSeq s (negSeq b))) :=
    addSeq_assoc_eventually a s (negSeq b)
  have hcomm :
      relEventually
        (addSeq s (negSeq b))
        (addSeq (negSeq b) s) :=
    addSeq_comm_eventually s (negSeq b)
  have h2 :
      relEventually
        (addSeq a (addSeq s (negSeq b)))
        (addSeq a (addSeq (negSeq b) s)) :=
    addSeq_respects_eventually
      a a
      (addSeq s (negSeq b)) (addSeq (negSeq b) s)
      (relEventually_refl a)
      hcomm
  have h3 :
      relEventually
        (addSeq a (addSeq (negSeq b) s))
        (addSeq (addSeq a (negSeq b)) s) :=
    relEventually_symm
      (addSeq (addSeq a (negSeq b)) s)
      (addSeq a (addSeq (negSeq b) s))
      (addSeq_assoc_eventually a (negSeq b) s)
  have hleft :
      relEventually
        (addSeq a (negSeq b))
        (subSeq a b) :=
    relEventually_symm
      (subSeq a b)
      (addSeq a (negSeq b))
      (subSeq_eq_add_neg_eventually a b)
  have h4 :
      relEventually
        (addSeq (addSeq a (negSeq b)) s)
        (addSeq (subSeq a b) s) :=
    addSeq_respects_eventually
      (addSeq a (negSeq b)) (subSeq a b)
      s s
      hleft
      (relEventually_refl s)
  exact
    relEventually_trans
      (subSeq (addSeq a s) b)
      (addSeq (addSeq a s) (negSeq b))
      (addSeq (subSeq a b) s)
      h0
      (relEventually_trans
        (addSeq (addSeq a s) (negSeq b))
        (addSeq a (addSeq s (negSeq b)))
        (addSeq (subSeq a b) s)
        h1
        (relEventually_trans
          (addSeq a (addSeq s (negSeq b)))
          (addSeq a (addSeq (negSeq b) s))
          (addSeq (subSeq a b) s)
          h2
          (relEventually_trans
            (addSeq a (addSeq (negSeq b) s))
            (addSeq (addSeq a (negSeq b)) s)
            (addSeq (subSeq a b) s)
            h3
            h4)))

/-- The shifted difference in line 743:
`(x+d)-c = x-(c-d)` over eventual equality. -/
theorem subSeq_add_right_sub_shift_eventually
    (x d c : RegularSeq) :
    relEventually
      (subSeq (addSeq x d) c)
      (subSeq x (subSeq c d)) := by
  have h0 :
      relEventually
        (subSeq (addSeq x d) c)
        (addSeq (addSeq x d) (negSeq c)) :=
    subSeq_eq_add_neg_eventually (addSeq x d) c
  have h1 :
      relEventually
        (addSeq (addSeq x d) (negSeq c))
        (addSeq x (addSeq d (negSeq c))) :=
    addSeq_assoc_eventually x d (negSeq c)
  have hcomm_inner :
      relEventually
        (addSeq d (negSeq c))
        (addSeq (negSeq c) d) :=
    addSeq_comm_eventually d (negSeq c)
  have h2 :
      relEventually
        (addSeq x (addSeq d (negSeq c)))
        (addSeq x (addSeq (negSeq c) d)) :=
    addSeq_respects_eventually
      x x
      (addSeq d (negSeq c)) (addSeq (negSeq c) d)
      (relEventually_refl x)
      hcomm_inner
  have hd_c_to_add :
      relEventually
        (subSeq d c)
        (addSeq (negSeq c) d) := by
    have hdc0 :
        relEventually
          (subSeq d c)
          (addSeq d (negSeq c)) :=
      subSeq_eq_add_neg_eventually d c
    have hdc1 :
        relEventually
          (addSeq d (negSeq c))
          (addSeq (negSeq c) d) :=
      addSeq_comm_eventually d (negSeq c)
    exact
      relEventually_trans
        (subSeq d c)
        (addSeq d (negSeq c))
        (addSeq (negSeq c) d)
        hdc0
        hdc1
  have hadd_to_neg_sub :
      relEventually
        (addSeq (negSeq c) d)
        (negSeq (subSeq c d)) :=
    relEventually_trans
      (addSeq (negSeq c) d)
      (subSeq d c)
      (negSeq (subSeq c d))
      (relEventually_symm
        (subSeq d c)
        (addSeq (negSeq c) d)
        hd_c_to_add)
      (subSeq_comm_neg_eventually d c)
  have h3 :
      relEventually
        (addSeq x (addSeq (negSeq c) d))
        (addSeq x (negSeq (subSeq c d))) :=
    addSeq_respects_eventually
      x x
      (addSeq (negSeq c) d) (negSeq (subSeq c d))
      (relEventually_refl x)
      hadd_to_neg_sub
  have h4 :
      relEventually
        (addSeq x (negSeq (subSeq c d)))
        (subSeq x (subSeq c d)) :=
    relEventually_symm
      (subSeq x (subSeq c d))
      (addSeq x (negSeq (subSeq c d)))
      (subSeq_eq_add_neg_eventually x (subSeq c d))
  exact
    relEventually_trans
      (subSeq (addSeq x d) c)
      (addSeq (addSeq x d) (negSeq c))
      (subSeq x (subSeq c d))
      h0
      (relEventually_trans
        (addSeq (addSeq x d) (negSeq c))
        (addSeq x (addSeq d (negSeq c)))
        (subSeq x (subSeq c d))
        h1
        (relEventually_trans
          (addSeq x (addSeq d (negSeq c)))
          (addSeq x (addSeq (negSeq c) d))
          (subSeq x (subSeq c d))
          h2
          (relEventually_trans
            (addSeq x (addSeq (negSeq c) d))
            (addSeq x (negSeq (subSeq c d)))
            (subSeq x (subSeq c d))
            h3
            h4)))

/-- Once the sum parts are translated, the full pre-half body translation
follows; subtraction shifting and the absolute-value subterm are closed here. -/
theorem minSeqBody_translate_right_eventually_from_sum
    (x d c : RegularSeq)
    (hsum :
      relEventually
        (addSeq (addSeq x d) c)
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))) :
    relEventually
      (minSeqBody (addSeq x d) c)
      (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)) := by
  have hsub :
      relEventually
        (subSeq (addSeq x d) c)
        (subSeq x (subSeq c d)) :=
    subSeq_add_right_sub_shift_eventually x d c
  have habs :
      relEventually
        (absSeq (subSeq (addSeq x d) c))
        (absSeq (subSeq x (subSeq c d))) :=
    absSeq_respects_eventually
      (subSeq (addSeq x d) c)
      (subSeq x (subSeq c d))
      hsub
  have hbody0 :
      relEventually
        (minSeqBody (addSeq x d) c)
        (subSeq
          (addSeq (addSeq x (subSeq c d)) (addSeq d d))
          (absSeq (subSeq x (subSeq c d)))) := by
    unfold minSeqBody
    exact
      subSeq_respects_eventually
        (addSeq (addSeq x d) c)
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))
        (absSeq (subSeq (addSeq x d) c))
        (absSeq (subSeq x (subSeq c d)))
        hsum
        habs
  have hshift :
      relEventually
        (subSeq
          (addSeq (addSeq x (subSeq c d)) (addSeq d d))
          (absSeq (subSeq x (subSeq c d))))
        (addSeq
          (subSeq
            (addSeq x (subSeq c d))
            (absSeq (subSeq x (subSeq c d))))
          (addSeq d d)) :=
    subSeq_add_left_shift_eventually
      (addSeq x (subSeq c d))
      (addSeq d d)
      (absSeq (subSeq x (subSeq c d)))
  change
    relEventually
      (minSeqBody (addSeq x d) c)
      (addSeq
        (subSeq
          (addSeq x (subSeq c d))
          (absSeq (subSeq x (subSeq c d))))
        (addSeq d d))
  exact
    relEventually_trans
      (minSeqBody (addSeq x d) c)
      (subSeq
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))
        (absSeq (subSeq x (subSeq c d))))
      (addSeq
        (subSeq
          (addSeq x (subSeq c d))
          (absSeq (subSeq x (subSeq c d))))
        (addSeq d d))
      hbody0
      hshift

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
