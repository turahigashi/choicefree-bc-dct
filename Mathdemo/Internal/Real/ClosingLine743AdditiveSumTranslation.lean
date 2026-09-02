import Mathdemo.Internal.Real.ReducingShiftedMinBodyIdentitySum

set_option linter.style.longLine false

/-!
# G118: closing the line-743 additive sum translation

G117 reduced the shifted-min line-743 obligation to the sum identity

`(x+d)+c ~ (x+(c-d))+(d+d)`.

This file closes that identity over `relEventually`, using only the already
available RegularSeq algebra laws.  The property (4) frontier is therefore
reduced to the line-735 left monotonicity of `minSeqWith`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The cancellation needed inside the line-743 sum translation:
`-d + (d+d) = d` over eventual equality. -/
theorem addSeq_neg_left_double_eventually (d : RegularSeq) :
    relEventually (addSeq (negSeq d) (addSeq d d)) d := by
  have hassoc :
      relEventually
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq (negSeq d) (addSeq d d)) :=
    addSeq_assoc_eventually (negSeq d) d d
  have hcancel :
      relEventually
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq zeroSeq d) :=
    addSeq_respects_eventually
      (addSeq (negSeq d) d) zeroSeq
      d d
      (addSeq_neg_left_eventually d)
      (relEventually_refl d)
  have hzero :
      relEventually (addSeq zeroSeq d) d :=
    addSeq_zero_left_eventually d
  exact
    relEventually_trans
      (addSeq (negSeq d) (addSeq d d))
      (addSeq (addSeq (negSeq d) d) d)
      d
      (relEventually_symm
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq (negSeq d) (addSeq d d))
        hassoc)
      (relEventually_trans
        (addSeq (addSeq (negSeq d) d) d)
        (addSeq zeroSeq d)
        d
        hcancel
        hzero)

/-- `c-d + (d+d) = c+d` over eventual equality. -/
theorem addSeq_sub_add_double_eventually (c d : RegularSeq) :
    relEventually
      (addSeq (subSeq c d) (addSeq d d))
      (addSeq c d) := by
  have hsub :
      relEventually
        (subSeq c d)
        (addSeq c (negSeq d)) :=
    subSeq_eq_add_neg_eventually c d
  have h0 :
      relEventually
        (addSeq (subSeq c d) (addSeq d d))
        (addSeq (addSeq c (negSeq d)) (addSeq d d)) :=
    addSeq_respects_eventually
      (subSeq c d) (addSeq c (negSeq d))
      (addSeq d d) (addSeq d d)
      hsub
      (relEventually_refl (addSeq d d))
  have hassoc :
      relEventually
        (addSeq (addSeq c (negSeq d)) (addSeq d d))
        (addSeq c (addSeq (negSeq d) (addSeq d d))) :=
    addSeq_assoc_eventually c (negSeq d) (addSeq d d)
  have hinner :
      relEventually
        (addSeq (negSeq d) (addSeq d d))
        d :=
    addSeq_neg_left_double_eventually d
  have h1 :
      relEventually
        (addSeq c (addSeq (negSeq d) (addSeq d d)))
        (addSeq c d) :=
    addSeq_respects_eventually
      c c
      (addSeq (negSeq d) (addSeq d d)) d
      (relEventually_refl c)
      hinner
  exact
    relEventually_trans
      (addSeq (subSeq c d) (addSeq d d))
      (addSeq (addSeq c (negSeq d)) (addSeq d d))
      (addSeq c d)
      h0
      (relEventually_trans
        (addSeq (addSeq c (negSeq d)) (addSeq d d))
        (addSeq c (addSeq (negSeq d) (addSeq d d)))
        (addSeq c d)
        hassoc
        h1)

/-- The G117 additive sum translation is closed:
`(x+d)+c = (x+(c-d))+(d+d)` over eventual equality. -/
theorem minSeqSum_translate_right_eventually
    (x d c : RegularSeq) :
    relEventually
      (addSeq (addSeq x d) c)
      (addSeq (addSeq x (subSeq c d)) (addSeq d d)) := by
  have h0 :
      relEventually
        (addSeq (addSeq x d) c)
        (addSeq x (addSeq d c)) :=
    addSeq_assoc_eventually x d c
  have hcomm :
      relEventually
        (addSeq d c)
        (addSeq c d) :=
    addSeq_comm_eventually d c
  have h1 :
      relEventually
        (addSeq x (addSeq d c))
        (addSeq x (addSeq c d)) :=
    addSeq_respects_eventually
      x x
      (addSeq d c) (addSeq c d)
      (relEventually_refl x)
      hcomm
  have hinner :
      relEventually
        (addSeq c d)
        (addSeq (subSeq c d) (addSeq d d)) :=
    relEventually_symm
      (addSeq (subSeq c d) (addSeq d d))
      (addSeq c d)
      (addSeq_sub_add_double_eventually c d)
  have h2 :
      relEventually
        (addSeq x (addSeq c d))
        (addSeq x (addSeq (subSeq c d) (addSeq d d))) :=
    addSeq_respects_eventually
      x x
      (addSeq c d) (addSeq (subSeq c d) (addSeq d d))
      (relEventually_refl x)
      hinner
  have hassocR :
      relEventually
        (addSeq x (addSeq (subSeq c d) (addSeq d d)))
        (addSeq (addSeq x (subSeq c d)) (addSeq d d)) :=
    relEventually_symm
      (addSeq (addSeq x (subSeq c d)) (addSeq d d))
      (addSeq x (addSeq (subSeq c d) (addSeq d d)))
      (addSeq_assoc_eventually x (subSeq c d) (addSeq d d))
  exact
    relEventually_trans
      (addSeq (addSeq x d) c)
      (addSeq x (addSeq d c))
      (addSeq (addSeq x (subSeq c d)) (addSeq d d))
      h0
      (relEventually_trans
        (addSeq x (addSeq d c))
        (addSeq x (addSeq c d))
        (addSeq (addSeq x (subSeq c d)) (addSeq d d))
        h1
        (relEventually_trans
          (addSeq x (addSeq c d))
          (addSeq x (addSeq (subSeq c d) (addSeq d d)))
          (addSeq (addSeq x (subSeq c d)) (addSeq d d))
          h2
          hassocR))

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}







end BishopRegularSeqTheorem118





end BishopCReal
