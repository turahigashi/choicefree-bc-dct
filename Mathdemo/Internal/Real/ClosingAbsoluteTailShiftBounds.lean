import Mathdemo.Internal.Real.ClosingNonnegativityAbsSeq

set_option linter.style.longLine false

/-!
# G93: closing the absolute-tail shift bounds

G92 left the two displayed scalar bounds behind the source estimates

* `u <= b + |u-b|`;
* `b <= u + |u-b|`.

This file closes them in the source order used by the proof of Theorem 1.18
property (4): first prove the scalar absolute-value nonnegativity tails
`x+|x| >= 0` and `-x+|x| >= 0`, then transport those tails across the
eventual-equality identities for the displayed shifted differences.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}


/-- Representative-level nonnegativity of `-x + |x|`. -/
theorem neg_add_abs_regularSeqNonneg
    (x : RegularSeq) :
    RegularSeqNonneg (addSeq (negSeq x) (absSeq x)) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  have hpoint' : COF.lt (eps k)
      (0 - (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) := by
    simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal,
      addSeq, addVal, addIndex, negSeq, negVal, absSeq, absVal] using hpoint
  have hzero :
      COF.lt (0 : Scalar)
        (0 - (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint'
  have hbad_sum :
      COF.lt (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) 0 := by
    have t :=
      COF.lt_add_left
        (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) hzero
    rwa [show
        (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) + 0 =
          -x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))
        from by ring,
      show
        (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) +
            (0 - (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) =
          0
        from by ring] at t
  have hbad :
      COF.lt (COF.abs (x.val ((N + 1) + 1)) - x.val ((N + 1) + 1)) 0 := by
    rwa [show
        COF.abs (x.val ((N + 1) + 1)) - x.val ((N + 1) + 1) =
          -x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))
        from by ring]
  exact scalar_abs_sub_self_nonneg (x.val ((N + 1) + 1)) hbad


/-- Difference identity for the source-side bound
`u <= b + |u-b|`: `(b+|u-b|)-u = -(u-b)+|u-b|`. -/
theorem self_shift_diff_eventually
    (u b : RegularSeq) :
    relEventually
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq (negSeq (subSeq u b)) (absSeq (subSeq u b))) := by
  have h0 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq (addSeq b (absSeq (subSeq u b))) (negSeq u)) :=
    subSeq_eq_add_neg_eventually
      (addSeq b (absSeq (subSeq u b))) u
  have h1 :
      relEventually
        (addSeq (addSeq b (absSeq (subSeq u b))) (negSeq u))
        (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u))) :=
    addSeq_assoc_eventually b (absSeq (subSeq u b)) (negSeq u)
  have hcomm :
      relEventually
        (addSeq (absSeq (subSeq u b)) (negSeq u))
        (addSeq (negSeq u) (absSeq (subSeq u b))) :=
    addSeq_comm_eventually (absSeq (subSeq u b)) (negSeq u)
  have h2 :
      relEventually
        (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u)))
        (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b)))) :=
    addSeq_respects_eventually
      b b
      (addSeq (absSeq (subSeq u b)) (negSeq u))
      (addSeq (negSeq u) (absSeq (subSeq u b)))
      (relEventually_refl b)
      hcomm
  have h3 :
      relEventually
        (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
        (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b))) :=
    relEventually_symm
      (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
      (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
      (addSeq_assoc_eventually b (negSeq u) (absSeq (subSeq u b)))
  have hleft_sub :
      relEventually
        (addSeq b (negSeq u))
        (subSeq b u) :=
    relEventually_symm
      (subSeq b u)
      (addSeq b (negSeq u))
      (subSeq_eq_add_neg_eventually b u)
  have hleft_neg :
      relEventually
        (subSeq b u)
        (negSeq (subSeq u b)) :=
    subSeq_comm_neg_eventually b u
  have hleft :
      relEventually
        (addSeq b (negSeq u))
        (negSeq (subSeq u b)) :=
    relEventually_trans
      (addSeq b (negSeq u))
      (subSeq b u)
      (negSeq (subSeq u b))
      hleft_sub
      hleft_neg
  have h4 :
      relEventually
        (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
        (addSeq (negSeq (subSeq u b)) (absSeq (subSeq u b))) :=
    addSeq_respects_eventually
      (addSeq b (negSeq u)) (negSeq (subSeq u b))
      (absSeq (subSeq u b)) (absSeq (subSeq u b))
      hleft
      (relEventually_refl (absSeq (subSeq u b)))
  have h01 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u))) :=
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq (addSeq b (absSeq (subSeq u b))) (negSeq u))
      (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u)))
      h0
      h1
  have h012 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b)))) :=
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u)))
      (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
      h01
      h2
  have h0123 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b))) :=
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
      (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
      h012
      h3
  exact
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
      (addSeq (negSeq (subSeq u b)) (absSeq (subSeq u b)))
      h0123
      h4


/-- Source-side displayed bound `u <= b + |u-b|`. -/
theorem self_le_base_plus_abs_tail_regularSeqLe
    (u b : RegularSeq) :
    RegularSeqLe u (addSeq b (absSeq (subSeq u b))) :=
  regularSeqNonneg_of_eventual
    (self_shift_diff_eventually u b)
    (neg_add_abs_regularSeqNonneg (subSeq u b))

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
