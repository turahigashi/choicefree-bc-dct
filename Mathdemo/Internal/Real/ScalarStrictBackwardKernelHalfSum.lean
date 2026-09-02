import Mathdemo.Internal.Real.StrictBackwardTransportRemainingMinMonotonicity

set_option linter.style.longLine false

/-!
# G122: scalar strict-backward kernel for the half-sum minimum

G121 reduced the remaining line-735 `RegularSeqLe` min monotonicity target to
strict-backward transport.  This file closes the scalar pointwise kernel:

`eps k < min(a,c) - min(b,c)` implies `eps k < a - b`,

where `min` is the Bishop half-sum expression.  The remaining work after this
file is only the transport of this scalar kernel through the concrete
`minSeqWith` representative and its bounded multiplication sampling indices.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- If a positive dyadic lies below the positive part `half * (d + |d|)`, then
it already lies below `d`. -/
theorem scalar_eps_lt_half_add_abs_implies_eps_lt
    (d : Scalar) {k : Nat}
    (h : COF.lt (eps k)
      ((COF.half : Scalar) * (d + COF.abs d))) :
    COF.lt (eps k) d := by
  have hsum0 :
      COF.lt (eps k + eps k)
        (((COF.half : Scalar) * (d + COF.abs d)) +
          ((COF.half : Scalar) * (d + COF.abs d))) :=
    scalar_lt_add h h
  have hhalf :
      ((COF.half : Scalar) * (d + COF.abs d)) +
          ((COF.half : Scalar) * (d + COF.abs d)) =
        d + COF.abs d := by
    rw [show
        ((COF.half : Scalar) * (d + COF.abs d)) +
            ((COF.half : Scalar) * (d + COF.abs d)) =
          ((COF.half : Scalar) + COF.half) * (d + COF.abs d)
        from by ring, COF.half_add_half]
    ring
  have hsum : COF.lt (eps k + eps k) (d + COF.abs d) := by
    rwa [hhalf] at hsum0
  rcases scalar_lt_split_add (e := eps k) (u := d) (v := COF.abs d) hsum
    with hd | habs
  · exact hd
  · rcases scalar_eps_lt_abs_split_lower habs with hd | hneg
    · exact hd
    · have hzero_negd : COF.lt (0 : Scalar) (-d) :=
        scalarCOFOSeed.lt_trans (eps_pos k) hneg
      have hnotneg_negd : ¬ COF.lt (-d) 0 := by
        intro hlt
        exact COF.lt_irrefl (0 : Scalar)
          (scalarCOFOSeed.lt_trans hzero_negd hlt)
      have habs_eq_neg : COF.abs d = -d := by
        change BishopCRat.CRat.absF d = -d
        rw [← scalarCOFOSeed.abs_neg d]
        exact scalarCOFOSeed.abs_of_nonneg hnotneg_negd
      have hbad : COF.lt (eps k + eps k) (0 : Scalar) := by
        rwa [habs_eq_neg, show d + -d = (0 : Scalar) from by ring] at hsum
      have hpossum : COF.lt (0 : Scalar) (eps k + eps k) := by
        have hp := scalar_lt_add (eps_pos k) (eps_pos k)
        rwa [zero_add] at hp
      exact False.elim
        (COF.lt_irrefl (0 : Scalar)
          (scalarCOFOSeed.lt_trans hpossum hbad))

/-- The half-sum min difference is bounded above by the positive part of the
left input difference. -/
theorem scalar_min_halfsum_left_difference_le_pospart
    (a b c : Scalar) :
    Le
      (((COF.half : Scalar) * (a + c - COF.abs (a - c))) -
        ((COF.half : Scalar) * (b + c - COF.abs (b - c))))
      ((COF.half : Scalar) * ((a - b) + COF.abs (a - b))) := by
  have hgap_abs :
      Le
        (COF.abs (COF.abs (b - c) - COF.abs (a - c)))
        (COF.abs ((b - c) - (a - c))) :=
    scalar_abs_abs_sub_abs_le (b - c) (a - c)
  have hgap_self :
      Le
        (COF.abs (b - c) - COF.abs (a - c))
        (COF.abs (COF.abs (b - c) - COF.abs (a - c))) := by
    change ¬ COF.lt
      (COF.abs (COF.abs (b - c) - COF.abs (a - c)))
      (COF.abs (b - c) - COF.abs (a - c))
    exact scalarCOFOSeed.le_abs_self
      (COF.abs (b - c) - COF.abs (a - c))
  have hgap :
      Le (COF.abs (b - c) - COF.abs (a - c)) (COF.abs (a - b)) := by
    have h0 : Le
        (COF.abs (b - c) - COF.abs (a - c))
        (COF.abs ((b - c) - (a - c))) :=
      BishopC.le_trans hgap_self hgap_abs
    rw [show (b - c) - (a - c) = -(a - b) from by ring,
      show COF.abs (-(a - b)) = COF.abs (a - b) from by
        change BishopCRat.CRat.absF (-(a - b)) =
          BishopCRat.CRat.absF (a - b)
        exact scalarCOFOSeed.abs_neg (a - b)] at h0
    exact h0
  have hinner :
      Le
        ((a + c - COF.abs (a - c)) -
          (b + c - COF.abs (b - c)))
        ((a - b) + COF.abs (a - b)) := by
    have hadd := BishopC.le_add (BishopC.le_refl (a - b)) hgap
    rwa [show
        (a - b) + (COF.abs (b - c) - COF.abs (a - c)) =
          (a + c - COF.abs (a - c)) -
            (b + c - COF.abs (b - c))
        from by ring] at hadd
  have hmul :
      Le
        ((COF.half : Scalar) *
          ((a + c - COF.abs (a - c)) -
            (b + c - COF.abs (b - c))))
        ((COF.half : Scalar) * ((a - b) + COF.abs (a - b))) :=
    scalar_mul_le_mul_left hinner
      (scalar_nonneg_of_pos scalarCOFOSeed.half_pos)
  rwa [show
      (COF.half : Scalar) *
          ((a + c - COF.abs (a - c)) -
            (b + c - COF.abs (b - c))) =
        ((COF.half : Scalar) * (a + c - COF.abs (a - c))) -
          ((COF.half : Scalar) * (b + c - COF.abs (b - c)))
      from by ring] at hmul

/-- Scalar strict-backward kernel for the half-sum minimum in the left input. -/
theorem scalar_min_halfsum_left_strict_backward
    (a b c : Scalar) {k : Nat}
    (h : COF.lt (eps k)
      (((COF.half : Scalar) * (a + c - COF.abs (a - c))) -
        ((COF.half : Scalar) * (b + c - COF.abs (b - c))))) :
    COF.lt (eps k) (a - b) := by
  have hle := scalar_min_halfsum_left_difference_le_pospart a b c
  have hpospart :
      COF.lt (eps k)
        ((COF.half : Scalar) * ((a - b) + COF.abs (a - b))) :=
    BishopC.lt_of_lt_of_le h hle
  exact scalar_eps_lt_half_add_abs_implies_eps_lt (a - b) hpospart

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}





end BishopRegularSeqTheorem118





end BishopCReal
