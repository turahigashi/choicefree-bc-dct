import Mathdemo.Internal.Real.QuotientMaxMinNonnegativityFields

/-!
# Quotient max/min absolute bounds

`QuotientMaxMinNonnegativityFields` closed the nonnegativity half of the max/min fields.  This file
closes the two remaining max/min absolute-value bounds:

* `max x 0 <= |x|`;
* `-min x 0 <= |x|`.

The only extra issue beyond the scalar half-sum inequalities is index drift:
the quotient max/min representative samples `x` at a multiplication index,
while `absQuot x` samples it at the outer subtraction index.  Regularity of the
representative absorbs that drift by choosing a late enough tail point.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar half-sum form of `max a 0` is bounded by `|a|`. -/
theorem scalar_half_mul_add_abs_le_abs (a : Scalar) :
    Le ((COF.half : Scalar) * (a + COF.abs a)) (COF.abs a) := by
  have hnn : BishopC.Nonneg
      (COF.abs a - ((COF.half : Scalar) * (a + COF.abs a))) := by
    have h := scalar_half_mul_abs_sub_nonneg a
    simpa [show
        COF.abs a - ((COF.half : Scalar) * (a + COF.abs a)) =
          (COF.half : Scalar) * (COF.abs a - a)
        from by
          calc
            COF.abs a - ((COF.half : Scalar) * (a + COF.abs a))
                = 1 * COF.abs a - ((COF.half : Scalar) * (a + COF.abs a)) := by
                    ring
            _ = ((COF.half : Scalar) + COF.half) * COF.abs a -
                  ((COF.half : Scalar) * (a + COF.abs a)) := by
                    rw [COF.half_add_half]
            _ = (COF.half : Scalar) * (COF.abs a - a) := by
                    ring] using h
  exact BishopC.le_of_nonneg_sub hnn

/-- Scalar half-sum form of `-min a 0` is bounded by `|a|`. -/
theorem scalar_half_mul_abs_sub_le_abs (a : Scalar) :
    Le ((COF.half : Scalar) * (COF.abs a - a)) (COF.abs a) := by
  have hnn : BishopC.Nonneg
      (COF.abs a - ((COF.half : Scalar) * (COF.abs a - a))) := by
    have h := scalar_half_mul_add_abs_nonneg a
    simpa [show
        COF.abs a - ((COF.half : Scalar) * (COF.abs a - a)) =
          (COF.half : Scalar) * (a + COF.abs a)
        from by
          calc
            COF.abs a - ((COF.half : Scalar) * (COF.abs a - a))
                = 1 * COF.abs a - ((COF.half : Scalar) * (COF.abs a - a)) := by
                    ring
            _ = ((COF.half : Scalar) + COF.half) * COF.abs a -
                  ((COF.half : Scalar) * (COF.abs a - a)) := by
                    rw [COF.half_add_half]
            _ = (COF.half : Scalar) * (a + COF.abs a) := by
                    ring] using h
  exact BishopC.le_of_nonneg_sub hnn

/-- A scalar absolute-difference bound gives an upper estimate. -/
theorem scalar_le_add_of_abs_diff_le {a b c : Scalar}
    (h : Le (COF.abs (a - b)) c) : Le a (b + c) := by
  have hlow : Le (a - c) b := scalar_point_lower_of_abs_le h
  have hadd := BishopC.le_add hlow (BishopC.le_refl c)
  rwa [show a - c + c = a from by ring] at hadd

/-- Regularity controls the drift between two absolute-value samples. -/
theorem abs_sample_le_abs_add_eps_of_budget
    (x : RegularSeq) {p q k : Nat}
    (hbudget : Le (eps p + eps q) (eps k)) :
    Le (COF.abs (x.val p)) (COF.abs (x.val q) + eps k) := by
  have hrev : Le
      (COF.abs (COF.abs (x.val p) - COF.abs (x.val q)))
      (COF.abs (x.val p - x.val q)) :=
    scalar_abs_abs_sub_abs_le (x.val p) (x.val q)
  have hdist : Le (COF.abs (x.val p - x.val q)) (eps k) :=
    BishopC.le_trans (x.regular p q) hbudget
  exact scalar_le_add_of_abs_diff_le (BishopC.le_trans hrev hdist)

/-- The product sampling index is late enough for the absolute-value comparison
budget used in this file. -/
theorem eps_mul_sample_add_outer_le
    (K n k : Nat) (hkn : k ≤ n) :
    Le (eps (mulIndexFromBound K (n + 1) + 2) + eps (n + 1)) (eps k) := by
  have hpn : n + 1 ≤ mulIndexFromBound K (n + 1) + 2 := by
    rw [mulIndexFromBound_eq_core_succ]
    have hcore := le_mulIndexCoreFromBound K (n + 1)
    omega
  have hp : Le (eps (mulIndexFromBound K (n + 1) + 2)) (eps (n + 1)) :=
    eps_le_of_le hpn
  have hsum := BishopC.le_add hp (BishopC.le_refl (eps (n + 1)))
  have hsum' : Le
      (eps (mulIndexFromBound K (n + 1) + 2) + eps (n + 1)) (eps n) := by
    rwa [eps_succ_add_self n] at hsum
  exact BishopC.le_trans hsum' (eps_le_of_le hkn)

/-- Representative form of `max x 0 <= |x|`. -/
theorem not_posEventually_max_sub_abs_with
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    ¬ PosEventually
      (subSeq
        (mulSeqConcreteWith A halfSeq
          (addSeq (addSeq x zeroSeq)
            (absSeq (addSeq x (negSeq zeroSeq)))))
        (absSeq x)) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  let n : Nat := N + k
  have hNn : N ≤ n := by
    unfold n
    omega
  have hkn : k ≤ n := by
    unfold n
    omega
  have hpoint := hN n hNn
  set K : Nat := mulBoundWith A halfSeq
    (addSeq (addSeq x zeroSeq) (absSeq (addSeq x (negSeq zeroSeq)))) with hKdef
  set m : Nat := mulIndexFromBound K (n + 1) with hmdef
  have hpoint' : COF.lt (eps k)
      (((COF.half : Scalar) *
          (x.val (m + 2) + COF.abs (x.val (m + 2)))) -
        COF.abs (x.val (n + 1))) := by
    simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal,
      mulSeqConcreteWith, mulSeqWith, boundedMulValWith, mulValWithBound,
      halfSeq, halfVal, addSeq, addVal, addIndex, absSeq, absVal, negSeq,
      negVal, hKdef, hmdef, zero_add, add_zero] using hpoint
  have hstrict : COF.lt
      (COF.abs (x.val (n + 1)) + eps k)
      ((COF.half : Scalar) *
        (x.val (m + 2) + COF.abs (x.val (m + 2)))) := by
    have t := COF.lt_add_left (COF.abs (x.val (n + 1))) hpoint'
    rwa [show
        COF.abs (x.val (n + 1)) + eps k =
          COF.abs (x.val (n + 1)) + eps k
        from rfl,
      show
        COF.abs (x.val (n + 1)) +
            (((COF.half : Scalar) *
                (x.val (m + 2) + COF.abs (x.val (m + 2)))) -
              COF.abs (x.val (n + 1))) =
          (COF.half : Scalar) *
            (x.val (m + 2) + COF.abs (x.val (m + 2)))
        from by ring] at t
  have hbudget : Le (eps (m + 2) + eps (n + 1)) (eps k) := by
    rw [hmdef]
    exact eps_mul_sample_add_outer_le K n k hkn
  have hsample : Le (COF.abs (x.val (m + 2)))
      (COF.abs (x.val (n + 1)) + eps k) :=
    abs_sample_le_abs_add_eps_of_budget x hbudget
  have hle : Le
      ((COF.half : Scalar) *
        (x.val (m + 2) + COF.abs (x.val (m + 2))))
      (COF.abs (x.val (n + 1)) + eps k) :=
    BishopC.le_trans (scalar_half_mul_add_abs_le_abs (x.val (m + 2))) hsample
  exact hle hstrict

/-- Representative form of `-min x 0 <= |x|`. -/
theorem not_posEventually_neg_min_sub_abs_with
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    ¬ PosEventually
      (subSeq
        (negSeq
          (mulSeqConcreteWith A halfSeq
            (addSeq (addSeq x zeroSeq)
              (negSeq (absSeq (addSeq x (negSeq zeroSeq)))))))
        (absSeq x)) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  let n : Nat := N + k
  have hNn : N ≤ n := by
    unfold n
    omega
  have hkn : k ≤ n := by
    unfold n
    omega
  have hpoint := hN n hNn
  set K : Nat := mulBoundWith A halfSeq
    (addSeq (addSeq x zeroSeq)
      (negSeq (absSeq (addSeq x (negSeq zeroSeq))))) with hKdef
  set m : Nat := mulIndexFromBound K (n + 1) with hmdef
  have hpoint_raw : COF.lt (eps k)
      (-((COF.half : Scalar) *
          (x.val (m + 2) + -COF.abs (x.val (m + 2)))) +
        -COF.abs (x.val (n + 1))) := by
    simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal,
      mulSeqConcreteWith, mulSeqWith, boundedMulValWith, mulValWithBound,
      halfSeq, halfVal, addSeq, addVal, addIndex, absSeq, absVal, negSeq,
      negVal, hKdef, hmdef, zero_add, add_zero, sub_eq_add_neg] using hpoint
  have hpoint' : COF.lt (eps k)
      (((COF.half : Scalar) *
          (COF.abs (x.val (m + 2)) - x.val (m + 2))) -
        COF.abs (x.val (n + 1))) := by
    rwa [show
        -((COF.half : Scalar) *
            (x.val (m + 2) + -COF.abs (x.val (m + 2)))) +
          -COF.abs (x.val (n + 1)) =
        ((COF.half : Scalar) *
            (COF.abs (x.val (m + 2)) - x.val (m + 2))) -
          COF.abs (x.val (n + 1))
      from by ring] at hpoint_raw
  have hstrict : COF.lt
      (COF.abs (x.val (n + 1)) + eps k)
      ((COF.half : Scalar) *
        (COF.abs (x.val (m + 2)) - x.val (m + 2))) := by
    have t := COF.lt_add_left (COF.abs (x.val (n + 1))) hpoint'
    rwa [show
        COF.abs (x.val (n + 1)) + eps k =
          COF.abs (x.val (n + 1)) + eps k
        from rfl,
      show
        COF.abs (x.val (n + 1)) +
            (((COF.half : Scalar) *
                (COF.abs (x.val (m + 2)) - x.val (m + 2))) -
              COF.abs (x.val (n + 1))) =
          (COF.half : Scalar) *
            (COF.abs (x.val (m + 2)) - x.val (m + 2))
        from by ring] at t
  have hbudget : Le (eps (m + 2) + eps (n + 1)) (eps k) := by
    rw [hmdef]
    exact eps_mul_sample_add_outer_le K n k hkn
  have hsample : Le (COF.abs (x.val (m + 2)))
      (COF.abs (x.val (n + 1)) + eps k) :=
    abs_sample_le_abs_add_eps_of_budget x hbudget
  have hle : Le
      ((COF.half : Scalar) *
        (COF.abs (x.val (m + 2)) - x.val (m + 2)))
      (COF.abs (x.val (n + 1)) + eps k) :=
    BishopC.le_trans (scalar_half_mul_abs_sub_le_abs (x.val (m + 2))) hsample
  exact hle hstrict

/-- Quotient-level `max x 0 <= |x|`. -/
theorem maxQuotCOF_le_abs_with
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    ¬ ltQuot (absQuot x) (maxQuotCOFWith A x zeroQuot) := by
  refine Quotient.inductionOn x ?_
  intro xr
  change ¬ PosEventually
      (subSeq
        (mulSeqConcreteWith A halfSeq
          (addSeq (addSeq xr zeroSeq)
            (absSeq (addSeq xr (negSeq zeroSeq)))))
        (absSeq xr))
  exact not_posEventually_max_sub_abs_with A xr

/-- Quotient-level `-min x 0 <= |x|`. -/
theorem neg_minQuotCOF_le_abs_with
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    ¬ ltQuot (absQuot x) (negQuot (minQuotCOFWith A x zeroQuot)) := by
  refine Quotient.inductionOn x ?_
  intro xr
  change ¬ PosEventually
      (subSeq
        (negSeq
          (mulSeqConcreteWith A halfSeq
            (addSeq (addSeq xr zeroSeq)
              (negSeq (absSeq (addSeq xr (negSeq zeroSeq)))))))
        (absSeq xr))
  exact not_posEventually_neg_min_sub_abs_with A xr






end BishopCReal

