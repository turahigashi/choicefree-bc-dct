import Mathdemo.Internal.Real.CRealQuotientAdditiveAlgebraLaws

/-!
# CReal common-bound distributivity estimates

This file starts Phase 11-B proper. It proves the common-bound value-level
estimates needed for left and right distributivity of concrete quotient
multiplication. Pair-specific bound transport to the final quotient laws
remains the next frontier.
-/

namespace BishopCReal
open BishopC
open BishopCRat

/-- A standard bound absorbs a dyadic error at any later index. -/
theorem standard_bound_eps_le_of_ge (A : ScalarMulArchimedeanData)
    (x : RegularSeq) {j r : Nat}
    (hj : standardBoundWith A x + r <= j) :
    Le ((COF.abs (x.val 1) + 1) * eps j) (eps r) := by
  set B : Scalar := COF.abs (x.val 1) + 1
  set s : Nat := standardBoundWith A x
  have hidx : Le (eps j) (eps (s + r)) := eps_le_of_le (by simpa [s] using hj)
  have hidx' : Le (eps j) (eps s * eps r) := by
    rwa [eps_add_mul_local s r] at hidx
  have hBnonneg : Le 0 B := by
    unfold B
    exact BishopC.le_add (scalar_abs_nonneg (x.val 1))
      (scalar_nonneg_of_pos scalarCOFOSeed.one_pos)
  have hleft : Le (B * eps j) (B * (eps s * eps r)) :=
    scalar_mul_le_mul_left hidx' hBnonneg
  have hleft' : Le (B * eps j) ((B * eps s) * eps r) := by
    rwa [show B * (eps s * eps r) = (B * eps s) * eps r from by ring] at hleft
  have hspec : Le (B * eps s) 1 := by
    unfold B s
    exact standardBoundWith_spec_base A x
  have hright : Le ((B * eps s) * eps r) (1 * eps r) :=
    scalar_mul_le_mul_right hspec (eps_nonneg r)
  have hright' : Le ((B * eps s) * eps r) (eps r) := by
    rwa [one_mul] at hright
  exact BishopC.le_trans hleft' hright'

/-- A standard bound absorbs two later dyadic errors into the same output gauge. -/
theorem standard_bound_eps_pair_le_of_ge (A : ScalarMulArchimedeanData)
    (x : RegularSeq) {j l r : Nat}
    (hj : standardBoundWith A x + r <= j)
    (hl : standardBoundWith A x + r <= l) :
    Le ((COF.abs (x.val 1) + 1) * (eps j + eps l)) (eps r + eps r) := by
  have hj' := standard_bound_eps_le_of_ge A x (j := j) (r := r) hj
  have hl' := standard_bound_eps_le_of_ge A x (j := l) (r := r) hl
  have hsum := BishopC.le_add hj' hl'
  rw [show (COF.abs (x.val 1) + 1) * (eps j + eps l) =
      (COF.abs (x.val 1) + 1) * eps j +
      (COF.abs (x.val 1) + 1) * eps l from by ring]
  exact hsum

/-- One product term in the common-bound distributivity comparison. -/
theorem common_bound_product_shift_le_tol (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) {C n : Nat}
    (hxC : standardBoundWith A x <= C) (hyC : standardBoundWith A y <= C) :
    Le (COF.abs (x.val (mulIndexFromBound C n) * y.val (mulIndexFromBound C n + 1) -
        x.val (mulIndexFromBound C (n + 1)) * y.val (mulIndexFromBound C (n + 1))))
      (tol n) := by
  set p : Nat := mulIndexFromBound C n
  set q : Nat := mulIndexFromBound C (n + 1)
  have hx_bound_p : Le (COF.abs (x.val p)) (COF.abs (x.val 1) + 1) := by
    simpa [p] using regular_value_bound_from_one x C n
  have hy_bound_q : Le (COF.abs (y.val q)) (COF.abs (y.val 1) + 1) := by
    simpa [q] using regular_value_bound_from_one y C (n + 1)
  have hdy : Le (COF.abs (y.val (p + 1) - y.val q)) (eps (p + 1) + eps q) :=
    y.regular (p + 1) q
  have hdx : Le (COF.abs (x.val p - x.val q)) (eps p + eps q) :=
    x.regular p q
  have hp_ge_x : standardBoundWith A x + (n + 1) <= p + 1 := by
    have hp : standardBoundWith A x + (n + 1) <= p := by
      simpa [p] using mulIndexFromBound_absorb_le (s := standardBoundWith A x)
        (K := C) (n := n) hxC
    exact Nat.le_trans hp (Nat.le_succ p)
  have hq_ge_x : standardBoundWith A x + (n + 1) <= q := by
    have hq : standardBoundWith A x + ((n + 1) + 1) <= q := by
      simpa [q] using mulIndexFromBound_absorb_le (s := standardBoundWith A x)
        (K := C) (n := n + 1) hxC
    exact Nat.le_trans (by omega) hq
  have hp_ge_y : standardBoundWith A y + (n + 1) <= p := by
    simpa [p] using mulIndexFromBound_absorb_le (s := standardBoundWith A y)
      (K := C) (n := n) hyC
  have hq_ge_y : standardBoundWith A y + (n + 1) <= q := by
    have hq : standardBoundWith A y + ((n + 1) + 1) <= q := by
      simpa [q] using mulIndexFromBound_absorb_le (s := standardBoundWith A y)
        (K := C) (n := n + 1) hyC
    exact Nat.le_trans (by omega) hq
  have term1_step1 : Le
      (COF.abs (x.val p) * COF.abs (y.val (p + 1) - y.val q))
      (COF.abs (x.val p) * (eps (p + 1) + eps q)) :=
    scalar_mul_le_mul_left hdy (scalar_abs_nonneg (x.val p))
  have term1_step2 : Le
      (COF.abs (x.val p) * (eps (p + 1) + eps q))
      ((COF.abs (x.val 1) + 1) * (eps (p + 1) + eps q)) :=
    scalar_mul_le_mul_right hx_bound_p (eps_add_nonneg (p + 1) q)
  have term1_budget : Le
      ((COF.abs (x.val 1) + 1) * (eps (p + 1) + eps q))
      (eps (n + 1) + eps (n + 1)) :=
    standard_bound_eps_pair_le_of_ge A x (j := p + 1) (l := q) (r := n + 1)
      hp_ge_x hq_ge_x
  have hterm1 : Le
      (COF.abs (x.val p) * COF.abs (y.val (p + 1) - y.val q))
      (eps (n + 1) + eps (n + 1)) :=
    BishopC.le_trans term1_step1 (BishopC.le_trans term1_step2 term1_budget)
  have term2_step1 : Le
      (COF.abs (x.val p - x.val q) * COF.abs (y.val q))
      ((eps p + eps q) * COF.abs (y.val q)) :=
    scalar_mul_le_mul_right hdx (scalar_abs_nonneg (y.val q))
  have term2_step2 : Le
      ((eps p + eps q) * COF.abs (y.val q))
      ((eps p + eps q) * (COF.abs (y.val 1) + 1)) :=
    scalar_mul_le_mul_left hy_bound_q (eps_add_nonneg p q)
  have term2_step2' : Le
      ((eps p + eps q) * COF.abs (y.val q))
      ((COF.abs (y.val 1) + 1) * (eps p + eps q)) := by
    rwa [show (eps p + eps q) * (COF.abs (y.val 1) + 1) =
        (COF.abs (y.val 1) + 1) * (eps p + eps q) from by ring] at term2_step2
  have term2_budget : Le
      ((COF.abs (y.val 1) + 1) * (eps p + eps q))
      (eps (n + 1) + eps (n + 1)) :=
    standard_bound_eps_pair_le_of_ge A y (j := p) (l := q) (r := n + 1)
      hp_ge_y hq_ge_y
  have hterm2 : Le
      (COF.abs (x.val p - x.val q) * COF.abs (y.val q))
      (eps (n + 1) + eps (n + 1)) :=
    BishopC.le_trans term2_step1 (BishopC.le_trans term2_step2' term2_budget)
  have hprod := scalar_product_diff_le (x.val p) (x.val q) (y.val (p + 1)) (y.val q)
  have hsum := BishopC.le_add hterm1 hterm2
  have hbudget : Le
      ((eps (n + 1) + eps (n + 1)) + (eps (n + 1) + eps (n + 1))) (tol n) := by
    unfold tol
    rw [eps_succ_add_self n]
    exact BishopC.le_refl (eps n + eps n)
  exact BishopC.le_trans hprod (BishopC.le_trans hsum hbudget)

/-- At a common multiplication bound, left distributivity holds eventually after reindexing. -/
theorem mulValWithBound_common_left_distrib_eventually_with
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C)
    (hzC : standardBoundWith A z <= C) :
    forall k : Nat, exists N : Nat, forall n : Nat, N <= n ->
      Le (COF.abs (mulValWithBound C x.val (addVal y.val z.val) n -
        addVal (mulValWithBound C x.val y.val) (mulValWithBound C x.val z.val) n))
        (eps k) := by
  intro k
  refine ⟨k + 2, ?_⟩
  intro n hn
  have htol : k + 1 + 1 <= n := by omega
  set p : Nat := mulIndexFromBound C n
  set q : Nat := mulIndexFromBound C (n + 1)
  have hyprod : Le (COF.abs (x.val p * y.val (p + 1) - x.val q * y.val q)) (tol n) := by
    simpa [p, q] using
      common_bound_product_shift_le_tol A x y (C := C) (n := n) hxC hyC
  have hzprod : Le (COF.abs (x.val p * z.val (p + 1) - x.val q * z.val q)) (tol n) := by
    simpa [p, q] using
      common_bound_product_shift_le_tol A x z (C := C) (n := n) hxC hzC
  have htri : Le
      (COF.abs (x.val p * (y.val (p + 1) + z.val (p + 1)) -
        (x.val q * y.val q + x.val q * z.val q)))
      (COF.abs (x.val p * y.val (p + 1) - x.val q * y.val q) +
        COF.abs (x.val p * z.val (p + 1) - x.val q * z.val q)) := by
    have h := scalar_abs_add_le
      (x.val p * y.val (p + 1) - x.val q * y.val q)
      (x.val p * z.val (p + 1) - x.val q * z.val q)
    rwa [show (x.val p * y.val (p + 1) - x.val q * y.val q) +
        (x.val p * z.val (p + 1) - x.val q * z.val q) =
        x.val p * (y.val (p + 1) + z.val (p + 1)) -
          (x.val q * y.val q + x.val q * z.val q) from by ring] at h
  have hsum := BishopC.le_add hyprod hzprod
  have hbudget : Le (tol n + tol n) (eps k) := by
    have htwo := BishopC.le_add
      (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
      (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
    rwa [eps_succ_add_self k] at htwo
  unfold mulValWithBound addVal addIndex
  change Le (COF.abs (x.val p * (y.val (p + 1) + z.val (p + 1)) -
      (x.val q * y.val q + x.val q * z.val q))) (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

/-- Symmetric product-shift estimate, used for right distributivity. -/
theorem common_bound_product_shift_right_le_tol (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) {C n : Nat}
    (hxC : standardBoundWith A x <= C) (hyC : standardBoundWith A y <= C) :
    Le (COF.abs (x.val (mulIndexFromBound C n + 1) * y.val (mulIndexFromBound C n) -
        x.val (mulIndexFromBound C (n + 1)) * y.val (mulIndexFromBound C (n + 1))))
      (tol n) := by
  have h := common_bound_product_shift_le_tol A y x (C := C) (n := n) hyC hxC
  rwa [show y.val (mulIndexFromBound C n) * x.val (mulIndexFromBound C n + 1) -
        y.val (mulIndexFromBound C (n + 1)) * x.val (mulIndexFromBound C (n + 1)) =
      x.val (mulIndexFromBound C n + 1) * y.val (mulIndexFromBound C n) -
        x.val (mulIndexFromBound C (n + 1)) * y.val (mulIndexFromBound C (n + 1)) from by ring] at h

/-- At a common multiplication bound, right distributivity holds eventually after reindexing. -/
theorem mulValWithBound_common_right_distrib_eventually_with
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C)
    (hzC : standardBoundWith A z <= C) :
    forall k : Nat, exists N : Nat, forall n : Nat, N <= n ->
      Le (COF.abs (mulValWithBound C (addVal x.val y.val) z.val n -
        addVal (mulValWithBound C x.val z.val) (mulValWithBound C y.val z.val) n))
        (eps k) := by
  intro k
  refine ⟨k + 2, ?_⟩
  intro n hn
  have htol : k + 1 + 1 <= n := by omega
  set p : Nat := mulIndexFromBound C n
  set q : Nat := mulIndexFromBound C (n + 1)
  have hxprod : Le (COF.abs (x.val (p + 1) * z.val p - x.val q * z.val q)) (tol n) := by
    simpa [p, q] using
      common_bound_product_shift_right_le_tol A x z (C := C) (n := n) hxC hzC
  have hyprod : Le (COF.abs (y.val (p + 1) * z.val p - y.val q * z.val q)) (tol n) := by
    simpa [p, q] using
      common_bound_product_shift_right_le_tol A y z (C := C) (n := n) hyC hzC
  have htri : Le
      (COF.abs ((x.val (p + 1) + y.val (p + 1)) * z.val p -
        (x.val q * z.val q + y.val q * z.val q)))
      (COF.abs (x.val (p + 1) * z.val p - x.val q * z.val q) +
        COF.abs (y.val (p + 1) * z.val p - y.val q * z.val q)) := by
    have h := scalar_abs_add_le
      (x.val (p + 1) * z.val p - x.val q * z.val q)
      (y.val (p + 1) * z.val p - y.val q * z.val q)
    rwa [show (x.val (p + 1) * z.val p - x.val q * z.val q) +
        (y.val (p + 1) * z.val p - y.val q * z.val q) =
        (x.val (p + 1) + y.val (p + 1)) * z.val p -
          (x.val q * z.val q + y.val q * z.val q) from by ring] at h
  have hsum := BishopC.le_add hxprod hyprod
  have hbudget : Le (tol n + tol n) (eps k) := by
    have htwo := BishopC.le_add
      (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
      (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
    rwa [eps_succ_add_self k] at htwo
  unfold mulValWithBound addVal addIndex
  change Le (COF.abs ((x.val (p + 1) + y.val (p + 1)) * z.val p -
      (x.val q * z.val q + y.val q * z.val q))) (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

end BishopCReal

