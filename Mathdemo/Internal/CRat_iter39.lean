import Mathdemo.Internal.CRat_iter38

/-!
# CReal common-bound multiplication associativity estimates

This file starts the associativity step after quotient distributivity.  The
new issue is nested sampling: `(x*y)*z` samples `x` and `y` at an index obtained
by applying the multiplication index twice, while `z` is sampled once.  The
main result proves that, under a shared bound, the two nested products are
eventually equal.
-/

namespace BishopCReal
open BishopC
open BishopCRat

/-- Product comparison for the two indices that appear in nested common-bound
multiplication. -/
theorem common_bound_nested_product_xz_le_tol (A : ScalarMulArchimedeanData)
    (x z : RegularSeq) {C m n : Nat}
    (hxC : standardBoundWith A x <= C)
    (hzC : standardBoundWith A z <= C)
    (hm : m <= n) :
    Le (COF.abs
      (x.val (mulIndexFromBound C (mulIndexFromBound C n)) *
          z.val (mulIndexFromBound C n) -
        x.val (mulIndexFromBound C n) *
          z.val (mulIndexFromBound C (mulIndexFromBound C n))))
      (tol m) := by
  set p : Nat := mulIndexFromBound C n
  set q : Nat := mulIndexFromBound C p
  have hx_bound_q : Le (COF.abs (x.val q)) (COF.abs (x.val 1) + 1) := by
    simpa [q] using regular_value_bound_from_one x C p
  have hz_bound_q : Le (COF.abs (z.val q)) (COF.abs (z.val 1) + 1) := by
    simpa [q] using regular_value_bound_from_one z C p
  have hdz : Le (COF.abs (z.val p - z.val q)) (eps p + eps q) :=
    z.regular p q
  have hdx : Le (COF.abs (x.val q - x.val p)) (eps q + eps p) :=
    x.regular q p
  have hm_succ : m + 1 <= n + 1 := by omega
  have hp_ge_x : standardBoundWith A x + (m + 1) <= p := by
    have hp : standardBoundWith A x + (n + 1) <= p := by
      simpa [p] using mulIndexFromBound_absorb_le (s := standardBoundWith A x)
        (K := C) (n := n) hxC
    exact Nat.le_trans (Nat.add_le_add_left hm_succ (standardBoundWith A x)) hp
  have hq_ge_x : standardBoundWith A x + (m + 1) <= q := by
    have hpq : p <= q := by
      simpa [q] using le_mulIndexFromBound C p
    exact Nat.le_trans hp_ge_x hpq
  have hp_ge_z : standardBoundWith A z + (m + 1) <= p := by
    have hp : standardBoundWith A z + (n + 1) <= p := by
      simpa [p] using mulIndexFromBound_absorb_le (s := standardBoundWith A z)
        (K := C) (n := n) hzC
    exact Nat.le_trans (Nat.add_le_add_left hm_succ (standardBoundWith A z)) hp
  have hq_ge_z : standardBoundWith A z + (m + 1) <= q := by
    have hpq : p <= q := by
      simpa [q] using le_mulIndexFromBound C p
    exact Nat.le_trans hp_ge_z hpq
  have term1_step1 : Le
      (COF.abs (x.val q) * COF.abs (z.val p - z.val q))
      (COF.abs (x.val q) * (eps p + eps q)) :=
    scalar_mul_le_mul_left hdz (scalar_abs_nonneg (x.val q))
  have term1_step2 : Le
      (COF.abs (x.val q) * (eps p + eps q))
      ((COF.abs (x.val 1) + 1) * (eps p + eps q)) :=
    scalar_mul_le_mul_right hx_bound_q (eps_add_nonneg p q)
  have term1_budget : Le
      ((COF.abs (x.val 1) + 1) * (eps p + eps q))
      (eps (m + 1) + eps (m + 1)) :=
    standard_bound_eps_pair_le_of_ge A x (j := p) (l := q) (r := m + 1)
      hp_ge_x hq_ge_x
  have hterm1 : Le
      (COF.abs (x.val q) * COF.abs (z.val p - z.val q))
      (eps (m + 1) + eps (m + 1)) :=
    BishopC.le_trans term1_step1 (BishopC.le_trans term1_step2 term1_budget)
  have term2_step1 : Le
      (COF.abs (x.val q - x.val p) * COF.abs (z.val q))
      ((eps q + eps p) * COF.abs (z.val q)) :=
    scalar_mul_le_mul_right hdx (scalar_abs_nonneg (z.val q))
  have term2_step2 : Le
      ((eps q + eps p) * COF.abs (z.val q))
      ((eps q + eps p) * (COF.abs (z.val 1) + 1)) :=
    scalar_mul_le_mul_left hz_bound_q (eps_add_nonneg q p)
  have term2_step2' : Le
      ((eps q + eps p) * COF.abs (z.val q))
      ((COF.abs (z.val 1) + 1) * (eps q + eps p)) := by
    rwa [show (eps q + eps p) * (COF.abs (z.val 1) + 1) =
        (COF.abs (z.val 1) + 1) * (eps q + eps p) from by ring] at term2_step2
  have term2_budget : Le
      ((COF.abs (z.val 1) + 1) * (eps q + eps p))
      (eps (m + 1) + eps (m + 1)) :=
    standard_bound_eps_pair_le_of_ge A z (j := q) (l := p) (r := m + 1)
      hq_ge_z hp_ge_z
  have hterm2 : Le
      (COF.abs (x.val q - x.val p) * COF.abs (z.val q))
      (eps (m + 1) + eps (m + 1)) :=
    BishopC.le_trans term2_step1 (BishopC.le_trans term2_step2' term2_budget)
  have hprod := scalar_product_diff_le (x.val q) (x.val p) (z.val p) (z.val q)
  have hsum := BishopC.le_add hterm1 hterm2
  have hbudget : Le
      ((eps (m + 1) + eps (m + 1)) + (eps (m + 1) + eps (m + 1))) (tol m) := by
    unfold tol
    rw [eps_succ_add_self m]
    exact BishopC.le_refl (eps m + eps m)
  exact BishopC.le_trans hprod (BishopC.le_trans hsum hbudget)

/-- At a common multiplication bound, multiplication is associative up to
eventual equality despite nested sampling. -/
theorem mulValWithBound_common_assoc_eventually_with
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (_hyC : standardBoundWith A y <= C)
    (hzC : standardBoundWith A z <= C) :
    forall k : Nat, exists N : Nat, forall n : Nat, N <= n ->
      Le (COF.abs (mulValWithBound C (mulValWithBound C x.val y.val) z.val n -
        mulValWithBound C x.val (mulValWithBound C y.val z.val) n))
        (eps k) := by
  intro k
  set m : Nat := standardBoundWith A y + (k + 1) with hmdef
  refine ⟨m, ?_⟩
  intro n hn
  set p : Nat := mulIndexFromBound C n
  set q : Nat := mulIndexFromBound C p
  have hdiff0 : Le (COF.abs (x.val q * z.val p - x.val p * z.val q)) (tol m) := by
    simpa [p, q] using
      common_bound_nested_product_xz_le_tol A x z (C := C) (m := m) (n := n)
        hxC hzC hn
  have hdiff : Le (COF.abs (x.val q * z.val p - x.val p * z.val q))
      (eps (standardBoundWith A y + k)) := by
    have htol : Le (tol m) (eps (standardBoundWith A y + k)) := by
      unfold tol
      rw [hmdef]
      rw [show standardBoundWith A y + (k + 1) =
          standardBoundWith A y + k + 1 from by omega]
      rw [eps_succ_add_self (standardBoundWith A y + k)]
      exact BishopC.le_refl (eps (standardBoundWith A y + k))
    exact BishopC.le_trans hdiff0 htol
  have hy_bound_q : Le (COF.abs (y.val q)) (COF.abs (y.val 1) + 1) := by
    simpa [q] using regular_value_bound_from_one y C p
  have hmul1 : Le
      (COF.abs (y.val q) * COF.abs (x.val q * z.val p - x.val p * z.val q))
      (COF.abs (y.val q) * eps (standardBoundWith A y + k)) :=
    scalar_mul_le_mul_left hdiff (scalar_abs_nonneg (y.val q))
  have hmul2 : Le
      (COF.abs (y.val q) * eps (standardBoundWith A y + k))
      ((COF.abs (y.val 1) + 1) * eps (standardBoundWith A y + k)) :=
    scalar_mul_le_mul_right hy_bound_q (eps_nonneg (standardBoundWith A y + k))
  have hmul3 : Le
      ((COF.abs (y.val 1) + 1) * eps (standardBoundWith A y + k)) (eps k) :=
    standard_bound_tail_eps_le A y k
  have hmain : Le
      (COF.abs (y.val q) * COF.abs (x.val q * z.val p - x.val p * z.val q))
      (eps k) :=
    BishopC.le_trans hmul1 (BishopC.le_trans hmul2 hmul3)
  unfold mulValWithBound
  change Le (COF.abs ((x.val q * y.val q) * z.val p -
      x.val p * (y.val q * z.val q))) (eps k)
  rw [show (x.val q * y.val q) * z.val p -
      x.val p * (y.val q * z.val q) =
      y.val q * (x.val q * z.val p - x.val p * z.val q) from by ring]
  rw [scalar_abs_mul]
  exact hmain

end BishopCReal

