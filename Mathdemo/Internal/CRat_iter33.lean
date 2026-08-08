import Mathdemo.Internal.CRat_iter32

/-!
# CReal bounded multiplication eventual respect

This file closes the second half of the Phase 10 multiplication closure data.
The proof compares two bounded-product representatives by moving both products
to a common explicit multiplication bound, applying eventual equality at that
common sample index, and then moving back to the original pairwise bounds.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A standard bound absorbs any fixed tail gauge. -/
theorem standard_bound_tail_eps_le (A : ScalarMulArchimedeanData)
    (x : RegularSeq) (r : Nat) :
    Le ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x + r)) (eps r) := by
  set B : Scalar := COF.abs (x.val 1) + 1
  set s : Nat := standardBoundWith A x
  have hidx : eps (s + r) = eps s * eps r := eps_add_mul_local s r
  have hrew : B * eps (s + r) = (B * eps s) * eps r := by
    rw [hidx]
    ring
  have hspec : Le (B * eps s) 1 := by
    unfold B s
    exact standardBoundWith_spec_base A x
  have hmul : Le ((B * eps s) * eps r) (1 * eps r) :=
    scalar_mul_le_mul_right hspec (eps_nonneg r)
  have hmul' : Le ((B * eps s) * eps r) (eps r) := by
    rwa [one_mul] at hmul
  rwa [hrew]

/-- A standard bound absorbs dyadic errors sampled at two possibly different
multiplication bounds. -/
theorem standard_bound_eps_two_bounds_le (A : ScalarMulArchimedeanData)
    (x : RegularSeq) {K L n : Nat}
    (hxK : standardBoundWith A x ≤ K) (hxL : standardBoundWith A x ≤ L) :
    Le ((COF.abs (x.val 1) + 1) *
        (eps (mulIndexFromBound K n) + eps (mulIndexFromBound L n)))
      (eps (n + 1) + eps (n + 1)) := by
  have hK := standard_bound_mul_eps_le A x (K := K) (n := n) hxK
  have hL := standard_bound_mul_eps_le A x (K := L) (n := n) hxL
  have hsum := BishopC.le_add hK hL
  rw [show (COF.abs (x.val 1) + 1) *
        (eps (mulIndexFromBound K n) + eps (mulIndexFromBound L n)) =
      (COF.abs (x.val 1) + 1) * eps (mulIndexFromBound K n) +
        (COF.abs (x.val 1) + 1) * eps (mulIndexFromBound L n) from by ring]
  exact hsum

/-- Changing the explicit multiplication bound changes a product representative
by at most the raw pointwise tolerance at the output index. -/
theorem mulValWithBound_change_le_tol (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) {K L n : Nat}
    (hxK : standardBoundWith A x ≤ K) (hxL : standardBoundWith A x ≤ L)
    (hyK : standardBoundWith A y ≤ K) (hyL : standardBoundWith A y ≤ L) :
    Le (COF.abs (mulValWithBound K x.val y.val n -
        mulValWithBound L x.val y.val n)) (tol n) := by
  unfold mulValWithBound
  set p : Nat := mulIndexFromBound K n
  set q : Nat := mulIndexFromBound L n
  have hx_bound_p : Le (COF.abs (x.val p)) (COF.abs (x.val 1) + 1) := by
    simpa [p] using regular_value_bound_from_one x K n
  have hy_bound_q : Le (COF.abs (y.val q)) (COF.abs (y.val 1) + 1) := by
    simpa [q] using regular_value_bound_from_one y L n
  have hdy : Le (COF.abs (y.val p - y.val q)) (eps p + eps q) :=
    y.regular p q
  have hdx : Le (COF.abs (x.val p - x.val q)) (eps p + eps q) :=
    x.regular p q
  have term1_step1 : Le
      (COF.abs (x.val p) * COF.abs (y.val p - y.val q))
      (COF.abs (x.val p) * (eps p + eps q)) :=
    scalar_mul_le_mul_left hdy (scalar_abs_nonneg (x.val p))
  have term1_step2 : Le
      (COF.abs (x.val p) * (eps p + eps q))
      ((COF.abs (x.val 1) + 1) * (eps p + eps q)) :=
    scalar_mul_le_mul_right hx_bound_p (eps_add_nonneg p q)
  have term1_budget : Le
      ((COF.abs (x.val 1) + 1) * (eps p + eps q))
      (eps (n + 1) + eps (n + 1)) := by
    simpa [p, q] using
      standard_bound_eps_two_bounds_le A x (K := K) (L := L) (n := n) hxK hxL
  have hterm1 : Le
      (COF.abs (x.val p) * COF.abs (y.val p - y.val q))
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
      (eps (n + 1) + eps (n + 1)) := by
    simpa [p, q] using
      standard_bound_eps_two_bounds_le A y (K := K) (L := L) (n := n) hyK hyL
  have hterm2 : Le
      (COF.abs (x.val p - x.val q) * COF.abs (y.val q))
      (eps (n + 1) + eps (n + 1)) :=
    BishopC.le_trans term2_step1 (BishopC.le_trans term2_step2' term2_budget)
  have hprod := scalar_product_diff_le (x.val p) (x.val q) (y.val p) (y.val q)
  have hsum := BishopC.le_add hterm1 hterm2
  have hbudget : Le
      ((eps (n + 1) + eps (n + 1)) + (eps (n + 1) + eps (n + 1))) (tol n) := by
    unfold tol
    rw [eps_succ_add_self n]
    exact BishopC.le_refl (eps n + eps n)
  exact BishopC.le_trans hprod (BishopC.le_trans hsum hbudget)

/-- Product representatives with a common multiplication bound respect close
inputs at the common sampled index. -/
theorem mulValWithBound_common_respects_point (A : ScalarMulArchimedeanData)
    (x x' y y' : RegularSeq) (C k n : Nat)
    (hcx : Le (COF.abs
        (x.val (mulIndexFromBound C n) - x'.val (mulIndexFromBound C n)))
      (eps (standardBoundWith A y' + (k + 2))))
    (hcy : Le (COF.abs
        (y.val (mulIndexFromBound C n) - y'.val (mulIndexFromBound C n)))
      (eps (standardBoundWith A x + (k + 2)))) :
    Le (COF.abs (mulValWithBound C x.val y.val n -
        mulValWithBound C x'.val y'.val n)) (eps (k + 1)) := by
  unfold mulValWithBound
  set c : Nat := mulIndexFromBound C n
  have hx_bound : Le (COF.abs (x.val c)) (COF.abs (x.val 1) + 1) := by
    simpa [c] using regular_value_bound_from_one x C n
  have hy'_bound : Le (COF.abs (y'.val c)) (COF.abs (y'.val 1) + 1) := by
    simpa [c] using regular_value_bound_from_one y' C n
  have term1_step1 : Le
      (COF.abs (x.val c) * COF.abs (y.val c - y'.val c))
      (COF.abs (x.val c) * eps (standardBoundWith A x + (k + 2))) :=
    scalar_mul_le_mul_left (by simpa [c] using hcy) (scalar_abs_nonneg (x.val c))
  have term1_step2 : Le
      (COF.abs (x.val c) * eps (standardBoundWith A x + (k + 2)))
      ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x + (k + 2))) :=
    scalar_mul_le_mul_right hx_bound (eps_nonneg (standardBoundWith A x + (k + 2)))
  have term1_budget : Le
      ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x + (k + 2)))
      (eps (k + 2)) :=
    standard_bound_tail_eps_le A x (k + 2)
  have hterm1 : Le
      (COF.abs (x.val c) * COF.abs (y.val c - y'.val c))
      (eps (k + 2)) :=
    BishopC.le_trans term1_step1 (BishopC.le_trans term1_step2 term1_budget)
  have term2_step1 : Le
      (COF.abs (x.val c - x'.val c) * COF.abs (y'.val c))
      (eps (standardBoundWith A y' + (k + 2)) * COF.abs (y'.val c)) :=
    scalar_mul_le_mul_right (by simpa [c] using hcx) (scalar_abs_nonneg (y'.val c))
  have term2_step2 : Le
      (eps (standardBoundWith A y' + (k + 2)) * COF.abs (y'.val c))
      (eps (standardBoundWith A y' + (k + 2)) * (COF.abs (y'.val 1) + 1)) :=
    scalar_mul_le_mul_left hy'_bound
      (eps_nonneg (standardBoundWith A y' + (k + 2)))
  have term2_step2' : Le
      (eps (standardBoundWith A y' + (k + 2)) * COF.abs (y'.val c))
      ((COF.abs (y'.val 1) + 1) *
        eps (standardBoundWith A y' + (k + 2))) := by
    rwa [show eps (standardBoundWith A y' + (k + 2)) *
          (COF.abs (y'.val 1) + 1) =
        (COF.abs (y'.val 1) + 1) *
          eps (standardBoundWith A y' + (k + 2)) from by ring] at term2_step2
  have term2_budget : Le
      ((COF.abs (y'.val 1) + 1) *
        eps (standardBoundWith A y' + (k + 2))) (eps (k + 2)) :=
    standard_bound_tail_eps_le A y' (k + 2)
  have hterm2 : Le
      (COF.abs (x.val c - x'.val c) * COF.abs (y'.val c))
      (eps (k + 2)) :=
    BishopC.le_trans term2_step1 (BishopC.le_trans term2_step2' term2_budget)
  have hprod := scalar_product_diff_le (x.val c) (x'.val c) (y.val c) (y'.val c)
  have hsum := BishopC.le_add hterm1 hterm2
  have hbudget : Le (eps (k + 2) + eps (k + 2)) (eps (k + 1)) := by
    rw [show k + 2 = k + 1 + 1 from by omega, eps_succ_add_self (k + 1)]
    exact BishopC.le_refl (eps (k + 1))
  exact BishopC.le_trans hprod (BishopC.le_trans hsum hbudget)

/-- Three-step scalar triangle inequality. -/
theorem scalar_abs_sub_le_three (a b c d : Scalar) :
    Le (COF.abs (a - d))
      (COF.abs (a - b) + (COF.abs (b - c) + COF.abs (c - d))) := by
  have h1 : Le (COF.abs (a - d))
      (COF.abs (a - b) + COF.abs ((b - c) + (c - d))) := by
    have h := scalar_abs_add_le (a - b) ((b - c) + (c - d))
    rwa [show (a - b) + ((b - c) + (c - d)) = a - d from by ring] at h
  have h2 := scalar_abs_add_le (b - c) (c - d)
  have hsum := BishopC.le_add (BishopC.le_refl (COF.abs (a - b))) h2
  exact BishopC.le_trans h1 hsum

/-- Bounded multiplication respects eventual equality once the explicit scalar
multiplicative Archimedean data is supplied. -/
theorem boundedMul_respects_eventually_with (A : ScalarMulArchimedeanData)
    (x x' y y' : RegularSeq)
    (hxx : relEventually x x') (hyy : relEventually y y') :
    relEventually
      { val := boundedMulValWith A x y, regular := boundedMul_regular_with A x y }
      { val := boundedMulValWith A x' y', regular := boundedMul_regular_with A x' y' } := by
  intro k
  set K : Nat := mulBoundWith A x y with hKdef
  set L : Nat := mulBoundWith A x' y' with hLdef
  set C : Nat := Nat.max K L with hCdef
  have hKleC : K ≤ C := by
    rw [hCdef]
    exact Nat.le_max_left K L
  have hLleC : L ≤ C := by
    rw [hCdef]
    exact Nat.le_max_right K L
  have hxK : standardBoundWith A x ≤ K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_left A x y
  have hyK : standardBoundWith A y ≤ K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_right A x y
  have hxC : standardBoundWith A x ≤ C := Nat.le_trans hxK hKleC
  have hyC : standardBoundWith A y ≤ C := Nat.le_trans hyK hKleC
  have hx'L : standardBoundWith A x' ≤ L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_left A x' y'
  have hy'L : standardBoundWith A y' ≤ L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_right A x' y'
  have hx'C : standardBoundWith A x' ≤ C := Nat.le_trans hx'L hLleC
  have hy'C : standardBoundWith A y' ≤ C := Nat.le_trans hy'L hLleC
  rcases hxx (standardBoundWith A y' + (k + 2)) with ⟨Nx, hNx⟩
  rcases hyy (standardBoundWith A x + (k + 2)) with ⟨Ny, hNy⟩
  refine ⟨Nx + Ny + (k + 3), ?_⟩
  intro n hn
  have hnNx : Nx ≤ n := by omega
  have hnNy : Ny ≤ n := by omega
  have htoln : k + 2 + 1 ≤ n := by omega
  set cidx : Nat := mulIndexFromBound C n
  have hn_cidx : n ≤ cidx := by
    unfold cidx
    exact le_mulIndexFromBound C n
  have hNx_cidx : Nx ≤ cidx := Nat.le_trans hnNx hn_cidx
  have hNy_cidx : Ny ≤ cidx := Nat.le_trans hnNy hn_cidx
  have hx_close : Le (COF.abs (x.val cidx - x'.val cidx))
      (eps (standardBoundWith A y' + (k + 2))) :=
    hNx cidx hNx_cidx
  have hy_close : Le (COF.abs (y.val cidx - y'.val cidx))
      (eps (standardBoundWith A x + (k + 2))) :=
    hNy cidx hNy_cidx
  have hleft0 : Le (COF.abs (mulValWithBound K x.val y.val n -
      mulValWithBound C x.val y.val n)) (tol n) :=
    mulValWithBound_change_le_tol A x y (K := K) (L := C) (n := n)
      hxK hxC hyK hyC
  have hleft : Le (COF.abs (mulValWithBound K x.val y.val n -
      mulValWithBound C x.val y.val n)) (eps (k + 2)) :=
    BishopC.le_trans hleft0 (tol_le_eps_of_succ_le (k := k + 2) (n := n) htoln)
  have hmid : Le (COF.abs (mulValWithBound C x.val y.val n -
      mulValWithBound C x'.val y'.val n)) (eps (k + 1)) :=
    mulValWithBound_common_respects_point A x x' y y' C k n
      (by simpa [cidx] using hx_close)
      (by simpa [cidx] using hy_close)
  have hright0 : Le (COF.abs (mulValWithBound C x'.val y'.val n -
      mulValWithBound L x'.val y'.val n)) (tol n) :=
    mulValWithBound_change_le_tol A x' y' (K := C) (L := L) (n := n)
      hx'C hx'L hy'C hy'L
  have hright : Le (COF.abs (mulValWithBound C x'.val y'.val n -
      mulValWithBound L x'.val y'.val n)) (eps (k + 2)) :=
    BishopC.le_trans hright0 (tol_le_eps_of_succ_le (k := k + 2) (n := n) htoln)
  change Le (COF.abs (boundedMulValWith A x y n - boundedMulValWith A x' y' n)) (eps k)
  unfold boundedMulValWith
  rw [← hKdef, ← hLdef]
  have htri := scalar_abs_sub_le_three
    (mulValWithBound K x.val y.val n)
    (mulValWithBound C x.val y.val n)
    (mulValWithBound C x'.val y'.val n)
    (mulValWithBound L x'.val y'.val n)
  have htail := BishopC.le_add hmid hright
  have hsum := BishopC.le_add hleft htail
  have hbudget : Le (eps (k + 2) + (eps (k + 1) + eps (k + 2))) (eps k) := by
    rw [show eps (k + 2) + (eps (k + 1) + eps (k + 2)) =
        (eps (k + 2) + eps (k + 2)) + eps (k + 1) from by ring]
    rw [show k + 2 = k + 1 + 1 from by omega]
    rw [eps_succ_add_self (k + 1), eps_succ_add_self k]
    exact BishopC.le_refl (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

/-- The multiplication closure data is now constructive from the explicit
scalar multiplicative Archimedean data. -/
def cRealMulClosureDataWith (A : ScalarMulArchimedeanData) : CRealMulClosureData A where
  mul_regular := boundedMul_regular_with A
  mul_respects_eventually := boundedMul_respects_eventually_with A

/-- Audited Phase 10 multiplication closure seed. -/
structure CRealMulClosureSeed : Type where
  scalarData : ScalarMulArchimedeanData
  closureData : CRealMulClosureData scalarData
  respects_eventually : ∀ x x' y y' : RegularSeq,
    relEventually x x' → relEventually y y' →
      relEventually
        { val := boundedMulValWith scalarData x y,
          regular := closureData.mul_regular x y }
        { val := boundedMulValWith scalarData x' y',
          regular := closureData.mul_regular x' y' }

def cRealMulClosureSeedWith (A : ScalarMulArchimedeanData) : CRealMulClosureSeed where
  scalarData := A
  closureData := cRealMulClosureDataWith A
  respects_eventually := boundedMul_respects_eventually_with A

end BishopCReal

