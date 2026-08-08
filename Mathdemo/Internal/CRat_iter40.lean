import Mathdemo.Internal.CRat_iter39

/-!
# CReal common-bound multiplication transport

The associativity estimate in `CRat_iter39` is stated for products sampled at
one shared multiplication bound.  The concrete quotient multiplication,
however, uses the pairwise bound `mulBoundWith A x y`.  This file adds the
transport layer between those two representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Multiplication sampled at any explicit common bound is regular, provided
the common bound dominates the two standard bounds. -/
theorem mulValWithBound_regular_with_bound (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C) :
    RegularVal (mulValWithBound C x.val y.val) := by
  intro m n
  unfold mulValWithBound
  set p : Nat := mulIndexFromBound C m
  set q : Nat := mulIndexFromBound C n
  have hx_bound_p : Le (COF.abs (x.val p)) (COF.abs (x.val 1) + 1) := by
    simpa [p] using regular_value_bound_from_one x C m
  have hy_bound_q : Le (COF.abs (y.val q)) (COF.abs (y.val 1) + 1) := by
    simpa [q] using regular_value_bound_from_one y C n
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
      (eps (m + 1) + eps (n + 1)) := by
    simpa [p, q] using
      standard_bound_eps_sum_le A x (K := C) (m := m) (n := n) hxC
  have hterm1 : Le
      (COF.abs (x.val p) * COF.abs (y.val p - y.val q))
      (eps (m + 1) + eps (n + 1)) :=
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
      (eps (m + 1) + eps (n + 1)) := by
    simpa [p, q] using
      standard_bound_eps_sum_le A y (K := C) (m := m) (n := n) hyC
  have hterm2 : Le
      (COF.abs (x.val p - x.val q) * COF.abs (y.val q))
      (eps (m + 1) + eps (n + 1)) :=
    BishopC.le_trans term2_step1 (BishopC.le_trans term2_step2' term2_budget)
  have hprod := scalar_product_diff_le (x.val p) (x.val q) (y.val p) (y.val q)
  have hsum := BishopC.le_add hterm1 hterm2
  have hbudget : Le
      ((eps (m + 1) + eps (n + 1)) + (eps (m + 1) + eps (n + 1)))
      (eps m + eps n) := by
    rw [show (eps (m + 1) + eps (n + 1)) + (eps (m + 1) + eps (n + 1)) =
        (eps (m + 1) + eps (m + 1)) + (eps (n + 1) + eps (n + 1))
        from by ring,
      eps_succ_add_self m, eps_succ_add_self n]
    exact BishopC.le_refl (eps m + eps n)
  exact BishopC.le_trans hprod (BishopC.le_trans hsum hbudget)

/-- Regular representative for multiplication sampled at a chosen common
bound. -/
def mulSeqAtBoundWith (A : ScalarMulArchimedeanData) (C : Nat)
    (x y : RegularSeq)
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C) : RegularSeq where
  val := mulValWithBound C x.val y.val
  regular := mulValWithBound_regular_with_bound A x y hxC hyC

/-- The concrete pairwise-bound product is eventually equal to the same product
sampled at any larger common bound. -/
theorem mulSeqConcrete_to_common_bound_eventually_with
    (A : ScalarMulArchimedeanData) (x y : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C) :
    relEventually (mulSeqConcreteWith A x y)
      (mulSeqAtBoundWith A C x y hxC hyC) := by
  intro k
  set K : Nat := mulBoundWith A x y with hKdef
  have hxK : standardBoundWith A x <= K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_left A x y
  have hyK : standardBoundWith A y <= K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_right A x y
  refine ⟨k + 1, ?_⟩
  intro n hn
  have h0 : Le (COF.abs (mulValWithBound K x.val y.val n -
      mulValWithBound C x.val y.val n)) (tol n) :=
    mulValWithBound_change_le_tol A x y (K := K) (L := C) (n := n)
      hxK hxC hyK hyC
  have h1 : Le (COF.abs (mulValWithBound K x.val y.val n -
      mulValWithBound C x.val y.val n)) (eps k) :=
    BishopC.le_trans h0 (tol_le_eps_of_succ_le (k := k) (n := n) hn)
  change Le (COF.abs (boundedMulValWith A x y n -
      mulValWithBound C x.val y.val n)) (eps k)
  unfold boundedMulValWith
  rw [← hKdef]
  exact h1

/-- Symmetric transport from a common-bound product back to the concrete
pairwise-bound product. -/
theorem mulSeqCommon_to_concrete_bound_eventually_with
    (A : ScalarMulArchimedeanData) (x y : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C) :
    relEventually (mulSeqAtBoundWith A C x y hxC hyC)
      (mulSeqConcreteWith A x y) := by
  exact relEventually_symm
    (mulSeqConcreteWith A x y)
    (mulSeqAtBoundWith A C x y hxC hyC)
    (mulSeqConcrete_to_common_bound_eventually_with A x y hxC hyC)

/-- A common-bound representative denotes the same quotient product as the
concrete pairwise-bound multiplication. -/
theorem mkQuot_mulSeqAtBound_eq_mulQuotConcrete
    (A : ScalarMulArchimedeanData) (x y : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C) :
    mkQuot (mulSeqAtBoundWith A C x y hxC hyC) =
      mulQuotConcreteWith A (mkQuot x) (mkQuot y) := by
  change mkQuot (mulSeqAtBoundWith A C x y hxC hyC) =
    mkQuot (mulSeqConcreteWith A x y)
  apply Quotient.sound
  exact mulSeqCommon_to_concrete_bound_eventually_with A x y hxC hyC

/-- Audited transport package for the forthcoming quotient associativity
proof. -/
structure CRealCommonBoundMulTransportSeed
    (A : ScalarMulArchimedeanData) : Type where
  common_regular : ∀ (C : Nat) (x y : RegularSeq),
    standardBoundWith A x <= C → standardBoundWith A y <= C →
      RegularVal (mulValWithBound C x.val y.val)
  concrete_to_common : ∀ (C : Nat) (x y : RegularSeq)
    (hxC : standardBoundWith A x <= C) (hyC : standardBoundWith A y <= C),
      relEventually (mulSeqConcreteWith A x y)
        (mulSeqAtBoundWith A C x y hxC hyC)
  common_to_concrete : ∀ (C : Nat) (x y : RegularSeq)
    (hxC : standardBoundWith A x <= C) (hyC : standardBoundWith A y <= C),
      relEventually (mulSeqAtBoundWith A C x y hxC hyC)
        (mulSeqConcreteWith A x y)
  quotient_common : ∀ (C : Nat) (x y : RegularSeq)
    (hxC : standardBoundWith A x <= C) (hyC : standardBoundWith A y <= C),
      mkQuot (mulSeqAtBoundWith A C x y hxC hyC) =
        mulQuotConcreteWith A (mkQuot x) (mkQuot y)

def cRealCommonBoundMulTransportSeedWith
    (A : ScalarMulArchimedeanData) : CRealCommonBoundMulTransportSeed A where
  common_regular := by
    intro C x y hxC hyC
    exact mulValWithBound_regular_with_bound A x y hxC hyC
  concrete_to_common := by
    intro C x y hxC hyC
    exact mulSeqConcrete_to_common_bound_eventually_with A x y hxC hyC
  common_to_concrete := by
    intro C x y hxC hyC
    exact mulSeqCommon_to_concrete_bound_eventually_with A x y hxC hyC
  quotient_common := by
    intro C x y hxC hyC
    exact mkQuot_mulSeqAtBound_eq_mulQuotConcrete A x y hxC hyC

end BishopCReal

