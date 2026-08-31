import Mathdemo.Internal.Rat.CRatAbsoluteValueProducts

/-!
# CReal bounded multiplication regularity

This file closes the first half of the Phase 10 multiplication closure data:
bounded multiplication is regular once the explicit scalar multiplicative
Archimedean data is supplied.  The eventual-equality respect proof remains a
separate frontier because it uses the same estimate with tail witnesses.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Dyadic gauges multiply by adding indices, proved locally from the `COF`
data because the current CRat scalar is not yet emitted as a full `COFO`
instance. -/
theorem eps_add_mul_local (j m : Nat) : eps (j + m) = eps j * eps m := by
  unfold eps
  induction m with
  | zero =>
      show COF.halfPow (R := Scalar) j =
        COF.halfPow (R := Scalar) j * COF.halfPow (R := Scalar) 0
      rw [show COF.halfPow (R := Scalar) 0 = (1 : Scalar) from rfl, mul_one]
  | succ m ih =>
      show COF.halfPow (R := Scalar) (j + (m + 1)) =
        COF.halfPow (R := Scalar) j * COF.halfPow (R := Scalar) (m + 1)
      rw [show COF.halfPow (R := Scalar) (j + (m + 1)) =
            COF.half * COF.halfPow (R := Scalar) (j + m) from rfl,
          show COF.halfPow (R := Scalar) (m + 1) =
            COF.half * COF.halfPow (R := Scalar) m from rfl, ih]
      ring

/-- The multiplication reindexing absorbs both the representative bound and
the requested output precision. -/
theorem mulIndexFromBound_absorb_le {s K n : Nat} (hs : s ≤ K) :
    s + (n + 1) ≤ mulIndexFromBound K n := by
  unfold mulIndexFromBound
  have h1 : s + (n + 1) ≤ K + (n + 1) := Nat.add_le_add_right hs (n + 1)
  have hKmul : K ≤ K * (n + 1) := Nat.le_mul_of_pos_right K (Nat.succ_pos n)
  have h2a : K + (n + 1) ≤ K * (n + 1) + (n + 1) :=
    Nat.add_le_add_right hKmul (n + 1)
  have h2 : K + (n + 1) ≤ (K + 1) * (n + 1) := by
    rw [show (K + 1) * (n + 1) = K * (n + 1) + (n + 1) from by ring]
    exact h2a
  have h3a : (K + 1) * (n + 1) ≤ 2 * ((K + 1) * (n + 1)) :=
    Nat.le_mul_of_pos_left ((K + 1) * (n + 1)) (by decide : 0 < 2)
  have h3 : (K + 1) * (n + 1) ≤ 2 * (K + 1) * (n + 1) := by
    rw [Nat.mul_assoc]
    exact h3a
  have h4 : 2 * (K + 1) * (n + 1) ≤ 2 * (K + 1) * (n + 1) + 1 :=
    Nat.le_succ _
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))

/-- A standard bound absorbs one sampled dyadic error into the next output
precision. -/
theorem standard_bound_mul_eps_le (A : ScalarMulArchimedeanData)
    (x : RegularSeq) {K n : Nat} (hxK : standardBoundWith A x ≤ K) :
    Le ((COF.abs (x.val 1) + 1) * eps (mulIndexFromBound K n)) (eps (n + 1)) := by
  set B : Scalar := COF.abs (x.val 1) + 1
  set s : Nat := standardBoundWith A x
  have hidx_nat : s + (n + 1) ≤ mulIndexFromBound K n := by
    exact mulIndexFromBound_absorb_le (s := s) (K := K) (n := n)
      (by simpa [s] using hxK)
  have hidx : Le (eps (mulIndexFromBound K n)) (eps (s + (n + 1))) :=
    eps_le_of_le hidx_nat
  have hidx' : Le (eps (mulIndexFromBound K n)) (eps s * eps (n + 1)) := by
    rwa [eps_add_mul_local s (n + 1)] at hidx
  have hBnonneg : Le 0 B := by
    unfold B
    exact BishopC.le_add (scalar_abs_nonneg (x.val 1))
      (scalar_nonneg_of_pos scalarCOFOSeed.one_pos)
  have hleft :
      Le (B * eps (mulIndexFromBound K n)) (B * (eps s * eps (n + 1))) :=
    scalar_mul_le_mul_left hidx' hBnonneg
  have hleft' :
      Le (B * eps (mulIndexFromBound K n)) ((B * eps s) * eps (n + 1)) := by
    rwa [show B * (eps s * eps (n + 1)) = (B * eps s) * eps (n + 1)
      from by ring] at hleft
  have hspec : Le (B * eps s) 1 := by
    unfold B s
    exact standardBoundWith_spec_base A x
  have hright : Le ((B * eps s) * eps (n + 1)) (1 * eps (n + 1)) :=
    scalar_mul_le_mul_right hspec (eps_nonneg (n + 1))
  have hright' : Le ((B * eps s) * eps (n + 1)) (eps (n + 1)) := by
    rwa [one_mul] at hright
  exact BishopC.le_trans hleft' hright'

/-- Scalar product-difference estimate used by bounded multiplication. -/
theorem scalar_product_diff_le (a a' b b' : Scalar) :
    Le (COF.abs (a * b - a' * b'))
      (COF.abs a * COF.abs (b - b') + COF.abs (a - a') * COF.abs b') := by
  have htri : Le (COF.abs (a * b - a' * b'))
      (COF.abs (a * (b - b')) + COF.abs ((a - a') * b')) := by
    have h := scalar_abs_add_le (a * (b - b')) ((a - a') * b')
    rwa [show a * (b - b') + (a - a') * b' = a * b - a' * b'
      from by ring] at h
  have hrew : COF.abs (a * (b - b')) + COF.abs ((a - a') * b') =
      COF.abs a * COF.abs (b - b') + COF.abs (a - a') * COF.abs b' := by
    rw [scalar_abs_mul a (b - b'), scalar_abs_mul (a - a') b']
  rwa [hrew] at htri

/-- A standard bound absorbs the two dyadic errors appearing in a regularity
comparison. -/
theorem standard_bound_eps_sum_le (A : ScalarMulArchimedeanData)
    (x : RegularSeq) {K m n : Nat} (hxK : standardBoundWith A x ≤ K) :
    Le ((COF.abs (x.val 1) + 1) *
        (eps (mulIndexFromBound K m) + eps (mulIndexFromBound K n)))
      (eps (m + 1) + eps (n + 1)) := by
  have hm := standard_bound_mul_eps_le A x (K := K) (n := m) hxK
  have hn := standard_bound_mul_eps_le A x (K := K) (n := n) hxK
  have hsum := BishopC.le_add hm hn
  rw [show (COF.abs (x.val 1) + 1) *
        (eps (mulIndexFromBound K m) + eps (mulIndexFromBound K n)) =
      (COF.abs (x.val 1) + 1) * eps (mulIndexFromBound K m) +
        (COF.abs (x.val 1) + 1) * eps (mulIndexFromBound K n) from by ring]
  exact hsum

/-- Bounded multiplication is regular under explicit scalar bound data. -/
theorem boundedMul_regular_with (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) : RegularVal (boundedMulValWith A x y) := by
  intro m n
  unfold boundedMulValWith mulValWithBound
  set K : Nat := mulBoundWith A x y
  set p : Nat := mulIndexFromBound K m
  set q : Nat := mulIndexFromBound K n
  have hxK : standardBoundWith A x ≤ K := by
    unfold K
    exact standardBoundWith_le_mulBound_left A x y
  have hyK : standardBoundWith A y ≤ K := by
    unfold K
    exact standardBoundWith_le_mulBound_right A x y
  have hx_bound_p : Le (COF.abs (x.val p)) (COF.abs (x.val 1) + 1) := by
    simpa [p] using regular_value_bound_from_one x K m
  have hy_bound_q : Le (COF.abs (y.val q)) (COF.abs (y.val 1) + 1) := by
    simpa [q] using regular_value_bound_from_one y K n
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
      standard_bound_eps_sum_le A x (K := K) (m := m) (n := n) hxK
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
      standard_bound_eps_sum_le A y (K := K) (m := m) (n := n) hyK
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

/-- Audited regularity seed for the first half of Phase 10 closure. -/
structure CRealMulRegularitySeed : Type where
  eps_add_mul : ∀ j m : Nat, eps (j + m) = eps j * eps m
  standard_bound_mul_eps_le : ∀ A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
    ∀ {K n : Nat}, standardBoundWith A x ≤ K →
      Le ((COF.abs (x.val 1) + 1) * eps (mulIndexFromBound K n)) (eps (n + 1))
  scalar_product_diff_le : ∀ a a' b b' : Scalar,
    Le (COF.abs (a * b - a' * b'))
      (COF.abs a * COF.abs (b - b') + COF.abs (a - a') * COF.abs b')
  boundedMul_regular : ∀ A : ScalarMulArchimedeanData, ∀ x y : RegularSeq,
    RegularVal (boundedMulValWith A x y)

def cRealMulRegularitySeed : CRealMulRegularitySeed where
  eps_add_mul := eps_add_mul_local
  standard_bound_mul_eps_le := by
    intro A x K n h
    exact standard_bound_mul_eps_le A x (K := K) (n := n) h
  scalar_product_diff_le := scalar_product_diff_le
  boundedMul_regular := boundedMul_regular_with

end BishopCReal

