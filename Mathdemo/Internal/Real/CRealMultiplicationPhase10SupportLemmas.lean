import Mathdemo.Internal.Real.CRealMultiplicationCompletionFrontier

/-!
# CReal multiplication Phase 10 support lemmas

This file starts Phase 10 without hiding the remaining product estimate.  It
proves the scalar/order and index-budget facts needed to turn the conditional
multiplication frontier into a real closure proof.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Absolute values are nonnegative for the audited CRat scalar seed. -/
theorem scalar_abs_nonneg (a : Scalar) : Le 0 (COF.abs a) := by
  intro hlt
  have ha_neg : COF.lt a 0 := by
    rcases COF.lt_cotrans hlt a with habs_lt_a | ha_lt_zero
    · exact False.elim (scalarCOFOSeed.le_abs_self a habs_lt_a)
    · exact ha_lt_zero
  have hnega_neg : COF.lt (-a) 0 := by
    rcases COF.lt_cotrans hlt (-a) with habs_lt_neg | hneg_lt_zero
    · exact False.elim (scalarCOFOSeed.neg_le_abs a habs_lt_neg)
    · exact hneg_lt_zero
  have ha_pos : COF.lt 0 a := by
    have h := BishopC.neg_pos_of_neg hnega_neg
    rwa [show -(-a) = a from by ring] at h
  exact COF.lt_irrefl (0 : Scalar) (scalarCOFOSeed.lt_trans ha_pos ha_neg)

/-- Multiplication by a nonnegative scalar is monotone on the left. -/
theorem scalar_mul_le_mul_left {a b c : Scalar} (hab : Le a b) (hc : Le 0 c) :
    Le (c * a) (c * b) := by
  have hsub : BishopC.Nonneg (c * (b - a)) :=
    scalarCOFOSeed.mul_nonneg hc (BishopC.nonneg_sub_of_le hab)
  rw [show c * (b - a) = c * b - c * a from by ring] at hsub
  exact BishopC.le_of_nonneg_sub hsub

/-- Multiplication by a nonnegative scalar is monotone on the right. -/
theorem scalar_mul_le_mul_right {a b c : Scalar} (hab : Le a b) (hc : Le 0 c) :
    Le (a * c) (b * c) := by
  have h := scalar_mul_le_mul_left (c := c) hab hc
  rwa [mul_comm c a, mul_comm c b] at h

/-- Multiplication indices are always at least one. -/
theorem one_le_mulIndexFromBound (K n : Nat) : 1 ≤ mulIndexFromBound K n := by
  unfold mulIndexFromBound
  exact Nat.le_add_left 1 (2 * (K + 1) * (n + 1))

/-- Multiplication indices are large enough to compare against the `x.val 1`
base point used by `standardBoundWith`. -/
theorem eps_mulIndex_le_eps_one (K n : Nat) :
    Le (eps (mulIndexFromBound K n)) (eps 1) :=
  eps_le_of_le (one_le_mulIndexFromBound K n)

/-- The regularity error between a multiplication index and index `1` is at
most one. -/
theorem eps_mulIndex_add_eps_one_le_one (K n : Nat) :
    Le (eps (mulIndexFromBound K n) + eps 1) 1 := by
  have hsum := BishopC.le_add (eps_mulIndex_le_eps_one K n) (BishopC.le_refl (eps 1))
  rw [show (1 : Scalar) = eps 0 from rfl]
  rw [show eps 1 + eps 1 = eps 0 from eps_succ_add_self 0] at hsum
  exact hsum

/-- Values sampled by multiplication are uniformly bounded by the index-`1`
base point plus one. -/
theorem regular_value_bound_from_one (x : RegularSeq) (K n : Nat) :
    Le (COF.abs (x.val (mulIndexFromBound K n))) (COF.abs (x.val 1) + 1) := by
  have htri : Le
      (COF.abs (x.val (mulIndexFromBound K n)))
      (COF.abs (x.val (mulIndexFromBound K n) - x.val 1) + COF.abs (x.val 1)) := by
    have h := scalar_abs_add_le
      (x.val (mulIndexFromBound K n) - x.val 1)
      (x.val 1)
    rwa [show
      (x.val (mulIndexFromBound K n) - x.val 1) + x.val 1 =
        x.val (mulIndexFromBound K n) from by ring] at h
  have hdist : Le
      (COF.abs (x.val (mulIndexFromBound K n) - x.val 1)) 1 := by
    exact BishopC.le_trans (x.regular (mulIndexFromBound K n) 1)
      (eps_mulIndex_add_eps_one_le_one K n)
  have hsum := BishopC.le_add hdist (BishopC.le_refl (COF.abs (x.val 1)))
  have hsum' : Le
      (COF.abs (x.val (mulIndexFromBound K n) - x.val 1) + COF.abs (x.val 1))
      (COF.abs (x.val 1) + 1) := by
    rwa [show 1 + COF.abs (x.val 1) = COF.abs (x.val 1) + 1 from by ring] at hsum
  exact BishopC.le_trans htri hsum'

/-- The shifted standard bound has the right base-point estimate for later
product-continuity arguments. -/
theorem standardBoundWith_spec_base (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    Le ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x)) 1 := by
  have hbase_nonneg : Le 0 (COF.abs (x.val 1) + 1) :=
    BishopC.le_add (scalar_abs_nonneg (x.val 1))
      (scalar_nonneg_of_pos scalarCOFOSeed.one_pos)
  have h := standardBoundWith_spec A x
  change Le (BishopCRat.CRat.absF (COF.abs (x.val 1) + 1) *
    eps (standardBoundWith A x)) 1 at h
  change Le ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x)) 1
  rwa [scalarCOFOSeed.abs_of_nonneg hbase_nonneg] at h

/-- Audited Phase 10 support seed. -/
structure CRealMulPhase10SupportSeed : Type where
  scalar_abs_nonneg : ∀ a : Scalar, Le 0 (COF.abs a)
  scalar_mul_le_mul_left : ∀ {a b c : Scalar}, Le a b → Le 0 c → Le (c * a) (c * b)
  scalar_mul_le_mul_right : ∀ {a b c : Scalar}, Le a b → Le 0 c → Le (a * c) (b * c)
  one_le_mulIndexFromBound : ∀ K n : Nat, 1 ≤ mulIndexFromBound K n
  eps_mulIndex_add_eps_one_le_one : ∀ K n : Nat,
    Le (eps (mulIndexFromBound K n) + eps 1) 1
  regular_value_bound_from_one : ∀ x : RegularSeq, ∀ K n : Nat,
    Le (COF.abs (x.val (mulIndexFromBound K n))) (COF.abs (x.val 1) + 1)
  standardBoundWith_spec_base : ∀ A : ScalarMulArchimedeanData, ∀ x : RegularSeq,
    Le ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x)) 1

def cRealMulPhase10SupportSeed : CRealMulPhase10SupportSeed where
  scalar_abs_nonneg := scalar_abs_nonneg
  scalar_mul_le_mul_left := fun h hc => scalar_mul_le_mul_left h hc
  scalar_mul_le_mul_right := fun h hc => scalar_mul_le_mul_right h hc
  one_le_mulIndexFromBound := one_le_mulIndexFromBound
  eps_mulIndex_add_eps_one_le_one := eps_mulIndex_add_eps_one_le_one
  regular_value_bound_from_one := regular_value_bound_from_one
  standardBoundWith_spec_base := standardBoundWith_spec_base

end BishopCReal

