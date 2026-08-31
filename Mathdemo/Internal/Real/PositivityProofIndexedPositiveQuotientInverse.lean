import Mathdemo.Internal.Real.CancellationConditionalTotalInverseSelector

/-!
# Positivity of the proof-indexed positive quotient inverse

`CancellationConditionalTotalInverseSelector` closes cancellation for the proof-indexed positive inverse and
for the decidable total selector.  This file closes the next local ingredient:
the reciprocal representative of a positive quotient has a uniform positive
dyadic lower bound, hence supplies `ltQuotData zeroQuot` for the inverse.

This is still the data-indexed positive branch.  The live `COFO.inv_pos` field
will additionally need this transported through the final total inverse
selector/field assembly decision.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- If a positive scalar is bounded by `1 / eps K` in the form
`a * eps K <= 1`, then its positive reciprocal is bounded below by the next
dyadic gauge. -/
theorem scalar_eps_succ_lt_posInv_of_pos_mul_eps_le_one
    {a : Scalar} {K : Nat}
    (ha : COF.lt 0 a)
    (hbound : Le (a * eps K) 1) :
    COF.lt (eps (K + 1)) (scalarPositiveInverseSeed.inv a) := by
  have hle : Le (eps K) (scalarPositiveInverseSeed.inv a) := by
    intro hlt
    have hmul :
        COF.lt (a * scalarPositiveInverseSeed.inv a) (a * eps K) :=
      scalar_mul_lt_mul_left hlt ha
    have hcancel :
        a * scalarPositiveInverseSeed.inv a = 1 :=
      scalarPositiveInverseSeed.mul_inv_cancel a ha
    rw [hcancel] at hmul
    exact hbound hmul
  exact BishopC.lt_of_lt_of_le (eps_succ_lt_eps K) hle

/-- Once an index is at least one, its dyadic regularity error against index
`1` is bounded by one. -/
theorem eps_index_add_eps_one_le_one {j : Nat} (hj : 1 ≤ j) :
    Le (eps j + eps 1) 1 := by
  have hleft : Le (eps j) (eps 1) := eps_le_of_le hj
  have hsum := BishopC.le_add hleft (BishopC.le_refl (eps 1))
  have hone : (1 : Scalar) = eps 0 := rfl
  have hhalf : eps 1 + eps 1 = eps 0 := eps_succ_add_self 0
  rw [hone, ← hhalf]
  exact hsum

/-- Any regular-sequence value sampled at index at least one is bounded by the
index-`1` base point plus one. -/
theorem regular_value_bound_from_one_ge_one
    (x : RegularSeq) {j : Nat} (hj : 1 ≤ j) :
    Le (COF.abs (x.val j)) (COF.abs (x.val 1) + 1) := by
  have htri :
      Le (COF.abs (x.val j))
        (COF.abs (x.val j - x.val 1) + COF.abs (x.val 1)) := by
    have h := scalar_abs_add_le (x.val j - x.val 1) (x.val 1)
    rwa [show (x.val j - x.val 1) + x.val 1 = x.val j from by ring] at h
  have hdist :
      Le (COF.abs (x.val j - x.val 1)) 1 :=
    BishopC.le_trans (x.regular j 1) (eps_index_add_eps_one_le_one hj)
  have hsum := BishopC.le_add hdist (BishopC.le_refl (COF.abs (x.val 1)))
  have hsum' :
      Le (COF.abs (x.val j - x.val 1) + COF.abs (x.val 1))
        (COF.abs (x.val 1) + 1) := by
    rwa [show 1 + COF.abs (x.val 1) = COF.abs (x.val 1) + 1 from by ring] at hsum
  exact BishopC.le_trans htri hsum'

/-- The standard bound controls every sample at index at least one after
multiplication by the bound gauge. -/
theorem regular_value_mul_standard_eps_le_one_of_ge_one
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    {j : Nat} (hj : 1 ≤ j) :
    Le (x.val j * eps (standardBoundWith A x)) 1 := by
  have hsample_abs :
      Le (COF.abs (x.val j)) (COF.abs (x.val 1) + 1) :=
    regular_value_bound_from_one_ge_one x hj
  have hsample :
      Le (x.val j) (COF.abs (x.val 1) + 1) :=
    BishopC.le_trans (by
      change ¬ COF.lt (COF.abs (x.val j)) (x.val j)
      exact scalarCOFOSeed.le_abs_self (x.val j)) hsample_abs
  have hmul :
      Le (x.val j * eps (standardBoundWith A x))
        ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x)) :=
    scalar_mul_le_mul_right hsample (eps_nonneg (standardBoundWith A x))
  exact BishopC.le_trans hmul (standardBoundWith_spec_base A x)

/-- The bound-sensitive reciprocal tail has a uniform positive dyadic lower
bound after one output-index shift. -/
theorem positiveTailInvValWithBound_uniform_lower_succ
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    COF.lt (eps (standardBoundWith A x + 1))
      (positiveTailInvValWithBound A x h (n + 1)) := by
  set q : Nat := reciprocalTailIndexWith A x h (n + 1)
  have hq_tail : h.N ≤ q := by
    simpa [q] using reciprocalTailIndex_tail A x h (n + 1)
  have hq_one : 1 ≤ q := by
    have hn_one : 1 ≤ reciprocalTailBoundWith A x h + (n + 1) :=
      Nat.le_trans (Nat.succ_pos n)
        (Nat.le_add_left (n + 1) (reciprocalTailBoundWith A x h))
    exact Nat.le_trans hn_one (by
      simpa [q] using reciprocalTailIndex_bound A x h (n + 1))
  have hq_pos : COF.lt 0 (x.val q) :=
    scalar_pos_of_posEventuallyData_tail x h hq_tail
  have hq_bound :
      Le (x.val q * eps (standardBoundWith A x)) 1 :=
    regular_value_mul_standard_eps_le_one_of_ge_one A x hq_one
  unfold positiveTailInvValWithBound positiveTailInvVal
  rw [show reciprocalTailIndexWith A x h (n + 1) = q from by simp [q],
    if_pos hq_tail]
  exact scalar_eps_succ_lt_posInv_of_pos_mul_eps_le_one hq_pos hq_bound

/-- Positivity data for the reciprocal representative, expressed in the same
`subSeq _ zeroSeq` shape used by quotient strict positivity. -/
def positiveTailInvSeqWithBound_sub_zero_posData
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) :
    PosEventuallyData (subSeq (positiveTailInvSeqWithBound A x h) zeroSeq) where
  k := standardBoundWith A x + 1
  N := 0
  tail_pos := by
    intro n _hn
    have hpos := positiveTailInvValWithBound_uniform_lower_succ A x h n
    change COF.lt (eps (standardBoundWith A x + 1))
      (positiveTailInvValWithBound A x h (n + 1) - 0)
    rwa [sub_zero]

/-- Prop-valued positivity of the reciprocal representative. -/
theorem positiveTailInvSeqWithBound_sub_zero_pos
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) :
    PosEventually (subSeq (positiveTailInvSeqWithBound A x h) zeroSeq) :=
  (positiveTailInvSeqWithBound_sub_zero_posData A x h).toProp

/-- Data-valued quotient positivity for the proof-indexed positive inverse. -/
def positiveQuotInvWithData_posData
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h : ltQuotData zeroQuot x) :
    ltQuotData zeroQuot (positiveQuotInvWithData A h) where
  left := zeroSeq
  right := positiveQuotInvSeqWithData A h
  left_eq := rfl
  right_eq := rfl
  pos := positiveTailInvSeqWithBound_sub_zero_posData
    A (subSeq h.right h.left) h.pos

/-- Prop-valued quotient positivity for the proof-indexed positive inverse. -/
theorem positiveQuotInvWithData_pos
    (A : ScalarMulArchimedeanData) {x : CRealQuot}
    (h : ltQuotData zeroQuot x) :
    ltQuot zeroQuot (positiveQuotInvWithData A h) :=
  ltQuotData_to_ltQuot (positiveQuotInvWithData_posData A h)

/-- In the decidable-order branch, the total selector sends positive quotient
elements to positive quotient elements. -/
theorem positiveQuotInvOrZeroWithDecidable_inv_pos
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    {x : CRealQuot} (hx : ltQuot zeroQuot x) :
    ltQuot zeroQuot (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x) := by
  rw [positiveQuotInvOrZeroWithDecidable_eq_of_pos A hdec ltDataOf hx]
  exact positiveQuotInvWithData_pos A (ltDataOf hx)

/-- Data package for the positive-inverse positivity layer. -/
structure PositiveQuotInversePositivitySeed : Type 1 where
  scalar_lower :
    ∀ {a : Scalar} {K : Nat}, COF.lt 0 a → Le (a * eps K) 1 →
      COF.lt (eps (K + 1)) (scalarPositiveInverseSeed.inv a)
  tail_uniform_lower :
    ∀ A : ScalarMulArchimedeanData,
      ∀ x : RegularSeq, ∀ h : PosEventuallyData x, ∀ n : Nat,
        COF.lt (eps (standardBoundWith A x + 1))
          (positiveTailInvValWithBound A x h (n + 1))
  tail_posData :
    ∀ A : ScalarMulArchimedeanData,
      ∀ x : RegularSeq, ∀ h : PosEventuallyData x,
        PosEventuallyData (subSeq (positiveTailInvSeqWithBound A x h) zeroSeq)
  inv_posData :
    ∀ A : ScalarMulArchimedeanData,
      ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
        ltQuotData zeroQuot (positiveQuotInvWithData A h)
  inv_pos :
    ∀ A : ScalarMulArchimedeanData,
      ∀ {x : CRealQuot}, ∀ h : ltQuotData zeroQuot x,
        ltQuot zeroQuot (positiveQuotInvWithData A h)
  total_selector_inv_pos :
    ∀ A : ScalarMulArchimedeanData,
      ∀ hdec : CRealQuotLTDecidable,
      ∀ ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b,
      ∀ {x : CRealQuot}, ltQuot zeroQuot x →
        ltQuot zeroQuot (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x)

def positiveQuotInversePositivitySeed :
    PositiveQuotInversePositivitySeed where
  scalar_lower := fun ha hb =>
    scalar_eps_succ_lt_posInv_of_pos_mul_eps_le_one ha hb
  tail_uniform_lower := positiveTailInvValWithBound_uniform_lower_succ
  tail_posData := positiveTailInvSeqWithBound_sub_zero_posData
  inv_posData := fun A {x} h => positiveQuotInvWithData_posData A (x := x) h
  inv_pos := fun A {x} h => positiveQuotInvWithData_pos A (x := x) h
  total_selector_inv_pos :=
    positiveQuotInvOrZeroWithDecidable_inv_pos

/-- Frontier after `inv_pos` is closed for the positive branch and transported
to the decidable total selector. -/
structure CRealQuotPositiveInversePositivityFrontier : Type where
  full_positive_inverse_field_data : Prop
  cauchy_completeness : Prop

def cRealQuotPositiveInversePositivityFrontier :
    CRealQuotPositiveInversePositivityFrontier where
  full_positive_inverse_field_data := True
  cauchy_completeness := True

end BishopCReal

