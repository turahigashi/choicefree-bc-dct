import Mathdemo.Internal.CRat_iter322

set_option linter.style.longLine false

/-!
# G224: scalar increment bounds for the Theorem 4.6 local steps

G223 closed the characteristic expansion laws.  This file closes the remaining
pure scalar increment estimates needed for the source two-step proof:

* set expansion: if `χ₀ ≤ χ₁` and both are characteristic values, then the
  `f+`/`f-` increment is bounded by the `|f|` increment;
* truncation expansion: if `n ≤ m`, the increment from level `n` to level `m`
  is monotone in the underlying nonnegative value.

The proofs use only the `0/1` characteristic alternatives and the existing
`min` telescope identity from Proposition 4.2.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge

/-- Characteristic values are exactly `0` or `1`. -/
theorem theorem46_chi_value_zero_or_one
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {x : Y}
    (hADom : hA.rep.MemAt x)
    (hAabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hADom m))) :
    (BishopC.seriesSum_of_abs hAabs).sum = 0 ∨
      (BishopC.seriesSum_of_abs hAabs).sum = 1 := by
  rcases (hA.valid x hADom hAabs).1 with hA1 | hA2
  · exact Or.inr
      ((hA.valid x hADom hAabs).2.1 hA1
        (BishopC.seriesSum_of_abs hAabs))
  · exact Or.inl
      ((hA.valid x hADom hAabs).2.2 hA2
        (BishopC.seriesSum_of_abs hAabs))

/-- The tail `a - min(a,c)` is monotone in `a`. -/
theorem theorem46_min_tail_mono
    {R : Type*} [COFOC R] {a b c : R}
    (hab : BishopC.Le a b) :
    BishopC.Le (a - COF.min a c) (b - COF.min b c) := by
  apply BishopC.le_of_nonneg_sub
  have hdiff :
      BishopC.Le
        (COF.min b c - COF.min a c)
        (b - a) := by
    have h := BishopC.abs_min_sub_min_le b a c
    rw [COFO.abs_of_nonneg (BishopC.nonneg_sub_of_le hab)] at h
    exact BishopC.le_trans (COFO.le_abs_self _) h
  have hnon : BishopC.Nonneg ((b - a) - (COF.min b c - COF.min a c)) :=
    BishopC.nonneg_sub_of_le hdiff
  convert hnon using 1
  ring

/-- The increment `min(a,m)-min(a,n)` is monotone in `a`, for `n ≤ m`. -/
theorem theorem46_min_increment_mono
    {R : Type*} [COFOC R] {n m : Nat} {a b : R}
    (hnm : n ≤ m) (hab : BishopC.Le a b) :
    BishopC.Le
      (COF.min a (m : R) - COF.min a (n : R))
      (COF.min b (m : R) - COF.min b (n : R)) := by
  have hnmR : BishopC.Le (n : R) (m : R) :=
    BishopC.lemma33_natCast_mono hnm
  have htail :
      BishopC.Le
        (a - COF.min a (n : R))
        (b - COF.min b (n : R)) :=
    theorem46_min_tail_mono hab
  rw [← BishopC.prop42_term_chi1 a (n : R) (m : R) hnmR,
    ← BishopC.prop42_term_chi1 b (n : R) (m : R) hnmR]
  exact BishopC.min_le_min_right ((m : R) - (n : R))
    (a - COF.min a (n : R)) (b - COF.min b (n : R)) htail

/-- Two formal self-subtractions are order-equal. -/
theorem theorem46_sub_self_le_sub_self
    {R : Type*} [COFOC R] (a b : R) :
    BishopC.Le (a - a) (b - b) := by
  apply BishopC.le_of_nonneg_sub
  convert (BishopC.le_refl (0 : R)) using 1
  ring

/-- Set-expansion increment bound for scalar characteristic values. -/
theorem theorem46_scalarMid_chi_set_increment_bound
    {R : Type*} [COFOC R] (n : Nat)
    {χ₀ χ₁ p q : R}
    (hχ₀ : χ₀ = 0 ∨ χ₀ = 1)
    (hχ₁ : χ₁ = 0 ∨ χ₁ = 1)
    (hχle : BishopC.Le χ₀ χ₁)
    (hp : BishopC.Nonneg p) (hq : BishopC.Nonneg q)
    (hpq : BishopC.Le p q) :
    BishopC.Le
      (prop412ScalarMid n (χ₁ * p) -
        prop412ScalarMid n (χ₀ * p))
      (prop412ScalarMid n (χ₁ * q) -
        prop412ScalarMid n (χ₀ * q)) := by
  rcases hχ₀ with hχ₀0 | hχ₀1
  · rcases hχ₁ with hχ₁0 | hχ₁1
    · rw [hχ₀0, hχ₁0]
      exact theorem46_sub_self_le_sub_self
        (prop412ScalarMid n ((0 : R) * p))
        (prop412ScalarMid n ((0 : R) * q))
    · rw [hχ₀0, hχ₁1]
      have hleft :
          prop412ScalarMid n ((1 : R) * p) -
              prop412ScalarMid n ((0 : R) * p) =
            prop412ScalarMid n p := by
        rw [one_mul, zero_mul, prop412_scalarMid_zero, sub_zero]
      have hright :
          prop412ScalarMid n ((1 : R) * q) -
              prop412ScalarMid n ((0 : R) * q) =
            prop412ScalarMid n q := by
        rw [one_mul, zero_mul, prop412_scalarMid_zero, sub_zero]
      rw [hleft, hright]
      exact theorem46_scalarMid_nonneg_value_mono n hp hq hpq
  · rcases hχ₁ with hχ₁0 | hχ₁1
    · rw [hχ₀1, hχ₁0] at hχle
      exact False.elim (hχle COFO.one_pos)
    · rw [hχ₀1, hχ₁1]
      exact theorem46_sub_self_le_sub_self
        (prop412ScalarMid n ((1 : R) * p))
        (prop412ScalarMid n ((1 : R) * q))

/-- Truncation-expansion increment bound for scalar characteristic values. -/
theorem theorem46_scalarMid_chi_trunc_increment_bound
    {R : Type*} [COFOC R] {n m : Nat}
    {χ p q : R}
    (hnm : n ≤ m)
    (hχ : χ = 0 ∨ χ = 1)
    (hp : BishopC.Nonneg p) (hq : BishopC.Nonneg q)
    (hpq : BishopC.Le p q) :
    BishopC.Le
      (prop412ScalarMid m (χ * p) -
        prop412ScalarMid n (χ * p))
      (prop412ScalarMid m (χ * q) -
        prop412ScalarMid n (χ * q)) := by
  rcases hχ with hχ0 | hχ1
  · rw [hχ0]
    have hleft :
        prop412ScalarMid m ((0 : R) * p) -
            prop412ScalarMid n ((0 : R) * p) = 0 := by
      rw [zero_mul, prop412_scalarMid_zero, prop412_scalarMid_zero]
      ring
    have hright :
        prop412ScalarMid m ((0 : R) * q) -
            prop412ScalarMid n ((0 : R) * q) = 0 := by
      rw [zero_mul, prop412_scalarMid_zero, prop412_scalarMid_zero]
      ring
    rw [hleft, hright]
    exact BishopC.le_refl (0 : R)
  · rw [hχ1]
    have hleft :
        prop412ScalarMid m ((1 : R) * p) -
            prop412ScalarMid n ((1 : R) * p) =
          COF.min p (m : R) - COF.min p (n : R) := by
      rw [one_mul, theorem46_scalarMid_nonneg_arg_eq_min m hp,
        theorem46_scalarMid_nonneg_arg_eq_min n hp]
    have hright :
        prop412ScalarMid m ((1 : R) * q) -
            prop412ScalarMid n ((1 : R) * q) =
          COF.min q (m : R) - COF.min q (n : R) := by
      rw [one_mul, theorem46_scalarMid_nonneg_arg_eq_min m hq,
        theorem46_scalarMid_nonneg_arg_eq_min n hq]
    rw [hleft, hright]
    exact theorem46_min_increment_mono hnm hpq

/-- Audit after G224. -/
structure Theorem46ScalarIncrementAuditAfterG224 : Type where
  characteristic_zero_or_one_exposed : Nat
  min_tail_monotone_closed : Nat
  min_increment_monotone_closed : Nat
  set_expansion_increment_bound_closed : Nat
  truncation_expansion_increment_bound_closed : Nat
  classical_choice_inputs_added : Nat
  prop_to_data_selector_inputs_added : Nat
  remaining_connect_increment_bounds_to_mid_sources : Nat
  remaining_corollary47_connection_steps : Nat

def theorem46ScalarIncrementAuditAfterG224 :
    Theorem46ScalarIncrementAuditAfterG224 where
  characteristic_zero_or_one_exposed := 1
  min_tail_monotone_closed := 1
  min_increment_monotone_closed := 1
  set_expansion_increment_bound_closed := 1
  truncation_expansion_increment_bound_closed := 1
  classical_choice_inputs_added := 0
  prop_to_data_selector_inputs_added := 0
  remaining_connect_increment_bounds_to_mid_sources := 1
  remaining_corollary47_connection_steps := 1

/-- G224 package. -/
structure Chapter4G224Theorem46ScalarIncrementPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g223 : Chapter4G223Theorem46CharacteristicExpansionPackage S
  audit : Theorem46ScalarIncrementAuditAfterG224
  scalar_increment_laws_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G224Theorem46ScalarIncrementPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G224Theorem46ScalarIncrementPackage S where
  g223 := chapter4G223Theorem46CharacteristicExpansionPackage S
  audit := theorem46ScalarIncrementAuditAfterG224
  scalar_increment_laws_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G224. -/
def bishopRegularSeqChapter4Theorem46ScalarIncrementProgressAfterG224 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 95
  total_final_goal_percent := 98
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G224: closed the scalar increment laws for Theorem 4.6: set-expansion \
    increments for 0/1 characteristic values and truncation-expansion \
    increments for n<=m are bounded by the corresponding abs increments. \
    Remaining: connect these increment laws to the carried mid source values, \
    then Corollary 4.7/4.10."


end BishopCReal
