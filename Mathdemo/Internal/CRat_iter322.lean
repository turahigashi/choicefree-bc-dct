import Mathdemo.Internal.CRat_iter321

set_option linter.style.longLine false

/-!
# G223: characteristic expansion laws for Theorem 4.6 local steps

G222 closed the scalar `f+`, `f-`, `|f|`, and nonnegative-`mid` ingredients.
This file closes the characteristic-function part of the set-expansion
calculation: the values of `χ_A` and `χ_B` are bounded by `χ_(A∨B)`, using
only the `IntegrableSet1.valid` witnesses already carried by the sets.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge

/-- Characteristic values supplied by `IntegrableSet1.valid` are nonnegative. -/
theorem theorem46_chi_value_nonneg
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {x : Y}
    (hADom : hA.rep.MemAt x)
    (hAabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hADom m))) :
    BishopC.Nonneg (BishopC.seriesSum_of_abs hAabs).sum := by
  rcases (hA.valid x hADom hAabs).1 with hA1 | hA2
  · have h1 :
        (BishopC.seriesSum_of_abs hAabs).sum = 1 :=
      (hA.valid x hADom hAabs).2.1 hA1
        (BishopC.seriesSum_of_abs hAabs)
    rw [h1]
    exact BishopC.le_of_lt COFO.one_pos
  · have h0 :
        (BishopC.seriesSum_of_abs hAabs).sum = 0 :=
      (hA.valid x hADom hAabs).2.2 hA2
        (BishopC.seriesSum_of_abs hAabs)
    rw [h0]
    exact BishopC.le_refl 0

/-- `χ_A ≤ χ_(A∨B)` at the carried characteristic values. -/
theorem theorem46_chi_or_left_value_le
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A B : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hB : BishopC.IntegrableSet1 S B)
    {x : Y}
    (hADom : hA.rep.MemAt x)
    (hBDom : hB.rep.MemAt x)
    (hOrDom : (BishopC.IntegrableSet1_or hA hB).rep.MemAt x)
    (hAabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hADom m)))
    (hBabs : RSeq.SeriesSum
      (fun m => COF.abs (hB.rep.valueAt x hBDom m)))
    (hOrabs : RSeq.SeriesSum
      (fun m =>
        COF.abs ((BishopC.IntegrableSet1_or hA hB).rep.valueAt
          x hOrDom m))) :
    BishopC.Le
      (BishopC.seriesSum_of_abs hAabs).sum
      (BishopC.seriesSum_of_abs hOrabs).sum := by
  rcases (hA.valid x hADom hAabs).1 with hA1 | hA2
  · have hAeq :
        (BishopC.seriesSum_of_abs hAabs).sum = 1 :=
      (hA.valid x hADom hAabs).2.1 hA1
        (BishopC.seriesSum_of_abs hAabs)
    have hOr1 : x ∈ (BishopC.BSet.or A B).S1 := by
      rcases (hB.valid x hBDom hBabs).1 with hB1 | hB2
      · exact Or.inl (Or.inl ⟨hA1, hB1⟩)
      · exact Or.inl (Or.inr ⟨hA1, hB2⟩)
    have hOreq :
        (BishopC.seriesSum_of_abs hOrabs).sum = 1 :=
      ((BishopC.IntegrableSet1_or hA hB).valid x hOrDom hOrabs).2.1 hOr1
        (BishopC.seriesSum_of_abs hOrabs)
    rw [hAeq, hOreq]
    exact BishopC.le_refl 1
  · have hAeq :
        (BishopC.seriesSum_of_abs hAabs).sum = 0 :=
      (hA.valid x hADom hAabs).2.2 hA2
        (BishopC.seriesSum_of_abs hAabs)
    rw [hAeq]
    exact theorem46_chi_value_nonneg
      (BishopC.IntegrableSet1_or hA hB) hOrDom hOrabs

/-- `χ_B ≤ χ_(A∨B)` at the carried characteristic values. -/
theorem theorem46_chi_or_right_value_le
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A B : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hB : BishopC.IntegrableSet1 S B)
    {x : Y}
    (hADom : hA.rep.MemAt x)
    (hBDom : hB.rep.MemAt x)
    (hOrDom : (BishopC.IntegrableSet1_or hA hB).rep.MemAt x)
    (hAabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hADom m)))
    (hBabs : RSeq.SeriesSum
      (fun m => COF.abs (hB.rep.valueAt x hBDom m)))
    (hOrabs : RSeq.SeriesSum
      (fun m =>
        COF.abs ((BishopC.IntegrableSet1_or hA hB).rep.valueAt
          x hOrDom m))) :
    BishopC.Le
      (BishopC.seriesSum_of_abs hBabs).sum
      (BishopC.seriesSum_of_abs hOrabs).sum := by
  rcases (hB.valid x hBDom hBabs).1 with hB1 | hB2
  · have hBeq :
        (BishopC.seriesSum_of_abs hBabs).sum = 1 :=
      (hB.valid x hBDom hBabs).2.1 hB1
        (BishopC.seriesSum_of_abs hBabs)
    have hOr1 : x ∈ (BishopC.BSet.or A B).S1 := by
      rcases (hA.valid x hADom hAabs).1 with hA1 | hA2
      · exact Or.inl (Or.inl ⟨hA1, hB1⟩)
      · exact Or.inr ⟨hA2, hB1⟩
    have hOreq :
        (BishopC.seriesSum_of_abs hOrabs).sum = 1 :=
      ((BishopC.IntegrableSet1_or hA hB).valid x hOrDom hOrabs).2.1 hOr1
        (BishopC.seriesSum_of_abs hOrabs)
    rw [hBeq, hOreq]
    exact BishopC.le_refl 1
  · have hBeq :
        (BishopC.seriesSum_of_abs hBabs).sum = 0 :=
      (hB.valid x hBDom hBabs).2.2 hB2
        (BishopC.seriesSum_of_abs hBabs)
    rw [hBeq]
    exact theorem46_chi_value_nonneg
      (BishopC.IntegrableSet1_or hA hB) hOrDom hOrabs

/-- Left set expansion, after multiplying by a nonnegative scalar value and
applying `mid`. -/
theorem theorem46_scalarMid_or_left_expansion_mono
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A B : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hB : BishopC.IntegrableSet1 S B)
    {x : Y}
    (hADom : hA.rep.MemAt x)
    (hBDom : hB.rep.MemAt x)
    (hOrDom : (BishopC.IntegrableSet1_or hA hB).rep.MemAt x)
    (hAabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hADom m)))
    (hBabs : RSeq.SeriesSum
      (fun m => COF.abs (hB.rep.valueAt x hBDom m)))
    (hOrabs : RSeq.SeriesSum
      (fun m =>
        COF.abs ((BishopC.IntegrableSet1_or hA hB).rep.valueAt
          x hOrDom m)))
    (n : Nat) {v : R} (hv : BishopC.Nonneg v) :
    BishopC.Le
      (prop412ScalarMid n ((BishopC.seriesSum_of_abs hAabs).sum * v))
      (prop412ScalarMid n ((BishopC.seriesSum_of_abs hOrabs).sum * v)) := by
  have hχA : BishopC.Nonneg (BishopC.seriesSum_of_abs hAabs).sum :=
    theorem46_chi_value_nonneg hA hADom hAabs
  have hχOr : BishopC.Nonneg (BishopC.seriesSum_of_abs hOrabs).sum :=
    theorem46_chi_value_nonneg
      (BishopC.IntegrableSet1_or hA hB) hOrDom hOrabs
  have hleft_nonneg :
      BishopC.Nonneg ((BishopC.seriesSum_of_abs hAabs).sum * v) :=
    COFO.mul_nonneg hχA hv
  have hright_nonneg :
      BishopC.Nonneg ((BishopC.seriesSum_of_abs hOrabs).sum * v) :=
    COFO.mul_nonneg hχOr hv
  have hχle :
      BishopC.Le
        (BishopC.seriesSum_of_abs hAabs).sum
        (BishopC.seriesSum_of_abs hOrabs).sum :=
    theorem46_chi_or_left_value_le hA hB
      hADom hBDom hOrDom hAabs hBabs hOrabs
  have hmul :
      BishopC.Le
        ((BishopC.seriesSum_of_abs hAabs).sum * v)
        ((BishopC.seriesSum_of_abs hOrabs).sum * v) :=
    BishopC.lemma33_mul_le_mul_right hχle hv
  exact theorem46_scalarMid_nonneg_value_mono n
    hleft_nonneg hright_nonneg hmul

/-- Right set expansion, after multiplying by a nonnegative scalar value and
applying `mid`. -/
theorem theorem46_scalarMid_or_right_expansion_mono
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A B : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hB : BishopC.IntegrableSet1 S B)
    {x : Y}
    (hADom : hA.rep.MemAt x)
    (hBDom : hB.rep.MemAt x)
    (hOrDom : (BishopC.IntegrableSet1_or hA hB).rep.MemAt x)
    (hAabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hADom m)))
    (hBabs : RSeq.SeriesSum
      (fun m => COF.abs (hB.rep.valueAt x hBDom m)))
    (hOrabs : RSeq.SeriesSum
      (fun m =>
        COF.abs ((BishopC.IntegrableSet1_or hA hB).rep.valueAt
          x hOrDom m)))
    (n : Nat) {v : R} (hv : BishopC.Nonneg v) :
    BishopC.Le
      (prop412ScalarMid n ((BishopC.seriesSum_of_abs hBabs).sum * v))
      (prop412ScalarMid n ((BishopC.seriesSum_of_abs hOrabs).sum * v)) := by
  have hχB : BishopC.Nonneg (BishopC.seriesSum_of_abs hBabs).sum :=
    theorem46_chi_value_nonneg hB hBDom hBabs
  have hχOr : BishopC.Nonneg (BishopC.seriesSum_of_abs hOrabs).sum :=
    theorem46_chi_value_nonneg
      (BishopC.IntegrableSet1_or hA hB) hOrDom hOrabs
  have hleft_nonneg :
      BishopC.Nonneg ((BishopC.seriesSum_of_abs hBabs).sum * v) :=
    COFO.mul_nonneg hχB hv
  have hright_nonneg :
      BishopC.Nonneg ((BishopC.seriesSum_of_abs hOrabs).sum * v) :=
    COFO.mul_nonneg hχOr hv
  have hχle :
      BishopC.Le
        (BishopC.seriesSum_of_abs hBabs).sum
        (BishopC.seriesSum_of_abs hOrabs).sum :=
    theorem46_chi_or_right_value_le hA hB
      hADom hBDom hOrDom hAabs hBabs hOrabs
  have hmul :
      BishopC.Le
        ((BishopC.seriesSum_of_abs hBabs).sum * v)
        ((BishopC.seriesSum_of_abs hOrabs).sum * v) :=
    BishopC.lemma33_mul_le_mul_right hχle hv
  exact theorem46_scalarMid_nonneg_value_mono n
    hleft_nonneg hright_nonneg hmul

/-- Audit after G223. -/
structure Theorem46CharacteristicExpansionAuditAfterG223 : Type where
  chi_value_nonnegative_from_valid_closed : Nat
  chi_left_le_or_closed : Nat
  chi_right_le_or_closed : Nat
  nonnegative_value_set_expansion_mid_mono_closed : Nat
  classical_choice_inputs_added : Nat
  prop_to_data_selector_inputs_added : Nat
  remaining_increment_bound_laws_for_set_and_truncation_steps : Nat
  remaining_corollary47_connection_steps : Nat

def theorem46CharacteristicExpansionAuditAfterG223 :
    Theorem46CharacteristicExpansionAuditAfterG223 where
  chi_value_nonnegative_from_valid_closed := 1
  chi_left_le_or_closed := 1
  chi_right_le_or_closed := 1
  nonnegative_value_set_expansion_mid_mono_closed := 1
  classical_choice_inputs_added := 0
  prop_to_data_selector_inputs_added := 0
  remaining_increment_bound_laws_for_set_and_truncation_steps := 1
  remaining_corollary47_connection_steps := 1

/-- G223 package. -/
structure Chapter4G223Theorem46CharacteristicExpansionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g222 : Chapter4G222Theorem46ScalarPointwisePackage S
  audit : Theorem46CharacteristicExpansionAuditAfterG223
  characteristic_expansion_laws_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G223Theorem46CharacteristicExpansionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G223Theorem46CharacteristicExpansionPackage S where
  g222 := chapter4G222Theorem46ScalarPointwisePackage S
  audit := theorem46CharacteristicExpansionAuditAfterG223
  characteristic_expansion_laws_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G223. -/
def bishopRegularSeqChapter4Theorem46CharacteristicExpansionProgressAfterG223 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 94
  total_final_goal_percent := 98
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G223: closed the characteristic set-expansion laws for Theorem 4.6: \
    chi_A and chi_B are pointwise bounded by chi_(A∨B), and this lifts through \
    multiplication by a nonnegative value and scalar mid. Remaining: increment \
    bound laws for the set/truncation steps, then Corollary 4.7/4.10."


end BishopCReal
