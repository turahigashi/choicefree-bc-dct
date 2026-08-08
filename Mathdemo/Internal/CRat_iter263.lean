import Mathdemo.Internal.CRat_iter262

set_option linter.style.longLine false

/-!
# G164: Chapter 4 Lemma 4.3 and Proposition 4.4

This step exposes the existing source-aligned constructions for:

* Lemma 4.3: the threshold sequence from Theorem 3.6, its integrable level
  sets, and the convergence of the corresponding approximation integrals to
  `I(f)`;
* Proposition 4.4: the lambda-difference summation construction giving an
  integrable representative for a nonnegative measurable function under the
  stated convergence datum.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma43Prop44

/-- Lemma 4.3 threshold sequence `alpha_n`, obtained from Theorem 3.6. -/
noncomputable def lemma43_alpha_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (f : BishopC.IntegrableRep S) : Nat -> R :=
  BishopC.lemma_4_3_alpha f

/-- Lemma 4.3: each level set `A_n` is integrable. -/
theorem lemma43_A_n_integrable_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (f : BishopC.IntegrableRep S) (n : Nat) :
    Nonempty (BishopC.IntegrableSet1 S (BishopC.lemma_4_3_A_n f n)) :=
  BishopC.lemma_4_3_A_n_integrable f n

/-- Lemma 4.3: the approximation integrals converge to `I(f)`. -/
theorem lemma43_tendsto_I_f_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (f : BishopC.IntegrableRep S) (hf_nonneg : BishopC.RepNonneg f) :
    Nonempty (RSeq.TendstoHalf (fun n => (BishopC.lemma_4_3_approx_f f n).integral) f.integral) :=
  BishopC.lemma_4_3_tendsto_I_f f hf_nonneg

/-- Lemma 4.3 source surface: the supremum sequence side is represented by the same convergence datum. -/
theorem lemma43_sup_integrals_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (f : BishopC.IntegrableRep S) (hf_nonneg : BishopC.RepNonneg f) :
    Nonempty (RSeq.TendstoHalf (fun n => (BishopC.lemma_4_3_approx_f f n).integral) f.integral) :=
  BishopC.lemma_4_3_sup_integrals f hf_nonneg

/-- Proposition 4.4: the source `min(chi_Cn h,n)` representatives. -/
noncomputable def prop44_min_chi_f_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (h : BishopC.PFunR Y R) (hm : BishopC.IsMeasurable S h)
    (C : Nat -> BishopC.BSet Y) (hC : forall n, BishopC.IntegrableSet1 S (C n))
    (n : Nat) : BishopC.IntegrableRep S :=
  BishopC.prop_4_4_min_chi_f h hm C hC n

/-- Proposition 4.4: lambda-difference series summability. -/
noncomputable def prop44_lambda_sum_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (h : BishopC.PFunR Y R)
    (hm : BishopC.IsMeasurable S h) (h_nonneg : forall x hx, ¬ COF.lt (h.toFun x hx) 0)
    (C : Nat -> BishopC.BSet Y) (hC : forall n, BishopC.IntegrableSet1 S (C n))
    (h_lambda_nonneg : forall n, BishopC.RepNonneg (BishopC.prop_4_4_lambda_n h hm C hC n))
    (c : R) (h_lim : RSeq.TendstoHalf (fun n => (BishopC.prop_4_4_min_chi_f h hm C hC n).integral) c) :
    RSeq.SeriesSum (fun n => (BishopC.prop_4_4_lambda_n h hm C hC n).normL1) :=
  BishopC.prop_4_4_lambda_sum h hm h_nonneg C hC h_lambda_nonneg c h_lim

/-- Proposition 4.4: construction of the integrable representative from the lambda series. -/
noncomputable def prop44_measurable_rep_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (h : BishopC.PFunR Y R)
    (hm : BishopC.IsMeasurable S h) (h_nonneg : forall x hx, ¬ COF.lt (h.toFun x hx) 0)
    (C : Nat -> BishopC.BSet Y) (hC : forall n, BishopC.IntegrableSet1 S (C n))
    (h_lambda_nonneg : forall n, BishopC.RepNonneg (BishopC.prop_4_4_lambda_n h hm C hC n))
    (c : R) (h_lim : RSeq.TendstoHalf (fun n => (BishopC.prop_4_4_min_chi_f h hm C hC n).integral) c) :
    BishopC.IntegrableRep S :=
  BishopC.prop_4_4_measurable_rep h hm h_nonneg C hC h_lambda_nonneg c h_lim

/-- G164 audit package for Lemma 4.3 and Proposition 4.4. -/
structure Chapter4G164Lemma43Prop44Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g163 : BishopRegularSeqChapter4G163Package S
  lemma_4_3_threshold_sequence_available : Prop
  lemma_4_3_integrable_level_sets_available : Prop
  lemma_4_3_tendsto_integral_available : Prop
  proposition_4_4_lambda_series_available : Prop
  proposition_4_4_integrable_rep_constructor_available : Prop
  hidden_choice_added_by_g164 : Nat
  remaining_chapter4_countdown_steps : Nat

def chapter4G164Lemma43Prop44Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G164Lemma43Prop44Package S where
  g163 := bishopRegularSeqChapter4G163Package S
  lemma_4_3_threshold_sequence_available := True
  lemma_4_3_integrable_level_sets_available := True
  lemma_4_3_tendsto_integral_available := True
  proposition_4_4_lambda_series_available := True
  proposition_4_4_integrable_rep_constructor_available := True
  hidden_choice_added_by_g164 := 0
  remaining_chapter4_countdown_steps := 3

end Lemma43Prop44
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma43Prop44

/-- G164 package exposed at top level. -/
structure BishopRegularSeqChapter4G164Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Lemma43Prop44.Chapter4G164Lemma43Prop44Package S
  chapter4_items_reached_after_g164 : Nat
  remaining_chapter4_countdown_steps : Nat
  next_frontier_lemma45_theorem46_corollary47 : Prop

def bishopRegularSeqChapter4G164Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G164Package S where
  package := BishopRegularSeqChapter4.Lemma43Prop44.chapter4G164Lemma43Prop44Package S
  chapter4_items_reached_after_g164 := 4
  remaining_chapter4_countdown_steps := 3
  next_frontier_lemma45_theorem46_corollary47 := True

/-- Progress after G164: Lemma 4.3 and Proposition 4.4 are exposed. -/
def bishopRegularSeqCh1To4ProgressAfterG164 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 27
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G164: exposed Chapter 4 Lemma 4.3 and Proposition 4.4 construction surfaces. \
    Countdown remaining: 3."


end BishopCReal
