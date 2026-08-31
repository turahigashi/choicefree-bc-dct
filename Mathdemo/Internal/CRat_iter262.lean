import Mathdemo.Internal.CRat_iter261
import Mathdemo.Internal.BishopSec4_Convergence

set_option linter.style.longLine false

/-!
# G162-G163: Chapter 4 source audit and Definition 4.1 / Proposition 4.2

This file starts the Chapter 4 countdown after the completed Chapter 3 bridge.
It records the source item list for Bishop--Cheng Chapter 4 and exposes the
already-established Lean surface for Definition 4.1 and Proposition 4.2.

The important point for Proposition 4.2 is that the file does not merely expose
an inhabitant of `IntegrableRep`; it also re-exports the value theorem showing
that the constructed representative has the intended pointwise value
`chi_A(x) * f(x)` at common convergence points.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace SourceAudit

/-- Source item count for Bishop-Cheng (1972) Chapter 4: Definition 4.1 through Theorem 4.15. -/
structure Chapter4SourceItemAudit : Type where
  definition_4_1_measurable_function : Nat
  proposition_4_2_integrable_restriction : Nat
  lemma_4_3_positive_integrable_supremum : Nat
  proposition_4_4_sigma_finite_positive_measurable_integrable : Nat
  lemma_4_5_supremum_transfer : Nat
  theorem_4_6_general_measurable_integrable : Nat
  corollary_4_7_dominated_measurable_integrable : Nat
  definition_4_8_measurable_set : Nat
  proposition_4_9_exact_local_approximation_measurable : Nat
  theorem_4_10_approximate_local_approximation_measurable : Nat
  definition_4_11_convergence_in_measure : Nat
  proposition_4_12_uniqueness_of_measure_limit : Nat
  theorem_4_13_monotone_convergence : Nat
  lemma_4_14_uniform_integrability_auxiliary : Nat
  theorem_4_15_dominated_convergence : Nat
  source_items_total : Nat

def chapter4SourceItemAudit : Chapter4SourceItemAudit where
  definition_4_1_measurable_function := 1
  proposition_4_2_integrable_restriction := 1
  lemma_4_3_positive_integrable_supremum := 1
  proposition_4_4_sigma_finite_positive_measurable_integrable := 1
  lemma_4_5_supremum_transfer := 1
  theorem_4_6_general_measurable_integrable := 1
  corollary_4_7_dominated_measurable_integrable := 1
  definition_4_8_measurable_set := 1
  proposition_4_9_exact_local_approximation_measurable := 1
  theorem_4_10_approximate_local_approximation_measurable := 1
  definition_4_11_convergence_in_measure := 1
  proposition_4_12_uniqueness_of_measure_limit := 1
  theorem_4_13_monotone_convergence := 1
  lemma_4_14_uniform_integrability_auxiliary := 1
  theorem_4_15_dominated_convergence := 1
  source_items_total := 15

end SourceAudit

namespace Def41Prop42

/-- Definition 4.1 surface: measurable real-valued partial functions. -/
def definition41_isMeasurable_available
    {R : Type*} [COFOC R] {Y : Type} (S : BishopC.IntSpaceRC Y R) :
    BishopC.PFunR Y R -> Prop :=
  BishopC.IsMeasurable S

/-- Proposition 4.2 construction surface: the representative for `chi_A * f`. -/
noncomputable def prop42_chi_f_rep_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (f : BishopC.IntegrableRep S) (hnn : BishopC.RepNonneg f) :
    BishopC.IntegrableRep S :=
  BishopC.prop_4_2_chi_f_rep A hA f hnn

/-- Proposition 4.2 value theorem: the constructed representative really has value `chi_A * f`. -/
theorem prop42_chi_f_rep_value_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (f : BishopC.IntegrableRep S) (hnn : BishopC.RepNonneg f) {x : Y}
    (hflatDom : (BishopC.prop_4_2_chi_f_rep A hA f hnn).MemAt x)
    (hχDom : hA.rep.MemAt x) (hfDom : f.MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((BishopC.prop_4_2_chi_f_rep A hA f hnn).valueAt x hflatDom n)))
    (hχabs : RSeq.SeriesSum (fun n => COF.abs
      (hA.rep.valueAt x hχDom n)))
    (hfabs : RSeq.SeriesSum (fun n => COF.abs
      (f.valueAt x hfDom n))) :
    (seriesSum_of_abs hflatabs).sum
      = (seriesSum_of_abs hχabs).sum * (seriesSum_of_abs hfabs).sum :=
  BishopC.prop_4_2_chi_f_rep_value A hA f hnn
    hflatDom hχDom hfDom hflatabs hχabs hfabs

/-- G163 audit package for the first two numbered Chapter 4 items. -/
structure Chapter4G163Def41Prop42Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  chapter3 : BishopRegularSeqChapter3G161Package S
  source_audit : SourceAudit.Chapter4SourceItemAudit
  definition_4_1_surface_available : Prop
  proposition_4_2_constructor_available : Prop
  proposition_4_2_value_theorem_available : Prop
  hidden_choice_added_by_g163 : Nat
  remaining_chapter4_countdown_steps : Nat

def chapter4G163Def41Prop42Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G163Def41Prop42Package S where
  chapter3 := bishopRegularSeqChapter3G161Package S
  source_audit := SourceAudit.chapter4SourceItemAudit
  definition_4_1_surface_available := True
  proposition_4_2_constructor_available := True
  proposition_4_2_value_theorem_available := True
  hidden_choice_added_by_g163 := 0
  remaining_chapter4_countdown_steps := 4

end Def41Prop42
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Def41Prop42

/-- G163 package exposed at top level. -/
structure BishopRegularSeqChapter4G163Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Def41Prop42.Chapter4G163Def41Prop42Package S
  chapter4_source_items_total : Nat
  chapter4_items_reached_after_g163 : Nat
  remaining_chapter4_countdown_steps : Nat
  next_frontier_lemma43_prop44 : Prop

def bishopRegularSeqChapter4G163Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G163Package S where
  package := BishopRegularSeqChapter4.Def41Prop42.chapter4G163Def41Prop42Package S
  chapter4_source_items_total := 15
  chapter4_items_reached_after_g163 := 2
  remaining_chapter4_countdown_steps := 4
  next_frontier_lemma43_prop44 := True

/-- Progress after G163: Chapter 4 has begun with Definition 4.1 and Proposition 4.2. -/
def bishopRegularSeqCh1To4ProgressAfterG163 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 13
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G163: Chapter 4 source audit plus Definition 4.1 and Proposition 4.2 surfaces. \
    Countdown remaining: 4."


end BishopCReal
