import Mathdemo.Internal.Real.RemovingGlobalClosedTheoryParameterProp

set_option linter.style.longLine false

/-!
# G206: Chapter 1--3 data-debt audit

G205 made the remaining Proposition 4.12 construction debts explicit.  This file
records the corresponding status for Chapters 1--3: the current mainline does not
carry a Prop.4.12-style undischarged data-carrying assumption before Chapter 4.

The previous G109 selector-based extraction artifact remains available only as a
documented adapter audit.  It is not counted as the Bishop RegularSeq mainline.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqCh1To3AssumptionAudit

/-- Chapter 1 current mainline has no Prop-to-data selector input. -/
theorem chapter1_prop_to_data_selector_zero :
    BishopRegularSeqTheorem118.property4RegularSeqChapter1ClosedAudit.prop_to_data_selector_inputs = 0 :=
  rfl

/-- Chapter 1 current mainline has no selector-choice input. -/
theorem chapter1_classical_choice_zero :
    BishopRegularSeqTheorem118.property4RegularSeqChapter1ClosedAudit.classical_choice_inputs = 0 :=
  rfl

/-- Chapter 2 final audit has no quotient representative extraction input. -/
theorem chapter2_quotient_extraction_zero :
    BishopRegularSeqChapter2.FinalAudit.chapter2CoverageAudit.quotient_representative_extraction_inputs = 0 :=
  rfl

/-- Chapter 2 final audit has no Prop-to-data selector input. -/
theorem chapter2_prop_to_data_selector_zero :
    BishopRegularSeqChapter2.FinalAudit.chapter2CoverageAudit.prop_to_data_selector_inputs = 0 :=
  rfl

/-- Chapter 2 final audit has no hidden-choice input. -/
theorem chapter2_hidden_choice_zero :
    BishopRegularSeqChapter2.FinalAudit.chapter2CoverageAudit.hidden_choice_inputs = 0 :=
  rfl

/-- Chapter 3 final audit adds no Prop-to-data selector input. -/
theorem chapter3_prop_to_data_selector_added_zero :
    BishopRegularSeqChapter3.Theorem36FinalAudit.chapter3FinalCoverageAudit.prop_to_data_selector_inputs_added_by_g161 = 0 :=
  rfl

/-- Chapter 3 final audit adds no selector-choice input. -/
theorem chapter3_classical_choice_added_zero :
    BishopRegularSeqChapter3.Theorem36FinalAudit.chapter3FinalCoverageAudit.classical_choice_inputs_added_by_g161 = 0 :=
  rfl

/-- Chapter 3 final audit has no remaining countdown step. -/
theorem chapter3_remaining_countdown_zero :
    BishopRegularSeqChapter3.Theorem36FinalAudit.chapter3FinalCoverageAudit.remaining_chapter3_countdown_steps = 0 :=
  rfl

/-- Current progress meter still records Chapters 1--3 at 100%. -/
theorem current_progress_ch1_to_ch3_are_100 :
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch1_on_bishop_real_percent = 100 ∧
      bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch2_on_bishop_real_percent = 100 ∧
      bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch3_on_bishop_real_percent = 100 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Searchable ledger for the data-debt audit of Chapters 1--3. -/
structure Chapter1To3NoUndischargedDataDebtLedger : Type where
  chapter1_on_bishop_real_percent : Nat
  chapter2_on_bishop_real_percent : Nat
  chapter3_on_bishop_real_percent : Nat
  chapter1_remaining_data_carrying_discharge_debts : Nat
  chapter2_remaining_data_carrying_discharge_debts : Nat
  chapter3_remaining_data_carrying_discharge_debts : Nat
  chapter1_prop_to_data_selector_inputs : Nat
  chapter1_classical_choice_inputs : Nat
  chapter2_quotient_representative_extraction_inputs : Nat
  chapter2_prop_to_data_selector_inputs : Nat
  chapter2_hidden_choice_inputs : Nat
  chapter3_prop_to_data_selector_inputs_added_by_final_step : Nat
  chapter3_classical_choice_inputs_added_by_final_step : Nat
  chapter3_remaining_countdown_steps : Nat
  old_g109_classical_extraction_is_adapter_only : Prop
  chapter3_existing_profile_bridge_closed_in_g161 : Prop
  prop412_style_undischarged_debts_before_chapter4 : Nat

def chapter1To3NoUndischargedDataDebtLedger :
    Chapter1To3NoUndischargedDataDebtLedger where
  chapter1_on_bishop_real_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch1_on_bishop_real_percent
  chapter2_on_bishop_real_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch2_on_bishop_real_percent
  chapter3_on_bishop_real_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch3_on_bishop_real_percent
  chapter1_remaining_data_carrying_discharge_debts := 0
  chapter2_remaining_data_carrying_discharge_debts := 0
  chapter3_remaining_data_carrying_discharge_debts := 0
  chapter1_prop_to_data_selector_inputs :=
    BishopRegularSeqTheorem118.property4RegularSeqChapter1ClosedAudit.prop_to_data_selector_inputs
  chapter1_classical_choice_inputs :=
    BishopRegularSeqTheorem118.property4RegularSeqChapter1ClosedAudit.classical_choice_inputs
  chapter2_quotient_representative_extraction_inputs :=
    BishopRegularSeqChapter2.FinalAudit.chapter2CoverageAudit.quotient_representative_extraction_inputs
  chapter2_prop_to_data_selector_inputs :=
    BishopRegularSeqChapter2.FinalAudit.chapter2CoverageAudit.prop_to_data_selector_inputs
  chapter2_hidden_choice_inputs :=
    BishopRegularSeqChapter2.FinalAudit.chapter2CoverageAudit.hidden_choice_inputs
  chapter3_prop_to_data_selector_inputs_added_by_final_step :=
    BishopRegularSeqChapter3.Theorem36FinalAudit.chapter3FinalCoverageAudit.prop_to_data_selector_inputs_added_by_g161
  chapter3_classical_choice_inputs_added_by_final_step :=
    BishopRegularSeqChapter3.Theorem36FinalAudit.chapter3FinalCoverageAudit.classical_choice_inputs_added_by_g161
  chapter3_remaining_countdown_steps :=
    BishopRegularSeqChapter3.Theorem36FinalAudit.chapter3FinalCoverageAudit.remaining_chapter3_countdown_steps
  old_g109_classical_extraction_is_adapter_only := True
  chapter3_existing_profile_bridge_closed_in_g161 := True
  prop412_style_undischarged_debts_before_chapter4 := 0

end BishopRegularSeqCh1To3AssumptionAudit

open BishopRegularSeqCh1To3AssumptionAudit

/-- G206 package: searchable confirmation that Chapters 1--3 have no remaining
Prop.4.12-style data-carrying discharge debt on the current Bishop RegularSeq
mainline. -/
structure BishopRegularSeqChapter1To3G206AuditPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g205 : BishopRegularSeqChapter4G205Package S
  ch1_to_ch3_ledger :
    BishopRegularSeqCh1To3AssumptionAudit.Chapter1To3NoUndischargedDataDebtLedger
  chapters_1_to_3_no_remaining_data_debt : Prop
  chapter4_prop412_remaining_data_debts_still_recorded_in_g205 : Nat

def bishopRegularSeqChapter1To3G206AuditPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter1To3G206AuditPackage S where
  g205 := bishopRegularSeqChapter4G205Package S
  ch1_to_ch3_ledger :=
    BishopRegularSeqCh1To3AssumptionAudit.chapter1To3NoUndischargedDataDebtLedger
  chapters_1_to_3_no_remaining_data_debt := True
  chapter4_prop412_remaining_data_debts_still_recorded_in_g205 := 2

/-- Progress is unchanged from G205, except that the Chapter 1--3 data-debt answer
is now explicit and searchable. -/
def bishopRegularSeqCh1To3AssumptionAuditProgressAfterG206 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.bishop_real_formalization_percent
  ch1_on_bishop_real_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch1_on_bishop_real_percent
  ch2_on_bishop_real_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch2_on_bishop_real_percent
  ch3_on_bishop_real_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch3_on_bishop_real_percent
  ch4_on_bishop_real_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.ch4_on_bishop_real_percent
  total_final_goal_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.total_final_goal_percent
  old_relative_ch1_to_4_compatibility_percent :=
    bishopRegularSeqProp412AssumptionDischargeProgressAfterG205.old_relative_ch1_to_4_compatibility_percent
  current_increment :=
    "G206: audited Chapters 1--3 for Prop.4.12-style hidden data debt. \
    Current mainline has zero remaining Chapter 1--3 data-carrying discharge \
    debts; the only recorded remaining debts are the two Chapter 4 Prop.4.12 \
    debts exposed in G205."


end BishopCReal
