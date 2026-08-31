import Mathdemo.Internal.Real.RemoveDirectAbsErrorRowSeeds

set_option linter.style.longLine false

/-!
# G255: build the theorem-4.15 majorant split from source cover-set data

G254 still accepted the full majorant split estimate as a public input.  The
older source route already proves that estimate from Bishop's displayed
cover-set/tail-budget argument for the constructive majorant `g + |f|`.

This file reuses that argument without reintroducing PFun representatives:
the only theorem-4.15 convergence datum left in the mainline is the
source-level measure convergence of the absolute-error sequence.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 local source data after the majorant split is constructed
internally from the source cover-set/tail-budget argument. -/
structure Theorem415DomainResidualMeasureStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  abs_error_converges :
    BishopC.Lemma414ConvergeInMeasureToZeroData
      (S := S) (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- Row-seed provider for the G255 source data. -/
noncomputable def theorem415_domainResidualMeasure_rowSeedProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415DomainResidualMeasureStatementData (S := S) fn f) :
    BishopC.Lemma415Prop42RowSeedToolsProvider (S := S) :=
  BishopC.Lemma415Prop42RowSeedToolsProvider.of_generalIBDomainResidualProvider
    (S := S) D.domainResidualProvider

/-- Build majorant-choice data for the constructive majorant `g + |f|`.

This is the source proof's cover-set construction specialized to the current
domain-residual route.
-/
noncomputable def theorem415_domainResidual_majorant_choice_from_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415DomainResidualMeasureStatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantChoiceSourceData
      (S := S) fn f (D.g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f D.g D.domination.g_nonneg)
      eps :=
  let P := theorem415_domainResidualMeasure_rowSeedProvider (S := S) D
  let majorant := D.g.add f.absVal
  let majorant_nonneg :=
    theorem415_g_add_absf_majorant_nonneg
      (S := S) f D.g D.domination.g_nonneg
  let budget : BishopC.Lemma415TailBudgetSourceData (R := R) eps :=
    BishopC.lemma_4_15_default_tail_budget (R := R) eps heps
  let majorantComp :
      BishopC.Lemma415GComplementTailRelChoiceSourceData
        (S := S) majorant majorant_nonneg eps :=
    BishopC.lemma_4_15_g_complement_tail_rel_choice_data_from_coverSetBudget
      (S := S) majorant majorant_nonneg eps
      (P.rowSeeds majorant majorant_nonneg)
      budget
  let majorantTail :
      BishopC.Lemma415GSingleTailRelChoiceSourceData
        (S := S) majorant majorant_nonneg eps :=
    BishopC.lemma_4_15_g_single_tail_rel_choice_source_data_from_g_complement_tail_data
      (S := S) majorant majorant_nonneg eps majorantComp
  {
    majorantSeeds := majorantTail.gSeeds
    A := majorantTail.A
    hA := majorantTail.hA
    N := majorantTail.N
    N_ge_one := majorantTail.N_ge_one
    epsAB := budget.epsAB
    epsNeg := budget.epsNeg
    epsAB_pos := budget.epsAB_pos
    pieces_sum_lt := budget.pieces_sum_lt
    dominatesError :=
      theorem415_abs_error_dominated_by_g_add_absf
        (S := S) fn f D.g D.domination.dominated_fn
    majorantNegSmall := by
      have h_epsG_nonneg : BishopC.Nonneg budget.epsG :=
        BishopC.le_of_lt budget.epsG_pos
      have h_epsG_le_double :
          BishopC.Le budget.epsG (budget.epsG + budget.epsG) := by
        apply BishopC.le_of_nonneg_sub
        rw [show (budget.epsG + budget.epsG) - budget.epsG =
            budget.epsG from by ring]
        exact h_epsG_nonneg
      have h_epsG_lt_epsNeg : COF.lt budget.epsG budget.epsNeg :=
        BishopC.lt_of_le_of_lt h_epsG_le_double budget.gTailBudget
      exact COFO.lt_trans majorantTail.gNegSmall h_epsG_lt_epsNeg
  }

/-- Build the full majorant split from source cover-set data. -/
noncomputable def theorem415_domainResidual_majorant_split_from_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415DomainResidualMeasureStatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f (D.g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f D.g D.domination.g_nonneg)
      eps :=
  BishopC.lemma_4_15_majorant_split_uniform_source_data_from_choice_data
    (S := S) fn f (D.g.add f.absVal)
    (theorem415_g_add_absf_majorant_nonneg
      (S := S) f D.g D.domination.g_nonneg)
    eps
    (theorem415_domainResidual_majorant_choice_from_sourceData
      (S := S) D eps heps)

/-- Rebuild the G254 statement data with the majorant split supplied by the
source constructor above. -/
noncomputable def theorem415_domainResidual_statement_data_of_measureData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415DomainResidualMeasureStatementData (S := S) fn f) :
    Theorem415LocalMajorantSplitDomainResidualStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  domainResidualProvider := D.domainResidualProvider
  majorant_split :=
    theorem415_domainResidual_majorant_split_from_sourceData (S := S) D
  abs_error_converges := D.abs_error_converges

/-- Theorem 4.15 after the majorant split has been rebuilt from source
cover-set data. -/
noncomputable def
    theorem415_integral_convergence_from_domainResidual_measure_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415DomainResidualMeasureStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_domainResidual_statement_data
    (S := S)
    (theorem415_domainResidual_statement_data_of_measureData (S := S) D)

structure Theorem415MeasureRouteAuditAfterG255 : Type where
  majorant_split_public_input_required : Nat
  majorant_split_built_from_source_cover_set_data : Nat
  direct_abs_error_rowSeeds_public_input_required : Nat
  domainResidualProvider_visible_frontier : Nat
  pfun_representation_data_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_measure_convergence_frontier : Nat

def theorem415MeasureRouteAuditAfterG255 :
    Theorem415MeasureRouteAuditAfterG255 where
  majorant_split_public_input_required := 0
  majorant_split_built_from_source_cover_set_data := 1
  direct_abs_error_rowSeeds_public_input_required := 0
  domainResidualProvider_visible_frontier := 1
  pfun_representation_data_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_measure_convergence_frontier := 1

structure Chapter4G255Theorem415MeasurePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g254 : Chapter4G254Theorem415DomainResidualPackage S
  audit : Theorem415MeasureRouteAuditAfterG255
  majorant_split_removed_this_step : Nat
  remaining_core_source_frontiers : Nat
  remaining_chapter4_provider_frontiers : Nat

def chapter4G255Theorem415MeasurePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G255Theorem415MeasurePackage S where
  g254 := chapter4G254Theorem415DomainResidualPackage S
  audit := theorem415MeasureRouteAuditAfterG255
  majorant_split_removed_this_step := 1
  remaining_core_source_frontiers := 1
  remaining_chapter4_provider_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G255. -/
def bishopRegularSeqChapter4Theorem415MeasureProgressAfterG255 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G255: removed the majorant split estimate as a public theorem 4.15 input. \
    It is now built from the source cover-set/tail-budget construction for the \
    constructive majorant g + |f|. The remaining core source frontier is \
    measure convergence of the absolute-error sequence; the domain-residual \
    provider remains as the visible Proposition 4.2 provider frontier."


end BishopCReal
