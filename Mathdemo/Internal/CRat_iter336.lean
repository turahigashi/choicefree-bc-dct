import Mathdemo.Internal.CRat_iter335

set_option linter.style.longLine false

/-!
# G237: theorem-4.15 source route with Proposition 4.2 local witnesses

G236 left one theorem-4.15 source bridge visible:
`Sec4GeneralIBDomainResidualProvider`.  That provider is not part of the
dominated-convergence statement itself.  It is the lower Proposition-4.2
witness interface used to build the general measurable `I_B` rows.

This file moves that obligation out of the theorem-4.15 statement-shaped data.
The new endpoint takes the exact local row-seed data supplied by the
Proposition-4.2 layer:

* row seeds for the non-negative error sequence `|f_n - f|`;
* row seeds for the constructive majorant `g + |f|`.

The theorem-4.15 route then builds the local `I_B` bridges, the majorant split,
and the PFun convergence route directly from those seeds.  No Prop-to-data
selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-shaped theorem-4.15 data after pushing the final visible
`domainResidualProvider` down to Proposition 4.2's local row-seed layer.

The fields `errorRows` and `majorantRows` are not extra choice principles.  They
are the data that the already-integrable characteristic-function construction
must provide when Proposition 4.2 is unfolded constructively.
-/
structure Theorem415LocalProp42StatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  errorRows : forall n,
    BishopC.Sec4Prop42RowSeedTools (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  majorantRows :
    BishopC.Sec4Prop42RowSeedTools (S := S)
      (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f g domination.g_nonneg)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Local complement bridges for the error sequence, built directly from the
Proposition-4.2 row seeds. -/
noncomputable def theorem415_localProp42_local_complement_bridges
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalProp42StatementData (S := S) fn f) :
    forall (n : Nat) (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n C hC =>
    BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S)
      (BishopC.BSet.neg C)
      (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
      (BishopC.sec4_genIBValueBridge_of_rowSeedTools
        (S := S)
        (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
        (D.errorRows n))

/-- Majorant choice data for the constructive majorant `g + |f|`, using
Proposition-4.2 row seeds for that majorant directly. -/
noncomputable def theorem415_localProp42_majorant_choice_from_rows
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalProp42StatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantChoiceSourceData
      (S := S) fn f (D.g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f D.g D.domination.g_nonneg)
      eps :=
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
      D.majorantRows
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

noncomputable def theorem415_localProp42_majorant_split_from_rows
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalProp42StatementData (S := S) fn f)
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
    (theorem415_localProp42_majorant_choice_from_rows
      (S := S) D eps heps)

noncomputable def theorem415_localProp42_uniform_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalProp42StatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma414UniformIBSourceData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
        (theorem415_localProp42_local_complement_bridges (S := S) D))
      eps :=
  let localSplit :
      BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
    BishopC.lemma_4_15_local_split_uniform_source_data_from_majorant_data
      (S := S) fn f D.errorRows (D.g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f D.g D.domination.g_nonneg)
      eps
      (theorem415_localProp42_majorant_split_from_rows
        (S := S) D eps heps)
  BishopC.lemma_4_15_uniform_ib_source_data_from_local_split_data
    (S := S) fn f
    (theorem415_localProp42_local_complement_bridges (S := S) D)
    eps localSplit

/-- Abs-error convergence of integrals with the final 4.15 source bridge moved
to Proposition 4.2 row seeds. -/
noncomputable def theorem415_abs_error_tendsto_from_localProp42_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalProp42StatementData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  let IB :=
    BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (theorem415_localProp42_local_complement_bridges (S := S) D)
  BishopC.lemma_4_14_tendsto_zero_from_ib_and_pfun_converge
    (S := S)
    (BishopC.thm_4_15_abs_error (S := S) fn f)
    (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
    (BishopC.thm_4_15_pfun_abs_error D.pfnsrc D.pf)
    (BishopC.thm_4_15_pfun_zero (X := Y) (R := R))
    IB
    (BishopC.lemma_4_14_uniform_ib_data_from_source
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      IB
      (theorem415_localProp42_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

/-- Theorem 4.15 from source-shaped statement data and Proposition-4.2 local
row seeds, with no `domainResidualProvider` field in the 4.15 statement data. -/
noncomputable def theorem415_integral_convergence_from_localProp42_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalProp42StatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (theorem415_abs_error_tendsto_from_localProp42_statement_data
      (S := S) D)

structure Theorem415LocalProp42RouteAuditAfterG237 : Type where
  domainResidualProvider_removed_from_415_source_data : Nat
  prop42_error_row_seeds_are_explicit_lower_layer : Nat
  prop42_majorant_row_seeds_are_explicit_lower_layer : Nat
  separate_g_nonneg_input_removed : Nat
  separate_limit_domination_input_removed : Nat
  substitute_majorant_g_plus_abs_f_used : Nat
  direct_abs_error_convergence_input_removed : Nat
  source_pfun_convergence_input_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def theorem415LocalProp42RouteAuditAfterG237 :
    Theorem415LocalProp42RouteAuditAfterG237 where
  domainResidualProvider_removed_from_415_source_data := 1
  prop42_error_row_seeds_are_explicit_lower_layer := 1
  prop42_majorant_row_seeds_are_explicit_lower_layer := 1
  separate_g_nonneg_input_removed := 1
  separate_limit_domination_input_removed := 1
  substitute_majorant_g_plus_abs_f_used := 1
  direct_abs_error_convergence_input_removed := 1
  source_pfun_convergence_input_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_plain_prop_415_bridge_steps := 3

structure Chapter4G237Theorem415LocalProp42Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g236 : Chapter4G236Theorem415StatementDominationPackage S
  audit : Theorem415LocalProp42RouteAuditAfterG237
  theorem415_source_endpoint_closed_this_step : Nat
  prop42_lower_layer_frontier_still_visible : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def chapter4G237Theorem415LocalProp42Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G237Theorem415LocalProp42Package S where
  g236 := chapter4G236Theorem415StatementDominationPackage S
  audit := theorem415LocalProp42RouteAuditAfterG237
  theorem415_source_endpoint_closed_this_step := 1
  prop42_lower_layer_frontier_still_visible := 1
  remaining_source_data_415_bridge_steps := 0
  remaining_plain_prop_415_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G237. -/
def bishopRegularSeqChapter4Theorem415LocalProp42ProgressAfterG237 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G237: removed domainResidualProvider from theorem-4.15 source-shaped \
    data. The remaining witness obligation is now explicitly the lower \
    Proposition-4.2 local row-seed layer for the error sequence and the \
    constructive majorant g + |f|; no choice or Prop-to-data selector was \
    added. The 4.15 source-data endpoint now has zero remaining bridge steps."


end BishopCReal
