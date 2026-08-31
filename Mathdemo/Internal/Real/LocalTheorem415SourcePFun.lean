import Mathdemo.Internal.Real.LocalTheorem415DomainResidual

set_option linter.style.longLine false

/-!
# G234: Local theorem 4.15 from source PFun convergence data

G233 still accepted `Lemma414ConvergeInMeasureToZeroData` for the abs-error
sequence.  This file removes that direct abs-error convergence input from the
local route.  Instead it consumes the source-shaped Type/Sigma convergence
data `fn -> f` at the PFun level, together with representation data connecting
the chosen PFun representatives to the integrable representatives.

This is still data-carrying: no witness is extracted from the Prop-valued
`ConvergeInMeasure`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- The local theorem-4.15 source data with convergence supplied at the
source PFun level, not as a prebuilt abs-error convergence datum. -/
structure Theorem415LocalCoverSetPFunSourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S) : Type _ where
  g_nonneg : BishopC.RepNonneg g
  dominated_fn : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)
  dominated_limit : BishopC.RepNonneg (g.sub f.absVal)
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- The row-seed provider induced by the source-faithful domain-residual
provider. -/
noncomputable def theorem415_pfun_rowSeedProvider_of_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetPFunSourceData fn f g) :
    BishopC.Lemma415Prop42RowSeedToolsProvider (S := S) :=
  BishopC.Lemma415Prop42RowSeedToolsProvider.of_generalIBDomainResidualProvider
    (S := S) D.domainResidualProvider

/-- Local complement bridges for the abs-error sequence, obtained from the
domain-residual provider. -/
noncomputable def theorem415_pfun_local_complement_bridges
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetPFunSourceData fn f g) :
    forall (n : Nat) (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n C hC =>
    let P := theorem415_pfun_rowSeedProvider_of_sourceData (S := S) D
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
        (P.rowSeeds
          (BishopC.thm_4_15_abs_error (S := S) fn f n)
          (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)))

/-- Build the source proof's single-`g` tail choice directly from the
domain-residual provider route.  This is the PFun-source analogue of the
G232 cover-set construction, without packaging a direct abs-error convergence
field. -/
noncomputable def theorem415_pfun_g_single_tail_choice_from_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetPFunSourceData fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415GSingleTailChoiceSourceData
      (S := S) g D.g_nonneg eps :=
  let P := theorem415_pfun_rowSeedProvider_of_sourceData (S := S) D
  let budget : BishopC.Lemma415TailBudgetSourceData (R := R) eps :=
    BishopC.lemma_4_15_default_tail_budget (R := R) eps heps
  let gComp :
      BishopC.Lemma415GComplementTailRelChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    BishopC.lemma_4_15_g_complement_tail_rel_choice_data_from_coverSetBudget
      (S := S) g D.g_nonneg eps
      (P.rowSeeds g D.g_nonneg)
      budget
  let gRel :
      BishopC.Lemma415GSingleTailRelChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    BishopC.lemma_4_15_g_single_tail_rel_choice_source_data_from_g_complement_tail_data
      (S := S) g D.g_nonneg eps gComp
  {
    gSeeds := gRel.gSeeds
    twoGSeeds :=
      P.rowSeeds (g.add g)
        (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
    A := gRel.A
    hA := gRel.hA
    N := gRel.N
    N_ge_one := gRel.N_ge_one
    epsAB := gRel.epsAB
    epsG := gRel.epsG
    epsNeg := gRel.epsNeg
    epsAB_pos := gRel.epsAB_pos
    gTailBudget := gRel.gTailBudget
    pieces_sum_lt := gRel.pieces_sum_lt
    gNegSmall := gRel.gNegSmall
  }

/-- Construct the `2g` majorant split from source PFun data without assuming a
prebuilt abs-error convergence-in-measure datum. -/
noncomputable def theorem415_pfun_majorant_split_from_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetPFunSourceData fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f (g.add g)
      (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
      eps :=
  let gTail :
      BishopC.Lemma415GSingleTailChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    theorem415_pfun_g_single_tail_choice_from_sourceData
      (S := S) D eps heps
  let twoGTail :
      BishopC.Lemma415TwoGTailChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    BishopC.lemma_4_15_two_g_tail_choice_source_data_from_g_single_tail_choice_data
      (S := S) g D.g_nonneg eps gTail
  let twoGChoice :
      BishopC.Lemma415TwoGChoiceSourceData
        (S := S) fn f g D.g_nonneg eps :=
    BishopC.lemma_4_15_two_g_choice_source_data_from_tail_choice_data
      (S := S) fn f g D.g_nonneg
      D.dominated_fn D.dominated_limit eps twoGTail
  let majorantChoice :
      BishopC.Lemma415MajorantChoiceSourceData
        (S := S) fn f (g.add g)
        (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
        eps :=
    BishopC.lemma_4_15_majorant_choice_source_data_from_two_g_choice_data
      (S := S) fn f g D.g_nonneg eps twoGChoice
  BishopC.lemma_4_15_majorant_split_uniform_source_data_from_choice_data
    (S := S) fn f (g.add g)
    (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
    eps majorantChoice

/-- The local source-uniform `I_B` datum for the abs-error sequence, generated
from cover-set tail data and domination by `g`. -/
noncomputable def theorem415_pfun_uniform_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetPFunSourceData fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma414UniformIBSourceData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
        (theorem415_pfun_local_complement_bridges (S := S) D))
      eps :=
  let P := theorem415_pfun_rowSeedProvider_of_sourceData (S := S) D
  let majorantSplit :=
    theorem415_pfun_majorant_split_from_sourceData
      (S := S) D eps heps
  let hSeeds : forall n,
      BishopC.Sec4Prop42RowSeedTools (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
    fun n =>
      P.rowSeeds
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  let localSplit :
      BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
    BishopC.lemma_4_15_local_split_uniform_source_data_from_majorant_data
      (S := S) fn f hSeeds (g.add g)
      (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
      eps majorantSplit
  BishopC.lemma_4_15_uniform_ib_source_data_from_local_split_data
    (S := S) fn f
    (theorem415_pfun_local_complement_bridges (S := S) D)
    eps localSplit

/-- Abs-error convergence of integrals from source PFun convergence and the
local full-set `I_B` interface. -/
noncomputable def theorem415_abs_error_tendsto_from_local_pfun_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetPFunSourceData fn f g) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  let IB :=
    BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (theorem415_pfun_local_complement_bridges (S := S) D)
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
      (theorem415_pfun_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

/-- Theorem 4.15 from source PFun convergence data. -/
noncomputable def theorem415_integral_convergence_from_local_pfun_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetPFunSourceData fn f g) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (theorem415_abs_error_tendsto_from_local_pfun_source_data
      (S := S) D)

/-- Audit after replacing direct abs-error convergence by source PFun
convergence plus representation data. -/
structure Theorem415PFunSourceRouteAuditAfterG234 : Type where
  direct_abs_error_convergence_input_removed : Nat
  source_pfun_convergence_input_used : Nat
  representation_data_for_fn_and_limit_explicit : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def theorem415PFunSourceRouteAuditAfterG234 :
    Theorem415PFunSourceRouteAuditAfterG234 where
  direct_abs_error_convergence_input_removed := 1
  source_pfun_convergence_input_used := 1
  representation_data_for_fn_and_limit_explicit := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 2
  remaining_plain_prop_415_bridge_steps := 3

/-- G234 package. -/
structure Chapter4G234Theorem415PFunSourcePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g233 : Chapter4G233Theorem415DomainResidualPackage S
  audit : Theorem415PFunSourceRouteAuditAfterG234
  theorem415_pfun_source_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def chapter4G234Theorem415PFunSourcePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G234Theorem415PFunSourcePackage S where
  g233 := chapter4G233Theorem415DomainResidualPackage S
  audit := theorem415PFunSourceRouteAuditAfterG234
  theorem415_pfun_source_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 2
  remaining_plain_prop_415_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G234. -/
def bishopRegularSeqChapter4Theorem415PFunSourceProgressAfterG234 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G234: replaced the direct abs-error convergence input by source PFun \
    convergence plus explicit representation data. Source-data countdown is 2; \
    the completely plain Prop statement remains 3 because Prop-to-Type \
    extraction is still intentionally avoided."


end BishopCReal
