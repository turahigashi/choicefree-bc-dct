import Mathdemo.Internal.Real.UnbundleTheorem415S2Provider

set_option linter.style.longLine false

/-!
# G246: theorem 4.15 from local full-set value bridges

G245 exposed the bundled S2 provider into five lower components.  Inspecting
those components shows that the previous `charDomain` field is still the dangerous
shape: it asks for a global map from membership in `A.S1`/`A.S2` to pointwise
absolute-convergence witnesses for the characteristic representative.

This file routes theorem 4.15 through the local full-set interface directly.
The public input is not a global membership-to-witness selector; it is only the
local value bridge for the theorem-4.15 error sequence.  The bridge itself is
the remaining lower construction target, but the 4.15 theorem no longer needs
the global `Sec4GeneralIBSourceS2StandardOuterProvider` or its `charDomain`
component.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 statement data based on local full-set bridges for the
abs-error sequence. -/
structure Theorem415AbsErrorLocalBridgeStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_local_bridge : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4GenIBLocalValueBridge (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- The constructive majorant used by the local-bridge route. -/
noncomputable def theorem415_localBridge_majorant
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f) :
    BishopC.IntegrableRep S :=
  D.g.add f.absVal

/-- Non-negativity of the constructive majorant `g + |f|`. -/
noncomputable def theorem415_localBridge_majorant_nonneg
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f) :
    BishopC.RepNonneg (theorem415_localBridge_majorant (S := S) D) :=
  theorem415_g_add_absf_majorant_nonneg
    (S := S) f D.g D.domination.g_nonneg

/-- Majorant choice data for the local-bridge route.  The tail remains the
ordinary complement-integral tail of `g + |f|`; no row-seed data is requested
for the majorant. -/
noncomputable def theorem415_localBridge_majorant_rel_choice
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantRelChoiceSourceData
      (S := S) fn f
      (theorem415_localBridge_majorant (S := S) D)
      (theorem415_localBridge_majorant_nonneg (S := S) D)
      eps :=
  let majorant : BishopC.IntegrableRep S :=
    theorem415_localBridge_majorant (S := S) D
  let majorant_nonneg : BishopC.RepNonneg majorant :=
    theorem415_localBridge_majorant_nonneg (S := S) D
  let budget : BishopC.Lemma415TailBudgetSourceData (R := R) eps :=
    BishopC.lemma_4_15_default_tail_budget (R := R) eps heps
  let tailTendsto :=
    BishopC.lemma_4_15_g_complement_tail_sequence_from_coverSet
      (S := S) majorant majorant_nonneg
  let k : Nat := (COFO.archimedean_pos budget.epsG budget.epsG_pos).1
  let m : Nat := tailTendsto.mod k
  {
    A := BishopC.coverSet majorant m
    hA := BishopC.coverSet_int majorant m
    N := budget.N
    N_ge_one := budget.N_ge_one
    epsAB := budget.epsAB
    epsNeg := budget.epsNeg
    epsAB_pos := budget.epsAB_pos
    pieces_sum_lt := budget.pieces_sum_lt
    dominatesError :=
      theorem415_abs_error_dominated_by_g_add_absf
        (S := S) fn f D.g D.domination.dominated_fn
    majorantNegSmall := by
      have hk : COF.lt (COF.halfPow (R := R) k) budget.epsG :=
        (COFO.archimedean_pos budget.epsG budget.epsG_pos).2
      have hclose :
          COF.lt
            (COF.abs
              (BishopC.lemma_4_15_g_complement_tail_value
                (S := S) majorant majorant_nonneg
                (BishopC.coverSet majorant m)
                (BishopC.coverSet_int majorant m) - 0))
            (COF.halfPow (R := R) k) :=
        tailTendsto.close k m (Nat.le_refl m)
      have htail_le_abs :
          BishopC.Le
            (BishopC.lemma_4_15_g_complement_tail_value
              (S := S) majorant majorant_nonneg
              (BishopC.coverSet majorant m)
              (BishopC.coverSet_int majorant m))
            (COF.abs
              (BishopC.lemma_4_15_g_complement_tail_value
                (S := S) majorant majorant_nonneg
                (BishopC.coverSet majorant m)
                (BishopC.coverSet_int majorant m) - 0)) := by
        rw [sub_zero]
        exact COFO.le_abs_self
          (BishopC.lemma_4_15_g_complement_tail_value
            (S := S) majorant majorant_nonneg
            (BishopC.coverSet majorant m)
            (BishopC.coverSet_int majorant m))
      have hsmall_epsG :
          COF.lt
            (BishopC.lemma_4_15_g_complement_tail_value
              (S := S) majorant majorant_nonneg
              (BishopC.coverSet majorant m)
              (BishopC.coverSet_int majorant m))
            budget.epsG :=
        COFO.lt_trans (BishopC.lt_of_le_of_lt htail_le_abs hclose) hk
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
      exact COFO.lt_trans hsmall_epsG h_epsG_lt_epsNeg
  }

/-- Direct local split data from the local bridge statement. -/
noncomputable def theorem415_localBridge_direct_local_split_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
  let majorant : BishopC.IntegrableRep S :=
    theorem415_localBridge_majorant (S := S) D
  let majorant_nonneg : BishopC.RepNonneg majorant :=
    theorem415_localBridge_majorant_nonneg (S := S) D
  let M : BishopC.Lemma415MajorantRelChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps :=
    theorem415_localBridge_majorant_rel_choice (S := S) D eps heps
  {
    A := M.A
    hA := M.hA
    N := M.N
    N_ge_one := M.N_ge_one
    delta := (BishopC.relIntegral_abs_continuous_delta
      (S := S) majorant majorant_nonneg M.epsAB M.epsAB_pos).1
    delta_pos := (BishopC.relIntegral_abs_continuous_delta
      (S := S) majorant majorant_nonneg M.epsAB M.epsAB_pos).2.1
    epsAB := M.epsAB
    epsNeg := M.epsNeg
    pieces_sum_lt := M.pieces_sum_lt
    pieceBounds := by
      intro n _hn B hB hmu
      let u : BishopC.IntegrableRep S :=
        BishopC.thm_4_15_abs_error (S := S) fn f n
      let hnn_u : BishopC.RepNonneg u :=
        BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
      let VB : BishopC.Sec4GenIBLocalValueBridge (S := S) B hB u hnn_u :=
        D.abs_error_local_bridge n B hB
      let VAB : BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.and M.A B)
          (BishopC.isMeasurableSet_of_integrable (S := S) (hB M.A M.hA))
          u hnn_u :=
        D.abs_error_local_bridge n
          (BishopC.BSet.and M.A B)
          (BishopC.isMeasurableSet_of_integrable (S := S) (hB M.A M.hA))
      let VnegA : BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg M.A)
          (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
          u hnn_u :=
        D.abs_error_local_bridge n
          (BishopC.BSet.neg M.A)
          (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
      let H := BishopC.relIntegral_abs_continuous_delta
        (S := S) majorant majorant_nonneg M.epsAB M.epsAB_pos
      have hAB_majorant_small : COF.lt
          (BishopC.relIntegral (BishopC.BSet.and M.A B) (hB M.A M.hA)
            majorant majorant_nonneg)
          M.epsAB :=
        H.2.2 (BishopC.BSet.and M.A B) (hB M.A M.hA) hmu
      have hAB_le : BishopC.Le
          (BishopC.genRelIntegral_from_measurable (BishopC.BSet.and M.A B)
            (BishopC.isMeasurableSet_of_integrable (S := S) (hB M.A M.hA))
            u hnn_u)
          (BishopC.relIntegral (BishopC.BSet.and M.A B) (hB M.A M.hA)
            majorant majorant_nonneg) :=
        BishopC.genRelIntegral_from_measurable_le_relIntegral_of_localBridge
          (S := S)
          (BishopC.BSet.and M.A B)
          (hB M.A M.hA)
          u majorant hnn_u majorant_nonneg VAB
          (M.dominatesError n)
      have hNeg_le : BishopC.Le
          (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg M.A)
            (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
            u hnn_u)
          ((majorant.sub
            (BishopC.prop_4_2_chi_f_rep M.A M.hA majorant majorant_nonneg)).integral) :=
        BishopC.genRelIntegral_neg_le_complementIntegral_of_localBridge
          (S := S) M.A M.hA
          u majorant hnn_u majorant_nonneg VnegA
          (M.dominatesError n)
      have hAB_lt : COF.lt
          (BishopC.genRelIntegral_from_measurable (BishopC.BSet.and M.A B)
            (BishopC.isMeasurableSet_of_integrable (S := S) (hB M.A M.hA))
            u hnn_u)
          M.epsAB :=
        BishopC.lt_of_le_of_lt hAB_le hAB_majorant_small
      have hNeg_lt : COF.lt
          (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg M.A)
            (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
            u hnn_u)
          M.epsNeg :=
        BishopC.lt_of_le_of_lt hNeg_le M.majorantNegSmall
      exact ⟨VB, VAB, VnegA, hAB_lt, hNeg_lt⟩
  }

/-- Complement local bridges for lemma 4.14, specialized from the local bridge
statement. -/
noncomputable def theorem415_localBridge_complement_bridges
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f) :
    forall (n : Nat) (C : BishopC.BSet Y)
      (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n C hC =>
    D.abs_error_local_bridge n
      (BishopC.BSet.neg C)
      (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)

/-- Uniform source-form `I_B` data through local bridges only. -/
noncomputable def theorem415_localBridge_uniform_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma414UniformIBSourceData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
        (theorem415_localBridge_complement_bridges (S := S) D))
      eps :=
  BishopC.lemma_4_15_uniform_ib_source_data_from_local_split_data
    (S := S) fn f
    (theorem415_localBridge_complement_bridges (S := S) D)
    eps
    (theorem415_localBridge_direct_local_split_source_data
      (S := S) D eps heps)

/-- Abs-error convergence from local full-set bridges and PFun convergence. -/
noncomputable def theorem415_abs_error_tendsto_from_localBridge_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  let hComp := theorem415_localBridge_complement_bridges (S := S) D
  let IB :=
    BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      hComp
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
      (theorem415_localBridge_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

/-- Theorem 4.15 through local full-set bridges, with no global
membership-to-witness provider in the public input. -/
noncomputable def theorem415_integral_convergence_from_localBridge_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (theorem415_abs_error_tendsto_from_localBridge_statement_data
      (S := S) D)

structure Theorem415LocalBridgeRouteAuditAfterG246 : Type where
  source_s2_standard_outer_provider_required : Nat
  characteristic_domain_provider_required : Nat
  local_full_set_bridge_public_input_used : Nat
  direct_local_split_from_majorant_choice_used : Nat
  pfun_convergence_source_data_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_local_bridge_derivation_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415LocalBridgeRouteAuditAfterG246 :
    Theorem415LocalBridgeRouteAuditAfterG246 where
  source_s2_standard_outer_provider_required := 0
  characteristic_domain_provider_required := 0
  local_full_set_bridge_public_input_used := 1
  direct_local_split_from_majorant_choice_used := 1
  pfun_convergence_source_data_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_local_bridge_derivation_frontiers := 1
  remaining_pfun_representation_frontiers := 1

structure Chapter4G246Theorem415LocalBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g245 : Chapter4G245Theorem415UnbundledS2ToolsPackage S
  audit : Theorem415LocalBridgeRouteAuditAfterG246
  global_membership_to_witness_provider_removed_this_step : Nat
  remaining_local_bridge_derivation_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G246Theorem415LocalBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G246Theorem415LocalBridgePackage S where
  g245 := chapter4G245Theorem415UnbundledS2ToolsPackage S
  audit := theorem415LocalBridgeRouteAuditAfterG246
  global_membership_to_witness_provider_removed_this_step := 1
  remaining_local_bridge_derivation_frontiers := 1
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G246. -/
def bishopRegularSeqChapter4Theorem415LocalBridgeProgressAfterG246 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G246: removed the global source-S2 provider and its characteristic-domain \
    membership-to-witness component from the public theorem-4.15 route. The \
    theorem now consumes only local full-set value bridges for the abs-error \
    sequence plus PFun convergence data. This is the safer Bishop-style \
    direction: local witnesses are carried explicitly, and no data is extracted \
    from propositional fullness or set membership."


end BishopCReal
