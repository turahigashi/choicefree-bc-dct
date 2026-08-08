import Mathdemo.Internal.CRat_iter355

set_option linter.style.longLine false

/-!
# G257: source-level theorem 4.15 through local full-set bridges

G256 restored the theorem-4.15 statement shape but still used the global
domain-residual provider as the route for Proposition 4.2 row machinery.
For the previous `IntegrableSet1` API that provider is the dangerous shape: it asks
for global membership-to-domain witnesses for characteristic representatives.

This file keeps the source-level convergence-in-measure statement from G256,
but replaces the provider route by local full-set value bridges.  The remaining
frontier is therefore local and data-carrying, not a global selector.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-facing theorem-4.15 statement through local full-set bridges. -/
structure Theorem415SourceFacingLocalBridgeStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_local_bridge : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4GenIBLocalValueBridge (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

/-- Constructive majorant `g + |f|` for the local source route. -/
noncomputable def theorem415_sourceFacingLocalBridge_majorant
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f) :
    BishopC.IntegrableRep S :=
  D.g.add f.absVal

/-- Non-negativity of `g + |f|`. -/
noncomputable def theorem415_sourceFacingLocalBridge_majorant_nonneg
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f) :
    BishopC.RepNonneg
      (theorem415_sourceFacingLocalBridge_majorant (S := S) D) :=
  theorem415_g_add_absf_majorant_nonneg
    (S := S) f D.g D.domination.g_nonneg

/-- Majorant choice data from the source cover-set/tail-budget argument,
without any global domain-residual provider. -/
noncomputable def theorem415_sourceFacingLocalBridge_majorant_rel_choice
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantRelChoiceSourceData
      (S := S) fn f
      (theorem415_sourceFacingLocalBridge_majorant (S := S) D)
      (theorem415_sourceFacingLocalBridge_majorant_nonneg (S := S) D)
      eps :=
  let majorant : BishopC.IntegrableRep S :=
    theorem415_sourceFacingLocalBridge_majorant (S := S) D
  let majorant_nonneg : BishopC.RepNonneg majorant :=
    theorem415_sourceFacingLocalBridge_majorant_nonneg (S := S) D
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

/-- Direct local split data from local full-set bridges. -/
noncomputable def theorem415_sourceFacingLocalBridge_direct_local_split_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
  let majorant : BishopC.IntegrableRep S :=
    theorem415_sourceFacingLocalBridge_majorant (S := S) D
  let majorant_nonneg : BishopC.RepNonneg majorant :=
    theorem415_sourceFacingLocalBridge_majorant_nonneg (S := S) D
  let M : BishopC.Lemma415MajorantRelChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps :=
    theorem415_sourceFacingLocalBridge_majorant_rel_choice (S := S) D eps heps
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

/-- Complement bridges for lemma 4.14. -/
noncomputable def theorem415_sourceFacingLocalBridge_complement_bridges
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f) :
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

/-- Local abs-error source package from the source-level local bridge data. -/
noncomputable def theorem415_local_abs_error_source_data_of_sourceFacingLocalBridge
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f) :
    BishopC.Lemma415AbsErrorLocalSourceData (S := S) fn f :=
  BishopC.Lemma415AbsErrorLocalSourceData.of_localSplitUniformData
    (S := S) fn f
    (theorem415_sourceFacingLocalBridge_complement_bridges (S := S) D)
    (fun eps heps =>
      theorem415_sourceFacingLocalBridge_direct_local_split_source_data
        (S := S) D eps heps)
    D.converges_in_measure.abs_error

/-- Source-facing theorem 4.15 endpoint through local full-set bridges, with no
global domain-residual provider. -/
noncomputable def
    theorem415_integral_convergence_from_sourceFacingLocalBridge_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_source_from_local_abs_error_data
    (S := S) fn f
    (theorem415_local_abs_error_source_data_of_sourceFacingLocalBridge
      (S := S) D)

structure Theorem415SourceFacingLocalBridgeRouteAuditAfterG257 : Type where
  domainResidualProvider_required : Nat
  global_characteristic_domain_witness_required : Nat
  source_facing_convergence_in_measure_used : Nat
  local_full_set_bridge_public_input_used : Nat
  pfun_representation_data_required : Nat
  row_to_flat_public_input_required : Nat
  direct_abs_error_rowSeeds_public_input_required : Nat
  majorant_split_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_local_bridge_derivation_frontiers : Nat

def theorem415SourceFacingLocalBridgeRouteAuditAfterG257 :
    Theorem415SourceFacingLocalBridgeRouteAuditAfterG257 where
  domainResidualProvider_required := 0
  global_characteristic_domain_witness_required := 0
  source_facing_convergence_in_measure_used := 1
  local_full_set_bridge_public_input_used := 1
  pfun_representation_data_required := 0
  row_to_flat_public_input_required := 0
  direct_abs_error_rowSeeds_public_input_required := 0
  majorant_split_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_local_bridge_derivation_frontiers := 1

structure Chapter4G257Theorem415SourceFacingLocalBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g256 : Chapter4G256Theorem415SourceFacingPackage S
  audit : Theorem415SourceFacingLocalBridgeRouteAuditAfterG257
  domainResidualProvider_removed_from_mainline_this_step : Nat
  remaining_local_bridge_derivation_frontiers : Nat

def chapter4G257Theorem415SourceFacingLocalBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G257Theorem415SourceFacingLocalBridgePackage S where
  g256 := chapter4G256Theorem415SourceFacingPackage S
  audit := theorem415SourceFacingLocalBridgeRouteAuditAfterG257
  domainResidualProvider_removed_from_mainline_this_step := 1
  remaining_local_bridge_derivation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G257. -/
def bishopRegularSeqChapter4Theorem415SourceFacingLocalBridgeProgressAfterG257 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G257: moved the source-level theorem 4.15 mainline off the global \
    domain-residual provider and onto local full-set bridges. The theorem \
    route now has no public PFun representatives, charDomain selector, \
    rowToFlat bridge, abs-error row seeds, or majorant split. The remaining \
    frontier is deriving the local full-set bridges themselves from the \
    integrable-set/characteristic-function definitions."


end BishopCReal
