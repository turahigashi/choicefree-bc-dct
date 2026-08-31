import Mathdemo.Internal.Real.Theorem415LocalFullSetBridgesPFunConvergence

set_option linter.style.longLine false

/-!
# G244: direct local split data for theorem 4.15

G243 routed theorem 4.15 through the local full-set `I_B` interface, but its
local split package was obtained by first building the older global split data
and then converting its bridges to local bridges.

This file removes that intermediate split conversion.  The displayed theorem
4.15 decomposition is rebuilt directly from the source majorant choice data,
with local bridges supplied by the completed `remainingAtoms` interface on the
error side.  The remaining compatibility wrapper is only the value-bridge to
local-witness bridge for those already-completed atoms.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Direct local split data from the G242 source-shaped majorant choice.  This
is the local-bridge analogue of
`lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data_of_atoms`,
but it is written directly instead of passing through the previous global split
package. -/
noncomputable def theorem415_sourceS2_direct_local_split_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
  let hAtoms := theorem415_sourceS2_error_atoms (S := S) D
  let majorant : BishopC.IntegrableRep S :=
    theorem415_sourceS2_majorant (S := S) D
  let majorant_nonneg : BishopC.RepNonneg majorant :=
    theorem415_sourceS2_majorant_nonneg (S := S) D
  let M : BishopC.Lemma415MajorantRelChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps :=
    theorem415_sourceS2_majorant_rel_choice (S := S) D eps heps
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
      let T : BishopC.Sec4Prop42RemainingAtomTools (S := S) u hnn_u :=
        hAtoms n
      let VB : BishopC.Sec4GenIBLocalValueBridge (S := S) B hB u hnn_u :=
        BishopC.sec4_genIBLocalValueBridge_of_valueBridge
          (S := S) B hB u hnn_u
          (BishopC.sec4_genIBValueBridge_of_remainingAtoms
            (S := S) B hB u hnn_u T)
      let VAB : BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.and M.A B)
          (BishopC.isMeasurableSet_of_integrable (S := S) (hB M.A M.hA))
          u hnn_u :=
        BishopC.sec4_genIBLocalValueBridge_of_valueBridge
          (S := S)
          (BishopC.BSet.and M.A B)
          (BishopC.isMeasurableSet_of_integrable (S := S) (hB M.A M.hA))
          u hnn_u
          (BishopC.sec4_genIBValueBridge_of_remainingAtoms
            (S := S)
            (BishopC.BSet.and M.A B)
            (BishopC.isMeasurableSet_of_integrable (S := S) (hB M.A M.hA))
            u hnn_u T)
      let VnegA : BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg M.A)
          (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
          u hnn_u :=
        BishopC.sec4_genIBLocalValueBridge_of_valueBridge
          (S := S)
          (BishopC.BSet.neg M.A)
          (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
          u hnn_u
          (BishopC.sec4_genIBValueBridge_of_remainingAtoms
            (S := S)
            (BishopC.BSet.neg M.A)
            (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
            u hnn_u T)
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

/-- Uniform source-form `I_B` data using the direct local split construction. -/
noncomputable def theorem415_sourceS2_direct_local_uniform_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma414UniformIBSourceData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
        (theorem415_sourceS2_local_complement_bridges (S := S) D))
      eps :=
  BishopC.lemma_4_15_uniform_ib_source_data_from_local_split_data
    (S := S) fn f
    (theorem415_sourceS2_local_complement_bridges (S := S) D)
    eps
    (theorem415_sourceS2_direct_local_split_source_data (S := S) D eps heps)

/-- Abs-error convergence through the local full-set `I_B` interface, using
the direct local split construction. -/
noncomputable def theorem415_abs_error_tendsto_from_sourceS2_direct_local_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  let hComp := theorem415_sourceS2_local_complement_bridges (S := S) D
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
      (theorem415_sourceS2_direct_local_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

/-- Theorem 4.15 through the direct local split and local full-set `I_B`
interface. -/
noncomputable def theorem415_integral_convergence_from_sourceS2_direct_local_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (theorem415_abs_error_tendsto_from_sourceS2_direct_local_statement_data
      (S := S) D)

structure Theorem415SourceS2DirectLocalRouteAuditAfterG244 : Type where
  source_s2_standard_outer_provider_used : Nat
  error_side_lowered_to_remaining_atoms : Nat
  local_full_set_ib_interface_used : Nat
  direct_local_split_from_majorant_choice_used : Nat
  global_split_to_local_conversion_used : Nat
  pfun_convergence_source_data_used : Nat
  majorant_tail_kept_on_complement_integral_side : Nat
  global_to_local_compat_bridge_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_source_shaped_provider_frontiers : Nat
  remaining_lower_layer_frontiers : Nat

def theorem415SourceS2DirectLocalRouteAuditAfterG244 :
    Theorem415SourceS2DirectLocalRouteAuditAfterG244 where
  source_s2_standard_outer_provider_used := 1
  error_side_lowered_to_remaining_atoms := 1
  local_full_set_ib_interface_used := 1
  direct_local_split_from_majorant_choice_used := 1
  global_split_to_local_conversion_used := 0
  pfun_convergence_source_data_used := 1
  majorant_tail_kept_on_complement_integral_side := 1
  global_to_local_compat_bridge_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_source_shaped_provider_frontiers := 1
  remaining_lower_layer_frontiers := 2

structure Chapter4G244Theorem415SourceS2DirectLocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g243 : Chapter4G243Theorem415SourceS2LocalPackage S
  audit : Theorem415SourceS2DirectLocalRouteAuditAfterG244
  theorem415_sourceS2_direct_local_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_source_shaped_provider_frontiers : Nat
  remaining_lower_layer_frontiers : Nat

def chapter4G244Theorem415SourceS2DirectLocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G244Theorem415SourceS2DirectLocalPackage S where
  g243 := chapter4G243Theorem415SourceS2LocalPackage S
  audit := theorem415SourceS2DirectLocalRouteAuditAfterG244
  theorem415_sourceS2_direct_local_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 0
  remaining_source_shaped_provider_frontiers := 1
  remaining_lower_layer_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G244. -/
def bishopRegularSeqChapter4Theorem415SourceS2DirectLocalProgressAfterG244 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G244: rebuilt the theorem-4.15 split estimate directly as local full-set \
    source data from the majorant relative-choice package. This removes the \
    intermediate global-split-to-local conversion used in G243. The endpoint \
    still adds no choice principle and keeps zero 4.15 source bridge steps; \
    remaining work is below this theorem endpoint, namely deriving the \
    source-shaped standard-row provider and the PFun/representation source \
    layer from still lower definitions."


end BishopCReal
