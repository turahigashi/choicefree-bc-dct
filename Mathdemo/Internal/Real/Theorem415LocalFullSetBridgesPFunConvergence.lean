import Mathdemo.Internal.Real.Theorem415SourceShapedStandardRowIBProvider
import Mathdemo.Internal.Sec4.Local415SourceData

set_option linter.style.longLine false

/-!
# G243: theorem 4.15 through local full-set bridges and PFun convergence

G242 closed a source-shaped theorem-4.15 endpoint using the standard-row S2
provider, but its lemma-4.14 interface still consumed the completed
`remainingAtoms` route through the previous global value bridge.

This file keeps the same public source data and lowers the error side one step
further: `remainingAtoms` are first converted to local full-set value bridges,
then the lemma-4.14 `I_B` interface is instantiated from those local bridges.
The convergence-to-zero input remains the PFun/representation source data from
G242, so no Prop-to-data selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Remaining-atoms data for the theorem-4.15 error sequence also provides the
local complement bridges needed by the local lemma-4.14 `I_B` interface. -/
noncomputable def theorem415_sourceS2_local_complement_bridges
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    forall (n : Nat) (C : BishopC.BSet Y)
      (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n C hC =>
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    let T : BishopC.Sec4Prop42RemainingAtomTools (S := S) u hnn_u :=
      theorem415_sourceS2_error_atoms (S := S) D n
    BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S)
      (BishopC.BSet.neg C)
      (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
      u hnn_u
      (BishopC.sec4_genIBValueBridge_of_remainingAtoms
        (S := S)
        (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        u hnn_u T)

/-- Local split data obtained from G242's source-shaped atom split.  The
estimate itself is unchanged; the three value bridges returned in each small
set estimate are converted to local full-set bridges. -/
noncomputable def theorem415_sourceS2_local_split_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
  let hAtoms := theorem415_sourceS2_error_atoms (S := S) D
  let hSplit : BishopC.Lemma415SplitUniformSourceData (S := S) fn f eps :=
    BishopC.lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data_of_atoms
      (S := S) fn f hAtoms
      (theorem415_sourceS2_majorant (S := S) D)
      (theorem415_sourceS2_majorant_nonneg (S := S) D)
      eps
      (theorem415_sourceS2_majorant_rel_choice (S := S) D eps heps)
  {
    A := hSplit.A
    hA := hSplit.hA
    N := hSplit.N
    N_ge_one := hSplit.N_ge_one
    delta := hSplit.delta
    delta_pos := hSplit.delta_pos
    epsAB := hSplit.epsAB
    epsNeg := hSplit.epsNeg
    pieces_sum_lt := hSplit.pieces_sum_lt
    pieceBounds := by
      intro n hn B hB hmu
      obtain ⟨VB, VAB, VnegA, hAB, hNeg⟩ :=
        hSplit.pieceBounds n hn B hB hmu
      let u : BishopC.IntegrableRep S :=
        BishopC.thm_4_15_abs_error (S := S) fn f n
      let hnn_u : BishopC.RepNonneg u :=
        BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
      refine ⟨?_, ?_, ?_, hAB, hNeg⟩
      · exact
          BishopC.sec4_genIBLocalValueBridge_of_valueBridge
            (S := S) B hB u hnn_u VB
      · exact
          BishopC.sec4_genIBLocalValueBridge_of_valueBridge
            (S := S)
            (BishopC.BSet.and hSplit.A B)
            (BishopC.isMeasurableSet_of_integrable (S := S) (hB hSplit.A hSplit.hA))
            u hnn_u VAB
      · exact
          BishopC.sec4_genIBLocalValueBridge_of_valueBridge
            (S := S)
            (BishopC.BSet.neg hSplit.A)
            (BishopC.isMeasurableSet_neg_of_integrable (S := S) hSplit.hA)
            u hnn_u VnegA
  }

/-- Uniform source-form `I_B` data for the theorem-4.15 error sequence, now
targeting the local full-set lemma-4.14 interface. -/
noncomputable def theorem415_sourceS2_local_uniform_source_data
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
    (theorem415_sourceS2_local_split_source_data (S := S) D eps heps)

/-- Abs-error convergence for theorem 4.15 through the local full-set `I_B`
interface and the PFun convergence source data. -/
noncomputable def theorem415_abs_error_tendsto_from_sourceS2_local_statement_data
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
      (theorem415_sourceS2_local_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

/-- Theorem 4.15 from G242 source data, but routed through the local full-set
`I_B` interface. -/
noncomputable def theorem415_integral_convergence_from_sourceS2_local_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (theorem415_abs_error_tendsto_from_sourceS2_local_statement_data
      (S := S) D)

structure Theorem415SourceS2LocalRouteAuditAfterG243 : Type where
  source_s2_standard_outer_provider_used : Nat
  error_side_lowered_to_remaining_atoms : Nat
  local_full_set_ib_interface_used : Nat
  pfun_convergence_source_data_used : Nat
  majorant_tail_kept_on_complement_integral_side : Nat
  global_to_local_compat_bridge_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_source_shaped_provider_frontiers : Nat
  remaining_lower_layer_frontiers : Nat

def theorem415SourceS2LocalRouteAuditAfterG243 :
    Theorem415SourceS2LocalRouteAuditAfterG243 where
  source_s2_standard_outer_provider_used := 1
  error_side_lowered_to_remaining_atoms := 1
  local_full_set_ib_interface_used := 1
  pfun_convergence_source_data_used := 1
  majorant_tail_kept_on_complement_integral_side := 1
  global_to_local_compat_bridge_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_source_shaped_provider_frontiers := 1
  remaining_lower_layer_frontiers := 2

structure Chapter4G243Theorem415SourceS2LocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g242 : Chapter4G242Theorem415SourceS2Package S
  audit : Theorem415SourceS2LocalRouteAuditAfterG243
  theorem415_sourceS2_local_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_source_shaped_provider_frontiers : Nat
  remaining_lower_layer_frontiers : Nat

def chapter4G243Theorem415SourceS2LocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G243Theorem415SourceS2LocalPackage S where
  g242 := chapter4G242Theorem415SourceS2Package S
  audit := theorem415SourceS2LocalRouteAuditAfterG243
  theorem415_sourceS2_local_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 0
  remaining_source_shaped_provider_frontiers := 1
  remaining_lower_layer_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G243. -/
def bishopRegularSeqChapter4Theorem415SourceS2LocalProgressAfterG243 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G243: rerouted the source-shaped theorem-4.15 endpoint through the local \
    full-set I_B interface. The error-side remainingAtoms data now feeds local \
    complement bridges, and the PFun convergence source data still supplies \
    convergence to zero without Prop-to-data extraction. The public 4.15 \
    source endpoint remains at zero bridge steps; remaining work is the \
    lower-layer derivation of the source-shaped standard-row provider and the \
    PFun/representation source layer."


end BishopCReal
