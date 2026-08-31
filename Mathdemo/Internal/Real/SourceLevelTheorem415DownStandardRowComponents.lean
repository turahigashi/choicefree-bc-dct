import Mathdemo.Internal.Real.SourceLevelTheorem415Cover
import Mathdemo.Internal.Sec4.LayerTelescope
import Mathdemo.Internal.Sec4.CaseRowTools
import Mathdemo.Internal.Sec4.AbsOuterPack
import Mathdemo.Internal.Sec4.RowToFlat
import Mathdemo.Internal.Sec4.S2StandardOuterProvider
import Mathdemo.Internal.Sec4.S2StandardOuterBridge

set_option linter.style.longLine false

/-!
# G259: source-level theorem 4.15 down to standard row components

G258 restored the source-level theorem-4.15 route while lowering the public
bridge input to `chi` telescope data.  Older G248--G252 files had already
followed the `I_B` construction further downward, but they still carried the
temporary PFun/representation convergence layer.

This file replays those lower reductions on the G258 source-level surface:

* `chi` data is lowered to telescope/layer telescope data;
* per-set cover/chi data is replaced by function-side case tools;
* case tools are lowered to corrected abs-pack tools;
* abs-pack tools are supplied by the source-shaped standard-row provider;
* the generic row-to-flat bridge is filled by `sec4_rowToFlat_source`.

The remaining public frontier is now the source-shaped standard-row component
data: characteristic-domain data, standard outer convergence on `S1`,
standard rows on `S2`, and standard outer convergence on `S2`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing telescope and layer telescope routes -/

structure Theorem415SourceFacingTelescopeStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_telescopeData : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverTelescopeData (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingChiData_statement_data_of_telescopeData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingTelescopeStatementData (S := S) fn f) :
    Theorem415SourceFacingChiDataStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_chiData := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_canonicalCoverChiData_of_coreData
        (S := S) B hB u hnn_u
        (BishopC.sec4_coreData_of_telescopeData
          (S := S) B hB u hnn_u
          (D.abs_error_telescopeData n B hB))

noncomputable def theorem415_integral_convergence_from_sourceFacingTelescope_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingTelescopeStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingChiData_statement_data
    (S := S)
    (theorem415_sourceFacingChiData_statement_data_of_telescopeData
      (S := S) D)

structure Theorem415SourceFacingLayerTelescopeStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_layerTelescopeData : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverLayerTelescopeData (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingTelescope_statement_data_of_layerTelescopeData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLayerTelescopeStatementData (S := S) fn f) :
    Theorem415SourceFacingTelescopeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_telescopeData := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_telescopeData_of_layerTelescopeData
        (S := S) B hB u hnn_u
        (D.abs_error_layerTelescopeData n B hB)

noncomputable def theorem415_integral_convergence_from_sourceFacingLayerTelescope_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLayerTelescopeStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingTelescope_statement_data
    (S := S)
    (theorem415_sourceFacingTelescope_statement_data_of_layerTelescopeData
      (S := S) D)

/-! ## 2. Source-facing case tools and row-case tools -/

structure Theorem415SourceFacingCaseToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_caseTools : forall n : Nat,
    BishopC.Sec4ChiFCaseToolsData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingLocalBridge_statement_data_of_caseTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCaseToolsStatementData (S := S) fn f) :
    Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_local_bridge := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_genIBLocalValueBridge_of_valueBridge
        (S := S) B hB u hnn_u
        (BishopC.sec4_genIBValueBridge_of_chiFCaseTools
          (S := S) B hB u hnn_u
          (D.abs_error_caseTools n))

noncomputable def theorem415_integral_convergence_from_sourceFacingCaseTools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCaseToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalBridge_statement_data
    (S := S)
    (theorem415_sourceFacingLocalBridge_statement_data_of_caseTools
      (S := S) D)

structure Theorem415SourceFacingRowCaseToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_rowCaseTools : forall n : Nat,
    BishopC.Sec4ChiFCaseRowTools (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingCaseTools_statement_data_of_rowCaseTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowCaseToolsStatementData (S := S) fn f) :
    Theorem415SourceFacingCaseToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_caseTools := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_chiFCaseToolsData_of_rowTools
        (S := S) u hnn_u
        (D.abs_error_rowCaseTools n)

noncomputable def theorem415_integral_convergence_from_sourceFacingRowCaseTools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowCaseToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingCaseTools_statement_data
    (S := S)
    (theorem415_sourceFacingCaseTools_statement_data_of_rowCaseTools
      (S := S) D)

/-! ## 3. Source-facing abs-pack and provider routes -/

structure Theorem415SourceFacingAbsPackToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_absPackTools : forall n : Nat,
    BishopC.Sec4ChiFCaseAbsPackTools (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingCaseTools_statement_data_of_absPackTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackToolsStatementData (S := S) fn f) :
    Theorem415SourceFacingCaseToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_caseTools := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_chiFCaseToolsData_of_absPackTools
        (S := S) u hnn_u
        (D.abs_error_absPackTools n)

noncomputable def theorem415_integral_convergence_from_sourceFacingAbsPackTools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingCaseTools_statement_data
    (S := S)
    (theorem415_sourceFacingCaseTools_statement_data_of_absPackTools
      (S := S) D)

structure Theorem415SourceFacingS2StandardOuterProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  source_s2_standard_outer_provider :
    BishopC.Sec4GeneralIBSourceS2StandardOuterProvider (S := S)

noncomputable def theorem415_sourceFacingAbsPackTools_statement_data_of_s2StandardOuterProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingS2StandardOuterProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingAbsPackToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_absPackTools := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.Sec4GeneralIBSourceS2StandardOuterProvider.absPackTools
        (S := S) D.source_s2_standard_outer_provider u hnn_u

noncomputable def
    theorem415_integral_convergence_from_sourceFacingS2StandardOuterProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingS2StandardOuterProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingAbsPackTools_statement_data
    (S := S)
    (theorem415_sourceFacingAbsPackTools_statement_data_of_s2StandardOuterProvider
      (S := S) D)

/-! ## 4. Source-facing route with row-to-flat removed -/

structure Theorem415SourceFacingNoRowToFlatStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  charDomain : BishopC.Sec4Prop42CharacteristicDomainWitness (S := S)
  standard_outer_on_s1 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4Prop42StandardAbsOuterOnS1OfFAbs
        (S := S) charDomain u unn
  rows_on_s2 : BishopC.Lemma415Prop42RowsOnS2Tool (S := S)
  outer_on_s2 : BishopC.Lemma415Prop42AbsOuterOnS2Tool (S := S)

noncomputable def theorem415_sourceFacingS2StandardOuterProvider_statement_data_of_noRowToFlat
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingNoRowToFlatStatementData (S := S) fn f) :
    Theorem415SourceFacingS2StandardOuterProviderStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  source_s2_standard_outer_provider :=
    BishopC.Sec4GeneralIBSourceS2StandardOuterProvider.ofGenericS2Tools
      (S := S)
      (BishopC.sec4_rowToFlat_source (S := S))
      D.charDomain
      D.standard_outer_on_s1
      D.rows_on_s2
      D.outer_on_s2

noncomputable def theorem415_integral_convergence_from_sourceFacingNoRowToFlat_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingNoRowToFlatStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingS2StandardOuterProvider_statement_data
    (S := S)
    (theorem415_sourceFacingS2StandardOuterProvider_statement_data_of_noRowToFlat
      (S := S) D)

structure Theorem415SourceFacingNoRowToFlatRouteAuditAfterG259 : Type where
  source_facing_convergence_in_measure_used : Nat
  pfun_representation_data_required : Nat
  local_full_set_bridge_public_input_required : Nat
  chi_telescope_data_public_input_required : Nat
  per_set_cover_or_chi_data_required : Nat
  abs_pack_tools_per_error_required : Nat
  source_s2_standard_outer_provider_required : Nat
  row_to_flat_public_input_required : Nat
  row_to_flat_closed_by_sec4_rowToFlat_source : Nat
  characteristic_domain_witness_exposed : Nat
  standard_outer_s1_required : Nat
  standard_rows_s2_required : Nat
  standard_outer_s2_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_standard_row_component_frontiers : Nat

def theorem415SourceFacingNoRowToFlatRouteAuditAfterG259 :
    Theorem415SourceFacingNoRowToFlatRouteAuditAfterG259 where
  source_facing_convergence_in_measure_used := 1
  pfun_representation_data_required := 0
  local_full_set_bridge_public_input_required := 0
  chi_telescope_data_public_input_required := 0
  per_set_cover_or_chi_data_required := 0
  abs_pack_tools_per_error_required := 0
  source_s2_standard_outer_provider_required := 0
  row_to_flat_public_input_required := 0
  row_to_flat_closed_by_sec4_rowToFlat_source := 1
  characteristic_domain_witness_exposed := 1
  standard_outer_s1_required := 1
  standard_rows_s2_required := 1
  standard_outer_s2_required := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_standard_row_component_frontiers := 4

structure Chapter4G259Theorem415SourceFacingNoRowToFlatPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g258 : Chapter4G258Theorem415SourceFacingChiPackage S
  audit : Theorem415SourceFacingNoRowToFlatRouteAuditAfterG259
  pfun_representation_layer_removed_this_step : Nat
  row_to_flat_removed_from_public_frontier_this_step : Nat
  remaining_standard_row_component_frontiers : Nat

def chapter4G259Theorem415SourceFacingNoRowToFlatPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G259Theorem415SourceFacingNoRowToFlatPackage S where
  g258 := chapter4G258Theorem415SourceFacingChiPackage S
  audit := theorem415SourceFacingNoRowToFlatRouteAuditAfterG259
  pfun_representation_layer_removed_this_step := 1
  row_to_flat_removed_from_public_frontier_this_step := 1
  remaining_standard_row_component_frontiers := 4

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G259. -/
def bishopRegularSeqChapter4Theorem415SourceFacingNoRowToFlatProgressAfterG259 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G259: replayed the lower theorem-4.15 route on the source-level surface. \
    PFun/representation convergence is no longer part of this route, \
    row-to-flat is closed by sec4_rowToFlat_source, and the remaining public \
    frontier is the four source-shaped standard-row components: \
    characteristic-domain data, S1 standard outer convergence, S2 standard \
    rows, and S2 standard outer convergence."


end BishopCReal
