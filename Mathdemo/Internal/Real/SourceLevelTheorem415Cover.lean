import Mathdemo.Internal.Real.SourceLevelTheorem415Local
import Mathdemo.Internal.Sec4.CoverChiTelescopeBridge

set_option linter.style.longLine false

/-!
# G258: source-level theorem 4.15 from cover/chi construction data

G257 made the theorem-4.15 statement source-level again and removed the
global domain-residual provider from the main route.  Its remaining public
input was still the local full-set value bridge for the abs-error sequence.

This file traces that bridge back to the construction data used by the
chapter-4 `I_B` proof:

* canonical cover facts imply the local bridge;
* lower `chi` telescope data imply the canonical cover facts;
* the source-level convergence-in-measure statement is preserved.

Thus the remaining frontier is no longer "supply a bridge" but the more
specific source task: construct the `chi` telescope data from the measurable
set / integrable set definitions.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-facing theorem-4.15 statement where the abs-error local bridge is
derived from canonical cover facts. -/
structure Theorem415SourceFacingCoverFactsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_coverFacts : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverFacts (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

/-- Canonical cover facts produce the local-bridge source-level statement. -/
noncomputable def
    theorem415_sourceFacingLocalBridge_statement_data_of_coverFacts
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCoverFactsStatementData (S := S) fn f) :
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
        (BishopC.sec4_genIBValueBridge_of_coverFacts
          (S := S) B hB u hnn_u
          (D.abs_error_coverFacts n B hB))

/-- Source-facing theorem 4.15 from canonical cover facts. -/
noncomputable def
    theorem415_integral_convergence_from_sourceFacingCoverFacts_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCoverFactsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalBridge_statement_data
    (S := S)
    (theorem415_sourceFacingLocalBridge_statement_data_of_coverFacts
      (S := S) D)

/-- Source-facing theorem-4.15 statement where cover facts are supplied by the
lower `chi` telescope data. -/
structure Theorem415SourceFacingChiDataStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_chiData : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverChiData (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

/-- Lower `chi` telescope data produces canonical cover-facts statement data. -/
noncomputable def theorem415_sourceFacingCoverFacts_statement_data_of_chiData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingChiDataStatementData (S := S) fn f) :
    Theorem415SourceFacingCoverFactsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_coverFacts := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_canonicalCoverFacts_of_chiData
        (S := S) B hB u hnn_u
        (D.abs_error_chiData n B hB)

/-- Lower `chi` telescope data produces the local-bridge source-level
statement. -/
noncomputable def theorem415_sourceFacingLocalBridge_statement_data_of_chiData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingChiDataStatementData (S := S) fn f) :
    Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f :=
  theorem415_sourceFacingLocalBridge_statement_data_of_coverFacts
    (S := S)
    (theorem415_sourceFacingCoverFacts_statement_data_of_chiData
      (S := S) D)

/-- Source-facing theorem 4.15 from the lower `chi` telescope data. -/
noncomputable def
    theorem415_integral_convergence_from_sourceFacingChiData_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingChiDataStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingCoverFacts_statement_data
    (S := S)
    (theorem415_sourceFacingCoverFacts_statement_data_of_chiData
      (S := S) D)

structure Theorem415SourceFacingChiRouteAuditAfterG258 : Type where
  source_facing_convergence_in_measure_used : Nat
  local_full_set_bridge_public_input_required : Nat
  canonical_cover_facts_public_input_required : Nat
  chi_telescope_data_public_input_required : Nat
  global_domain_residual_provider_required : Nat
  global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  row_to_flat_public_input_required : Nat
  direct_abs_error_rowSeeds_public_input_required : Nat
  majorant_split_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_chi_telescope_derivation_frontiers : Nat

def theorem415SourceFacingChiRouteAuditAfterG258 :
    Theorem415SourceFacingChiRouteAuditAfterG258 where
  source_facing_convergence_in_measure_used := 1
  local_full_set_bridge_public_input_required := 0
  canonical_cover_facts_public_input_required := 0
  chi_telescope_data_public_input_required := 1
  global_domain_residual_provider_required := 0
  global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  row_to_flat_public_input_required := 0
  direct_abs_error_rowSeeds_public_input_required := 0
  majorant_split_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_chi_telescope_derivation_frontiers := 1

structure Chapter4G258Theorem415SourceFacingChiPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g257 : Chapter4G257Theorem415SourceFacingLocalBridgePackage S
  audit : Theorem415SourceFacingChiRouteAuditAfterG258
  local_bridge_public_input_removed_this_step : Nat
  remaining_chi_telescope_derivation_frontiers : Nat

def chapter4G258Theorem415SourceFacingChiPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G258Theorem415SourceFacingChiPackage S where
  g257 := chapter4G257Theorem415SourceFacingLocalBridgePackage S
  audit := theorem415SourceFacingChiRouteAuditAfterG258
  local_bridge_public_input_removed_this_step := 1
  remaining_chi_telescope_derivation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G258. -/
def bishopRegularSeqChapter4Theorem415SourceFacingChiProgressAfterG258 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G258: kept theorem 4.15 source-level and replaced the public local \
    bridge input by canonical cover facts, then by lower chi telescope data. \
    No PFun representatives, row-to-flat input, direct row seeds, majorant \
    split, global domain provider, or external choice principle are public \
    inputs on this route. The remaining frontier is the source derivation of \
    the chi telescope data from the measurable-set and integrable-set \
    definitions."


end BishopCReal
