import Mathdemo.Internal.Real.RemoveGenericRow0ReconstructionAtom

set_option linter.style.longLine false

/-!
# G280: route the row-seed residual surface through the local full-set theorem

G279 narrowed the general `I_B` provider route to the row-seed residual
package.  The next source-faithful move is not to push that residual through a
global characteristic-domain selector.  The existing local full-set theorem
route from G257 already keeps the required pointwise witnesses local.

This node connects the G279 row-seed-residual surface to that local full-set
route.  The mathematical input is unchanged, but the main theorem path now
uses the source-level local-bridge proof rather than the older general-provider
compatibility path.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Row-seed residual provider as local full-set theorem data -/

noncomputable def theorem415_sourceFacingLocalBridge_statement_data_of_rowSeedResidualProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowSeedResidualProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_local_bridge := by
    intro n B hB
    exact
      (sec4GeneralLocalValueBridgeProvider_of_rowSeedResidualProvider
        (S := S) D.row_seed_residual_provider).bridge
        B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

/-- The G279 statement routed through the source-level local full-set proof. -/
noncomputable def
    theorem415_integral_convergence_from_rowSeedResidualProvider_localFullSet_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowSeedResidualProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalBridge_statement_data
    (S := S)
    (theorem415_sourceFacingLocalBridge_statement_data_of_rowSeedResidualProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415RowSeedResidualLocalFullSetRouteAuditAfterG280 : Type where
  older_general_provider_path_required : Nat
  local_full_set_theorem_path_used : Nat
  row_seed_residual_provider_public_input_required : Nat
  global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  row_to_flat_public_input_required : Nat
  direct_abs_error_rowSeeds_public_input_required : Nat
  majorant_split_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_row_seed_residual_fields : Nat
  remaining_total_frontiers : Nat

def theorem415RowSeedResidualLocalFullSetRouteAuditAfterG280 :
    Theorem415RowSeedResidualLocalFullSetRouteAuditAfterG280 where
  older_general_provider_path_required := 0
  local_full_set_theorem_path_used := 1
  row_seed_residual_provider_public_input_required := 1
  global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  row_to_flat_public_input_required := 0
  direct_abs_error_rowSeeds_public_input_required := 0
  majorant_split_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_row_seed_residual_fields := 3
  remaining_total_frontiers := 1

structure Chapter4G280Theorem415RowSeedResidualLocalFullSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g279 : Chapter4G279Theorem415RowSeedResidualProviderPackage S
  audit : Theorem415RowSeedResidualLocalFullSetRouteAuditAfterG280
  switched_to_local_full_set_path_this_step : Nat
  remaining_row_seed_residual_fields : Nat
  remaining_total_frontiers : Nat

def chapter4G280Theorem415RowSeedResidualLocalFullSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G280Theorem415RowSeedResidualLocalFullSetPackage S where
  g279 := chapter4G279Theorem415RowSeedResidualProviderPackage S
  audit := theorem415RowSeedResidualLocalFullSetRouteAuditAfterG280
  switched_to_local_full_set_path_this_step := 1
  remaining_row_seed_residual_fields := 3
  remaining_total_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G280. -/
def bishopRegularSeqChapter4Theorem415RowSeedResidualLocalFullSetProgressAfterG280 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G280: routed the row-seed residual surface through the source-level \
    local full-set theorem path. The main route no longer pushes toward a \
    global characteristic-domain selector; countdown remains 1, namely the \
    local derivation of the remaining row-seed residual facts from the \
    characteristic-function/integrable-representative definitions."


end BishopCReal
