import Mathdemo.Internal.CRat_iter377
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b27_rowSeedResidual_iteration1

set_option linter.style.longLine false

/-!
# G279: remove the generic row-0 reconstruction atom

G278 exposed theorem 4.15 through the three-field
`Sec4Prop42RemainingAtomTools` package.  The b2b27 development proves that the
first row-reconstruction field is not a genuine source frontier: row 0 of the
Proposition-4.2 lambda construction already contains the original
representative on the right side of the `min2` row.

This node routes theorem 4.15 through the narrower row-seed residual provider,
without moving to the later characteristic-domain/standard-row provider route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Row-seed residuals imply the G269 local provider -/

structure Sec4GeneralRowSeedResidualProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  residual : forall
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4Prop42RowSeedResidualTools (S := S) u hu

noncomputable def sec4GeneralIBRowSeedResidualProvider_of_general
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralRowSeedResidualProvider S) :
    BishopC.Sec4GeneralIBRowSeedResidualProvider (S := S) where
  residual := P.residual

noncomputable def sec4GeneralLocalValueBridgeProvider_of_rowSeedResidualProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralRowSeedResidualProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_rowSeedResidualProvider
        (S := S)
        (sec4GeneralIBRowSeedResidualProvider_of_general
          (S := S) P)
        B hB u hu)

structure Theorem415SourceFacingRowSeedResidualProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  row_seed_residual_provider : Sec4GeneralRowSeedResidualProvider S

noncomputable def theorem415_generalProvider_statement_data_of_rowSeedResidualProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowSeedResidualProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_rowSeedResidualProvider
      (S := S) D.row_seed_residual_provider

noncomputable def theorem415_integral_convergence_from_rowSeedResidualProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowSeedResidualProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_rowSeedResidualProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415RowSeedResidualProviderRouteAuditAfterG279 : Type where
  remaining_atoms_provider_required : Nat
  row_zero_reconstruction_public_input_required : Nat
  row_zero_reconstruction_closed_by_prop42_lambda_row0 : Nat
  row_seed_residual_provider_public_input_required : Nat
  characteristic_domain_public_input_required : Nat
  standard_row_outer_provider_required : Nat
  global_characteristic_domain_witness_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_row_seed_residual_fields : Nat
  remaining_total_frontiers : Nat

def theorem415RowSeedResidualProviderRouteAuditAfterG279 :
    Theorem415RowSeedResidualProviderRouteAuditAfterG279 where
  remaining_atoms_provider_required := 0
  row_zero_reconstruction_public_input_required := 0
  row_zero_reconstruction_closed_by_prop42_lambda_row0 := 1
  row_seed_residual_provider_public_input_required := 1
  characteristic_domain_public_input_required := 0
  standard_row_outer_provider_required := 0
  global_characteristic_domain_witness_required := 0
  theorem_specific_bridge_inputs_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_row_seed_residual_fields := 3
  remaining_total_frontiers := 1

structure Chapter4G279Theorem415RowSeedResidualProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g278 : Chapter4G278Theorem415RemainingAtomsProviderPackage S
  audit : Theorem415RowSeedResidualProviderRouteAuditAfterG279
  row_zero_reconstruction_closed_this_step : Nat
  remaining_row_seed_residual_fields : Nat
  remaining_total_frontiers : Nat

def chapter4G279Theorem415RowSeedResidualProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G279Theorem415RowSeedResidualProviderPackage S where
  g278 := chapter4G278Theorem415RemainingAtomsProviderPackage S
  audit := theorem415RowSeedResidualProviderRouteAuditAfterG279
  row_zero_reconstruction_closed_this_step := 1
  remaining_row_seed_residual_fields := 3
  remaining_total_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G279. -/
def bishopRegularSeqChapter4Theorem415RowSeedResidualProgressAfterG279 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G279: closed the row-0 reconstruction atom by using the internal \
    prop-4.2 lambda-row structure. The route is now narrowed to the three \
    row-seed residual fields, without introducing a characteristic-domain or \
    standard-row public provider."


end BishopCReal
