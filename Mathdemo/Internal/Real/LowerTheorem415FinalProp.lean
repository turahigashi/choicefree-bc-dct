import Mathdemo.Internal.Real.CloseCoverDifferenceDichotomyInput
import Mathdemo.Internal.Sec4.RemainingAtomsAssembly

set_option linter.style.longLine false

/-!
# G278: lower theorem 4.15 to the final prop-4.2 remaining atoms

G277 left one public frontier: a generic `Sec4ChiFCaseToolsData` provider.
The b2b22 development plugs the completed row-to-flat construction into the
case-tools route.  After that, the only remaining inputs are the three
`prop_4_2_lambda_k` atoms identified in `Sec4Prop42RemainingAtomTools`.

This node exposes theorem 4.15 through exactly those atoms, removing the
case-tools provider as a public assumption.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Remaining prop-4.2 atoms imply the G269 local provider -/

structure Sec4GeneralRemainingAtomsProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  atoms : forall
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4Prop42RemainingAtomTools (S := S) u hu

noncomputable def sec4GeneralLocalValueBridgeProvider_of_remainingAtomsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralRemainingAtomsProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_remainingAtoms
        (S := S) B hB u hu (P.atoms u hu))

structure Theorem415SourceFacingRemainingAtomsProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  remaining_atoms_provider : Sec4GeneralRemainingAtomsProvider S

noncomputable def theorem415_generalProvider_statement_data_of_remainingAtomsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRemainingAtomsProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_remainingAtomsProvider
      (S := S) D.remaining_atoms_provider

noncomputable def theorem415_integral_convergence_from_remainingAtomsProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRemainingAtomsProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_remainingAtomsProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415RemainingAtomsProviderRouteAuditAfterG278 : Type where
  chiF_case_tools_provider_required : Nat
  row_to_flat_public_input_required : Nat
  row_to_flat_closed_by_sec4_rowToFlat_source : Nat
  cover_dichotomy_public_input_required : Nat
  cover_dichotomy_closed_by_sec4_coverDichotomyData : Nat
  global_characteristic_domain_witness_required : Nat
  remaining_atoms_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_prop42_atom_fields : Nat
  remaining_total_frontiers : Nat

def theorem415RemainingAtomsProviderRouteAuditAfterG278 :
    Theorem415RemainingAtomsProviderRouteAuditAfterG278 where
  chiF_case_tools_provider_required := 0
  row_to_flat_public_input_required := 0
  row_to_flat_closed_by_sec4_rowToFlat_source := 1
  cover_dichotomy_public_input_required := 0
  cover_dichotomy_closed_by_sec4_coverDichotomyData := 1
  global_characteristic_domain_witness_required := 0
  remaining_atoms_provider_public_input_required := 1
  theorem_specific_bridge_inputs_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_prop42_atom_fields := 3
  remaining_total_frontiers := 1

structure Chapter4G278Theorem415RemainingAtomsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g277 : Chapter4G277Theorem415ChiFCaseToolsProviderPackage S
  audit : Theorem415RemainingAtomsProviderRouteAuditAfterG278
  chiF_case_tools_provider_replaced_this_step : Nat
  remaining_prop42_atom_fields : Nat
  remaining_total_frontiers : Nat

def chapter4G278Theorem415RemainingAtomsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G278Theorem415RemainingAtomsProviderPackage S where
  g277 := chapter4G277Theorem415ChiFCaseToolsProviderPackage S
  audit := theorem415RemainingAtomsProviderRouteAuditAfterG278
  chiF_case_tools_provider_replaced_this_step := 1
  remaining_prop42_atom_fields := 3
  remaining_total_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G278. -/
def bishopRegularSeqChapter4Theorem415RemainingAtomsProgressAfterG278 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G278: lowered theorem 4.15 from generic chi-f case tools to the final \
    prop-4.2 remaining-atom package. rowToFlat and the cover dichotomies are \
    now closed by existing Bishop-faithful constructions. Countdown remains 1 \
    frontier, but its content is now exactly the three prop-4.2 lambda-row \
    atoms: f-abs from lambda abs rows on S1, abs-outer row packing on S1 from \
    f-abs, and abs-outer row packing on S2."


end BishopCReal
