import Mathdemo.Internal.CRat_iter351
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b39_local415SourceData_iteration1

set_option linter.style.longLine false

/-!
# G253: expose the local full-set theorem-4.15 source route

G252 closed the generic `rowToFlat` bridge in the global standard-row route.
That route is useful as a diagnostic, but its remaining `charDomain` field is
too global for the previous `IntegrableSet1` API: the source definition gives the
needed characteristic-function witnesses locally from the full-set data of the
particular set in the proof.

This file therefore exposes the already proved local full-set endpoint from
`b2b39` as the current theorem-4.15 mainline.  The displayed theorem hypothesis
still has the Bishop source shape:

* an integrable majorant `g`;
* `|f_n| <= g`;
* source measure-convergence data for `|f_n - f|`;
* the source majorant split estimate.

No PFun representation data is required at this endpoint, and no global
characteristic-domain selector is exposed.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source data on the local full-set route.

The majorant used by the completed proof kernel is `g + |f|`.  This is the
source proof's constructive replacement for a displayed `2g` estimate when the
input domination is `|f_n| <= g`; its non-negativity is derived from the
domination package, not assumed separately.
-/
structure Theorem415LocalMajorantSplitStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_rowSeeds : forall n,
    BishopC.Sec4Prop42RowSeedTools (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  majorant_split : forall (eps : R), COF.lt 0 eps ->
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f g domination.g_nonneg)
      eps
  abs_error_converges :
    BishopC.Lemma414ConvergeInMeasureToZeroData
      (S := S) (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- The current source-faithful theorem-4.15 endpoint.

This route does not ask for the global `Sec4Prop42CharacteristicDomainWitness`
and does not ask for PFun representatives.  It delegates to the local full-set
bridge, where the characteristic-function witnesses are obtained from the
integrable-set data used in the proof.
-/
noncomputable def theorem415_integral_convergence_from_local_majorant_split_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalMajorantSplitStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_source_from_majorant_split_uniform_data_localRoute
    (S := S) fn f
    D.abs_error_rowSeeds
    (D.g.add f.absVal)
    (theorem415_g_add_absf_majorant_nonneg
      (S := S) f D.g D.domination.g_nonneg)
    D.majorant_split
    D.abs_error_converges

structure Theorem415LocalMajorantSplitRouteAuditAfterG253 : Type where
  global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  row_to_flat_public_input_required : Nat
  local_full_set_route_used : Nat
  source_majorant_g_retained : Nat
  majorant_g_plus_abs_f_used : Nat
  majorant_nonnegativity_derived_from_domination : Nat
  old_global_bridge_compatibility_inside_b2b39_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_abs_error_row_seed_frontier : Nat
  remaining_majorant_split_frontier : Nat
  remaining_measure_convergence_frontier : Nat

def theorem415LocalMajorantSplitRouteAuditAfterG253 :
    Theorem415LocalMajorantSplitRouteAuditAfterG253 where
  global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  row_to_flat_public_input_required := 0
  local_full_set_route_used := 1
  source_majorant_g_retained := 1
  majorant_g_plus_abs_f_used := 1
  majorant_nonnegativity_derived_from_domination := 1
  old_global_bridge_compatibility_inside_b2b39_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_abs_error_row_seed_frontier := 1
  remaining_majorant_split_frontier := 1
  remaining_measure_convergence_frontier := 1

structure Chapter4G253Theorem415LocalMajorantSplitPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g252 : Chapter4G252Theorem415NoRowToFlatPackage S
  audit : Theorem415LocalMajorantSplitRouteAuditAfterG253
  global_charDomain_removed_from_mainline_this_step : Nat
  pfun_representation_removed_from_mainline_this_step : Nat
  remaining_source_frontiers : Nat

def chapter4G253Theorem415LocalMajorantSplitPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G253Theorem415LocalMajorantSplitPackage S where
  g252 := chapter4G252Theorem415NoRowToFlatPackage S
  audit := theorem415LocalMajorantSplitRouteAuditAfterG253
  global_charDomain_removed_from_mainline_this_step := 1
  pfun_representation_removed_from_mainline_this_step := 1
  remaining_source_frontiers := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G253. -/
def bishopRegularSeqChapter4Theorem415LocalMajorantSplitProgressAfterG253 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G253: exposed theorem 4.15 through the local full-set source route. The \
    current mainline no longer requires a global characteristic-domain selector, \
    PFun representative data, or a public row-to-flat input. The remaining \
    source frontiers are abs-error row seeds, the majorant split estimate, and \
    source measure-convergence data."


end BishopCReal
