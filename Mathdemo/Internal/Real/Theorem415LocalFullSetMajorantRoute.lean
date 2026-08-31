import Mathdemo.Internal.Real.Theorem415SourceRouteRow
import Mathdemo.Internal.Sec4.Local415SourceData

set_option linter.style.longLine false

/-!
# G231: Theorem 4.15 through the local full-set majorant route

G230 closed the current cover-set/default-budget/provider endpoint.  This file
adds the parallel local route from `b2b39`: the theorem-4.15 proof now consumes
the source majorant split estimate and assembles the `I_B` interface through
local full-set witnesses.  This keeps the printed Bishop proof shape visible:
choose a large set `A`, control the `A ∧ B` part by absolute continuity, control
the `-A` tail, then apply theorem 4.14 to the abs-error sequence.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-shaped theorem-4.15 data for the local full-set majorant route.

The field `majorantSplit` is the constructive content of the source proof's
large-set/tail split.  It is not obtained by selecting witnesses from a bare
Prop theorem; downstream code consumes it as ordinary data. -/
structure Theorem415LocalMajorantSourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f majorant : BishopC.IntegrableRep S) : Type _ where
  majorant_nonneg : BishopC.RepNonneg majorant
  rowSeedProvider : BishopC.Lemma415Prop42RowSeedToolsProvider (S := S)
  majorantSplit : forall (eps : R), COF.lt 0 eps ->
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f majorant majorant_nonneg eps
  abs_error_converges_in_measure :
    BishopC.Lemma414ConvergeInMeasureToZeroData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- Theorem 4.15 through the local full-set route.

Compared with the G230 cover-set endpoint, this entry point uses the local
`I_B` construction from `b2b39`, so the complement and split witnesses are
assembled from local full-set data rather than by exposing a global value
bridge as downstream theorem data. -/
noncomputable def theorem415_integral_convergence_from_local_majorant_provider_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f majorant : BishopC.IntegrableRep S}
    (D : Theorem415LocalMajorantSourceData fn f majorant) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_source_from_majorant_split_uniform_data_localRoute
    (S := S) fn f
    (fun n =>
      D.rowSeedProvider.rowSeeds
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n))
    majorant D.majorant_nonneg D.majorantSplit
    D.abs_error_converges_in_measure

/-- Audit after adding the local full-set majorant endpoint.

The countdown remains three for the completely plain theorem-4.15 statement:
this step relocates one frontier to source-shaped local data, but it does not
pretend to derive the majorant split, majorant nonnegativity, or convergence
witnesses from a thin Prop statement. -/
structure Theorem415LocalMajorantRouteAuditAfterG231 : Type where
  local_full_set_majorant_endpoint_connected : Nat
  coverSet_provider_endpoint_preserved : Nat
  global_value_bridge_exposed_as_downstream_endpoint_data : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_definition_witness_bridges_to_plain_415 : Nat

def theorem415LocalMajorantRouteAuditAfterG231 :
    Theorem415LocalMajorantRouteAuditAfterG231 where
  local_full_set_majorant_endpoint_connected := 1
  coverSet_provider_endpoint_preserved := 1
  global_value_bridge_exposed_as_downstream_endpoint_data := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_definition_witness_bridges_to_plain_415 := 3

/-- G231 package: 4.15 has both the cover-set provider endpoint and the local
full-set majorant endpoint available. -/
structure Chapter4G231Theorem415LocalMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g230 : Chapter4G230Theorem415ProviderPackage S
  audit : Theorem415LocalMajorantRouteAuditAfterG231
  theorem415_local_majorant_endpoint_closed_this_step : Nat
  remaining_plain_415_definition_bridge_steps : Nat

def chapter4G231Theorem415LocalMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G231Theorem415LocalMajorantPackage S where
  g230 := chapter4G230Theorem415ProviderPackage S
  audit := theorem415LocalMajorantRouteAuditAfterG231
  theorem415_local_majorant_endpoint_closed_this_step := 1
  remaining_plain_415_definition_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G231. -/
def bishopRegularSeqChapter4Theorem415LocalMajorantProgressAfterG231 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G231: connected theorem 4.15 to the local full-set majorant route. \
    The source-data endpoint is closed; countdown to the completely plain \
    theorem-4.15 statement remains 3 definition-witness bridges."


end BishopCReal
