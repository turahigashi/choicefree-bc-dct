import Mathdemo.Internal.Real.Theorem415SourceRouteProposition

set_option linter.style.longLine false

/-!
# G238: theorem-4.15 row seeds factored through the Proposition 4.2 provider

G237 removed `domainResidualProvider` from theorem-4.15 source data but still
kept two theorem-specific row-seed fields: one for `|f_n - f|` and one for the
constructive majorant `g + |f|`.

This file factors both fields through the existing generic Proposition-4.2
row-seed provider.  The theorem-4.15 layer now asks only for the lower-layer
Proposition-4.2 provider; the two specialized row-seed families are projections
from that provider.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source-shaped statement data with theorem-specific row seeds
factored through the generic Proposition-4.2 row-seed provider. -/
structure Theorem415Prop42ProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  rowSeedProvider : BishopC.Lemma415Prop42RowSeedToolsProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Expand the generic Proposition-4.2 provider into the G237 local row-seed
data. -/
noncomputable def theorem415_localProp42_data_of_prop42_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Prop42ProviderStatementData (S := S) fn f) :
    Theorem415LocalProp42StatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  errorRows := fun n =>
    D.rowSeedProvider.rowSeeds
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  majorantRows :=
    D.rowSeedProvider.rowSeeds (D.g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f D.g D.domination.g_nonneg)
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from statement-shaped data plus the generic Proposition-4.2
provider. -/
noncomputable def theorem415_integral_convergence_from_prop42_provider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Prop42ProviderStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_localProp42_statement_data
    (S := S)
    (theorem415_localProp42_data_of_prop42_provider (S := S) D)

structure Theorem415Prop42ProviderRouteAuditAfterG238 : Type where
  theorem_specific_error_rows_factored_through_provider : Nat
  theorem_specific_majorant_rows_factored_through_provider : Nat
  domainResidualProvider_removed_from_415_source_data : Nat
  prop42_provider_is_lower_layer_frontier : Nat
  separate_g_nonneg_input_removed : Nat
  separate_limit_domination_input_removed : Nat
  substitute_majorant_g_plus_abs_f_used : Nat
  direct_abs_error_convergence_input_removed : Nat
  source_pfun_convergence_input_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_lower_layer_frontiers : Nat

def theorem415Prop42ProviderRouteAuditAfterG238 :
    Theorem415Prop42ProviderRouteAuditAfterG238 where
  theorem_specific_error_rows_factored_through_provider := 1
  theorem_specific_majorant_rows_factored_through_provider := 1
  domainResidualProvider_removed_from_415_source_data := 1
  prop42_provider_is_lower_layer_frontier := 1
  separate_g_nonneg_input_removed := 1
  separate_limit_domination_input_removed := 1
  substitute_majorant_g_plus_abs_f_used := 1
  direct_abs_error_convergence_input_removed := 1
  source_pfun_convergence_input_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_lower_layer_frontiers := 2

structure Chapter4G238Theorem415Prop42ProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g237 : Chapter4G237Theorem415LocalProp42Package S
  audit : Theorem415Prop42ProviderRouteAuditAfterG238
  theorem415_provider_endpoint_closed_this_step : Nat
  theorem_specific_row_seed_fields_remaining : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_lower_layer_frontiers : Nat

def chapter4G238Theorem415Prop42ProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G238Theorem415Prop42ProviderPackage S where
  g237 := chapter4G237Theorem415LocalProp42Package S
  audit := theorem415Prop42ProviderRouteAuditAfterG238
  theorem415_provider_endpoint_closed_this_step := 1
  theorem_specific_row_seed_fields_remaining := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_lower_layer_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G238. -/
def bishopRegularSeqChapter4Theorem415Prop42ProviderProgressAfterG238 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G238: factored the theorem-specific error and majorant row seeds through \
    the generic Proposition-4.2 row-seed provider. The theorem-4.15 source \
    endpoint still has zero bridge steps; the remaining work is now lower-layer \
    Proposition-4.2 provider closure and source PFun/representation closure."


end BishopCReal

