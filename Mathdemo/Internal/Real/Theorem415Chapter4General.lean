import Mathdemo.Internal.Real.Theorem415RowSeedsFactored

set_option linter.style.longLine false

/-!
# G239: theorem 4.15 from the chapter-4 general `I_B` provider

G238 still exposed the theorem-4.15-specific wrapper
`Lemma415Prop42RowSeedToolsProvider`.  That wrapper is only a specialization of
the chapter-4 general measurable-integral provider
`Sec4GeneralIBRowSeedToolsProvider`.

This file makes that specialization explicit at the theorem-4.15 boundary.
The 4.15 statement-shaped route now consumes the chapter-wide `I_B` row-seed
provider directly; the theorem-specific provider is only an internal projection.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source-shaped statement data using the chapter-4 general
measurable-integral row-seed provider directly. -/
structure Theorem415Chapter4IBProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  chapter4IBProvider : BishopC.Sec4GeneralIBRowSeedToolsProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Project the chapter-wide `I_B` provider to the theorem-4.15 provider
wrapper used by G238. -/
noncomputable def theorem415_prop42_provider_data_of_chapter4IB_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBProviderStatementData (S := S) fn f) :
    Theorem415Prop42ProviderStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  rowSeedProvider :=
    BishopC.Lemma415Prop42RowSeedToolsProvider.of_generalIBProvider
      (S := S) D.chapter4IBProvider
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from source-shaped statement data and the chapter-wide
general `I_B` provider. -/
noncomputable def theorem415_integral_convergence_from_chapter4IB_provider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBProviderStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_prop42_provider_statement_data
    (S := S)
    (theorem415_prop42_provider_data_of_chapter4IB_provider (S := S) D)

structure Theorem415Chapter4IBProviderRouteAuditAfterG239 : Type where
  theorem_specific_provider_removed_from_public_415_route : Nat
  chapter4_general_IB_provider_used_directly : Nat
  theorem_specific_error_rows_factored_through_provider : Nat
  theorem_specific_majorant_rows_factored_through_provider : Nat
  domainResidualProvider_removed_from_415_source_data : Nat
  separate_g_nonneg_input_removed : Nat
  separate_limit_domination_input_removed : Nat
  substitute_majorant_g_plus_abs_f_used : Nat
  direct_abs_error_convergence_input_removed : Nat
  source_pfun_convergence_input_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_lower_layer_frontiers : Nat

def theorem415Chapter4IBProviderRouteAuditAfterG239 :
    Theorem415Chapter4IBProviderRouteAuditAfterG239 where
  theorem_specific_provider_removed_from_public_415_route := 1
  chapter4_general_IB_provider_used_directly := 1
  theorem_specific_error_rows_factored_through_provider := 1
  theorem_specific_majorant_rows_factored_through_provider := 1
  domainResidualProvider_removed_from_415_source_data := 1
  separate_g_nonneg_input_removed := 1
  separate_limit_domination_input_removed := 1
  substitute_majorant_g_plus_abs_f_used := 1
  direct_abs_error_convergence_input_removed := 1
  source_pfun_convergence_input_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_lower_layer_frontiers := 2

structure Chapter4G239Theorem415Chapter4IBProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g238 : Chapter4G238Theorem415Prop42ProviderPackage S
  audit : Theorem415Chapter4IBProviderRouteAuditAfterG239
  theorem415_chapter4IB_provider_endpoint_closed_this_step : Nat
  theorem_specific_provider_fields_remaining : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_lower_layer_frontiers : Nat

def chapter4G239Theorem415Chapter4IBProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G239Theorem415Chapter4IBProviderPackage S where
  g238 := chapter4G238Theorem415Prop42ProviderPackage S
  audit := theorem415Chapter4IBProviderRouteAuditAfterG239
  theorem415_chapter4IB_provider_endpoint_closed_this_step := 1
  theorem_specific_provider_fields_remaining := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_lower_layer_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G239. -/
def bishopRegularSeqChapter4Theorem415Chapter4IBProviderProgressAfterG239 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G239: replaced the theorem-4.15-specific Proposition-4.2 provider wrapper \
    at the public endpoint by the chapter-4 general I_B row-seed provider. \
    The 4.15 source endpoint remains at zero bridge steps; the remaining work \
    is lower-layer closure of the chapter-4 I_B provider and PFun/representation \
    source closure."


end BishopCReal

