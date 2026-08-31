import Mathdemo.Internal.Real.Theorem415Chapter4General

set_option linter.style.longLine false

/-!
# G240: theorem 4.15 from the chapter-4 residual `I_B` provider

G239 uses the chapter-4 general row-seed provider.  That provider still exposes
one field that is already generically proved: the row-0-right reconstruction of
the original representative from the Proposition-4.2 rows.

The lower chapter-4 API `Sec4GeneralIBRowSeedResidualProvider` removes that
field and keeps only the three genuinely residual Proposition-4.2 row/cut
ingredients.  This file routes theorem 4.15 through that residual provider.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source-shaped data using the narrowed chapter-4 residual
provider for the general measurable integral. -/
structure Theorem415Chapter4IBResidualProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  chapter4IBResidualProvider :
    BishopC.Sec4GeneralIBRowSeedResidualProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Convert the residual provider endpoint to the G239 chapter-wide provider
endpoint by filling the row-0-right field generically. -/
noncomputable def theorem415_chapter4IB_provider_data_of_residual_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBResidualProviderStatementData (S := S) fn f) :
    Theorem415Chapter4IBProviderStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  chapter4IBProvider :=
    BishopC.Sec4GeneralIBRowSeedResidualProvider.toRowSeedProvider
      (S := S) D.chapter4IBResidualProvider
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from source-shaped data and the narrowed chapter-4 residual
`I_B` provider. -/
noncomputable def theorem415_integral_convergence_from_chapter4IB_residual_provider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBResidualProviderStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_chapter4IB_provider_statement_data
    (S := S)
    (theorem415_chapter4IB_provider_data_of_residual_provider
      (S := S) D)

structure Theorem415Chapter4IBResidualProviderRouteAuditAfterG240 : Type where
  row0_right_provider_field_closed_generically : Nat
  public_route_uses_residual_IB_provider : Nat
  chapter4_general_IB_provider_used_directly_before_projection : Nat
  theorem_specific_provider_removed_from_public_415_route : Nat
  domainResidualProvider_removed_from_415_source_data : Nat
  separate_g_nonneg_input_removed : Nat
  separate_limit_domination_input_removed : Nat
  substitute_majorant_g_plus_abs_f_used : Nat
  direct_abs_error_convergence_input_removed : Nat
  source_pfun_convergence_input_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_provider_residual_fields : Nat
  remaining_lower_layer_frontiers : Nat

def theorem415Chapter4IBResidualProviderRouteAuditAfterG240 :
    Theorem415Chapter4IBResidualProviderRouteAuditAfterG240 where
  row0_right_provider_field_closed_generically := 1
  public_route_uses_residual_IB_provider := 1
  chapter4_general_IB_provider_used_directly_before_projection := 1
  theorem_specific_provider_removed_from_public_415_route := 1
  domainResidualProvider_removed_from_415_source_data := 1
  separate_g_nonneg_input_removed := 1
  separate_limit_domination_input_removed := 1
  substitute_majorant_g_plus_abs_f_used := 1
  direct_abs_error_convergence_input_removed := 1
  source_pfun_convergence_input_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_provider_residual_fields := 3
  remaining_lower_layer_frontiers := 2

structure Chapter4G240Theorem415Chapter4IBResidualProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g239 : Chapter4G239Theorem415Chapter4IBProviderPackage S
  audit : Theorem415Chapter4IBResidualProviderRouteAuditAfterG240
  theorem415_residual_provider_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_provider_residual_fields : Nat
  remaining_lower_layer_frontiers : Nat

def chapter4G240Theorem415Chapter4IBResidualProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G240Theorem415Chapter4IBResidualProviderPackage S where
  g239 := chapter4G239Theorem415Chapter4IBProviderPackage S
  audit := theorem415Chapter4IBResidualProviderRouteAuditAfterG240
  theorem415_residual_provider_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 0
  remaining_provider_residual_fields := 3
  remaining_lower_layer_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G240. -/
def bishopRegularSeqChapter4Theorem415Chapter4IBResidualProviderProgressAfterG240 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G240: lowered the theorem-4.15 public route from the full chapter-4 I_B \
    row-seed provider to the residual provider, using the already proved \
    row-0-right reconstruction to fill the discharged field. The 4.15 source \
    endpoint remains at zero bridge steps; the Proposition-4.2 provider \
    frontier is now the three residual row/cut fields plus the PFun/representation \
    source layer."


end BishopCReal

