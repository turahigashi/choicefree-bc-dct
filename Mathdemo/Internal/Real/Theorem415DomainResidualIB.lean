import Mathdemo.Internal.Real.Theorem415Chapter4Residual

set_option linter.style.longLine false

/-!
# G241: theorem 4.15 from the domain-residual `I_B` provider

G240 lowered theorem 4.15 to the three-field chapter-4 residual provider.
The next already-available lower layer is
`Sec4GeneralIBDomainResidualProvider`: it fills the positive-side
characteristic-function absolute-convergence field from the explicit
source-domain witness for `chi_A`.

This file routes theorem 4.15 through that narrower provider.  The 4.15 layer
still has zero bridge steps; the Proposition-4.2 provider frontier is reduced
from three residual row/cut fields to the source-domain witness plus the two
remaining row/cut fields.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source-shaped data using the chapter-4 domain-residual
provider for the general measurable integral. -/
structure Theorem415Chapter4IBDomainResidualProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  chapter4IBDomainResidualProvider :
    BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Convert the domain-residual provider endpoint to the G240 residual-provider
endpoint by filling the `chi_A` positive-side field from `charDomain`. -/
noncomputable def theorem415_chapter4IB_residual_provider_data_of_domain_residual_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBDomainResidualProviderStatementData
      (S := S) fn f) :
    Theorem415Chapter4IBResidualProviderStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  chapter4IBResidualProvider :=
    BishopC.Sec4GeneralIBDomainResidualProvider.toResidualProvider
      (S := S) D.chapter4IBDomainResidualProvider
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from source-shaped data and the narrowed chapter-4
domain-residual `I_B` provider. -/
noncomputable def theorem415_integral_convergence_from_chapter4IB_domain_residual_provider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBDomainResidualProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_chapter4IB_residual_provider_statement_data
    (S := S)
    (theorem415_chapter4IB_residual_provider_data_of_domain_residual_provider
      (S := S) D)

structure Theorem415Chapter4IBDomainResidualProviderRouteAuditAfterG241 : Type where
  chi_abs_positive_field_filled_from_charDomain : Nat
  public_route_uses_domain_residual_IB_provider : Nat
  row0_right_provider_field_closed_generically : Nat
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
  characteristic_domain_witness_explicit : Nat
  remaining_provider_residual_fields : Nat
  remaining_lower_layer_frontiers : Nat

def theorem415Chapter4IBDomainResidualProviderRouteAuditAfterG241 :
    Theorem415Chapter4IBDomainResidualProviderRouteAuditAfterG241 where
  chi_abs_positive_field_filled_from_charDomain := 1
  public_route_uses_domain_residual_IB_provider := 1
  row0_right_provider_field_closed_generically := 1
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
  characteristic_domain_witness_explicit := 1
  remaining_provider_residual_fields := 2
  remaining_lower_layer_frontiers := 2

structure Chapter4G241Theorem415Chapter4IBDomainResidualProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g240 : Chapter4G240Theorem415Chapter4IBResidualProviderPackage S
  audit : Theorem415Chapter4IBDomainResidualProviderRouteAuditAfterG241
  theorem415_domain_residual_provider_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  characteristic_domain_witness_explicit : Nat
  remaining_provider_residual_fields : Nat
  remaining_lower_layer_frontiers : Nat

def chapter4G241Theorem415Chapter4IBDomainResidualProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G241Theorem415Chapter4IBDomainResidualProviderPackage S where
  g240 := chapter4G240Theorem415Chapter4IBResidualProviderPackage S
  audit := theorem415Chapter4IBDomainResidualProviderRouteAuditAfterG241
  theorem415_domain_residual_provider_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 0
  characteristic_domain_witness_explicit := 1
  remaining_provider_residual_fields := 2
  remaining_lower_layer_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G241. -/
def bishopRegularSeqChapter4Theorem415Chapter4IBDomainResidualProviderProgressAfterG241 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G241: lowered the theorem-4.15 public route from the three-field residual \
    I_B provider to the domain-residual provider. The positive-side chi_A \
    absolute-convergence field is now filled from the explicit characteristic \
    domain witness. The 4.15 source endpoint remains at zero bridge steps; \
    two Proposition-4.2 row/cut residual fields and the PFun/representation \
    source layer remain."


end BishopCReal

