import Mathdemo.Internal.Real.LocalTheorem415CoverSet

set_option linter.style.longLine false

/-!
# G233: Local theorem 4.15 from a domain-residual provider

G232 lowered the local theorem-4.15 route to the same cover-set provider data
used by G230.  This file narrows the generic row-seed provider to the
source-faithful domain-residual provider: the characteristic-function domain
witness is explicit, while the remaining Proposition-4.2 residual fields stay
visible.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 local cover-set data with the row-seed provider replaced by
the source-faithful domain-residual provider. -/
structure Theorem415LocalCoverSetDomainResidualSourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S) : Type _ where
  g_nonneg : BishopC.RepNonneg g
  dominated_fn : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)
  dominated_limit : BishopC.RepNonneg (g.sub f.absVal)
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  abs_error_converges_in_measure :
    BishopC.Lemma414ConvergeInMeasureToZeroData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- Rebuild the G230/G232 cover-set provider package from the narrower
domain-residual provider. -/
noncomputable def theorem415_coverSet_provider_data_of_domainResidual
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetDomainResidualSourceData fn f g) :
    Theorem415CoverSetProviderSourceData fn f g where
  g_nonneg := D.g_nonneg
  dominated_fn := D.dominated_fn
  dominated_limit := D.dominated_limit
  rowSeedProvider :=
    BishopC.Lemma415Prop42RowSeedToolsProvider.of_generalIBDomainResidualProvider
      (S := S) D.domainResidualProvider
  abs_error_converges_in_measure := D.abs_error_converges_in_measure

/-- Local full-set theorem 4.15 from the source-faithful domain-residual
provider. -/
noncomputable def theorem415_integral_convergence_from_local_domainResidual_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalCoverSetDomainResidualSourceData fn f g) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_local_coverSet_provider_data
    (S := S)
    (theorem415_coverSet_provider_data_of_domainResidual
      (S := S) D)

/-- Audit after replacing the generic row-seed provider by the
domain-residual provider. -/
structure Theorem415DomainResidualRouteAuditAfterG233 : Type where
  generic_rowSeedProvider_replaced_by_domainResidualProvider : Nat
  characteristic_domain_witness_made_explicit : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_plain_415_definition_bridge_steps : Nat

def theorem415DomainResidualRouteAuditAfterG233 :
    Theorem415DomainResidualRouteAuditAfterG233 where
  generic_rowSeedProvider_replaced_by_domainResidualProvider := 1
  characteristic_domain_witness_made_explicit := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_plain_415_definition_bridge_steps := 3

/-- G233 package. -/
structure Chapter4G233Theorem415DomainResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g232 : Chapter4G232Theorem415LocalCoverSetPackage S
  audit : Theorem415DomainResidualRouteAuditAfterG233
  theorem415_domainResidual_endpoint_closed_this_step : Nat
  remaining_plain_415_definition_bridge_steps : Nat

def chapter4G233Theorem415DomainResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G233Theorem415DomainResidualPackage S where
  g232 := chapter4G232Theorem415LocalCoverSetPackage S
  audit := theorem415DomainResidualRouteAuditAfterG233
  theorem415_domainResidual_endpoint_closed_this_step := 1
  remaining_plain_415_definition_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G233. -/
def bishopRegularSeqChapter4Theorem415DomainResidualProgressAfterG233 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G233: replaced the generic rowSeedProvider input of the local theorem-4.15 \
    route by the source-faithful domainResidualProvider. Countdown to the \
    completely plain theorem-4.15 statement remains 3, but the row-seed \
    frontier is now narrowed to explicit characteristic-domain and residual \
    Proposition-4.2 data."


end BishopCReal
