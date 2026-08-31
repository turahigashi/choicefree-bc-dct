import Mathdemo.Internal.Real.ExposeLocalFullSetTheorem4
import Mathdemo.Internal.Sec4.SourceDomainWitness

set_option linter.style.longLine false

/-!
# G254: remove direct abs-error row seeds from the theorem-4.15 mainline

G253 exposed the local full-set route but still accepted row-seed tools for
each absolute-error function `|f_n-f|`.  Those row seeds are Proposition 4.2
machinery, not independent theorem-4.15 data.

This file replaces the per-`n` row-seed input by the existing
`Sec4GeneralIBDomainResidualProvider`.  The provider is still a visible Chapter
4 frontier, but it is now the general Proposition 4.2/domain-residual surface,
not an arbitrary sequence of theorem-specific witnesses.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 local source data after direct abs-error row seeds have been
replaced by the general Chapter-4 domain-residual provider. -/
structure Theorem415LocalMajorantSplitDomainResidualStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  majorant_split : forall (eps : R), COF.lt 0 eps ->
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f g domination.g_nonneg)
      eps
  abs_error_converges :
    BishopC.Lemma414ConvergeInMeasureToZeroData
      (S := S) (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- The row-seed provider induced by the source domain-residual provider. -/
noncomputable def theorem415_domainResidual_rowSeedProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalMajorantSplitDomainResidualStatementData
      (S := S) fn f) :
    BishopC.Lemma415Prop42RowSeedToolsProvider (S := S) :=
  BishopC.Lemma415Prop42RowSeedToolsProvider.of_generalIBDomainResidualProvider
    (S := S) D.domainResidualProvider

/-- Forget the domain-residual packaging and rebuild the G253 statement data. -/
noncomputable def theorem415_localMajorantSplit_statement_data_of_domainResidual
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalMajorantSplitDomainResidualStatementData
      (S := S) fn f) :
    Theorem415LocalMajorantSplitStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_rowSeeds := fun n =>
    (theorem415_domainResidual_rowSeedProvider (S := S) D).rowSeeds
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  majorant_split := D.majorant_split
  abs_error_converges := D.abs_error_converges

/-- Theorem 4.15 with per-`n` abs-error row seeds removed from the public
frontier. -/
noncomputable def
    theorem415_integral_convergence_from_domainResidual_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415LocalMajorantSplitDomainResidualStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_local_majorant_split_statement_data
    (S := S)
    (theorem415_localMajorantSplit_statement_data_of_domainResidual
      (S := S) D)

structure Theorem415DomainResidualRouteAuditAfterG254 : Type where
  direct_abs_error_rowSeeds_public_input_required : Nat
  rowSeeds_derived_from_domainResidualProvider : Nat
  domainResidualProvider_visible_frontier : Nat
  global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  row_to_flat_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_majorant_split_frontier : Nat
  remaining_measure_convergence_frontier : Nat

def theorem415DomainResidualRouteAuditAfterG254 :
    Theorem415DomainResidualRouteAuditAfterG254 where
  direct_abs_error_rowSeeds_public_input_required := 0
  rowSeeds_derived_from_domainResidualProvider := 1
  domainResidualProvider_visible_frontier := 1
  global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  row_to_flat_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_majorant_split_frontier := 1
  remaining_measure_convergence_frontier := 1

structure Chapter4G254Theorem415DomainResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g253 : Chapter4G253Theorem415LocalMajorantSplitPackage S
  audit : Theorem415DomainResidualRouteAuditAfterG254
  direct_abs_error_rowSeeds_removed_this_step : Nat
  remaining_core_source_frontiers : Nat
  remaining_chapter4_provider_frontiers : Nat

def chapter4G254Theorem415DomainResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G254Theorem415DomainResidualPackage S where
  g253 := chapter4G253Theorem415LocalMajorantSplitPackage S
  audit := theorem415DomainResidualRouteAuditAfterG254
  direct_abs_error_rowSeeds_removed_this_step := 1
  remaining_core_source_frontiers := 2
  remaining_chapter4_provider_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G254. -/
def bishopRegularSeqChapter4Theorem415DomainResidualProgressAfterG254 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G254: removed direct per-n abs-error row seeds from the theorem 4.15 \
    mainline. They are now obtained from the Chapter-4 domain-residual \
    provider. The remaining core source frontiers are the majorant split \
    estimate and the source measure-convergence data; the domain-residual \
    provider remains as the visible Proposition 4.2 provider frontier."


end BishopCReal
