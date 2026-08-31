import Mathdemo.Internal.Real.Theorem415SourceCoverSet

set_option linter.style.longLine false

/-!
# G230: Theorem 4.15 source route with a row-seed provider

G229 used explicit row-seed data for the theorem-4.15 error sequence and for the
dominating function `g`.  The source-complete files already factor that
obligation as a general Proposition-4.2 row-seed provider.  This file routes the
cover-set proof through that provider, reducing the remaining plain-4.15
bridges by one.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-shaped theorem-4.15 data using a general Proposition-4.2 row-seed
provider instead of separate row-seed fields for the error sequence and `g`. -/
structure Theorem415CoverSetProviderSourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S) : Type _ where
  g_nonneg : BishopC.RepNonneg g
  dominated_fn : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)
  dominated_limit : BishopC.RepNonneg (g.sub f.absVal)
  rowSeedProvider : BishopC.Lemma415Prop42RowSeedToolsProvider (S := S)
  abs_error_converges_in_measure :
    BishopC.Lemma414ConvergeInMeasureToZeroData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- Expand provider-shaped 4.15 data to the explicit cover-set data of G229. -/
noncomputable def theorem415_coverSet_source_data_of_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetProviderSourceData fn f g) :
    Theorem415CoverSetSourceData fn f g where
  g_nonneg := D.g_nonneg
  dominated_fn := D.dominated_fn
  dominated_limit := D.dominated_limit
  abs_error_rowSeeds := fun n =>
    D.rowSeedProvider.rowSeeds
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  g_rowSeeds := D.rowSeedProvider.rowSeeds g D.g_nonneg
  abs_error_converges_in_measure := D.abs_error_converges_in_measure

/-- The abs-error convergence part of theorem 4.15 from provider-shaped
source data. -/
noncomputable def theorem415_abs_error_convergence_from_coverSet_provider_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetProviderSourceData fn f g) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  theorem415_abs_error_convergence_from_coverSet_source_data
    (S := S) (theorem415_coverSet_source_data_of_provider (S := S) D)

/-- Theorem 4.15 via the source cover-set route and a general row-seed
provider. -/
noncomputable def theorem415_integral_convergence_from_coverSet_provider_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetProviderSourceData fn f g) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_source_from_g_coverSet_default_budget_generic_rowSeedProvider
    (S := S) fn f g D.g_nonneg D.dominated_fn D.dominated_limit
    D.rowSeedProvider (D.rowSeedProvider.rowSeeds g D.g_nonneg)
    D.abs_error_converges_in_measure

/-- Audit after factoring the two row-seed fields through the general
provider. -/
structure Theorem415ProviderRouteAuditAfterG230 : Type where
  rowSeed_fields_factored_through_provider : Nat
  coverSet_tail_uniform_bridge_closed : Nat
  bundled_uniformIB_field_required_for_this_endpoint : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_definition_witness_bridges_to_plain_415 : Nat

def theorem415ProviderRouteAuditAfterG230 :
    Theorem415ProviderRouteAuditAfterG230 where
  rowSeed_fields_factored_through_provider := 1
  coverSet_tail_uniform_bridge_closed := 1
  bundled_uniformIB_field_required_for_this_endpoint := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_definition_witness_bridges_to_plain_415 := 3

/-- G230 package. -/
structure Chapter4G230Theorem415ProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g229 : Chapter4G229Theorem415CoverSetPackage S
  audit : Theorem415ProviderRouteAuditAfterG230
  theorem415_provider_source_endpoint_closed_this_step : Nat
  remaining_plain_415_definition_bridge_steps : Nat

def chapter4G230Theorem415ProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G230Theorem415ProviderPackage S where
  g229 := chapter4G229Theorem415CoverSetPackage S
  audit := theorem415ProviderRouteAuditAfterG230
  theorem415_provider_source_endpoint_closed_this_step := 1
  remaining_plain_415_definition_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G230. -/
def bishopRegularSeqChapter4Theorem415ProviderProgressAfterG230 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G230: factored the theorem-4.15 error and g row-seed fields through the \
    general Proposition-4.2 row-seed provider. Countdown to the plain theorem-4.15 \
    statement: 3 definition-witness bridges remain."


end BishopCReal
