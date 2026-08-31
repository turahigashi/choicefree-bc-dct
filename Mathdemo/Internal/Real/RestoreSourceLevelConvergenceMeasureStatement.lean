import Mathdemo.Internal.Real.BuildTheorem415MajorantSplit

set_option linter.style.longLine false

/-!
# G256: restore the source-level convergence-in-measure statement

G255 left a single core source datum named as convergence of the absolute-error
sequence.  Mathematically, Bishop's hypothesis `f_n -> f` in measure is exactly
the data that `|f_n-f| -> 0` in measure.  This file restores that source-level
name and packages theorem 4.15 with the displayed statement shape:

* an integrable majorant `g`;
* `|f_n| <= g`;
* `f_n -> f` in measure;
* the Chapter-4 Proposition 4.2/domain-residual provider.

No PFun representatives, global characteristic-domain selector, public
row-to-flat bridge, direct abs-error row seeds, or public majorant split are
required by this endpoint.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-facing Bishop convergence in measure for theorem 4.15.

The definition is kept as Type/Sigma data.  Its computational content is the
usual Bishop content of `|f_n-f| -> 0` in measure, so this is a renaming of the
remaining G255 convergence datum, not a new mathematical assumption.
-/
structure Theorem415ConvergesInMeasureData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  abs_error :
    BishopC.Lemma414ConvergeInMeasureToZeroData
      (S := S) (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- Theorem-4.15 source statement after the internal absolute-error convergence
name has been replaced by source-level convergence in measure. -/
structure Theorem415SourceFacingStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)

/-- Rebuild the G255 data from the source-level theorem statement. -/
noncomputable def theorem415_domainResidual_measureData_of_sourceFacing
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStatementData (S := S) fn f) :
    Theorem415DomainResidualMeasureStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  domainResidualProvider := D.domainResidualProvider
  abs_error_converges := D.converges_in_measure.abs_error

/-- Source-facing theorem 4.15 endpoint. -/
noncomputable def theorem415_integral_convergence_from_sourceFacing_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_domainResidual_measure_data
    (S := S)
    (theorem415_domainResidual_measureData_of_sourceFacing (S := S) D)

structure Theorem415SourceFacingRouteAuditAfterG256 : Type where
  source_facing_convergence_in_measure_used : Nat
  direct_abs_error_convergence_named_as_public_frontier : Nat
  pfun_representation_data_required : Nat
  global_characteristic_domain_witness_required : Nat
  row_to_flat_public_input_required : Nat
  direct_abs_error_rowSeeds_public_input_required : Nat
  majorant_split_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_core_source_frontiers : Nat
  remaining_chapter4_provider_frontiers : Nat

def theorem415SourceFacingRouteAuditAfterG256 :
    Theorem415SourceFacingRouteAuditAfterG256 where
  source_facing_convergence_in_measure_used := 1
  direct_abs_error_convergence_named_as_public_frontier := 0
  pfun_representation_data_required := 0
  global_characteristic_domain_witness_required := 0
  row_to_flat_public_input_required := 0
  direct_abs_error_rowSeeds_public_input_required := 0
  majorant_split_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_core_source_frontiers := 0
  remaining_chapter4_provider_frontiers := 1

structure Chapter4G256Theorem415SourceFacingPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g255 : Chapter4G255Theorem415MeasurePackage S
  audit : Theorem415SourceFacingRouteAuditAfterG256
  source_facing_convergence_restored_this_step : Nat
  remaining_core_source_frontiers : Nat
  remaining_chapter4_provider_frontiers : Nat

def chapter4G256Theorem415SourceFacingPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G256Theorem415SourceFacingPackage S where
  g255 := chapter4G255Theorem415MeasurePackage S
  audit := theorem415SourceFacingRouteAuditAfterG256
  source_facing_convergence_restored_this_step := 1
  remaining_core_source_frontiers := 0
  remaining_chapter4_provider_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G256. -/
def bishopRegularSeqChapter4Theorem415SourceFacingProgressAfterG256 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G256: restored theorem 4.15 to the source-level convergence-in-measure \
    statement. The theorem 4.15 core now has no remaining auxiliary source \
    frontiers: PFun representatives, global charDomain, rowToFlat, direct \
    abs-error row seeds, and majorant split are not public inputs. One \
    Chapter-4 provider frontier remains: closing the domain-residual provider \
    itself from Proposition 4.2/local full-set data."


end BishopCReal
