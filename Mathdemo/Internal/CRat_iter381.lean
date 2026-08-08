import Mathdemo.Internal.CRat_iter380
import Mathdemo.Internal.CRat_iter370

set_option linter.style.longLine false

/-!
# G282: use Definition-2.3 data on the source-shaped standard-row route

G281 moved the characteristic-function absolute-convergence witness back to a
Definition-2.3 compatibility surface, but it did so on the older row-seed
residual route.  That route still bundled the remaining Proposition-4.2
obligations as two coarse fields.

This node combines G281 with the already existing G271 standard-row route.
The public theorem-4.15 statement now uses:

* Definition-2.3 characteristic-function domain data;
* the standard positive-side outer convergence for the Proposition-4.2 rows;
* the standard negative-side rows;
* the standard negative-side outer convergence for those rows.

Thus the direct `charDomain` input is no longer public on the source-shaped
standard-row path either.  The remaining frontier is no longer a vague
row-seed package; it is the three standard row/outer facts that belong to the
Proposition-4.2 proof.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Source-shaped standard-row provider over Definition 2.3 -/

/-- The source-shaped Proposition-4.2 provider after replacing the public
characteristic-domain witness by Definition-2.3 integrable-set data. -/
structure Sec4GeneralIBDef23S2StandardOuterProvider : Type _ where
  def23 : IntegrableSet1Def23Surface (S := S)
  standard_outer_on_s1 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42StandardAbsOuterOnS1OfFAbs
      (S := S)
      (Sec4Prop42CharacteristicDomainWitness.ofDef23Surface
        (S := S) def23)
      f hnn
  rows_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42RowsOnS2 (S := S) f hnn
  standard_outer_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4LambdaRowsAbsOuterOnS2ForRows (S := S)
      (rows_on_s2 f hnn)


/-- Forget the Definition-2.3 presentation by projecting the older
characteristic-domain witness, while filling the generic row-to-flat bridge
internally. -/
noncomputable def Sec4GeneralIBDef23S2StandardOuterProvider.toSourceS2StandardOuterProvider
    (P : Sec4GeneralIBDef23S2StandardOuterProvider (S := S)) :
    Sec4GeneralIBSourceS2StandardOuterProvider (S := S) where
  rowToFlat := sec4_rowToFlat_source (S := S)
  charDomain :=
    Sec4Prop42CharacteristicDomainWitness.ofDef23Surface
      (S := S) P.def23
  standard_outer_on_s1 := P.standard_outer_on_s1
  rows_on_s2 := P.rows_on_s2
  standard_outer_on_s2 := P.standard_outer_on_s2


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 2. Theorem 4.15 from Definition-2.3 standard-row data -/

structure Theorem415SourceFacingDef23GlobalStandardRowsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  def23 : BishopC.IntegrableSet1Def23Surface (S := S)
  standard_outer_on_s1 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4Prop42StandardAbsOuterOnS1OfFAbs
        (S := S)
        (BishopC.Sec4Prop42CharacteristicDomainWitness.ofDef23Surface
          (S := S) def23)
        u unn
  rows_on_s2 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4Prop42RowsOnS2 (S := S) u unn
  standard_outer_on_s2 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4LambdaRowsAbsOuterOnS2ForRows (S := S)
        (rows_on_s2 u unn)

noncomputable def theorem415_globalStandardRows_statement_data_of_def23GlobalStandardRows
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingDef23GlobalStandardRowsStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGlobalStandardRowsStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  charDomain :=
    BishopC.Sec4Prop42CharacteristicDomainWitness.ofDef23Surface
      (S := S) D.def23
  standard_outer_on_s1 := D.standard_outer_on_s1
  rows_on_s2 := D.rows_on_s2
  standard_outer_on_s2 := D.standard_outer_on_s2

/-- Theorem 4.15 on the local full-set path, with the characteristic-domain
field discharged by Definition 2.3 and the remaining obligations stated as
standard Proposition-4.2 row facts. -/
noncomputable def
    theorem415_integral_convergence_from_def23GlobalStandardRows_via_local_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingDef23GlobalStandardRowsStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_globalStandardRows_via_local_statement_data
    (S := S)
    (theorem415_globalStandardRows_statement_data_of_def23GlobalStandardRows
      (S := S) D)

/-! ## 3. Audit and package -/

structure Theorem415Def23GlobalStandardRowsRouteAuditAfterG282 : Type where
  local_full_set_theorem_path_used : Nat
  def23_surface_public_input_required : Nat
  direct_characteristic_domain_witness_public_input_required : Nat
  characteristic_domain_witness_closed_by_def23_surface : Nat
  row_seed_residual_provider_public_input_required : Nat
  bundled_pack_on_s2_public_input_required : Nat
  arbitrary_positive_row_outer_public_input_required : Nat
  standard_positive_row_outer_required : Nat
  standard_negative_rows_required : Nat
  standard_negative_row_outer_required : Nat
  row_to_flat_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_shaped_standard_row_components : Nat
  remaining_global_refactor_steps_after_chapter4_route : Nat

def theorem415Def23GlobalStandardRowsRouteAuditAfterG282 :
    Theorem415Def23GlobalStandardRowsRouteAuditAfterG282 where
  local_full_set_theorem_path_used := 1
  def23_surface_public_input_required := 1
  direct_characteristic_domain_witness_public_input_required := 0
  characteristic_domain_witness_closed_by_def23_surface := 1
  row_seed_residual_provider_public_input_required := 0
  bundled_pack_on_s2_public_input_required := 0
  arbitrary_positive_row_outer_public_input_required := 0
  standard_positive_row_outer_required := 1
  standard_negative_rows_required := 1
  standard_negative_row_outer_required := 1
  row_to_flat_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_shaped_standard_row_components := 3
  remaining_global_refactor_steps_after_chapter4_route := 1

structure Chapter4G282Theorem415Def23GlobalStandardRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g281 : Chapter4G281Theorem415Def23ResidualPackage S
  g271 : Chapter4G271Theorem415GlobalStandardRowsLocalPackage S
  audit : Theorem415Def23GlobalStandardRowsRouteAuditAfterG282
  characteristic_domain_field_closed_on_standard_row_route_this_step : Nat
  remaining_source_shaped_standard_row_components : Nat
  remaining_global_refactor_steps_after_chapter4_route : Nat

def chapter4G282Theorem415Def23GlobalStandardRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G282Theorem415Def23GlobalStandardRowsPackage S where
  g281 := chapter4G281Theorem415Def23ResidualPackage S
  g271 := chapter4G271Theorem415GlobalStandardRowsLocalPackage S
  audit := theorem415Def23GlobalStandardRowsRouteAuditAfterG282
  characteristic_domain_field_closed_on_standard_row_route_this_step := 1
  remaining_source_shaped_standard_row_components := 3
  remaining_global_refactor_steps_after_chapter4_route := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G282. -/
def bishopRegularSeqChapter4Theorem415Def23GlobalStandardRowsProgressAfterG282 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G282: moved the theorem-4.15 source-shaped standard-row route through \
    Definition-2.3 data. The public charDomain input is closed by the \
    integrable-set surface; the remaining Chapter-4 route frontier is now the \
    three standard Proposition-4.2 facts: S1 standard outer convergence, S2 \
    standard rows, and S2 standard outer convergence. Countdown: 3 standard \
    row facts, then 1 global refactor moving the Def23 surface into the \
    IntegrableSet1 constructors."


end BishopCReal
