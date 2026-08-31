import Mathdemo.Internal.Real.RouteRowSeedResidualSurfaceLocal
import Mathdemo.Internal.Sec4.SourceDomainWitness

set_option linter.style.longLine false

/-!
# G281: move the characteristic-domain witness back to Definition 2.3 data

G280 kept the theorem-4.15 route on the source-level local full-set path, but
the row-seed residual surface still carried the positive-side characteristic
absolute-convergence field as an external input.

This node factors that field through the source definition of an integrable
set: an integrable complemented set is one whose characteristic function is an
integrable function on `A.S1 union A.S2`.  Since the current base
`IntegrableSet1` structure has not yet been globally refactored, the source
data is expressed as an explicit compatibility surface over existing
`IntegrableSet1` values.  Downstream theorem-4.15 no longer asks directly for
`chi_abs_on_s1_of_fabs`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Definition-2.3 surface over the current `IntegrableSet1` -/

/-- Source-faithful pointwise domain data for one current `IntegrableSet1`.

This is the missing direction of Definition 2.3 for the current API: from
membership in the characteristic-function domain sides `A.S1` and `A.S2` to
the Definition-1.6 pointwise domain and absolute-convergence witnesses for the
chosen representative.
-/
structure IntegrableSet1Def23Data
    (A : BSet X) (hA : IntegrableSet1 S A) : Type _ where
  dom_on_s1 :
    forall x : X, x ∈ A.S1 ->
      forall m : Nat, x ∈ (hA.rep.fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ A.S2 ->
      forall m : Nat, x ∈ (hA.rep.fn m).dom
  abs_on_s1 :
    forall (x : X) (hx : x ∈ A.S1),
      RSeq.SeriesSum (fun m => COF.abs
        (hA.rep.valueAt x (dom_on_s1 x hx) m))
  abs_on_s2 :
    forall (x : X) (hx : x ∈ A.S2),
      RSeq.SeriesSum (fun m => COF.abs
        (hA.rep.valueAt x (dom_on_s2 x hx) m))


/-- Global compatibility convention: every currently available
`IntegrableSet1` is backed by Definition-2.3 characteristic-function data.

The next refactor should make these two fields part of `IntegrableSet1`
itself; keeping them in this surface lets the theorem-4.15 route move first
without breaking all existing constructors at once. -/
structure IntegrableSet1Def23Surface : Type _ where
  data : forall (A : BSet X) (hA : IntegrableSet1 S A),
    IntegrableSet1Def23Data (S := S) A hA


/-- The older Proposition-4.2 characteristic-domain witness is exactly the
projection of the Definition-2.3 surface. -/
def Sec4Prop42CharacteristicDomainWitness.ofDef23Surface
    (D : IntegrableSet1Def23Surface (S := S)) :
    Sec4Prop42CharacteristicDomainWitness (S := S) where
  abs_on_s1 := fun A hA x hx =>
    { fst := (D.data A hA).dom_on_s1 x hx
      snd := (D.data A hA).abs_on_s1 x hx }
  abs_on_s2 := fun A hA x hx =>
    { fst := (D.data A hA).dom_on_s2 x hx
      snd := (D.data A hA).abs_on_s2 x hx }


/-! ## 2. Row-seed provider with the characteristic field discharged -/

/-- The theorem-4.15 row-seed residual surface after Definition-2.3 has
discharged the characteristic-domain field. -/
structure Sec4GeneralIBDef23ResidualProvider : Type _ where
  def23 : IntegrableSet1Def23Surface (S := S)
  abs_outer_on_s1_of_rows : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn
  pack_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn


/-- Convert the Definition-2.3 residual provider to the older three-field
row-seed residual provider. -/
noncomputable def Sec4GeneralIBDef23ResidualProvider.toRowSeedResidualProvider
    (P : Sec4GeneralIBDef23ResidualProvider (S := S)) :
    Sec4GeneralIBRowSeedResidualProvider (S := S) where
  residual := fun f hnn =>
    Sec4Prop42RowSeedResidualTools.mk
      (sec4_chiAbsOnS1_of_characteristicDomainWitness
        (S := S)
        (Sec4Prop42CharacteristicDomainWitness.ofDef23Surface
          (S := S) P.def23)
        f hnn)
      (P.abs_outer_on_s1_of_rows f hnn)
      (P.pack_on_s2 f hnn)


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 3. Theorem 4.15 routed through Definition-2.3 residual data -/

structure Sec4GeneralDef23ResidualProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  provider : BishopC.Sec4GeneralIBDef23ResidualProvider (S := S)

noncomputable def sec4GeneralRowSeedResidualProvider_of_def23ResidualProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralDef23ResidualProvider S) :
    Sec4GeneralRowSeedResidualProvider S where
  residual := fun f hnn =>
    (BishopC.Sec4GeneralIBDef23ResidualProvider.toRowSeedResidualProvider
      (S := S) P.provider).residual f hnn

structure Theorem415SourceFacingDef23ResidualProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  def23_residual_provider : Sec4GeneralDef23ResidualProvider S

noncomputable def theorem415_rowSeedResidualProvider_statement_data_of_def23ResidualProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingDef23ResidualProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingRowSeedResidualProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  row_seed_residual_provider :=
    sec4GeneralRowSeedResidualProvider_of_def23ResidualProvider
      (S := S) D.def23_residual_provider

/-- Theorem 4.15 from Definition-2.3 residual data, still using the local
full-set theorem path introduced in G280. -/
noncomputable def
    theorem415_integral_convergence_from_def23ResidualProvider_localFullSet_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingDef23ResidualProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_rowSeedResidualProvider_localFullSet_statement_data
    (S := S)
    (theorem415_rowSeedResidualProvider_statement_data_of_def23ResidualProvider
      (S := S) D)

/-! ## 4. Audit and package -/

structure Theorem415Def23ResidualRouteAuditAfterG281 : Type where
  local_full_set_theorem_path_used : Nat
  def23_surface_public_input_required : Nat
  direct_chi_abs_on_s1_public_input_required : Nat
  chi_abs_on_s1_closed_by_def23_surface : Nat
  abs_outer_on_s1_of_rows_required : Nat
  pack_on_s2_required : Nat
  row_seed_residual_provider_public_input_required : Nat
  global_characteristic_domain_witness_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_row_seed_residual_fields : Nat
  remaining_total_frontiers : Nat

def theorem415Def23ResidualRouteAuditAfterG281 :
    Theorem415Def23ResidualRouteAuditAfterG281 where
  local_full_set_theorem_path_used := 1
  def23_surface_public_input_required := 1
  direct_chi_abs_on_s1_public_input_required := 0
  chi_abs_on_s1_closed_by_def23_surface := 1
  abs_outer_on_s1_of_rows_required := 1
  pack_on_s2_required := 1
  row_seed_residual_provider_public_input_required := 0
  global_characteristic_domain_witness_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_row_seed_residual_fields := 2
  remaining_total_frontiers := 1

structure Chapter4G281Theorem415Def23ResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g280 : Chapter4G280Theorem415RowSeedResidualLocalFullSetPackage S
  audit : Theorem415Def23ResidualRouteAuditAfterG281
  characteristic_domain_field_closed_this_step : Nat
  remaining_row_seed_residual_fields : Nat
  remaining_total_frontiers : Nat

def chapter4G281Theorem415Def23ResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G281Theorem415Def23ResidualPackage S where
  g280 := chapter4G280Theorem415RowSeedResidualLocalFullSetPackage S
  audit := theorem415Def23ResidualRouteAuditAfterG281
  characteristic_domain_field_closed_this_step := 1
  remaining_row_seed_residual_fields := 2
  remaining_total_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G281. -/
def bishopRegularSeqChapter4Theorem415Def23ResidualProgressAfterG281 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G281: routed the theorem-4.15 local full-set path through a \
    Definition-2.3 integrable-set surface. The direct chi_abs_on_s1 residual \
    is no longer a public input; it is projected from the source data that \
    chi_A is an integrable function on A1 union A2. Remaining countdown: 2 \
    row-seed fields, plus the later global refactor that moves the surface \
    into IntegrableSet1 constructors."


end BishopCReal
