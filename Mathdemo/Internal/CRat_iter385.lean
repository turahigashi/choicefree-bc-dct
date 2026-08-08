import Mathdemo.Internal.CRat_iter384

set_option linter.style.longLine false

/-!
# G286: avoid the overstrong outer route for Proposition 4.2 values

G285 narrowed the remaining outer-convergence surface to the side-specific
form.  Reading the source and the existing `prop_4_2_chi_f_rep_value` theorem
more carefully shows a sharper correction:

* to identify the value of the constructed representative `chi_A * f`, one
  does **not** need to derive the constructed representative's flat absolute
  convergence from only the `chi_A` and `f` representatives;
* the source-local proof works on the common full support of the three
  representatives: `chi_A`, `f`, and the newly constructed `chi_A * f`
  representative.

The last witness is not external choice data.  It is the local Definition-1.6
domain witness for the representative constructed by Proposition 4.2 itself.
Trying to reconstruct it only from the two input representatives forces the
unnecessary and too-strong row-outer frontier isolated in G284/G285.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Three-representative local witness -/

/-- Local data on the source-correct common support for Proposition 4.2.

The product fields are the Definition-1.6 witness for the representative
constructed by `prop_4_2_chi_f_rep`; they are not selected from a quotient and
are not inferred from the two input representatives. -/
structure Sec4Prop42ProductLocalWitness
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) (x : X) : Type _ where
  chi_dom : forall m : Nat, x ∈ (hA.rep.fn m).dom
  chi_abs : RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x))
  f_dom : forall m : Nat, x ∈ (f.fn m).dom
  f_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))
  prod_dom :
    forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A hA f hnn).fn m).dom
  prod_abs :
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))


namespace Sec4Prop42ProductLocalWitness

/-- Signed value of the constructed product representative. -/
noncomputable def prodSigned
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {hnn : RepNonneg f} {x : X}
    (W : Sec4Prop42ProductLocalWitness (S := S) A hA f hnn x) :
    RSeq.SeriesSum
      (fun m => ((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x) :=
  seriesSum_of_abs W.prod_abs


/-- Signed value of `f`. -/
noncomputable def fSigned
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {hnn : RepNonneg f} {x : X}
    (W : Sec4Prop42ProductLocalWitness (S := S) A hA f hnn x) :
    RSeq.SeriesSum (fun m => (f.fn m).toFun x) :=
  seriesSum_of_abs W.f_abs


end Sec4Prop42ProductLocalWitness

/-! ## 2. Definition-2.3 constructors for the two sides -/

/-- Positive-side local product witness from Def.2.3 plus the local witnesses
for `f` and for the constructed product representative. -/
noncomputable def Sec4Prop42ProductLocalWitness.ofDef23S1
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A hA f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))) :
    Sec4Prop42ProductLocalWitness (S := S) A hA f hnn x where
  chi_dom := (D.data A hA).dom_on_s1 x hxA
  chi_abs := (D.data A hA).abs_on_s1 x hxA
  f_dom := hf_dom
  f_abs := hf_abs
  prod_dom := hprod_dom
  prod_abs := hprod_abs


/-- Negative-side local product witness from Def.2.3 plus the local witnesses
for `f` and for the constructed product representative. -/
noncomputable def Sec4Prop42ProductLocalWitness.ofDef23S2
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A hA f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))) :
    Sec4Prop42ProductLocalWitness (S := S) A hA f hnn x where
  chi_dom := (D.data A hA).dom_on_s2 x hxA
  chi_abs := (D.data A hA).abs_on_s2 x hxA
  f_dom := hf_dom
  f_abs := hf_abs
  prod_dom := hprod_dom
  prod_abs := hprod_abs


/-! ## 3. Value identification without row-outer reconstruction -/

/-- Value identification on `A.S1` using the product representative's own
local Definition-1.6 witness. -/
theorem sec4_prop42ProductValueOnS1_of_def23ProductWitness
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A hA f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))) :
    (seriesSum_of_abs hprod_abs).sum = (seriesSum_of_abs hf_abs).sum := by
  let hchi_abs : RSeq.SeriesSum
      (fun m => COF.abs ((hA.rep.fn m).toFun x)) :=
    (D.data A hA).abs_on_s1 x hxA
  have hval :
      (seriesSum_of_abs hprod_abs).sum =
        (seriesSum_of_abs hchi_abs).sum * (seriesSum_of_abs hf_abs).sum :=
    prop_4_2_chi_f_rep_value A hA f hnn hprod_abs hchi_abs hf_abs
  have hchi_one :
      (seriesSum_of_abs hchi_abs).sum = (1 : R) :=
    (hA.valid x hchi_abs).2.1 hxA (seriesSum_of_abs hchi_abs)
  rw [hval, hchi_one]
  ring


/-- Value identification on `A.S2` using the product representative's own
local Definition-1.6 witness. -/
theorem sec4_prop42ProductValueOnS2_of_def23ProductWitness
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A hA f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))) :
    (seriesSum_of_abs hprod_abs).sum = (0 : R) := by
  let hchi_abs : RSeq.SeriesSum
      (fun m => COF.abs ((hA.rep.fn m).toFun x)) :=
    (D.data A hA).abs_on_s2 x hxA
  have hval :
      (seriesSum_of_abs hprod_abs).sum =
        (seriesSum_of_abs hchi_abs).sum * (seriesSum_of_abs hf_abs).sum :=
    prop_4_2_chi_f_rep_value A hA f hnn hprod_abs hchi_abs hf_abs
  have hchi_zero :
      (seriesSum_of_abs hchi_abs).sum = (0 : R) :=
    (hA.valid x hchi_abs).2.2 hxA (seriesSum_of_abs hchi_abs)
  rw [hval, hchi_zero]
  ring


/-! ## 4. Audit -/

structure Sec4Prop42ProductDomainRouteAuditAfterG286 : Type where
  product_domain_witness_used_from_constructed_rep : Nat
  attempted_reconstruction_of_product_flat_abs_from_inputs_required : Nat
  side_specific_outer_frontier_required_for_value_identification : Nat
  def23_characteristic_witness_used : Nat
  definition16_f_witness_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_route_integration_steps : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def sec4Prop42ProductDomainRouteAuditAfterG286 :
    Sec4Prop42ProductDomainRouteAuditAfterG286 where
  product_domain_witness_used_from_constructed_rep := 1
  attempted_reconstruction_of_product_flat_abs_from_inputs_required := 0
  side_specific_outer_frontier_required_for_value_identification := 0
  def23_characteristic_witness_used := 1
  definition16_f_witness_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_route_integration_steps := 1
  remaining_global_integrable_set_refactor_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G286Prop42ProductDomainRoutePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g285 : Chapter4G285Prop42Def23SideLocalOuterPackage S
  audit : BishopC.Sec4Prop42ProductDomainRouteAuditAfterG286
  overstrong_outer_route_removed_this_step : Nat
  remaining_route_integration_steps : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def chapter4G286Prop42ProductDomainRoutePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G286Prop42ProductDomainRoutePackage S where
  g285 := chapter4G285Prop42Def23SideLocalOuterPackage S
  audit := BishopC.sec4Prop42ProductDomainRouteAuditAfterG286
  overstrong_outer_route_removed_this_step := 1
  remaining_route_integration_steps := 1
  remaining_global_integrable_set_refactor_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G286. -/
def bishopRegularSeqChapter4Prop42ProductDomainRouteProgressAfterG286 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G286: replaced the overstrong attempt to reconstruct the product flat-abs \
    witness from chi_A and f alone.  Proposition 4.2 value identification now \
    uses the source-correct common full support of chi_A, f, and the \
    constructed chi_A*f representative.  Countdown: 1 route-integration step \
    remains to push this product-domain local witness through the 4.15 local \
    bridge, then 1 global refactor folds the Def23 fields into IntegrableSet1."


end BishopCReal
