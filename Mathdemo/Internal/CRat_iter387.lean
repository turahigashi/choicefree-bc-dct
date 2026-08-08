import Mathdemo.Internal.CRat_iter386

set_option linter.style.longLine false

/-!
# G288: local strengthened `IntegrableSet1` API for Definition 2.3 data

G287 still consumed the global compatibility surface
`IntegrableSet1Def23Surface`.  Source Definition 2.3 says more locally: an
integrable complemented set is carried by its own characteristic-function
representative, defined on `A.S1 union A.S2` and equal to `1` on `A.S1`, `0`
on `A.S2`.

This node introduces the local strengthened API that the later broad refactor
should migrate into `IntegrableSet1` itself.  The theorem-4.15 consistency
bridge can now be stated from one strengthened integrable set `C`, rather than
from a global external surface for all current `IntegrableSet1` values.

This is a staging step, not a claim that all Chapter-2 constructors have already
been migrated to the strengthened API.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Local Definition-2.3 strengthened integrable set -/

/-- A current `IntegrableSet1` bundled with the local Definition-2.3 witnesses
that the characteristic representative is defined, with absolute convergence,
on each side of the complemented set.

The `base` field is the existing API; the remaining fields are the proposed
future fields of `IntegrableSet1` itself. -/
structure IntegrableSet1WithDef23
    (S : IntSpaceRC X R) (A : BSet X) : Type _ where
  base : IntegrableSet1 S A
  dom_on_s1 :
    forall x : X, x ∈ A.S1 ->
      forall m : Nat, x ∈ (base.rep.fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ A.S2 ->
      forall m : Nat, x ∈ (base.rep.fn m).dom
  abs_on_s1 :
    forall x : X, x ∈ A.S1 ->
      RSeq.SeriesSum (fun m => COF.abs (((base.rep.fn m).toFun x)))
  abs_on_s2 :
    forall x : X, x ∈ A.S2 ->
      RSeq.SeriesSum (fun m => COF.abs (((base.rep.fn m).toFun x)))


namespace IntegrableSet1WithDef23

/-- The local strengthened API projects to the older Definition-2.3 data record
for its own base set. -/
def toDef23Data
    {A : BSet X} (H : IntegrableSet1WithDef23 (S := S) A) :
    IntegrableSet1Def23Data (S := S) A H.base where
  dom_on_s1 := H.dom_on_s1
  dom_on_s2 := H.dom_on_s2
  abs_on_s1 := H.abs_on_s1
  abs_on_s2 := H.abs_on_s2


end IntegrableSet1WithDef23

/-! ## 2. Product-local witnesses from one strengthened set -/

/-- Positive-side product-local witness using the local strengthened
Definition-2.3 data of `A`, instead of a global surface. -/
noncomputable def Sec4Prop42ProductLocalWitness.ofWithDef23S1
    {A : BSet X} (H : IntegrableSet1WithDef23 (S := S) A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A H.base f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A H.base f hnn).fn m).toFun x))) :
    Sec4Prop42ProductLocalWitness (S := S) A H.base f hnn x where
  chi_dom := H.dom_on_s1 x hxA
  chi_abs := H.abs_on_s1 x hxA
  f_dom := hf_dom
  f_abs := hf_abs
  prod_dom := hprod_dom
  prod_abs := hprod_abs


/-- Negative-side product-local witness using the local strengthened
Definition-2.3 data of `A`, instead of a global surface. -/
noncomputable def Sec4Prop42ProductLocalWitness.ofWithDef23S2
    {A : BSet X} (H : IntegrableSet1WithDef23 (S := S) A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A H.base f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A H.base f hnn).fn m).toFun x))) :
    Sec4Prop42ProductLocalWitness (S := S) A H.base f hnn x where
  chi_dom := H.dom_on_s2 x hxA
  chi_abs := H.abs_on_s2 x hxA
  f_dom := hf_dom
  f_abs := hf_abs
  prod_dom := hprod_dom
  prod_abs := hprod_abs


/-! ## 3. Product value identification from one strengthened set -/

/-- Product value on the positive side from the local strengthened
Definition-2.3 API. -/
theorem sec4_prop42ProductValueOnS1_of_withDef23ProductWitness
    {A : BSet X} (H : IntegrableSet1WithDef23 (S := S) A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A H.base f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A H.base f hnn).fn m).toFun x))) :
    (seriesSum_of_abs hprod_abs).sum = (seriesSum_of_abs hf_abs).sum := by
  let hchi_abs : RSeq.SeriesSum
      (fun m => COF.abs ((H.base.rep.fn m).toFun x)) :=
    H.abs_on_s1 x hxA
  have hval :
      (seriesSum_of_abs hprod_abs).sum =
        (seriesSum_of_abs hchi_abs).sum * (seriesSum_of_abs hf_abs).sum :=
    prop_4_2_chi_f_rep_value A H.base f hnn hprod_abs hchi_abs hf_abs
  have hchi_one :
      (seriesSum_of_abs hchi_abs).sum = (1 : R) :=
    (H.base.valid x hchi_abs).2.1 hxA (seriesSum_of_abs hchi_abs)
  rw [hval, hchi_one]
  ring


/-- Product value on the negative side from the local strengthened
Definition-2.3 API. -/
theorem sec4_prop42ProductValueOnS2_of_withDef23ProductWitness
    {A : BSet X} (H : IntegrableSet1WithDef23 (S := S) A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (hf_dom : forall m : Nat, x ∈ (f.fn m).dom)
    (hf_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x)))
    (hprod_dom :
      forall m : Nat, x ∈ ((prop_4_2_chi_f_rep A H.base f hnn).fn m).dom)
    (hprod_abs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A H.base f hnn).fn m).toFun x))) :
    (seriesSum_of_abs hprod_abs).sum = (0 : R) := by
  let hchi_abs : RSeq.SeriesSum
      (fun m => COF.abs ((H.base.rep.fn m).toFun x)) :=
    H.abs_on_s2 x hxA
  have hval :
      (seriesSum_of_abs hprod_abs).sum =
        (seriesSum_of_abs hchi_abs).sum * (seriesSum_of_abs hf_abs).sum :=
    prop_4_2_chi_f_rep_value A H.base f hnn hprod_abs hchi_abs hf_abs
  have hchi_zero :
      (seriesSum_of_abs hchi_abs).sum = (0 : R) :=
    (H.base.valid x hchi_abs).2.2 hxA (seriesSum_of_abs hchi_abs)
  rw [hval, hchi_zero]
  ring


/-! ## 4. 4.15 consistency comparison from one strengthened set -/

/-- Pointwise equality between the direct measurable representative and the
previous `prop_4_2` relative representative, with the characteristic data read from
one strengthened integrable set rather than from a global surface. -/
theorem sec4_genIB_value_eq_relRep_on_support_of_localBridge_withDef23ProductWitness
    (C : BSet X) (H : IntegrableSet1WithDef23 (S := S) C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge
      (S := S) C (isMeasurableSet_of_integrable H.base) f hnn) :
    ∀ x ∈ Sec4ConsistencySupport (S := S) C H.base f hnn,
      ∀ (hgen : RSeq.SeriesSum
        (fun n => ((genIB_rep_from_measurable C
          (isMeasurableSet_of_integrable H.base) f hnn).fn n).toFun x))
        (hrel : RSeq.SeriesSum
        (fun n => ((prop_4_2_chi_f_rep C H.base f hnn).fn n).toFun x)),
        hgen.sum = hrel.sum := by
  intro x hx hgen hrel
  rcases hx with ⟨⟨⟨hgenDom, hrelDom⟩, hχDom⟩, hfDom⟩
  rcases hgenDom.2 with ⟨hgenabs⟩
  rcases hrelDom.2 with ⟨hrelabs⟩
  rcases hχDom.2 with ⟨hχabs⟩
  rcases hfDom.2 with ⟨hfabs⟩
  let Wgen : Sec4GenIBLocalWitness
      (S := S) C (isMeasurableSet_of_integrable H.base) f hnn x := {
    gen_dom := hgenDom.1
    gen_abs := hgenabs
    f_dom := hfDom.1
    f_abs := hfabs
  }
  have hχvalid := H.base.valid x hχabs
  cases hχvalid.1 with
  | inl hxC1 =>
      let Wprod : Sec4Prop42ProductLocalWitness (S := S) C H.base f hnn x :=
        Sec4Prop42ProductLocalWitness.ofWithDef23S1
          (S := S) H hnn hxC1 hfDom.1 hfabs hrelDom.1 hrelabs
      have hgen_value :
          (Sec4GenIBLocalWitness.genSigned (S := S) Wgen).sum =
            (Sec4GenIBLocalWitness.fSigned (S := S) Wgen).sum :=
        V.value_s1 x hxC1 Wgen
      have hrel_value :
          (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod).sum =
            (Sec4Prop42ProductLocalWitness.fSigned (S := S) Wprod).sum :=
        sec4_prop42ProductValueOnS1_of_withDef23ProductWitness
          (S := S) H hnn hxC1 hfDom.1 hfabs hrelDom.1 hrelabs
      calc
        hgen.sum = (Sec4GenIBLocalWitness.genSigned (S := S) Wgen).sum :=
          seriesSum_unique hgen
            (Sec4GenIBLocalWitness.genSigned (S := S) Wgen)
        _ = (Sec4GenIBLocalWitness.fSigned (S := S) Wgen).sum :=
          hgen_value
        _ = (Sec4Prop42ProductLocalWitness.fSigned (S := S) Wprod).sum := rfl
        _ = (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod).sum :=
          hrel_value.symm
        _ = hrel.sum :=
          (seriesSum_unique hrel
            (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod)).symm
  | inr hxC2 =>
      let Wprod : Sec4Prop42ProductLocalWitness (S := S) C H.base f hnn x :=
        Sec4Prop42ProductLocalWitness.ofWithDef23S2
          (S := S) H hnn hxC2 hfDom.1 hfabs hrelDom.1 hrelabs
      have hgen_value :
          (Sec4GenIBLocalWitness.genSigned (S := S) Wgen).sum = (0 : R) :=
        V.value_s2 x hxC2 Wgen
      have hrel_value :
          (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod).sum =
            (0 : R) :=
        sec4_prop42ProductValueOnS2_of_withDef23ProductWitness
          (S := S) H hnn hxC2 hfDom.1 hfabs hrelDom.1 hrelabs
      calc
        hgen.sum = (Sec4GenIBLocalWitness.genSigned (S := S) Wgen).sum :=
          seriesSum_unique hgen
            (Sec4GenIBLocalWitness.genSigned (S := S) Wgen)
        _ = 0 := hgen_value
        _ = (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod).sum :=
          hrel_value.symm
        _ = hrel.sum :=
          (seriesSum_unique hrel
            (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod)).symm


/-- Consistency with the previous relative integral, using only the local
strengthened Definition-2.3 data of the set `C`. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_localValueBridge_withDef23ProductWitness
    (C : BSet X) (H : IntegrableSet1WithDef23 (S := S) C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge
      (S := S) C (isMeasurableSet_of_integrable H.base) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable H.base) f hnn =
      relIntegral C H.base f hnn := by
  unfold genRelIntegral_from_measurable relIntegral
  exact cor_1_12
    (sec4ConsistencySupport_full C H.base f hnn)
    (genIB_rep_from_measurable C (isMeasurableSet_of_integrable H.base) f hnn)
    (prop_4_2_chi_f_rep C H.base f hnn)
    (sec4_genIB_value_eq_relRep_on_support_of_localBridge_withDef23ProductWitness
      (S := S) C H f hnn V)


/-- Packaged consistency bridge from one locally strengthened integrable set. -/
noncomputable def sec4_genIBConsistencyBridge_of_localValueBridge_withDef23ProductWitness
    (C : BSet X) (H : IntegrableSet1WithDef23 (S := S) C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge
      (S := S) C (isMeasurableSet_of_integrable H.base) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C H.base f hnn := {
  integral_eq :=
    sec4_genRelIntegral_eq_relIntegral_of_localValueBridge_withDef23ProductWitness
      (S := S) C H f hnn V
}


/-! ## 5. Audit -/

structure Sec4Theorem415WithDef23LocalAPIAuditAfterG288 : Type where
  local_strengthened_integrable_set_api_introduced : Nat
  global_def23_surface_required_for_consistency_bridge : Nat
  local_def23_fields_used_for_characteristic_rep : Nat
  product_rep_definition16_witness_used : Nat
  chapter2_constructors_migrated_to_strengthened_api : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_constructor_migration_steps : Nat

def sec4Theorem415WithDef23LocalAPIAuditAfterG288 :
    Sec4Theorem415WithDef23LocalAPIAuditAfterG288 where
  local_strengthened_integrable_set_api_introduced := 1
  global_def23_surface_required_for_consistency_bridge := 0
  local_def23_fields_used_for_characteristic_rep := 1
  product_rep_definition16_witness_used := 1
  chapter2_constructors_migrated_to_strengthened_api := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_constructor_migration_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G288WithDef23LocalAPIPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g287 : Chapter4G287ProductWitnessBridgePackage S
  audit : BishopC.Sec4Theorem415WithDef23LocalAPIAuditAfterG288
  local_strengthened_integrable_set_api_added_this_step : Nat
  remaining_constructor_migration_steps : Nat

def chapter4G288WithDef23LocalAPIPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G288WithDef23LocalAPIPackage S where
  g287 := chapter4G287ProductWitnessBridgePackage S
  audit := BishopC.sec4Theorem415WithDef23LocalAPIAuditAfterG288
  local_strengthened_integrable_set_api_added_this_step := 1
  remaining_constructor_migration_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G288. -/
def bishopRegularSeqChapter4WithDef23LocalAPIProgressAfterG288 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G288: introduced a local strengthened IntegrableSet1 API carrying the \
    Definition-2.3 characteristic-domain fields and restated the 4.15 \
    consistency bridge from one strengthened set rather than a global \
    IntegrableSet1Def23Surface.  This is the staged start of the global \
    refactor; Chapter-2 constructors still need migration."


end BishopCReal
