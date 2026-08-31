import Mathdemo.Internal.CRat_iter385

set_option linter.style.longLine false

/-!
# G287: route the product-domain witness through the 4.15 local bridge

G286 identified the source-correct local support for Proposition 4.2 values:
the characteristic representative, the original representative, and the
constructed product representative must all be read with their own local
Definition-1.6 witnesses.

This node pushes that correction into the theorem-4.15 consistency comparison.
The comparison no longer calls the product-representative value theorem as a
bare global fact; it first packages the local data from the common support as a
`Sec4Prop42ProductLocalWitness`, then reads the product value from that local
witness.  The remaining local bridge for the direct measurable representative
is unchanged.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Product-local value wrappers -/

/-- Product value on the positive side, phrased directly in terms of the
three-representative local witness. -/
theorem sec4_prop42ProductValueOnS1_of_productLocalWitness
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S1)
    (W : Sec4Prop42ProductLocalWitness (S := S) A hA f hnn x) :
    (Sec4Prop42ProductLocalWitness.prodSigned (S := S) W).sum =
      (Sec4Prop42ProductLocalWitness.fSigned (S := S) W).sum := by
  unfold Sec4Prop42ProductLocalWitness.prodSigned
  unfold Sec4Prop42ProductLocalWitness.fSigned
  exact sec4_prop42ProductValueOnS1_of_def23ProductWitness
    (S := S) D hA hnn hxA W.f_dom W.f_abs W.prod_dom W.prod_abs


/-- Product value on the zero side, phrased directly in terms of the
three-representative local witness. -/
theorem sec4_prop42ProductValueOnS2_of_productLocalWitness
    (D : IntegrableSet1Def23Surface (S := S))
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (hxA : x ∈ A.S2)
    (W : Sec4Prop42ProductLocalWitness (S := S) A hA f hnn x) :
    (Sec4Prop42ProductLocalWitness.prodSigned (S := S) W).sum = (0 : R) := by
  unfold Sec4Prop42ProductLocalWitness.prodSigned
  exact sec4_prop42ProductValueOnS2_of_def23ProductWitness
    (S := S) D hA hnn hxA W.f_dom W.f_abs W.prod_dom W.prod_abs


/-! ## 2. 4.15 consistency comparison through product-local witnesses -/

/-- Pointwise equality between the direct measurable representative and the
previous `prop_4_2` relative representative, with the `prop_4_2` side read through
the product-local witness from G286. -/
theorem sec4_genIB_value_eq_relRep_on_support_of_localBridge_productWitness
    (D : IntegrableSet1Def23Surface (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    ∀ x ∈ Sec4ConsistencySupport (S := S) C hC f hnn,
      ∀ (hgenDom : (genIB_rep_from_measurable C
          (isMeasurableSet_of_integrable hC) f hnn).MemAt x),
      ∀ (hrelDom : (prop_4_2_chi_f_rep C hC f hnn).MemAt x),
      ∀ (hgen : RSeq.SeriesSum
        (fun n => (genIB_rep_from_measurable C
          (isMeasurableSet_of_integrable hC) f hnn).valueAt x hgenDom n))
        (hrel : RSeq.SeriesSum
        (fun n => (prop_4_2_chi_f_rep C hC f hnn).valueAt
          x hrelDom n)),
        hgen.sum = hrel.sum := by
  intro x hx hgenDom hrelDom hgen hrel
  rcases hx with ⟨⟨⟨hgenAt, hrelAt⟩, hχAt⟩, hfAt⟩
  rcases hgenAt with ⟨hgenSupportDom, ⟨hgenabs⟩⟩
  rcases hrelAt with ⟨hrelSupportDom, ⟨hrelabs⟩⟩
  rcases hχAt with ⟨hχSupportDom, ⟨hχabs⟩⟩
  rcases hfAt with ⟨hfSupportDom, ⟨hfabs⟩⟩
  let Wgen : Sec4GenIBLocalWitness
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn x := {
    gen_dom := hgenSupportDom
    gen_abs := hgenabs
    f_dom := hfSupportDom
    f_abs := hfabs
  }
  have hχvalid := hC.valid x hχSupportDom hχabs
  cases hχvalid.1 with
  | inl hxC1 =>
      let Wprod : Sec4Prop42ProductLocalWitness (S := S) C hC f hnn x :=
        Sec4Prop42ProductLocalWitness.ofDef23S1
          (S := S) D hC hnn hxC1 hfSupportDom hfabs
            hrelSupportDom hrelabs
      have hgen_value :
          (Sec4GenIBLocalWitness.genSigned (S := S) Wgen).sum =
            (Sec4GenIBLocalWitness.fSigned (S := S) Wgen).sum :=
        V.value_s1 x hxC1 Wgen
      have hrel_value :
          (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod).sum =
            (Sec4Prop42ProductLocalWitness.fSigned (S := S) Wprod).sum :=
        sec4_prop42ProductValueOnS1_of_productLocalWitness
          (S := S) D hC hnn hxC1 Wprod
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
      let Wprod : Sec4Prop42ProductLocalWitness (S := S) C hC f hnn x :=
        Sec4Prop42ProductLocalWitness.ofDef23S2
          (S := S) D hC hnn hxC2 hfSupportDom hfabs
            hrelSupportDom hrelabs
      have hgen_value :
          (Sec4GenIBLocalWitness.genSigned (S := S) Wgen).sum = (0 : R) :=
        V.value_s2 x hxC2 Wgen
      have hrel_value :
          (Sec4Prop42ProductLocalWitness.prodSigned (S := S) Wprod).sum =
            (0 : R) :=
        sec4_prop42ProductValueOnS2_of_productLocalWitness
          (S := S) D hC hnn hxC2 Wprod
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


/-- Consistency with the previous relative integral, using product-local witnesses
on the `prop_4_2` side of the comparison. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_localValueBridge_productWitness
    (D : IntegrableSet1Def23Surface (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn := by
  unfold genRelIntegral_from_measurable relIntegral
  exact cor_1_12
    (sec4ConsistencySupport_full C hC f hnn)
    (genIB_rep_from_measurable C (isMeasurableSet_of_integrable hC) f hnn)
    (prop_4_2_chi_f_rep C hC f hnn)
    (sec4_genIB_value_eq_relRep_on_support_of_localBridge_productWitness
      (S := S) D C hC f hnn V)


/-- Packaged consistency bridge from the local value bridge and Def.2.3 data. -/
noncomputable def sec4_genIBConsistencyBridge_of_localValueBridge_productWitness
    (D : IntegrableSet1Def23Surface (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn := {
  integral_eq :=
    sec4_genRelIntegral_eq_relIntegral_of_localValueBridge_productWitness
      (S := S) D C hC f hnn V
}


/-! ## 3. Audit -/

structure Sec4Theorem415ProductWitnessBridgeAuditAfterG287 : Type where
  product_local_witness_used_in_consistency : Nat
  direct_prop42_value_call_in_consistency_required : Nat
  local_genIB_bridge_still_required : Nat
  def23_characteristic_witness_used : Nat
  product_rep_definition16_witness_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_route_integration_steps : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def sec4Theorem415ProductWitnessBridgeAuditAfterG287 :
    Sec4Theorem415ProductWitnessBridgeAuditAfterG287 where
  product_local_witness_used_in_consistency := 1
  direct_prop42_value_call_in_consistency_required := 0
  local_genIB_bridge_still_required := 1
  def23_characteristic_witness_used := 1
  product_rep_definition16_witness_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_route_integration_steps := 0
  remaining_global_integrable_set_refactor_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G287ProductWitnessBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g286 : Chapter4G286Prop42ProductDomainRoutePackage S
  audit : BishopC.Sec4Theorem415ProductWitnessBridgeAuditAfterG287
  product_witness_bridge_integrated_this_step : Nat
  remaining_route_integration_steps : Nat
  remaining_global_integrable_set_refactor_steps : Nat

def chapter4G287ProductWitnessBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G287ProductWitnessBridgePackage S where
  g286 := chapter4G286Prop42ProductDomainRoutePackage S
  audit := BishopC.sec4Theorem415ProductWitnessBridgeAuditAfterG287
  product_witness_bridge_integrated_this_step := 1
  remaining_route_integration_steps := 0
  remaining_global_integrable_set_refactor_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G287. -/
def bishopRegularSeqChapter4ProductWitnessBridgeProgressAfterG287 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G287: pushed the G286 product-domain local witness through the 4.15 \
    consistency bridge.  The prop_4_2 side of the comparison now reads values \
    from the local Definition-1.6 witness of the constructed chi_A*f \
    representative, not from a reconstructed outer row witness.  Countdown: \
    route integration is 0; 1 global refactor remains, namely folding the \
    Def23 characteristic-domain fields into IntegrableSet1 itself."


end BishopCReal
