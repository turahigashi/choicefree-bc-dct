import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b36_localFlatValue_iteration1

/-!
# Sec4 Phase2-D2b2b_beta-b2b37: local value bridge for general `I_B`

The previous `Sec4GenIBValueBridge` is a global bridge: from a flat abs witness for
the direct measurable representative it proves domain membership and values on
`B.S1`/`B.S2`.  That shape is convenient downstream, but it can hide the same
membership-to-witness pressure that appeared in Proposition 4.2.

This file introduces a local counterpart.  The local bridge receives the
pointwise abs witnesses explicitly.  It is therefore the target that a
source-faithful full-set proof of the general measurable `I_B` should prove.
For compatibility, the previous bridge is shown to imply the local one, and the
already-integrable consistency theorem is reproved from the local bridge.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Local support and witnesses for the direct measurable representative -/

/-- Common support for the direct measurable representative and `f`. -/
def Sec4GenIBLocalSupport
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Set X :=
  (genIB_rep_from_measurable B hB f hnn).domain ∩ f.domain


/-- The direct measurable support is full. -/
theorem sec4_genIBLocalSupport_full
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IsFull S (Sec4GenIBLocalSupport (S := S) B hB f hnn) := by
  unfold Sec4GenIBLocalSupport
  exact isFull_inter
    (IntegrableRep.domain_isFull (genIB_rep_from_measurable B hB f hnn))
    (IntegrableRep.domain_isFull f)


/-- Pointwise local data for the direct measurable representative and `f`. -/
structure Sec4GenIBLocalWitness
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (x : X) : Type _ where
  gen_dom : (genIB_rep_from_measurable B hB f hnn).MemAt x
  gen_abs : RSeq.SeriesSum
    (fun m => COF.abs
      ((genIB_rep_from_measurable B hB f hnn).valueAt x gen_dom m))
  f_dom : f.MemAt x
  f_abs : RSeq.SeriesSum (fun m => COF.abs (f.valueAt x f_dom m))


namespace Sec4GenIBLocalWitness

/-- A local witness lies on the propositional common support. -/
theorem mem_support
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f} {x : X}
    (W : Sec4GenIBLocalWitness (S := S) B hB f hnn x) :
    x ∈ Sec4GenIBLocalSupport (S := S) B hB f hnn := by
  unfold Sec4GenIBLocalSupport
  exact ⟨⟨W.gen_dom, ⟨W.gen_abs⟩⟩, ⟨W.f_dom, ⟨W.f_abs⟩⟩⟩


/-- Signed value of the direct measurable representative at a local witness. -/
noncomputable def genSigned
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f} {x : X}
    (W : Sec4GenIBLocalWitness (S := S) B hB f hnn x) :
    RSeq.SeriesSum
      (fun m => (genIB_rep_from_measurable B hB f hnn).valueAt
        x W.gen_dom m) :=
  seriesSum_of_abs W.gen_abs


/-- Signed value of `f` at a local witness. -/
noncomputable def fSigned
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f} {x : X}
    (W : Sec4GenIBLocalWitness (S := S) B hB f hnn x) :
    RSeq.SeriesSum (fun m => f.valueAt x W.f_dom m) :=
  seriesSum_of_abs W.f_abs


end Sec4GenIBLocalWitness

/-! ## 2. Local replacement for `Sec4GenIBValueBridge` -/

/-- Local value bridge for the direct measurable representative.

This is the full-set-friendly replacement target for future proofs: values are
identified only at points where the relevant witnesses are already present. -/
structure Sec4GenIBLocalValueBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop where
  domain :
    ∀ x : X,
      Sec4GenIBLocalWitness (S := S) B hB f hnn x →
      x ∈ B.S1 ∪ B.S2
  value_s1 :
    ∀ x : X, x ∈ B.S1 →
      ∀ W : Sec4GenIBLocalWitness (S := S) B hB f hnn x,
        (Sec4GenIBLocalWitness.genSigned (S := S) W).sum =
          (Sec4GenIBLocalWitness.fSigned (S := S) W).sum
  value_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ W : Sec4GenIBLocalWitness (S := S) B hB f hnn x,
        (Sec4GenIBLocalWitness.genSigned (S := S) W).sum = (0 : R)


/-- Compatibility: the previous global value bridge implies the local one. -/
noncomputable def sec4_genIBLocalValueBridge_of_valueBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBValueBridge (S := S) B hB f hnn) :
    Sec4GenIBLocalValueBridge (S := S) B hB f hnn where
  domain := by
    intro x W
    exact V.domain x W.gen_dom W.gen_abs
  value_s1 := by
    intro x hxB W
    exact V.value_s1 x hxB W.gen_dom W.gen_abs W.f_dom W.f_abs
  value_s2 := by
    intro x hxB W
    exact V.value_s2 x hxB W.gen_dom W.gen_abs


/-! ## 3. Already-integrable consistency from the local bridge -/

/-- Pointwise equality between the direct representative and the previous relative
representative, using only the local value bridge. -/
theorem sec4_genIB_value_eq_relRep_on_support_of_localBridge
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
        (fun n => (prop_4_2_chi_f_rep C hC f hnn).valueAt x hrelDom n)),
        hgen.sum = hrel.sum := by
  intro x hx hgenDom hrelDom hgen hrel
  rcases hx with ⟨⟨⟨hgenAt, hrelAt⟩, hχAt⟩, hfAt⟩
  rcases hgenAt with ⟨hgenSupportDom, ⟨hgenabs⟩⟩
  rcases hrelAt with ⟨hrelSupportDom, ⟨hrelabs⟩⟩
  rcases hχAt with ⟨hχSupportDom, ⟨hχabs⟩⟩
  rcases hfAt with ⟨hfSupportDom, ⟨hfabs⟩⟩
  let W : Sec4GenIBLocalWitness
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn x := {
    gen_dom := hgenSupportDom
    gen_abs := hgenabs
    f_dom := hfSupportDom
    f_abs := hfabs
  }
  have hrel_value :
      (seriesSum_of_abs hrelabs).sum =
        (seriesSum_of_abs hχabs).sum * (seriesSum_of_abs hfabs).sum :=
    prop_4_2_chi_f_rep_value C hC f hnn (x := x)
      hrelSupportDom hχSupportDom hfSupportDom hrelabs hχabs hfabs
  have hχvalid := hC.valid x hχSupportDom hχabs
  cases hχvalid.1 with
  | inl hxC1 =>
      have hχ_one :
          (seriesSum_of_abs hχabs).sum = 1 :=
        hχvalid.2.1 hxC1 (seriesSum_of_abs hχabs)
      have hgen_value :
          (seriesSum_of_abs hgenabs).sum =
            (seriesSum_of_abs hfabs).sum :=
        V.value_s1 x hxC1 W
      calc
        hgen.sum = (seriesSum_of_abs hgenabs).sum :=
          seriesSum_unique hgen (seriesSum_of_abs hgenabs)
        _ = (seriesSum_of_abs hfabs).sum := hgen_value
        _ = 1 * (seriesSum_of_abs hfabs).sum := by ring
        _ = (seriesSum_of_abs hχabs).sum *
            (seriesSum_of_abs hfabs).sum := by
              rw [hχ_one]
        _ = (seriesSum_of_abs hrelabs).sum := hrel_value.symm
        _ = hrel.sum :=
          (seriesSum_unique hrel (seriesSum_of_abs hrelabs)).symm
  | inr hxC2 =>
      have hχ_zero :
          (seriesSum_of_abs hχabs).sum = 0 :=
        hχvalid.2.2 hxC2 (seriesSum_of_abs hχabs)
      have hgen_value :
          (seriesSum_of_abs hgenabs).sum = 0 :=
        V.value_s2 x hxC2 W
      calc
        hgen.sum = (seriesSum_of_abs hgenabs).sum :=
          seriesSum_unique hgen (seriesSum_of_abs hgenabs)
        _ = 0 := hgen_value
        _ = 0 * (seriesSum_of_abs hfabs).sum := by ring
        _ = (seriesSum_of_abs hχabs).sum *
            (seriesSum_of_abs hfabs).sum := by
              rw [hχ_zero]
        _ = (seriesSum_of_abs hrelabs).sum := hrel_value.symm
        _ = hrel.sum :=
          (seriesSum_unique hrel (seriesSum_of_abs hrelabs)).symm


/-- Consistency with the previous relative integral from the local value bridge. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_localValueBridge
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
    (sec4_genIB_value_eq_relRep_on_support_of_localBridge C hC f hnn V)


/-- Packaged consistency bridge from the local value bridge. -/
noncomputable def sec4_genIBConsistencyBridge_of_localValueBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn := {
  integral_eq := sec4_genRelIntegral_eq_relIntegral_of_localValueBridge
    C hC f hnn V
}


end BishopC
