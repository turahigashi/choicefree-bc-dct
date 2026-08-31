import Mathdemo.Internal.Sec4.ResidualData

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D1: value-bridge interface and consistency

C2bβ2bβ2bβ1 established the unconditional direct representative

```lean
genIB_rep_from_measurable B hB f hnn
```

for measurable `B` and non-negative integrable `f`.

This file begins Phase D.  It introduces the value bridge for the direct
representative and proves the consistency theorem:

```lean
genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn
  = relIntegral C hC f hnn
```

from that value bridge.

The hard remaining analytic step is the actual construction of
`Sec4GenIBValueBridge`, i.e. the telescope showing that the direct construction
has point values `χ_B · f`.
-/

#check genIB_rep_from_measurable
#check genRelIntegral_from_measurable
#check genIB_rep_from_measurable_repNonneg
#check relIntegral
#check isMeasurableSet_of_integrable
#check prop_4_2_chi_f_rep_value
#check cor_1_12
#check IntegrableRep.domain_isFull
#check isFull_inter
#check seriesSum_unique

/-! ## 1. Value bridge for the direct representative -/

/--
Value bridge for the direct general measurable relative-integral representative.

`domain` says the direct representative is defined only on the complemented
domain of `B`.

`value_s1` and `value_s2` identify its point value with `χ_B · f`: on `B.S1`
it is the value of `f`, and on `B.S2` it is zero.
-/
structure Sec4GenIBValueBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop where
  domain :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)) →
      x ∈ B.S1 ∪ B.S2
  value_s1 :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)),
      (seriesSum_of_abs hgenabs).sum = (seriesSum_of_abs hfabs).sum
  value_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
      (seriesSum_of_abs hgenabs).sum = 0


/--
A light-weight consistency package for already integrable sets.
-/
structure Sec4GenIBConsistencyBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop where
  integral_eq :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn


/-! ## 2. Full support for the consistency comparison -/

/--
Support on which the direct representative, the previous relative-integral
representative, `χ_C`, and `f` all have point-value witnesses.
-/
def Sec4ConsistencySupport
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Set X :=
  (((genIB_rep_from_measurable C (isMeasurableSet_of_integrable hC) f hnn).domain ∩
      (prop_4_2_chi_f_rep C hC f hnn).domain) ∩
      hC.rep.domain) ∩
      f.domain


/-- Fullness of the support used in the consistency comparison. -/
theorem sec4ConsistencySupport_full
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IsFull S (Sec4ConsistencySupport (S := S) C hC f hnn) := by
  unfold Sec4ConsistencySupport
  exact isFull_inter
    (isFull_inter
      (isFull_inter
        (IntegrableRep.domain_isFull
          (genIB_rep_from_measurable C (isMeasurableSet_of_integrable hC) f hnn))
        (IntegrableRep.domain_isFull (prop_4_2_chi_f_rep C hC f hnn)))
      (IntegrableRep.domain_isFull hC.rep))
    (IntegrableRep.domain_isFull f)


/-! ## 3. Consistency from the value bridge -/

/--
Pointwise equality between the direct representative and the old
`prop_4_2_chi_f_rep` representative, assuming the value bridge.
-/
theorem sec4_genIB_value_eq_relRep_on_support
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBValueBridge (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    ∀ x ∈ Sec4ConsistencySupport (S := S) C hC f hnn,
      ∀ (hgenDom : (genIB_rep_from_measurable C
          (isMeasurableSet_of_integrable hC) f hnn).MemAt x)
        (hrelDom : (prop_4_2_chi_f_rep C hC f hnn).MemAt x)
        (hgen : RSeq.SeriesSum (fun n =>
          (genIB_rep_from_measurable C
            (isMeasurableSet_of_integrable hC) f hnn).valueAt x hgenDom n))
        (hrel : RSeq.SeriesSum (fun n =>
          (prop_4_2_chi_f_rep C hC f hnn).valueAt x hrelDom n)),
        hgen.sum = hrel.sum := by
  intro x hx hgenDom hrelDom hgen hrel
  rcases hx with ⟨⟨⟨hxgen, hxrel⟩, hχDom⟩, hfDom⟩
  rcases hxgen with ⟨hgenAt, ⟨hgenabs⟩⟩
  rcases hxrel with ⟨hrelAt, ⟨hrelabs⟩⟩
  rcases hχDom with ⟨hχAt, ⟨hχabs⟩⟩
  rcases hfDom with ⟨hfAt, ⟨hfabs⟩⟩
  have hrel_value :
      (seriesSum_of_abs hrelabs).sum =
        (seriesSum_of_abs hχabs).sum * (seriesSum_of_abs hfabs).sum :=
    prop_4_2_chi_f_rep_value C hC f hnn (x := x)
      hrelAt hχAt hfAt hrelabs hχabs hfabs
  have hχvalid := hC.valid x hχAt hχabs
  cases hχvalid.1 with
  | inl hxC1 =>
      have hχ_one :
          (seriesSum_of_abs hχabs).sum = 1 :=
        hχvalid.2.1 hxC1 (seriesSum_of_abs hχabs)
      have hgen_value :
          (seriesSum_of_abs hgenabs).sum =
            (seriesSum_of_abs hfabs).sum :=
        V.value_s1 x hxC1 hgenAt hgenabs hfAt hfabs
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
        V.value_s2 x hxC2 hgenAt hgenabs
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


/--
Consistency of the direct relative integral with the previous relative integral for
an already integrable complemented set, assuming the value bridge.
-/
theorem sec4_genRelIntegral_eq_relIntegral_of_valueBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBValueBridge (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn := by
  unfold genRelIntegral_from_measurable relIntegral
  change
    (genIB_rep_from_measurable C (isMeasurableSet_of_integrable hC) f hnn).integral =
      (prop_4_2_chi_f_rep C hC f hnn).integral
  exact cor_1_12
    (sec4ConsistencySupport_full C hC f hnn)
    (genIB_rep_from_measurable C (isMeasurableSet_of_integrable hC) f hnn)
    (prop_4_2_chi_f_rep C hC f hnn)
    (sec4_genIB_value_eq_relRep_on_support C hC f hnn V)


/-- Package the consistency theorem as a bridge. -/
noncomputable def sec4_genIBConsistencyBridge_of_valueBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBValueBridge (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn := {
  integral_eq := sec4_genRelIntegral_eq_relIntegral_of_valueBridge C hC f hnn V
}


end BishopC
