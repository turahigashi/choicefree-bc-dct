import Mathdemo.Internal.Sec4.CoverEstimateData

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-a: canonical cover value

D2b2bα passed with zero changes.  The remaining object was
`Sec4GenIBCoverEstimateData`.

This file fixes the most economical `coverValue`:

`coverValue N := baseValue + partialSum tailRows N`.

With this choice the finite telescope field is definitional.  Thus the final
obligation is reduced to three pointwise fields only:

* domain membership in `B.S1 ∪ B.S2`;
* the `B.S1` close estimate for the canonical cover value;
* the `B.S2` close estimate for the canonical cover value.

From those three fields we construct `Sec4GenIBCoverEstimateData`, then the
value bridge and consistency theorem.
-/

#check Sec4GenIBCoverEstimateData
#check sec4_genIBValueBridge_of_estimateData
#check sec4_genRelIntegral_eq_relIntegral_of_estimateData
#check sec4_genIBConsistencyBridge_of_estimateData
#check sec4_genIB_baseValue
#check sec4_genIB_tailRowSeq

/-! ## 1. Canonical cover value -/

/--
Canonical cover value used for the final estimate step.

It is definitionally the finite expression already produced by the direct
construction: base value plus the first `N+1` tail rows, in the local
`partialSum` convention.
-/
noncomputable def sec4_canonicalCoverValue
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    Nat → R :=
  fun N =>
    sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
      RSeq.partialSum
        (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) N


/--
The finite telescope field for the canonical cover value is definitional.
-/
theorem sec4_canonicalCoverValue_finite_telescope
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    ∀ N : Nat,
      sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
        RSeq.partialSum
          (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) N =
      sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs N := by
  intro N
  rfl


/-! ## 2. Final close-data interface -/

/-- Domain field for the canonical cover value. -/
def Sec4CCD_domain
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ x : X,
    ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
    RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)) →
    x ∈ B.S1 ∪ B.S2


/-- `B.S1` close estimate for the canonical cover value. -/
def Sec4CCD_close_s1
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ x : X, x ∈ B.S1 →
    ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
    ∀ hgenabs :
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
    ∀ hfDom : f.MemAt x,
    ∀ hfabs :
      RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)),
    ∀ k n : Nat, k ≤ n →
      COF.Close k
        (sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n)
        (seriesSum_of_abs hfabs).sum


/-- `B.S2` close estimate for the canonical cover value. -/
def Sec4CCD_close_s2
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ x : X, x ∈ B.S2 →
    ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
    ∀ hgenabs :
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
    ∀ k n : Nat, k ≤ n →
      COF.Close k
        (sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n)
        0


/--
The final three fields needed for the canonical cover value.

This is a `PProd` chain rather than a structure with heavy generated
projections.
-/
def Sec4GenIBCanonicalCloseData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4CCD_domain (S := S) B hB f hnn)
    (PProd (Sec4CCD_close_s1 (S := S) B hB f hnn)
      (Sec4CCD_close_s2 (S := S) B hB f hnn))


namespace Sec4GenIBCanonicalCloseData

/-- Constructor with stable named arguments. -/
def mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (domain : Sec4CCD_domain (S := S) B hB f hnn)
    (close_s1 : Sec4CCD_close_s1 (S := S) B hB f hnn)
    (close_s2 : Sec4CCD_close_s2 (S := S) B hB f hnn) :
    Sec4GenIBCanonicalCloseData (S := S) B hB f hnn :=
  ⟨domain, close_s1, close_s2⟩


def domain
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4GenIBCanonicalCloseData (S := S) B hB f hnn) :
    Sec4CCD_domain (S := S) B hB f hnn :=
  T.1


def close_s1
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4GenIBCanonicalCloseData (S := S) B hB f hnn) :
    Sec4CCD_close_s1 (S := S) B hB f hnn :=
  T.2.1


def close_s2
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4GenIBCanonicalCloseData (S := S) B hB f hnn) :
    Sec4CCD_close_s2 (S := S) B hB f hnn :=
  T.2.2


end Sec4GenIBCanonicalCloseData

/-! ## 3. Estimate data and final bridges from canonical close data -/

/--
Build the full cover-estimate data from the three canonical close fields.
-/
noncomputable def sec4_coverEstimateData_of_canonicalCloseData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCanonicalCloseData (S := S) B hB f hnn) :
    Sec4GenIBCoverEstimateData (S := S) B hB f hnn := {
  coverValue := fun x hgenDom hgenabs =>
    sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs
  domain := T.domain
  finite_telescope := by
    intro x hgenDom hgenabs N
    exact sec4_canonicalCoverValue_finite_telescope
      B hB f hnn x hgenDom hgenabs N
  cover_close_s1 := by
    intro x hxB hgenDom hgenabs hfDom hfabs k n hn
    exact T.close_s1 x hxB hgenDom hgenabs hfDom hfabs k n hn
  cover_close_s2 := by
    intro x hxB hgenDom hgenabs k n hn
    exact T.close_s2 x hxB hgenDom hgenabs k n hn
}


/-- Full value bridge from canonical close data. -/
noncomputable def sec4_genIBValueBridge_of_canonicalCloseData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCanonicalCloseData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_estimateData B hB f hnn
    (sec4_coverEstimateData_of_canonicalCloseData B hB f hnn T)


/-- Consistency theorem from canonical close data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_canonicalCloseData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCanonicalCloseData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_estimateData C hC f hnn
    (sec4_coverEstimateData_of_canonicalCloseData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from canonical close data. -/
noncomputable def sec4_genIBConsistencyBridge_of_canonicalCloseData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCanonicalCloseData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_estimateData C hC f hnn
    (sec4_coverEstimateData_of_canonicalCloseData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
