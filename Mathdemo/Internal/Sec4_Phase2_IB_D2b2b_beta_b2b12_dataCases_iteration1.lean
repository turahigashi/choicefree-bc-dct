import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b10_stepAbs_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b12: data-valued dichotomy avoids `propRecLargeElim`

The b2b11 kernel response identified the real obstruction:
`valid.1` gives a Prop-valued `Or`, but the goal of `Sec4CoverChiFStepAbs` is
a data value `RSeq.SeriesSum`.  Eliminating a Prop `Or` into that Type-valued
goal causes `propRecLargeElim`.

This file avoids that completely.  It replaces Prop-valued case splits by
DATA-valued dichotomies (`PSum`) supplied as explicit data.

There are two independent ingredients:

* `Sec4ChiFCaseToolsData`: generic internal tools for `χ_A·f`;
* `Sec4CoverDichotomyData`: data-valued S1/S2 dichotomies for the two
  integrable sets occurring in the one-step cover assembly.

From these, we construct `Sec4CoverChiFStepAbs`, hence
`Sec4Prop42FinalTools`, `Sec4GenIBValueBridge`, and consistency.

The remaining task after this file is exactly to construct those two data
packages, with no Prop-to-Type elimination.
-/

#check Sec4CoverChiFStepAbs
#check sec4_prop42FinalTools_of_stepAbs
#check sec4_genIBValueBridge_of_stepAbs
#check sec4_genRelIntegral_eq_relIntegral_of_stepAbs
#check sec4_genIBConsistencyBridge_of_stepAbs
#check sec4_setChiAbsOfChiFAbs_of_row1
#check sec4_coverAnd_s1_mono
#check sec4CoverAnd
#check sec4CoverAnd_int
#check sec4CoverDiff
#check sec4CoverDiff_int
#check prop_4_2_chi_f_rep

/-! ## 1. Generic case-wise internal tools for `χ_A · f` -/

/--
On the positive side of `A`, an abs witness for `χ_A · f` exposes an abs
witness for `f`.
-/
def Sec4ChiFFAbsOfS1Data
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x)) →
    RSeq.SeriesSum (fun m => COF.abs (((f.fn m).toFun x)))


/--
Given an `f` abs witness, build an abs witness for `χ_A · f` on the positive
side of `A`.
-/
def Sec4ChiFAbsOnS1Data
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    RSeq.SeriesSum (fun m => COF.abs (((f.fn m).toFun x))) →
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))


/--
On the negative side of `A`, build an abs witness for `χ_A · f` without
extracting an `f` witness.
-/
def Sec4ChiFAbsOnS2Data
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S2 →
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))


/--
Generic case-wise internal tools for `prop_4_2_chi_f_rep`.

A `PProd` chain is used to avoid projection generation over heavy
representative expressions.
-/
def Sec4ChiFCaseToolsData
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4ChiFFAbsOfS1Data (S := S) f hnn)
    (PProd (Sec4ChiFAbsOnS1Data (S := S) f hnn)
      (Sec4ChiFAbsOnS2Data (S := S) f hnn))


namespace Sec4ChiFCaseToolsData

def mk
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (fabs_of_s1 : Sec4ChiFFAbsOfS1Data (S := S) f hnn)
    (abs_on_s1 : Sec4ChiFAbsOnS1Data (S := S) f hnn)
    (abs_on_s2 : Sec4ChiFAbsOnS2Data (S := S) f hnn) :
    Sec4ChiFCaseToolsData (S := S) f hnn :=
  ⟨fabs_of_s1, abs_on_s1, abs_on_s2⟩


def fabs_of_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseToolsData (S := S) f hnn) :
    Sec4ChiFFAbsOfS1Data (S := S) f hnn :=
  T.1


def abs_on_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseToolsData (S := S) f hnn) :
    Sec4ChiFAbsOnS1Data (S := S) f hnn :=
  T.2.1


def abs_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseToolsData (S := S) f hnn) :
    Sec4ChiFAbsOnS2Data (S := S) f hnn :=
  T.2.2


end Sec4ChiFCaseToolsData

/-! ## 2. Data-valued dichotomies -/

/--
A data-valued S1/S2 dichotomy for an already integrable complemented set.

This is deliberately `PSum`, not Prop `Or`, so that it can be eliminated when
constructing Type-valued witnesses such as `RSeq.SeriesSum`.
-/
def Sec4IntegrableSetDichotomy
    (A : BSet X) (hA : IntegrableSet1 S A) : Type _ :=
  ∀ x : X,
    RSeq.SeriesSum (fun m => COF.abs (((hA.rep.fn m).toFun x))) →
      PSum (x ∈ A.S1) (x ∈ A.S2)


/-- Data-valued dichotomies needed for the one-step cover assembly. -/
def Sec4CoverDichotomyData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) : Type _ :=
  PProd
    (∀ k : Nat,
      Sec4IntegrableSetDichotomy
        (sec4CoverAnd B f k)
        (sec4CoverAnd_int B hB f k))
    (∀ k : Nat,
      Sec4IntegrableSetDichotomy
        (sec4CoverDiff B f k)
        (sec4CoverDiff_int B hB f k))


namespace Sec4CoverDichotomyData

def mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S}
    (coverAnd_case :
      ∀ k : Nat,
        Sec4IntegrableSetDichotomy
          (sec4CoverAnd B f k)
          (sec4CoverAnd_int B hB f k))
    (coverDiff_case :
      ∀ k : Nat,
        Sec4IntegrableSetDichotomy
          (sec4CoverDiff B f k)
          (sec4CoverDiff_int B hB f k)) :
    Sec4CoverDichotomyData (S := S) B hB f :=
  ⟨coverAnd_case, coverDiff_case⟩


def coverAnd_case
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S}
    (D : Sec4CoverDichotomyData (S := S) B hB f) :
    ∀ k : Nat,
      Sec4IntegrableSetDichotomy
        (sec4CoverAnd B f k)
        (sec4CoverAnd_int B hB f k) :=
  D.1


def coverDiff_case
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S}
    (D : Sec4CoverDichotomyData (S := S) B hB f) :
    ∀ k : Nat,
      Sec4IntegrableSetDichotomy
        (sec4CoverDiff B f k)
        (sec4CoverDiff_int B hB f k) :=
  D.2


end Sec4CoverDichotomyData

/-! ## 3. Step-case data obtained from the data-valued dichotomies -/

/--
The current-cover case as data, extracted from `χ·f` abs by the row-1
characteristic extractor.
-/
noncomputable def sec4_coverAndCase_from_dichotomyData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (D : Sec4CoverDichotomyData (S := S) B hB f)
    (k : Nat) (x : X)
    (hVflat :
      RSeq.SeriesSum
        (fun m => COF.abs
          (((prop_4_2_chi_f_rep
              (sec4CoverAnd B f k)
              (sec4CoverAnd_int B hB f k)
              f hnn).fn m).toFun x))) :
    PSum (x ∈ (sec4CoverAnd B f k).S1)
         (x ∈ (sec4CoverAnd B f k).S2) := by
  let hVχ :=
    sec4_setChiAbsOfChiFAbs_of_row1 (S := S) f hnn
      (sec4CoverAnd B f k)
      (sec4CoverAnd_int B hB f k)
      x hVflat
  exact (Sec4CoverDichotomyData.coverAnd_case D k) x hVχ


/--
The difference-layer case as data, extracted from `χ·f` abs by the row-1
characteristic extractor.
-/
noncomputable def sec4_coverDiffCase_from_dichotomyData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (D : Sec4CoverDichotomyData (S := S) B hB f)
    (k : Nat) (x : X)
    (hDflat :
      RSeq.SeriesSum
        (fun m => COF.abs
          (((prop_4_2_chi_f_rep
              (sec4CoverDiff B f k)
              (sec4CoverDiff_int B hB f k)
              f hnn).fn m).toFun x))) :
    PSum (x ∈ (sec4CoverDiff B f k).S1)
         (x ∈ (sec4CoverDiff B f k).S2) := by
  let hDχ :=
    sec4_setChiAbsOfChiFAbs_of_row1 (S := S) f hnn
      (sec4CoverDiff B f k)
      (sec4CoverDiff_int B hB f k)
      x hDflat
  exact (Sec4CoverDichotomyData.coverDiff_case D k) x hDχ


/-! ## 4. Local set algebra for the remaining case split -/

/-- S1 membership of the difference layer implies S1 membership of the successor cover. -/
theorem sec4_coverDiff_s1_to_succCover_s1_data
    (B : BSet X) (f : IntegrableRep S) (k : Nat) (x : X)
    (hD : x ∈ (sec4CoverDiff B f k).S1) :
    x ∈ (sec4CoverAnd B f (k + 1)).S1 := by
  unfold sec4CoverDiff at hD
  exact hD.1


/--
If the current cover and the difference layer are both negative at `x`, then
the successor cover is negative at `x`.
-/
theorem sec4_succCover_s2_of_curr_s2_diff_s2_data
    (B : BSet X) (f : IntegrableRep S) (k : Nat) (x : X)
    (hV : x ∈ (sec4CoverAnd B f k).S2)
    (hD : x ∈ (sec4CoverDiff B f k).S2) :
    x ∈ (sec4CoverAnd B f (k + 1)).S2 := by
  unfold sec4CoverDiff at hD
  rcases hD with h12 | h3
  · rcases h12 with h1 | h2
    · exfalso
      exact (sec4CoverAnd B f k).disj x h1.2 x hV rfl
    · exact h2.1
  · exfalso
    exact (sec4CoverAnd B f k).disj x h3.2 x hV rfl


/-! ## 5. Choice-free one-step assembly from Type-valued cases -/

/--
Build the one-step finite-cover abs assembly from generic `χ·f` case tools and
data-valued cover/difference dichotomies.

The only case splits in this proof are on `PSum` values, so there is no
Prop-to-Type large elimination.
-/
noncomputable def sec4_coverChiFStepAbs_of_dataCases
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn)
    (D : Sec4CoverDichotomyData (S := S) B hB f) :
    Sec4CoverChiFStepAbs (S := S) B hB f hnn := by
  intro k x hVflat hDflat
  let vcase :=
    sec4_coverAndCase_from_dichotomyData B hB f hnn D k x hVflat
  cases vcase with
  | inl hV1 =>
      have hU1 : x ∈ (sec4CoverAnd B f (k + 1)).S1 :=
        sec4_coverAnd_s1_mono B f k x hV1
      let hfabs :=
        Sec4ChiFCaseToolsData.fabs_of_s1 T
          (sec4CoverAnd B f k)
          (sec4CoverAnd_int B hB f k)
          x hV1 hVflat
      exact Sec4ChiFCaseToolsData.abs_on_s1 T
        (sec4CoverAnd B f (k + 1))
        (sec4CoverAnd_int B hB f (k + 1))
        x hU1 hfabs
  | inr hV2 =>
      let dcase :=
        sec4_coverDiffCase_from_dichotomyData B hB f hnn D k x hDflat
      cases dcase with
      | inl hD1 =>
          have hU1 : x ∈ (sec4CoverAnd B f (k + 1)).S1 :=
            sec4_coverDiff_s1_to_succCover_s1_data B f k x hD1
          let hfabs :=
            Sec4ChiFCaseToolsData.fabs_of_s1 T
              (sec4CoverDiff B f k)
              (sec4CoverDiff_int B hB f k)
              x hD1 hDflat
          exact Sec4ChiFCaseToolsData.abs_on_s1 T
            (sec4CoverAnd B f (k + 1))
            (sec4CoverAnd_int B hB f (k + 1))
            x hU1 hfabs
      | inr hD2 =>
          have hU2 : x ∈ (sec4CoverAnd B f (k + 1)).S2 :=
            sec4_succCover_s2_of_curr_s2_diff_s2_data B f k x hV2 hD2
          exact Sec4ChiFCaseToolsData.abs_on_s2 T
            (sec4CoverAnd B f (k + 1))
            (sec4CoverAnd_int B hB f (k + 1))
            x hU2


/-! ## 6. Final bridge and consistency from data-valued cases -/

/-- The one-field final-tools package from data-valued cases. -/
noncomputable def sec4_prop42FinalTools_of_dataCases
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn)
    (D : Sec4CoverDichotomyData (S := S) B hB f) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  sec4_prop42FinalTools_of_stepAbs B hB f hnn
    (sec4_coverChiFStepAbs_of_dataCases B hB f hnn T D)


/-- Full value bridge from data-valued cases. -/
noncomputable def sec4_genIBValueBridge_of_dataCases
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn)
    (D : Sec4CoverDichotomyData (S := S) B hB f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_stepAbs B hB f hnn
    (sec4_coverChiFStepAbs_of_dataCases B hB f hnn T D)


/-- Consistency theorem from data-valued cases. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_dataCases
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn)
    (D : Sec4CoverDichotomyData
      (S := S) C (isMeasurableSet_of_integrable hC) f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_stepAbs C hC f hnn
    (sec4_coverChiFStepAbs_of_dataCases
      C (isMeasurableSet_of_integrable hC) f hnn T D)


/-- Packaged consistency bridge from data-valued cases. -/
noncomputable def sec4_genIBConsistencyBridge_of_dataCases
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn)
    (D : Sec4CoverDichotomyData
      (S := S) C (isMeasurableSet_of_integrable hC) f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_stepAbs C hC f hnn
    (sec4_coverChiFStepAbs_of_dataCases
      C (isMeasurableSet_of_integrable hC) f hnn T D)


end BishopC
