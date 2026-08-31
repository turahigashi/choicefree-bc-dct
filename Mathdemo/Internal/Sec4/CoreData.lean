import Mathdemo.Internal.Sec4.CoverChiTelescopeBridge

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b1: core telescope data → final bridge

The previous chunk verified `Sec4CanonicalCoverChiData` except for its actual
construction.  The remaining hard content is now compressed to four fields:

* an absolute-convergence witness for the characteristic representative
  `χ_(coverSet f n ∧ B)` at the point;
* the finite telescope identity on `B.S1`;
* the zero value on `B.S2`;
* the `coverApart` close estimate in the `coverSet.S2` branch.

From these four fields this file constructs `Sec4CanonicalCoverChiData`, then
the unconditional value bridge and consistency theorem.

This intentionally avoids reading χ-values from arbitrary signed witnesses and
uses only `IntegrableSet1.valid` with the supplied absolute witness.
-/

#check Sec4CanonicalCoverChiData
#check sec4_canonicalCoverFacts_of_chiData
#check sec4_genIBValueBridge_of_chiData
#check sec4_genRelIntegral_eq_relIntegral_of_chiData
#check sec4_genIBConsistencyBridge_of_chiData
#check sec4CoverAnd
#check sec4CoverAnd_int
#check coverSet

/-! ## 1. Core data: the true remaining telescope and estimate obligations -/

/--
The true remaining pointwise core for the general measurable relative integral.

`cover_chi_abs` supplies the characteristic-domain witness required by
`IntegrableSet1.valid`.

`cover_value_eq_chi_on_Bs1` is the real finite telescope identity.

`cover_value_on_B_s2` is the zero branch for points outside `B`.

`cover_small_s2` is the numerical `coverApart` estimate.
-/
structure Sec4CanonicalCoverCoreData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  cover_chi_dom :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        (sec4CoverAnd_int B hB f n).rep.MemAt x
  cover_chi_abs :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        RSeq.SeriesSum
          (fun m => COF.abs
            ((sec4CoverAnd_int B hB f n).rep.valueAt x
              (cover_chi_dom x hgenDom hgenabs n) m))
  cover_value_eq_chi_on_Bs1 :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
      ∀ n : Nat,
        sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n =
          (seriesSum_of_abs
            (cover_chi_abs x hgenDom hgenabs n)).sum *
            (seriesSum_of_abs hfabs).sum
  cover_value_on_B_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n = 0
  cover_small_s2 :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
      ∀ k n : Nat, k ≤ n →
        x ∈ (coverSet f n).S2 →
          COF.Close k 0 (seriesSum_of_abs hfabs).sum


/-! ## 2. Domain and cover-case from characteristic validness -/

/--
From the core characteristic witness at level `0`, obtain the `B` domain
membership required by `Sec4GenIBValueBridge`.
-/
theorem sec4_domain_of_coverCoreData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverCoreData (S := S) B hB f hnn) :
    Sec4CCD_domain (S := S) B hB f hnn := by
  intro x hgenDom hgenabs
  let hχDom := T.cover_chi_dom x hgenDom hgenabs 0
  let hχ := T.cover_chi_abs x hgenDom hgenabs 0
  have hvalid := (sec4CoverAnd_int B hB f 0).valid x hχDom hχ
  cases hvalid.1 with
  | inl hAnd1 =>
      unfold sec4CoverAnd at hAnd1
      exact Or.inl hAnd1.2
  | inr hAnd2 =>
      unfold sec4CoverAnd at hAnd2
      rcases hAnd2 with h12 | h3
      · rcases h12 with h1 | h2
        · exact Or.inr h1.2
        · exact Or.inl h2.2
      · exact Or.inr h3.2


/--
For every point where the canonical representative is defined, the
`coverSet f n` characteristic is defined.  This is obtained from validness of
`coverSet f n ∧ B` and then forgetting the `B` coordinate.
-/
theorem sec4_cover_case_of_coverCoreData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverCoreData (S := S) B hB f hnn) :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        x ∈ (coverSet f n).S1 ∨ x ∈ (coverSet f n).S2 := by
  intro x hgenDom hgenabs n
  let hχDom := T.cover_chi_dom x hgenDom hgenabs n
  let hχ := T.cover_chi_abs x hgenDom hgenabs n
  have hvalid := (sec4CoverAnd_int B hB f n).valid x hχDom hχ
  cases hvalid.1 with
  | inl hAnd1 =>
      unfold sec4CoverAnd at hAnd1
      exact Or.inl hAnd1.1
  | inr hAnd2 =>
      unfold sec4CoverAnd at hAnd2
      rcases hAnd2 with h12 | h3
      · rcases h12 with h1 | h2
        · exact Or.inl h1.1
        · exact Or.inr h2.1
      · exact Or.inr h3.1


/-! ## 3. Assemble `Sec4CanonicalCoverChiData` -/

/--
Build the χ-data used by the previous chunk from the core telescope data.
-/
noncomputable def sec4_canonicalCoverChiData_of_coreData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverCoreData (S := S) B hB f hnn) :
    Sec4CanonicalCoverChiData (S := S) B hB f hnn := {
  domain := sec4_domain_of_coverCoreData B hB f hnn T
  cover_case := sec4_cover_case_of_coverCoreData B hB f hnn T
  cover_chi_dom := T.cover_chi_dom
  cover_chi_abs := T.cover_chi_abs
  cover_value_eq_chi_on_Bs1 := T.cover_value_eq_chi_on_Bs1
  cover_value_on_B_s2 := T.cover_value_on_B_s2
  cover_small_s2 := T.cover_small_s2
}


/-- Full value bridge from the core telescope data. -/
noncomputable def sec4_genIBValueBridge_of_coreData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverCoreData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_chiData B hB f hnn
    (sec4_canonicalCoverChiData_of_coreData B hB f hnn T)


/-- Consistency theorem from the core telescope data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_coreData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverCoreData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_chiData C hC f hnn
    (sec4_canonicalCoverChiData_of_coreData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from the core telescope data. -/
noncomputable def sec4_genIBConsistencyBridge_of_coreData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverCoreData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_chiData C hC f hnn
    (sec4_canonicalCoverChiData_of_coreData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
