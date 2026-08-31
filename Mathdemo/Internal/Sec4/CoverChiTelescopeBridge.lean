import Mathdemo.Internal.Sec4.CoverFacts

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2a: cover-χ telescope bridge

This chunk assumes the D2b2bβ-b1 layer is available.  It reduces
`Sec4CanonicalCoverFacts` to a more concrete bridge:

* canonical cover value equals the point value of
  `χ_(coverSet f n ∧ B) · f` on the `B.S1` branch;
* the `B.S2` branch and the small-cover estimate are kept as separate fields.

The key benefit is that the hard finite telescope is isolated in exactly one
field, `cover_value_eq_chi_on_Bs1`.  From this field plus the validness of the
integrable set `coverSet f n ∧ B`, the two `B.S1` value cases are automatic.
-/

#check Sec4CanonicalCoverFacts
#check sec4_canonicalCloseData_of_coverFacts
#check sec4_genIBValueBridge_of_coverFacts
#check sec4_genRelIntegral_eq_relIntegral_of_coverFacts
#check sec4_genIBConsistencyBridge_of_coverFacts
#check sec4_canonicalCoverValue
#check sec4CoverAnd
#check sec4CoverAnd_int
#check coverSet_int

/-! ## 1. Raw membership constructors for `coverSet f n ∧ B` -/

/-- S1 constructor for `coverSet f n ∧ B`. -/
theorem sec4_coverAnd_mem_s1
    (B : BSet X) (f : IntegrableRep S) (n : Nat) (x : X)
    (hcover : x ∈ (coverSet f n).S1) (hB1 : x ∈ B.S1) :
    x ∈ (sec4CoverAnd B f n).S1 := by
  unfold sec4CoverAnd
  change x ∈ (coverSet f n).S1 ∧ x ∈ B.S1
  exact ⟨hcover, hB1⟩


/-- S2 constructor for `coverSet f n ∧ B` from `coverSet.S2` and `B.S1`. -/
theorem sec4_coverAnd_mem_s2_of_cover_s2_B_s1
    (B : BSet X) (f : IntegrableRep S) (n : Nat) (x : X)
    (hcover : x ∈ (coverSet f n).S2) (hB1 : x ∈ B.S1) :
    x ∈ (sec4CoverAnd B f n).S2 := by
  unfold sec4CoverAnd
  -- `BSet.and.S2 = ((A.S1∩B.S2) ∪ (A.S2∩B.S1)) ∪ (A.S2∩B.S2)` is LEFT-associated
  exact Or.inl (Or.inr ⟨hcover, hB1⟩)


/-- S2 constructor for `coverSet f n ∧ B` from `coverSet.S1` and `B.S2`. -/
theorem sec4_coverAnd_mem_s2_of_cover_s1_B_s2
    (B : BSet X) (f : IntegrableRep S) (n : Nat) (x : X)
    (hcover : x ∈ (coverSet f n).S1) (hB2 : x ∈ B.S2) :
    x ∈ (sec4CoverAnd B f n).S2 := by
  unfold sec4CoverAnd
  exact Or.inl (Or.inl ⟨hcover, hB2⟩)


/-- S2 constructor for `coverSet f n ∧ B` from `coverSet.S2` and `B.S2`. -/
theorem sec4_coverAnd_mem_s2_of_cover_s2_B_s2
    (B : BSet X) (f : IntegrableRep S) (n : Nat) (x : X)
    (hcover : x ∈ (coverSet f n).S2) (hB2 : x ∈ B.S2) :
    x ∈ (sec4CoverAnd B f n).S2 := by
  unfold sec4CoverAnd
  exact Or.inr ⟨hcover, hB2⟩


/-! ## 2. Concrete telescope/estimate data -/

/--
Concrete data just below `Sec4CanonicalCoverFacts`.

The field `cover_value_eq_chi_on_Bs1` is the finite telescope:
on the `B.S1` branch, the canonical value equals the product of the
characteristic value of `coverSet f n ∧ B` and the value of `f`.

The branch `B.S2` is kept separate because, constructively, the direct
representative may be defined there without separately extracting an `f` value.
-/
structure Sec4CanonicalCoverChiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  domain : Sec4CCD_domain (S := S) B hB f hnn
  cover_case :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        x ∈ (coverSet f n).S1 ∨ x ∈ (coverSet f n).S2
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


/-! ## 3. Value cases from the concrete χ-data -/

/-- On `B.S1` and `coverSet.S1`, the canonical cover value is the value of `f`. -/
theorem sec4_cover_value_on_cover_s1_of_chiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverChiData (S := S) B hB f hnn) :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
      ∀ n : Nat, x ∈ (coverSet f n).S1 →
        sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n =
          (seriesSum_of_abs hfabs).sum := by
  intro x hxB hgenDom hgenabs hfDom hfabs n hcover
  let hχDom := T.cover_chi_dom x hgenDom hgenabs n
  let hχ := T.cover_chi_abs x hgenDom hgenabs n
  have hmem : x ∈ (sec4CoverAnd B f n).S1 :=
    sec4_coverAnd_mem_s1 B f n x hcover hxB
  have hvalid := (sec4CoverAnd_int B hB f n).valid x hχDom hχ
  have hχone :
      (seriesSum_of_abs hχ).sum = 1 :=
    hvalid.2.1 hmem (seriesSum_of_abs hχ)
  calc
    sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n =
        (seriesSum_of_abs hχ).sum * (seriesSum_of_abs hfabs).sum :=
      T.cover_value_eq_chi_on_Bs1
        x hxB hgenDom hgenabs hfDom hfabs n
    _ = 1 * (seriesSum_of_abs hfabs).sum := by rw [hχone]
    _ = (seriesSum_of_abs hfabs).sum := by ring


/-- On `B.S1` and `coverSet.S2`, the canonical cover value is zero. -/
theorem sec4_cover_value_on_cover_s2_of_chiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverChiData (S := S) B hB f hnn) :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
      ∀ n : Nat, x ∈ (coverSet f n).S2 →
        sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n = 0 := by
  intro x hxB hgenDom hgenabs hfDom hfabs n hcover
  let hχDom := T.cover_chi_dom x hgenDom hgenabs n
  let hχ := T.cover_chi_abs x hgenDom hgenabs n
  have hmem : x ∈ (sec4CoverAnd B f n).S2 :=
    sec4_coverAnd_mem_s2_of_cover_s2_B_s1 B f n x hcover hxB
  have hvalid := (sec4CoverAnd_int B hB f n).valid x hχDom hχ
  have hχzero :
      (seriesSum_of_abs hχ).sum = 0 :=
    hvalid.2.2 hmem (seriesSum_of_abs hχ)
  calc
    sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n =
        (seriesSum_of_abs hχ).sum * (seriesSum_of_abs hfabs).sum :=
      T.cover_value_eq_chi_on_Bs1
        x hxB hgenDom hgenabs hfDom hfabs n
    _ = 0 * (seriesSum_of_abs hfabs).sum := by rw [hχzero]
    _ = 0 := by ring


/-! ## 4. Build `Sec4CanonicalCoverFacts` -/

/--
Build the cover-facts package required by β-b1 from concrete χ telescope data.
-/
noncomputable def sec4_canonicalCoverFacts_of_chiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverChiData (S := S) B hB f hnn) :
    Sec4CanonicalCoverFacts (S := S) B hB f hnn := {
  domain := T.domain
  cover_case_s1 := by
    intro x hxB hgenDom hgenabs hfDom hfabs n
    exact T.cover_case x hgenDom hgenabs n
  cover_value_on_cover_s1 :=
    sec4_cover_value_on_cover_s1_of_chiData B hB f hnn T
  cover_value_on_cover_s2 :=
    sec4_cover_value_on_cover_s2_of_chiData B hB f hnn T
  cover_value_on_B_s2 := T.cover_value_on_B_s2
  cover_small_s2 := T.cover_small_s2
}


/-- Full value bridge from concrete χ telescope data. -/
noncomputable def sec4_genIBValueBridge_of_chiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverChiData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_coverFacts B hB f hnn
    (sec4_canonicalCoverFacts_of_chiData B hB f hnn T)


/-- Consistency theorem from concrete χ telescope data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_chiData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverChiData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_coverFacts C hC f hnn
    (sec4_canonicalCoverFacts_of_chiData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from concrete χ telescope data. -/
noncomputable def sec4_genIBConsistencyBridge_of_chiData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverChiData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_coverFacts C hC f hnn
    (sec4_canonicalCoverFacts_of_chiData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
