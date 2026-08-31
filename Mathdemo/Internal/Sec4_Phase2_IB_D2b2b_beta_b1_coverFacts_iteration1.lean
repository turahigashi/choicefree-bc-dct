import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_a_canonicalCoverValue_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b1: canonical cover facts imply final close data

D2b2bβ-a fixed

`coverValue N = baseValue + partialSum tailRows N`

so that the finite telescope field is definitional.  This file pushes the last
three fields to a concrete pointwise package:

* domain membership in `B.S1 ∪ B.S2`;
* the canonical cover value on `B.S1`, split by whether
  `x ∈ (coverSet f n).S1` or `x ∈ (coverSet f n).S2`;
* the canonical cover value on `B.S2`;
* the single numerical estimate needed in the `coverSet.S2` branch.

From this package we build `Sec4GenIBCanonicalCloseData`, hence the value
bridge and consistency theorem.  The remaining kernel-loop chunk can focus on
the finite telescope equality
`canonicalCoverValue = χ_{coverSet f n ∧ B}·f` and the `coverApart` estimate.
-/

#check Sec4GenIBCanonicalCloseData
#check Sec4GenIBCanonicalCloseData.mk
#check sec4_genIBValueBridge_of_canonicalCloseData
#check sec4_genRelIntegral_eq_relIntegral_of_canonicalCloseData
#check sec4_genIBConsistencyBridge_of_canonicalCloseData
#check sec4_canonicalCoverValue
#check coverSet
#check COF.Close
#check halfPow_pos

/-! ## 1. A tiny `COF.Close` helper -/

/-- Reflexivity of `COF.Close`. -/
theorem sec4_Close_refl (k : Nat) (z : R) : COF.Close k z z := by
  unfold COF.Close COF_core.Close
  rw [show z - z = (0 : R) from by ring, COFO.abs_zero]
  exact halfPow_pos k


/-! ## 2. Final pointwise facts for the canonical cover value -/

/--
Concrete pointwise facts sufficient for the final close estimates.

`cover_case_s1` is the only domain/case data needed in the `B.S1` branch.
The equality fields are intentionally split into the three cases which occur
in the final proof.

The field `cover_small_s2` is the exact `coverApart` numerical estimate:
when `x∈B.S1` but `x∈(coverSet f n).S2`, the canonical cover value is zero and
it is `COF.Close k` to the value of `f`, for `k≤n`.
-/
structure Sec4CanonicalCoverFacts
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  domain : Sec4CCD_domain (S := S) B hB f hnn
  cover_case_s1 :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
      ∀ n : Nat, x ∈ (coverSet f n).S1 ∨ x ∈ (coverSet f n).S2
  cover_value_on_cover_s1 :
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
          (seriesSum_of_abs hfabs).sum
  cover_value_on_cover_s2 :
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
        sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n = 0
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


/-! ## 3. Close data from the pointwise cover facts -/

/-- `B.S1` close estimate from canonical cover facts. -/
theorem sec4_close_s1_of_canonicalCoverFacts
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverFacts (S := S) B hB f hnn) :
    Sec4CCD_close_s1 (S := S) B hB f hnn := by
  intro x hxB hgenDom hgenabs hfDom hfabs k n hn
  cases T.cover_case_s1 x hxB hgenDom hgenabs hfDom hfabs n with
  | inl hcover1 =>
      rw [T.cover_value_on_cover_s1
        x hxB hgenDom hgenabs hfDom hfabs n hcover1]
      exact sec4_Close_refl k (seriesSum_of_abs hfabs).sum
  | inr hcover2 =>
      rw [T.cover_value_on_cover_s2
        x hxB hgenDom hgenabs hfDom hfabs n hcover2]
      exact T.cover_small_s2
        x hxB hgenDom hgenabs hfDom hfabs k n hn hcover2


/-- `B.S2` close estimate from canonical cover facts. -/
theorem sec4_close_s2_of_canonicalCoverFacts
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverFacts (S := S) B hB f hnn) :
    Sec4CCD_close_s2 (S := S) B hB f hnn := by
  intro x hxB hgenDom hgenabs k n hn
  rw [T.cover_value_on_B_s2 x hxB hgenDom hgenabs n]
  exact sec4_Close_refl k (0 : R)


/--
Build the final canonical close data from pointwise canonical cover facts.
-/
noncomputable def sec4_canonicalCloseData_of_coverFacts
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverFacts (S := S) B hB f hnn) :
    Sec4GenIBCanonicalCloseData (S := S) B hB f hnn :=
  Sec4GenIBCanonicalCloseData.mk
    (domain := T.domain)
    (close_s1 := sec4_close_s1_of_canonicalCoverFacts B hB f hnn T)
    (close_s2 := sec4_close_s2_of_canonicalCoverFacts B hB f hnn T)


/-! ## 4. Final bridge and consistency from canonical cover facts -/

/-- Full value bridge from pointwise canonical cover facts. -/
noncomputable def sec4_genIBValueBridge_of_coverFacts
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverFacts (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_canonicalCloseData B hB f hnn
    (sec4_canonicalCloseData_of_coverFacts B hB f hnn T)


/-- Consistency theorem from pointwise canonical cover facts. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_coverFacts
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverFacts
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_canonicalCloseData C hC f hnn
    (sec4_canonicalCloseData_of_coverFacts
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from pointwise canonical cover facts. -/
noncomputable def sec4_genIBConsistencyBridge_of_coverFacts
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverFacts
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_canonicalCloseData C hC f hnn
    (sec4_canonicalCloseData_of_coverFacts
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
