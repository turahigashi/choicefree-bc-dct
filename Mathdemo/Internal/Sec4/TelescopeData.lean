import Mathdemo.Internal.Sec4.CoreData

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b2a-v2: cover-small estimate + final telescope interface

The b2b1 kernel response confirms that `Sec4CanonicalCoverCoreData` and its
downstream bridges passed with zero fixes and hardness 4.  This chunk now closes
the `cover_small_s2` branch from `coverSet.S2` and reduces the final core data
to the finite telescope / zero-branch witnesses.

What remains after this file is intended to be only:

* `cover_chi_abs`
* `cover_value_eq_chi_on_Bs1`
* `cover_value_on_B_s2`

The `cover_small_s2` field is supplied here by the `coverApart` estimate.
-/

#check Sec4CanonicalCoverCoreData
#check sec4_genIBValueBridge_of_coreData
#check sec4_genRelIntegral_eq_relIntegral_of_coreData
#check sec4_genIBConsistencyBridge_of_coreData
#check coverSet
#check coverApart
#check coverApart_t_le_halfPow
#check lemma35_halfPow_antitone
#check COF.Close
#check RepNonneg

/-! ## 1. The coverSet.S2 smallness branch -/

/--
If `x` is in the negative side of `coverSet f n`, then the value of `f` at
`x` is smaller than the cover threshold, hence `0` is `COF.Close k` to `f(x)`
whenever `k ≤ n`.

This is the numerical branch needed in `close_s1`.
-/
theorem sec4_cover_small_s2_from_coverSet
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    ∀ x : X,
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
      ∀ k n : Nat, k ≤ n →
        x ∈ (coverSet f n).S2 →
          COF.Close k 0 (seriesSum_of_abs hfabs).sum := by
  intro x hfDom hfabs k n hkn hcover
  -- `coverSet f n` is the level set of `f` at `(coverApart f n).t`.
  -- Its S2 side provides a signed value witness and a strict upper bound.
  rcases hcover with ⟨_hfDom0, _habs0, hx0, hlt0⟩
  have hx_eq : hx0.sum = (seriesSum_of_abs hfabs).sum :=
    seriesSum_unique hx0 (seriesSum_of_abs hfabs)
  rw [hx_eq] at hlt0
  have hnnx : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  have hthreshold :
      Le (coverApart f n).t (COF.halfPow k) :=
    le_trans (coverApart_t_le_halfPow f n)
      (lemma35_halfPow_antitone (R := R) hkn)
  have hsmall :
      COF.lt (seriesSum_of_abs hfabs).sum (COF.halfPow k) :=
    BishopC.lt_of_lt_of_le hlt0 hthreshold
  unfold COF.Close COF_core.Close
  rw [show (0 : R) - (seriesSum_of_abs hfabs).sum =
        - (seriesSum_of_abs hfabs).sum by ring]
  rw [COFO.abs_neg, COFO.abs_of_nonneg hnnx]
  exact hsmall


/-! ## 2. The remaining telescope data -/

/--
The final telescope data after the `coverSet.S2` estimate is discharged.

This is deliberately only the part that cannot be obtained from the numerical
coverApart estimate alone.
-/
structure Sec4CanonicalCoverTelescopeData
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


/--
Build the b2b1 core package from telescope data.

The only nontrivial field supplied here is `cover_small_s2`, obtained from
`sec4_cover_small_s2_from_coverSet`.
-/
noncomputable def sec4_coreData_of_telescopeData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverTelescopeData (S := S) B hB f hnn) :
    Sec4CanonicalCoverCoreData (S := S) B hB f hnn := {
  cover_chi_dom := T.cover_chi_dom
  cover_chi_abs := T.cover_chi_abs
  cover_value_eq_chi_on_Bs1 := T.cover_value_eq_chi_on_Bs1
  cover_value_on_B_s2 := T.cover_value_on_B_s2
  cover_small_s2 := by
    intro x hxB hgenDom hgenabs hfDom hfabs k n hkn hcover
    exact sec4_cover_small_s2_from_coverSet (S := S) f hnn
      x hfDom hfabs k n hkn hcover
}


/-! ## 3. Final bridges from telescope data -/

/-- Full value bridge from the remaining telescope data. -/
noncomputable def sec4_genIBValueBridge_of_telescopeData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverTelescopeData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_coreData B hB f hnn
    (sec4_coreData_of_telescopeData B hB f hnn T)


/-- Consistency theorem from the remaining telescope data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_telescopeData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverTelescopeData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_coreData C hC f hnn
    (sec4_coreData_of_telescopeData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from the remaining telescope data. -/
noncomputable def sec4_genIBConsistencyBridge_of_telescopeData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverTelescopeData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_coreData C hC f hnn
    (sec4_coreData_of_telescopeData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
