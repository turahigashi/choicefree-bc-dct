import Mathdemo.Internal.Sec4.CoverLimitData

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bα: cover estimates imply the final value bridge

D2b2a reduced the last analytic obligation to `Sec4GenIBCoverLimitData`.
This file performs one more conversion layer that is often easier to prove in
the final kernel pass: pointwise cover estimates.

Instead of constructing `TendstoHalf` directly, it is enough to provide, for
each modulus `k`, a tail index after which the cover values are `COF.Close k`
to the target.  Here we use the identity modulus `mod k = k`; the next chunk
may also feed this layer after reindexing its estimates.

Once `Sec4GenIBCoverEstimateData` is supplied, this file gives:

* `Sec4GenIBCoverLimitData`,
* `Sec4GenIBValueBridge`,
* the consistency theorem for already integrable complemented sets.

The only remaining proof after this file is the concrete estimate data:
finite telescope plus the two pointwise cover estimates.
-/

#check Sec4GenIBCoverLimitData
#check sec4_genIBValueBridge_of_coverLimitData
#check sec4_genRelIntegral_eq_relIntegral_of_coverLimitData
#check sec4_genIBConsistencyBridge_of_coverLimitData
#check COF.Close
#check RSeq.TendstoHalf

/-! ## 1. Constructing `TendstoHalf` from explicit close estimates -/

/--
A direct `TendstoHalf` constructor with identity modulus.

This avoids unfolding the internal definition of `COF.Close`.
-/
def sec4_tendstoHalf_of_close_self
    {u : Nat → R} {l : R}
    (hclose : ∀ k n : Nat, k ≤ n → COF.Close k (u n) l) :
    RSeq.TendstoHalf u l where
  mod := fun k => k
  close := by
    intro k n hn
    exact hclose k n hn


/--
Transport explicit close estimates along a pointwise equality of sequences.
-/
def sec4_tendstoHalf_of_close_self_congr
    {u v : Nat → R} {l : R}
    (hEq : ∀ n : Nat, v n = u n)
    (hclose : ∀ k n : Nat, k ≤ n → COF.Close k (u n) l) :
    RSeq.TendstoHalf v l :=
  sec4_tendstoHalf_of_close_self
    (fun k n hn => by
      rw [hEq n]
      exact hclose k n hn)


/-! ## 2. Estimate data for the final cover values -/

/--
Pointwise estimate data sufficient for the final `Sec4GenIBCoverLimitData`.

`coverValue` is intended to be the point value of
`χ_{coverSet f N ∧ B} · f`.

The `finite_telescope` field links it to the actual direct construction:
base plus the first `N+1` tail row values.

The two close fields are the final analytic estimates:
on `B.S1`, the cover values approach the point value of `f`; on `B.S2`, they
approach zero.
-/
structure Sec4GenIBCoverEstimateData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  coverValue :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)) →
      Nat → R
  domain :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)) →
      x ∈ B.S1 ∪ B.S2
  finite_telescope :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
      ∀ N : Nat,
        sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
          RSeq.partialSum
            (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) N =
        coverValue x hgenDom hgenabs N
  cover_close_s1 :
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
          (coverValue x hgenDom hgenabs n) (seriesSum_of_abs hfabs).sum
  cover_close_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
      ∀ k n : Nat, k ≤ n →
        COF.Close k (coverValue x hgenDom hgenabs n) 0


/-! ## 3. Estimate data gives cover-limit data -/

/-- The `B.S1` cover convergence extracted from close estimates. -/
noncomputable def sec4_cover_tendsto_s1_of_estimateData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverEstimateData (S := S) B hB f hnn)
    (x : X) (hxB : x ∈ B.S1)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs :
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)))
    (hfDom : f.MemAt x)
    (hfabs :
      RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n))) :
    RSeq.TendstoHalf
      (T.coverValue x hgenDom hgenabs) (seriesSum_of_abs hfabs).sum :=
  sec4_tendstoHalf_of_close_self
    (fun k n hn =>
      T.cover_close_s1 x hxB hgenDom hgenabs hfDom hfabs k n hn)


/-- The `B.S2` cover convergence extracted from close estimates. -/
noncomputable def sec4_cover_tendsto_s2_of_estimateData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverEstimateData (S := S) B hB f hnn)
    (x : X) (hxB : x ∈ B.S2)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs :
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    RSeq.TendstoHalf (T.coverValue x hgenDom hgenabs) 0 :=
  sec4_tendstoHalf_of_close_self
    (fun k n hn => T.cover_close_s2 x hxB hgenDom hgenabs k n hn)


/--
Build the exact D2b2a cover-limit data from pointwise close estimates.
-/
noncomputable def sec4_coverLimitData_of_estimateData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverEstimateData (S := S) B hB f hnn) :
    Sec4GenIBCoverLimitData (S := S) B hB f hnn := {
  coverValue := T.coverValue
  domain := T.domain
  finite_telescope := T.finite_telescope
  cover_tendsto_s1 := by
    intro x hxB hgenDom hgenabs hfDom hfabs
    exact sec4_cover_tendsto_s1_of_estimateData B hB f hnn T
      x hxB hgenDom hgenabs hfDom hfabs
  cover_tendsto_s2 := by
    intro x hxB hgenDom hgenabs
    exact sec4_cover_tendsto_s2_of_estimateData B hB f hnn T
      x hxB hgenDom hgenabs
}


/-! ## 4. Final bridge and consistency from estimate data -/

/-- Full value bridge from pointwise cover estimates. -/
noncomputable def sec4_genIBValueBridge_of_estimateData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverEstimateData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_coverLimitData B hB f hnn
    (sec4_coverLimitData_of_estimateData B hB f hnn T)


/-- Consistency theorem from pointwise cover estimates. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_estimateData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverEstimateData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_coverLimitData C hC f hnn
    (sec4_coverLimitData_of_estimateData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from pointwise cover estimates. -/
noncomputable def sec4_genIBConsistencyBridge_of_estimateData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverEstimateData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_coverLimitData C hC f hnn
    (sec4_coverLimitData_of_estimateData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
