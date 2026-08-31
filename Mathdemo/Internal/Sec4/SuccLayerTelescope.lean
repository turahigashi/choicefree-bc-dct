import Mathdemo.Internal.Sec4.LayerTelescope

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b4: corrected successor-index telescope interface

The b2b3 kernel response confirmed that the algebraic telescope assembly
passed.  During the final construction, however, the `partialSum` convention
matters:

```
RSeq.partialSum u 0 = u 0
```

so

```
base + partialSum rows n
```

corresponds to the cover set at level `n+1`, not at level `n`.

This file introduces the corrected successor-index telescope data and carries
it all the way to the final value bridge and consistency theorem.  The
remaining atomic work is now the same layer telescope as before, but with
`cover_chi_abs_succ` for `coverSet f (n+1) ∧ B`.

No extra choice principle is used; all fields are still meant to be supplied by
the final point-level telescope computation.
-/

#check Sec4CanonicalCoverLayerTelescopeData
#check sec4_genIBValueBridge_of_telescopeData
#check sec4_genRelIntegral_eq_relIntegral_of_telescopeData
#check sec4_genIBConsistencyBridge_of_telescopeData
#check sec4_cover_small_s2_from_coverSet
#check sec4_canonicalCoverValue
#check prop_4_2_chi_f_rep_value

/-! ## 1. Successor-index layer telescope data -/

/--
Corrected layer telescope data.

`cover_chi_abs_succ x hgenabs n` is the characteristic abs witness for
`coverSet f (n+1) ∧ B`, matching the convention that
`partialSum rows n` includes rows `0, …, n`.
-/
structure Sec4CanonicalCoverLayerTelescopeDataSucc
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  cover_chi_dom_succ :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        (sec4CoverAnd_int B hB f (n + 1)).rep.MemAt x
  cover_chi_abs_succ :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        RSeq.SeriesSum
          (fun m => COF.abs
            ((sec4CoverAnd_int B hB f (n + 1)).rep.valueAt x
              (cover_chi_dom_succ x hgenDom hgenabs n) m))
  base_chi_dom :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        (sec4CoverAnd_int B hB f 0).rep.MemAt x
  base_chi_abs :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        RSeq.SeriesSum
          (fun m => COF.abs
            ((sec4CoverAnd_int B hB f 0).rep.valueAt x
              (base_chi_dom x hgenDom hgenabs) m))
  term_chi_dom :
    ∀ k : Nat, ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        (sec4CoverDiff_int B hB f k).rep.MemAt x
  term_chi_abs :
    ∀ k : Nat, ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        RSeq.SeriesSum
          (fun m => COF.abs
            ((sec4CoverDiff_int B hB f k).rep.valueAt x
              (term_chi_dom k x hgenDom hgenabs) m))
  chi_telescope_s1 :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        (seriesSum_of_abs (base_chi_abs x hgenDom hgenabs)).sum +
          RSeq.partialSum
            (fun k =>
              (seriesSum_of_abs
                (term_chi_abs k x hgenDom hgenabs)).sum) n =
        (seriesSum_of_abs
          (cover_chi_abs_succ x hgenDom hgenabs n)).sum
  base_value_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs = 0
  row_value_s2 :
    ∀ k : Nat, ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs k = 0


/-! ## 2. Base and row values on `B.S1` -/

/-- Base row value from `prop_4_2_chi_f_rep_value`. -/
theorem sec4_baseValue_s1_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
        sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs =
          (seriesSum_of_abs
            (T.base_chi_abs x hgenDom hgenabs)).sum *
            (seriesSum_of_abs hfabs).sum := by
  intro x hxB hgenDom hgenabs hfDom hfabs
  let hflatDom := sec4_genIB_baseMemAt B hB f hnn hgenDom
  let hχDom := T.base_chi_dom x hgenDom hgenabs
  let hflat :=
    sec4_genIB_baseAbs_of_abs B hB f hnn x hgenDom hgenabs
  have hval :
      (seriesSum_of_abs hflat).sum =
        (seriesSum_of_abs (T.base_chi_abs x hgenDom hgenabs)).sum *
          (seriesSum_of_abs hfabs).sum :=
    prop_4_2_chi_f_rep_value
      (sec4CoverAnd B f 0)
      (sec4CoverAnd_int B hB f 0)
      f hnn (x := x) hflatDom hχDom hfDom
      hflat (T.base_chi_abs x hgenDom hgenabs) hfabs
  simpa [sec4_genIB_baseValue, hflat] using hval


/-- Tail row value from `prop_4_2_chi_f_rep_value`. -/
theorem sec4_rowValue_s1_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    ∀ k : Nat, ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun m => COF.abs (f.valueAt x hfDom m)),
        sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs k =
          (seriesSum_of_abs
            (T.term_chi_abs k x hgenDom hgenabs)).sum *
            (seriesSum_of_abs hfabs).sum := by
  intro k x hxB hgenDom hgenabs hfDom hfabs
  let PB := sec4_genIB_tailPointBridge B hB f hnn x hgenDom hgenabs
  let hflatDom := PB.rowDom k
  let hχDom := T.term_chi_dom k x hgenDom hgenabs
  let hflat := PB.rowAbs k
  have hrow :
      sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs k =
        (seriesSum_of_abs hflat).sum := by
    dsimp [sec4_genIB_tailRowSeq, hflat, PB]
    exact seriesSum_unique
      ((sec4_genIB_tailPointBridge
        B hB f hnn x hgenDom hgenabs).rowVal k)
      (seriesSum_of_abs ((sec4_genIB_tailPointBridge
        B hB f hnn x hgenDom hgenabs).rowAbs k))
  have hval :
      (seriesSum_of_abs hflat).sum =
        (seriesSum_of_abs
          (T.term_chi_abs k x hgenDom hgenabs)).sum *
          (seriesSum_of_abs hfabs).sum :=
    prop_4_2_chi_f_rep_value
      (sec4CoverDiff B f k)
      (sec4CoverDiff_int B hB f k)
      f hnn (x := x) hflatDom hχDom hfDom
      hflat (T.term_chi_abs k x hgenDom hgenabs) hfabs
  exact hrow.trans hval


/-! ## 3. Successor-index telescope values -/

/-- Canonical value equals the successor cover characteristic times `f` on `B.S1`. -/
theorem sec4_cover_value_eq_chiSucc_on_Bs1
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
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
            (T.cover_chi_abs_succ x hgenDom hgenabs n)).sum *
            (seriesSum_of_abs hfabs).sum := by
  intro x hxB hgenDom hgenabs hfDom hfabs n
  let baseχ : R :=
    (seriesSum_of_abs (T.base_chi_abs x hgenDom hgenabs)).sum
  let termχ : Nat → R :=
    fun k =>
      (seriesSum_of_abs (T.term_chi_abs k x hgenDom hgenabs)).sum
  let coverχ : R :=
    (seriesSum_of_abs
      (T.cover_chi_abs_succ x hgenDom hgenabs n)).sum
  let fval : R := (seriesSum_of_abs hfabs).sum
  have hrow :
      RSeq.partialSum
        (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) n =
        RSeq.partialSum (fun k => termχ k * fval) n :=
    sec4_partialSum_congr
      (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs)
      (fun k => termχ k * fval)
      (fun k => sec4_rowValue_s1_of_succLayerData B hB f hnn T
        k x hxB hgenDom hgenabs hfDom hfabs)
      n
  have hmul :
      RSeq.partialSum (fun k => termχ k * fval) n =
        RSeq.partialSum termχ n * fval :=
    sec4_partialSum_mul_right termχ fval n
  have hχ :
      baseχ + RSeq.partialSum termχ n = coverχ :=
    T.chi_telescope_s1 x hxB hgenDom hgenabs n
  calc
    sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n
        = sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
            RSeq.partialSum
              (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) n := by
          rfl
    _ = baseχ * fval +
            RSeq.partialSum
              (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) n := by
          rw [sec4_baseValue_s1_of_succLayerData
            B hB f hnn T x hxB hgenDom hgenabs hfDom hfabs]
    _ = baseχ * fval + RSeq.partialSum (fun k => termχ k * fval) n := by
          rw [hrow]
    _ = baseχ * fval + RSeq.partialSum termχ n * fval := by
          rw [hmul]
    _ = (baseχ + RSeq.partialSum termχ n) * fval := by
          ring
    _ = coverχ * fval := by
          rw [hχ]


/-- Canonical value is zero on `B.S2`. -/
theorem sec4_cover_value_on_Bs2_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n = 0 := by
  intro x hxB hgenDom hgenabs n
  have hrow :
      RSeq.partialSum
        (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) n =
        RSeq.partialSum (fun _ : Nat => (0 : R)) n :=
    sec4_partialSum_congr
      (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs)
      (fun _ : Nat => (0 : R))
      (fun k => T.row_value_s2 k x hxB hgenDom hgenabs)
      n
  calc
    sec4_canonicalCoverValue B hB f hnn x hgenDom hgenabs n
        = sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
            RSeq.partialSum
              (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) n := by
          rfl
    _ = 0 + RSeq.partialSum
            (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) n := by
          rw [T.base_value_s2 x hxB hgenDom hgenabs]
    _ = 0 + RSeq.partialSum (fun _ : Nat => (0 : R)) n := by
          rw [hrow]
    _ = 0 := by
          rw [sec4_partialSum_zero n]
          ring


/-! ## 4. Domain and close estimates -/

/-- Domain membership in `B.S1 ∪ B.S2` from the successor cover witness. -/
theorem sec4_domain_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    Sec4CCD_domain (S := S) B hB f hnn := by
  intro x hgenDom hgenabs
  let hχDom := T.cover_chi_dom_succ x hgenDom hgenabs 0
  let hχ := T.cover_chi_abs_succ x hgenDom hgenabs 0
  have hvalid :=
    (sec4CoverAnd_int B hB f (0 + 1)).valid x hχDom hχ
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


/-- `B.S1` close estimate from successor-index layer data. -/
theorem sec4_close_s1_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    Sec4CCD_close_s1 (S := S) B hB f hnn := by
  intro x hxB hgenDom hgenabs hfDom hfabs k n hkn
  let hχDom := T.cover_chi_dom_succ x hgenDom hgenabs n
  let hχ := T.cover_chi_abs_succ x hgenDom hgenabs n
  have hvalid :=
    (sec4CoverAnd_int B hB f (n + 1)).valid x hχDom hχ
  cases hvalid.1 with
  | inl hAnd1 =>
      unfold sec4CoverAnd at hAnd1
      have hχone :
          (seriesSum_of_abs hχ).sum = 1 :=
        hvalid.2.1 hAnd1 (seriesSum_of_abs hχ)
      have hval := sec4_cover_value_eq_chiSucc_on_Bs1
        B hB f hnn T x hxB hgenDom hgenabs hfDom hfabs n
      rw [hval, hχone]
      change COF.Close k ((1 : R) * (seriesSum_of_abs hfabs).sum)
        (seriesSum_of_abs hfabs).sum
      have hone : (1 : R) * (seriesSum_of_abs hfabs).sum =
          (seriesSum_of_abs hfabs).sum := by ring
      rw [hone]
      exact sec4_Close_refl k (seriesSum_of_abs hfabs).sum
  | inr hAnd2 =>
      unfold sec4CoverAnd at hAnd2
      rcases hAnd2 with h12 | h3
      · rcases h12 with h1 | h2
        · exfalso
          exact B.disj x hxB x h1.2 rfl
        · have hχzero :
              (seriesSum_of_abs hχ).sum = 0 :=
            hvalid.2.2 (Or.inl (Or.inr h2)) (seriesSum_of_abs hχ)
          have hval := sec4_cover_value_eq_chiSucc_on_Bs1
            B hB f hnn T x hxB hgenDom hgenabs hfDom hfabs n
          rw [hval, hχzero]
          change COF.Close k ((0 : R) * (seriesSum_of_abs hfabs).sum)
            (seriesSum_of_abs hfabs).sum
          have hzero : (0 : R) * (seriesSum_of_abs hfabs).sum = 0 := by ring
          rw [hzero]
          exact sec4_cover_small_s2_from_coverSet (S := S) f hnn
            x hfDom hfabs k (n + 1)
              (Nat.le_trans hkn (Nat.le_succ n)) h2.1
      · exfalso
        exact B.disj x hxB x h3.2 rfl


/-- `B.S2` close estimate from successor-index layer data. -/
theorem sec4_close_s2_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    Sec4CCD_close_s2 (S := S) B hB f hnn := by
  intro x hxB hgenDom hgenabs k n hkn
  rw [sec4_cover_value_on_Bs2_of_succLayerData
    B hB f hnn T x hxB hgenDom hgenabs n]
  exact sec4_Close_refl k (0 : R)


/-! ## 5. Final bridge and consistency from corrected successor data -/

/-- Canonical close data from corrected successor-index layer telescope data. -/
noncomputable def sec4_canonicalCloseData_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    Sec4GenIBCanonicalCloseData (S := S) B hB f hnn :=
  Sec4GenIBCanonicalCloseData.mk
    (domain := sec4_domain_of_succLayerData B hB f hnn T)
    (close_s1 := sec4_close_s1_of_succLayerData B hB f hnn T)
    (close_s2 := sec4_close_s2_of_succLayerData B hB f hnn T)


/-- Full value bridge from corrected successor-index layer telescope data. -/
noncomputable def sec4_genIBValueBridge_of_succLayerData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_canonicalCloseData B hB f hnn
    (sec4_canonicalCloseData_of_succLayerData B hB f hnn T)


/-- Consistency theorem from corrected successor-index layer telescope data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_succLayerData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_canonicalCloseData C hC f hnn
    (sec4_canonicalCloseData_of_succLayerData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from corrected successor-index layer telescope data. -/
noncomputable def sec4_genIBConsistencyBridge_of_succLayerData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeDataSucc
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_canonicalCloseData C hC f hnn
    (sec4_canonicalCloseData_of_succLayerData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
