import Mathdemo.Internal.Sec4.TelescopeData

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b3: finite telescope assembly

The b2b2a kernel response confirms that the `coverApart` estimate is complete.
Only the finite pointwise telescope remains.

This file proves the algebraic assembly part: once the base row, every tail
row, and the finite characteristic telescope are supplied, we obtain
`Sec4CanonicalCoverTelescopeData`, hence the final value bridge and
consistency theorem.

The genuinely remaining kernel task is now the construction of
`Sec4CanonicalCoverLayerTelescopeData`.
-/

#check Sec4CanonicalCoverTelescopeData
#check sec4_genIBValueBridge_of_telescopeData
#check sec4_genRelIntegral_eq_relIntegral_of_telescopeData
#check sec4_genIBConsistencyBridge_of_telescopeData
#check sec4_canonicalCoverValue
#check sec4_genIB_baseValue
#check sec4_genIB_tailRowSeq

/-! ## 1. Elementary finite-sum algebra -/

/-- Pointwise congruence for finite partial sums. -/
theorem sec4_partialSum_congr
    (u v : Nat → R)
    (h : ∀ k : Nat, u k = v k) :
    ∀ n : Nat, RSeq.partialSum u n = RSeq.partialSum v n := by
  intro n
  induction n with
  | zero =>
      exact h 0
  | succ n ih =>
      change RSeq.partialSum u n + u (n + 1) =
        RSeq.partialSum v n + v (n + 1)
      rw [ih, h (n + 1)]


/-- Finite partial sums commute with multiplication on the right. -/
theorem sec4_partialSum_mul_right
    (u : Nat → R) (c : R) :
    ∀ n : Nat,
      RSeq.partialSum (fun k => u k * c) n =
        RSeq.partialSum u n * c := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        RSeq.partialSum (fun k => u k * c) n + u (n + 1) * c =
          (RSeq.partialSum u n + u (n + 1)) * c
      rw [ih]
      ring


/-- The finite partial sum of the zero sequence is zero. -/
theorem sec4_partialSum_zero :
    ∀ n : Nat, RSeq.partialSum (fun _ : Nat => (0 : R)) n = 0 := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change RSeq.partialSum (fun _ : Nat => (0 : R)) n + 0 = 0
      rw [ih]
      ring


/-! ## 2. Layer telescope data -/

/--
Concrete layer-wise data for the final finite telescope.

* `base_chi_abs` is the characteristic witness for `coverSet f 0 ∧ B`;
* `term_chi_abs` is the characteristic witness for the layer
  `(coverSet f (k+1) ∧ B) - (coverSet f k ∧ B)`;
* `cover_chi_abs` is the characteristic witness for `coverSet f n ∧ B`;
* `base_value_s1` and `row_value_s1` identify the actual row values with
  characteristic value times the value of `f`;
* `chi_telescope_s1` is the pure finite characteristic identity;
* the two `*_s2` fields say the base and every tail row vanish on `B.S2`.
-/
structure Sec4CanonicalCoverLayerTelescopeData
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
              (cover_chi_dom x hgenDom hgenabs 0) m))
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
  base_value_s1 :
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
            (base_chi_abs x hgenDom hgenabs)).sum *
            (seriesSum_of_abs hfabs).sum
  row_value_s1 :
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
            (term_chi_abs k x hgenDom hgenabs)).sum *
            (seriesSum_of_abs hfabs).sum
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
          (cover_chi_abs x hgenDom hgenabs n)).sum
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


/-! ## 3. The actual final telescope equations -/

/-- The `B.S1` telescope equation from layer data. -/
theorem sec4_cover_value_eq_chi_on_Bs1_of_layerTelescopeData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeData (S := S) B hB f hnn) :
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
            (T.cover_chi_abs x hgenDom hgenabs n)).sum *
            (seriesSum_of_abs hfabs).sum := by
  intro x hxB hgenDom hgenabs hfDom hfabs n
  let baseχ : R :=
    (seriesSum_of_abs (T.base_chi_abs x hgenDom hgenabs)).sum
  let termχ : Nat → R :=
    fun k =>
      (seriesSum_of_abs (T.term_chi_abs k x hgenDom hgenabs)).sum
  let coverχ : R :=
    (seriesSum_of_abs (T.cover_chi_abs x hgenDom hgenabs n)).sum
  let fval : R := (seriesSum_of_abs hfabs).sum
  have hrow :
      RSeq.partialSum
        (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) n =
        RSeq.partialSum (fun k => termχ k * fval) n :=
    sec4_partialSum_congr
      (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs)
      (fun k => termχ k * fval)
      (fun k => T.row_value_s1
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
          rw [T.base_value_s1 x hxB hgenDom hgenabs hfDom hfabs]
    _ = baseχ * fval + RSeq.partialSum (fun k => termχ k * fval) n := by
          rw [hrow]
    _ = baseχ * fval + RSeq.partialSum termχ n * fval := by
          rw [hmul]
    _ = (baseχ + RSeq.partialSum termχ n) * fval := by
          ring
    _ = coverχ * fval := by
          rw [hχ]


/-- The `B.S2` zero equation from layer data. -/
theorem sec4_cover_value_on_Bs2_of_layerTelescopeData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeData (S := S) B hB f hnn) :
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


/-! ## 4. Final bridge from layer telescope data -/

/-- The final `Sec4CanonicalCoverTelescopeData` from layer telescope data. -/
noncomputable def sec4_telescopeData_of_layerTelescopeData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeData (S := S) B hB f hnn) :
    Sec4CanonicalCoverTelescopeData (S := S) B hB f hnn := {
  cover_chi_dom := T.cover_chi_dom
  cover_chi_abs := T.cover_chi_abs
  cover_value_eq_chi_on_Bs1 :=
    sec4_cover_value_eq_chi_on_Bs1_of_layerTelescopeData B hB f hnn T
  cover_value_on_B_s2 :=
    sec4_cover_value_on_Bs2_of_layerTelescopeData B hB f hnn T
}


/-- Full value bridge from layer telescope data. -/
noncomputable def sec4_genIBValueBridge_of_layerTelescopeData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_telescopeData B hB f hnn
    (sec4_telescopeData_of_layerTelescopeData B hB f hnn T)


/-- Consistency theorem from layer telescope data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_layerTelescopeData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_telescopeData C hC f hnn
    (sec4_telescopeData_of_layerTelescopeData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from layer telescope data. -/
noncomputable def sec4_genIBConsistencyBridge_of_layerTelescopeData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerTelescopeData
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_telescopeData C hC f hnn
    (sec4_telescopeData_of_layerTelescopeData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
