import Mathdemo.Internal.Sec4.PointDecomp

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b1: row-limit data → `Sec4GenIBValueBridge`

D2a proved the point decomposition

`genIB value = base value + tail rows value`.

This file packages the remaining telescope/limit computation into one
light-weight `Prop` structure.  If the row sums of the tail converge to the
expected residual value, then the full `Sec4GenIBValueBridge` follows
immediately.

The next chunk should prove `Sec4GenIBRowsLimitData` by the finite telescope
`base + Σ_{k<N} χ_{D_k}·f = χ_{A_N∧B}·f` and the limit of the cover sets.
-/

#check Sec4GenIBValueBridge
#check Sec4GenIBConsistencyBridge
#check sec4_genIB_value_eq_base_add_tailRows
#check sec4_genIB_tailPointBridge
#check sec4_genRelIntegral_eq_relIntegral_of_valueBridge
#check sec4_genIBConsistencyBridge_of_valueBridge
#check seriesSum_unique

/-! ## 1. Stable names for the base value and tail row series -/

/-- The base point value extracted from `hgenabs`. -/
noncomputable def sec4_genIB_baseValue
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) : R :=
  (seriesSum_of_abs
    (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenDom hgenabs)).sum


/-- The tail row-value sequence associated to the D2a point bridge. -/
noncomputable def sec4_genIB_tailRowSeq
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    Nat → R :=
  fun k =>
    ((sec4_genIB_tailPointBridge B hB f hnn x hgenDom hgenabs).rowVal k).sum


/-- The tail row series supplied by D2a, with a stable sequence name. -/
noncomputable def sec4_genIB_tailRows
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    RSeq.SeriesSum
      (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) :=
  (sec4_genIB_tailPointBridge B hB f hnn x hgenDom hgenabs).rows


/--
D2a's point decomposition rewritten in terms of the stable names above.
-/
theorem sec4_genIB_value_eq_baseValue_add_tailRows
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    (seriesSum_of_abs hgenabs).sum =
      sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
      (sec4_genIB_tailRows B hB f hnn x hgenDom hgenabs).sum := by
  unfold sec4_genIB_baseValue sec4_genIB_tailRows
  simpa [sec4_genIB_tailRowSeq] using
    sec4_genIB_value_eq_base_add_tailRows B hB f hnn x hgenDom hgenabs


/-! ## 2. The remaining row-limit data -/

/--
The remaining pointwise telescope/limit obligation for `genIB`.

For `x ∈ B.S1`, the tail rows must converge to
`f(x) - base(x)`.  For `x ∈ B.S2`, they must converge to `0 - base(x)`.
Together with D2a's decomposition this is exactly the value bridge.
-/
structure Sec4GenIBRowsLimitData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  domain :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      RSeq.SeriesSum
        (fun n => COF.abs
          ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)) →
      x ∈ B.S1 ∪ B.S2
  rows_tendsto_s1 :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
      ∀ hfDom : f.MemAt x,
      ∀ hfabs :
        RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)),
      RSeq.TendstoHalf
        (RSeq.partialSum
          (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs))
        ((seriesSum_of_abs hfabs).sum -
          sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs)
  rows_tendsto_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)),
      RSeq.TendstoHalf
        (RSeq.partialSum
          (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs))
        (0 - sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs)


/-! ## 3. Value bridge from row-limit data -/

/-- The `B.S1` value equation from row-limit data. -/
theorem sec4_genIB_value_s1_of_rowsLimit
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBRowsLimitData (S := S) B hB f hnn)
    (x : X) (hxB : x ∈ B.S1)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n)))
    (hfDom : f.MemAt x)
    (hfabs : RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n))) :
    (seriesSum_of_abs hgenabs).sum = (seriesSum_of_abs hfabs).sum := by
  let htarget : RSeq.SeriesSum
      (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) := {
    sum := (seriesSum_of_abs hfabs).sum -
      sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs
    tends := T.rows_tendsto_s1 x hxB hgenDom hgenabs hfDom hfabs
  }
  have hrows :
      (sec4_genIB_tailRows B hB f hnn x hgenDom hgenabs).sum =
        (seriesSum_of_abs hfabs).sum -
          sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs :=
    seriesSum_unique
      (sec4_genIB_tailRows B hB f hnn x hgenDom hgenabs)
      htarget
  calc
    (seriesSum_of_abs hgenabs).sum =
        sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
          (sec4_genIB_tailRows B hB f hnn x hgenDom hgenabs).sum :=
      sec4_genIB_value_eq_baseValue_add_tailRows
        B hB f hnn x hgenDom hgenabs
    _ = sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
          ((seriesSum_of_abs hfabs).sum -
            sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs) := by
      rw [hrows]
    _ = (seriesSum_of_abs hfabs).sum := by ring


/-- The `B.S2` value equation from row-limit data. -/
theorem sec4_genIB_value_s2_of_rowsLimit
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBRowsLimitData (S := S) B hB f hnn)
    (x : X) (hxB : x ∈ B.S2)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    (seriesSum_of_abs hgenabs).sum = 0 := by
  let htarget : RSeq.SeriesSum
      (sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs) := {
    sum := 0 - sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs
    tends := T.rows_tendsto_s2 x hxB hgenDom hgenabs
  }
  have hrows :
      (sec4_genIB_tailRows B hB f hnn x hgenDom hgenabs).sum =
        0 - sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs :=
    seriesSum_unique
      (sec4_genIB_tailRows B hB f hnn x hgenDom hgenabs)
      htarget
  calc
    (seriesSum_of_abs hgenabs).sum =
        sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
          (sec4_genIB_tailRows B hB f hnn x hgenDom hgenabs).sum :=
      sec4_genIB_value_eq_baseValue_add_tailRows
        B hB f hnn x hgenDom hgenabs
    _ = sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs +
          (0 - sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs) := by
      rw [hrows]
    _ = 0 := by ring


/--
Build the full value bridge from row-limit data.
-/
noncomputable def sec4_genIBValueBridge_of_rowsLimitData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBRowsLimitData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn := {
  domain := T.domain
  value_s1 := by
    intro x hxB hgenDom hgenabs hfDom hfabs
    exact sec4_genIB_value_s1_of_rowsLimit
      B hB f hnn T x hxB hgenDom hgenabs hfDom hfabs
  value_s2 := by
    intro x hxB hgenDom hgenabs
    exact sec4_genIB_value_s2_of_rowsLimit
      B hB f hnn T x hxB hgenDom hgenabs
}


/-! ## 4. Consistency from row-limit data -/

/--
Consistency with the previous relative integral for an integrable set, from the
row-limit telescope data.
-/
theorem sec4_genRelIntegral_eq_relIntegral_of_rowsLimitData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBRowsLimitData (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_valueBridge C hC f hnn
    (sec4_genIBValueBridge_of_rowsLimitData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from row-limit data. -/
noncomputable def sec4_genIBConsistencyBridge_of_rowsLimitData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBRowsLimitData (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn := {
  integral_eq := sec4_genRelIntegral_eq_relIntegral_of_rowsLimitData C hC f hnn T
}


end BishopC
