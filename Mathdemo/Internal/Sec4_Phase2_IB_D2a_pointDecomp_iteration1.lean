import Mathdemo.Internal.Sec4_Phase2_IB_D1_valueConsistency_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2a: base/tail point decomposition for `genIB_rep_from_measurable`

D1 reduced consistency to `Sec4GenIBValueBridge`.  This file starts the
actual bridge construction by exposing the point-value decomposition of

`genIB_rep_from_measurable B hB f hnn`

as

`base + tail`, where

* `base = χ_{A₀∧B} · f`;
* `tail = Σ_k χ_{D_k} · f`.

It also exposes the `seriesSumRep_L1` row bridge for the tail.  The remaining
D2b step is the finite telescope of the base plus row sums to
`χ_{A_N∧B}·f`, followed by the limit `N → ∞`.
-/

#check genIB_rep_from_measurable
#check sec4IBLayerResidualData_mk
#check sec4IBLayerSetMapData_of_residualData
#check sec4IBLayerRelData_of_setMapData
#check sec4IBIncrementBridge_of_layerRelData
#check sec4IBTailData_of_incrementBridge
#check sec4IB_baseRep
#check sec4IB_termRep
#check sec4IB_tailRep
#check add_absSeriesSum_left
#check add_absSeriesSum_right
#check add_seriesSum_value
#check sec4_make_pointBridge
#check Sec4SeriesSumRepL1PointBridge

/-! ## 1. Canonical measurable-data aliases -/

/-- The residual data already constructed in the previous chunk. -/
noncomputable def sec4MeasurableResidualData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4IBLayerResidualData (S := S) B hB f hnn :=
  sec4IBLayerResidualData_mk B hB f hnn


/-- The raw set-map data associated to a measurable `B`. -/
noncomputable def sec4MeasurableSetMapData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4IBLayerSetMapData (S := S) B hB f hnn :=
  sec4IBLayerSetMapData_of_residualData B hB f hnn
    (sec4MeasurableResidualData B hB f hnn)


/-- The layer relative data associated to a measurable `B`. -/
noncomputable def sec4MeasurableLayerRelData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4IBLayerRelData (S := S) B hB f hnn :=
  sec4IBLayerRelData_of_setMapData B hB f hnn
    (sec4MeasurableSetMapData B hB f hnn)


/-- The increment bridge associated to a measurable `B`. -/
noncomputable def sec4MeasurableIncrementBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4IBIncrementBridge (S := S) B hB f hnn :=
  sec4IBIncrementBridge_of_layerRelData B hB f hnn
    (sec4MeasurableLayerRelData B hB f hnn)


/-- The tail majorant series used by the measurable direct representative. -/
noncomputable def sec4MeasurableTailData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4IBTailData (S := S) B hB f hnn :=
  sec4IBTailData_of_incrementBridge B hB f hnn
    (sec4MeasurableIncrementBridge B hB f hnn)


/-- The base representative `χ_{A₀∧B}·f`. -/
noncomputable def sec4MeasurableBaseRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IntegrableRep S :=
  sec4IB_baseRep B hB f hnn


/-- The tail representative `Σ_k χ_{D_k}·f`. -/
noncomputable def sec4MeasurableTailRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IntegrableRep S :=
  sec4IB_tailRep B hB f hnn
    (sec4MeasurableTailData B hB f hnn)


/--
Definitional add decomposition of the measurable direct representative.
-/
theorem sec4_genIB_from_measurable_eq_add
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genIB_rep_from_measurable B hB f hnn =
      (sec4MeasurableBaseRep B hB f hnn).add
        (sec4MeasurableTailRep B hB f hnn) := by
  rfl


/-! ## 2. Extract base and tail absolute convergence at a point -/

/-- Transport a point domain witness to the explicit base-plus-tail form. -/
def sec4_genIB_addMemAt
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    {x : X}
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x) :
    ((sec4MeasurableBaseRep B hB f hnn).add
      (sec4MeasurableTailRep B hB f hnn)).MemAt x := by
  simpa only [sec4_genIB_from_measurable_eq_add] using hgenDom


/-- Recover the base domain from a direct-representative domain witness. -/
def sec4_genIB_baseMemAt
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    {x : X}
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x) :
    (sec4MeasurableBaseRep B hB f hnn).MemAt x :=
  add_dom_left (sec4_genIB_addMemAt B hB f hnn hgenDom)


/-- Recover the tail domain from a direct-representative domain witness. -/
def sec4_genIB_tailMemAt
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    {x : X}
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x) :
    (sec4MeasurableTailRep B hB f hnn).MemAt x :=
  add_dom_right (sec4_genIB_addMemAt B hB f hnn hgenDom)

/-- Cast a point abs-series for `genIB` to the explicit add representative. -/
noncomputable def sec4_genIB_abs_as_add
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    RSeq.SeriesSum
      (fun n => COF.abs
        (((sec4MeasurableBaseRep B hB f hnn).add
          (sec4MeasurableTailRep B hB f hnn)).valueAt x
            (sec4_genIB_addMemAt B hB f hnn hgenDom) n)) := by
  simpa only [sec4_genIB_from_measurable_eq_add] using hgenabs


/-- Extract the base absolute convergence from a `genIB` absolute convergence. -/
noncomputable def sec4_genIB_baseAbs_of_abs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    RSeq.SeriesSum
      (fun n => COF.abs
        ((sec4MeasurableBaseRep B hB f hnn).valueAt x
          (sec4_genIB_baseMemAt B hB f hnn hgenDom) n)) :=
  add_absSeriesSum_left
    (r := sec4MeasurableBaseRep B hB f hnn)
    (r' := sec4MeasurableTailRep B hB f hnn)
    (sec4_genIB_addMemAt B hB f hnn hgenDom)
    (sec4_genIB_abs_as_add B hB f hnn x hgenDom hgenabs)


/-- Extract the tail absolute convergence from a `genIB` absolute convergence. -/
noncomputable def sec4_genIB_tailAbs_of_abs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    RSeq.SeriesSum
      (fun n => COF.abs
        ((sec4MeasurableTailRep B hB f hnn).valueAt x
          (sec4_genIB_tailMemAt B hB f hnn hgenDom) n)) :=
  add_absSeriesSum_right
    (r := sec4MeasurableBaseRep B hB f hnn)
    (r' := sec4MeasurableTailRep B hB f hnn)
    (sec4_genIB_addMemAt B hB f hnn hgenDom)
    (sec4_genIB_abs_as_add B hB f hnn x hgenDom hgenabs)


/--
The value of `genIB` is the sum of the base value and the tail value.
-/
theorem sec4_genIB_value_eq_base_add_tail
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    (seriesSum_of_abs hgenabs).sum =
      (seriesSum_of_abs
        (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenDom hgenabs)).sum +
      (seriesSum_of_abs
        (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenDom hgenabs)).sum := by
  let hAddDom := sec4_genIB_addMemAt B hB f hnn hgenDom
  let hBaseDom := sec4_genIB_baseMemAt B hB f hnn hgenDom
  let hTailDom := sec4_genIB_tailMemAt B hB f hnn hgenDom
  let hgenSignedAdd : RSeq.SeriesSum
      (fun n => ((sec4MeasurableBaseRep B hB f hnn).add
        (sec4MeasurableTailRep B hB f hnn)).valueAt x hAddDom n) := by
    simpa only [sec4_genIB_from_measurable_eq_add]
      using (seriesSum_of_abs hgenabs)
  let hbaseSigned : RSeq.SeriesSum
      (fun n => (sec4MeasurableBaseRep B hB f hnn).valueAt x hBaseDom n) :=
    seriesSum_of_abs
      (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenDom hgenabs)
  let htailSigned : RSeq.SeriesSum
      (fun n => (sec4MeasurableTailRep B hB f hnn).valueAt x hTailDom n) :=
    seriesSum_of_abs
      (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenDom hgenabs)
  let hadd : RSeq.SeriesSum
      (fun n => ((sec4MeasurableBaseRep B hB f hnn).add
        (sec4MeasurableTailRep B hB f hnn)).valueAt x hAddDom n) :=
    add_seriesSum_value hBaseDom hTailDom hbaseSigned htailSigned
  have huniq : hgenSignedAdd.sum = hadd.sum :=
    seriesSum_unique hgenSignedAdd hadd
  simpa [hgenSignedAdd, hbaseSigned, htailSigned, hadd]
    using huniq


/-! ## 3. Tail row bridge -/

/--
The `seriesSumRep_L1` point bridge for the tail part of `genIB`.
-/
noncomputable def sec4_genIB_tailPointBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    Sec4SeriesSumRepL1PointBridge (S := S)
      (fun k => sec4IB_termRep B hB f hnn k)
      (sec4MeasurableTailData B hB f hnn)
      x :=
  (sec4_make_pointBridge
    (fun k => sec4IB_termRep B hB f hnn k)
    (sec4MeasurableTailData B hB f hnn)
    x
    (sec4_genIB_tailMemAt B hB f hnn hgenDom)
    (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenDom hgenabs)).val


/--
The tail value is the outer series of the row values.
-/
theorem sec4_genIB_tail_value_eq_rows
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    (seriesSum_of_abs
      (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenDom hgenabs)).sum =
      (sec4_genIB_tailPointBridge B hB f hnn x hgenDom hgenabs).rows.sum := by
  simpa [sec4_genIB_tailPointBridge] using
    (sec4_make_pointBridge
      (fun k => sec4IB_termRep B hB f hnn k)
      (sec4MeasurableTailData B hB f hnn)
      x
      (sec4_genIB_tailMemAt B hB f hnn hgenDom)
      (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenDom hgenabs)).property


/--
Combined value equation: `genIB` equals base value plus the row-sum value of
the tail.
-/
theorem sec4_genIB_value_eq_base_add_tailRows
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom n))) :
    (seriesSum_of_abs hgenabs).sum =
      (seriesSum_of_abs
        (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenDom hgenabs)).sum +
      (sec4_genIB_tailPointBridge B hB f hnn x hgenDom hgenabs).rows.sum := by
  rw [sec4_genIB_value_eq_base_add_tail B hB f hnn x hgenDom hgenabs,
      sec4_genIB_tail_value_eq_rows B hB f hnn x hgenDom hgenabs]


end BishopC
