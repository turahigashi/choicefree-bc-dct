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

/-- Cast a point abs-series for `genIB` to the explicit add representative. -/
noncomputable def sec4_genIB_abs_as_add
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    RSeq.SeriesSum
      (fun n => COF.abs
        ((((sec4MeasurableBaseRep B hB f hnn).add
          (sec4MeasurableTailRep B hB f hnn)).fn n).toFun x)) := by
  simpa [sec4_genIB_from_measurable_eq_add B hB f hnn] using hgenabs


/-- Extract the base absolute convergence from a `genIB` absolute convergence. -/
noncomputable def sec4_genIB_baseAbs_of_abs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    RSeq.SeriesSum
      (fun n => COF.abs
        (((sec4MeasurableBaseRep B hB f hnn).fn n).toFun x)) :=
  add_absSeriesSum_left
    (r := sec4MeasurableBaseRep B hB f hnn)
    (r' := sec4MeasurableTailRep B hB f hnn)
    (sec4_genIB_abs_as_add B hB f hnn x hgenabs)


/-- Extract the tail absolute convergence from a `genIB` absolute convergence. -/
noncomputable def sec4_genIB_tailAbs_of_abs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    RSeq.SeriesSum
      (fun n => COF.abs
        (((sec4MeasurableTailRep B hB f hnn).fn n).toFun x)) :=
  add_absSeriesSum_right
    (r := sec4MeasurableBaseRep B hB f hnn)
    (r' := sec4MeasurableTailRep B hB f hnn)
    (sec4_genIB_abs_as_add B hB f hnn x hgenabs)


/--
The value of `genIB` is the sum of the base value and the tail value.
-/
theorem sec4_genIB_value_eq_base_add_tail
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    (seriesSum_of_abs hgenabs).sum =
      (seriesSum_of_abs
        (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenabs)).sum +
      (seriesSum_of_abs
        (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenabs)).sum := by
  let hgenSignedAdd : RSeq.SeriesSum
      (fun n =>
        (((sec4MeasurableBaseRep B hB f hnn).add
          (sec4MeasurableTailRep B hB f hnn)).fn n).toFun x) := by
    simpa [sec4_genIB_from_measurable_eq_add B hB f hnn]
      using (seriesSum_of_abs hgenabs)
  let hbaseSigned : RSeq.SeriesSum
      (fun n => ((sec4MeasurableBaseRep B hB f hnn).fn n).toFun x) :=
    seriesSum_of_abs
      (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenabs)
  let htailSigned : RSeq.SeriesSum
      (fun n => ((sec4MeasurableTailRep B hB f hnn).fn n).toFun x) :=
    seriesSum_of_abs
      (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenabs)
  let hadd : RSeq.SeriesSum
      (fun n =>
        (((sec4MeasurableBaseRep B hB f hnn).add
          (sec4MeasurableTailRep B hB f hnn)).fn n).toFun x) :=
    add_seriesSum_value hbaseSigned htailSigned
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
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    Sec4SeriesSumRepL1PointBridge (S := S)
      (fun k => sec4IB_termRep B hB f hnn k)
      (sec4MeasurableTailData B hB f hnn)
      x
      (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenabs) :=
  sec4_make_pointBridge
    (fun k => sec4IB_termRep B hB f hnn k)
    (sec4MeasurableTailData B hB f hnn)
    x
    (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenabs)


/--
The tail value is the outer series of the row values.
-/
theorem sec4_genIB_tail_value_eq_rows
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    (seriesSum_of_abs
      (sec4_genIB_tailAbs_of_abs B hB f hnn x hgenabs)).sum =
      (sec4_genIB_tailPointBridge B hB f hnn x hgenabs).rows.sum :=
  (sec4_genIB_tailPointBridge B hB f hnn x hgenabs).value_eq


/--
Combined value equation: `genIB` equals base value plus the row-sum value of
the tail.
-/
theorem sec4_genIB_value_eq_base_add_tailRows
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenabs : RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    (seriesSum_of_abs hgenabs).sum =
      (seriesSum_of_abs
        (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenabs)).sum +
      (sec4_genIB_tailPointBridge B hB f hnn x hgenabs).rows.sum := by
  rw [sec4_genIB_value_eq_base_add_tail B hB f hnn x hgenabs,
      sec4_genIB_tail_value_eq_rows B hB f hnn x hgenabs]


end BishopC
