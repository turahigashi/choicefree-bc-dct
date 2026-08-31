import Mathdemo.Internal.Sec4_Phase2_IB_A1_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-B1: `seriesSumRep_L1` point bridge

This chunk implements the point bridge isolated in A1.

A1 was kernel-verified after changing `Sec4IBTailData` from a `structure`
to a `def`; this file assumes that corrected A1 is imported.

The key target is

```lean
sec4_make_pointBridge F hsum x hflatabs :
  Sec4SeriesSumRepL1PointBridge F hsum x hflatabs
```

The proof follows the kernel response:

* get row absolute convergence from the flattened `seriesSumRep_L1` abs-series;
* use `seriesSum_of_abs` for row signed values;
* use `seriesSumRep_L1_value` for the outer row series;
* convert its row term to `(rowVal m).sum` using
  `seriesSumRep_L1_hsplit_value`.

No extra nonconstructive placeholder is introduced.
The first kernel pass may only need argument-order adjustments for
`seriesIntegrable_value_of_flat`, `seriesSumRep_L1_value`, and
`seriesSumRep_L1_hsplit_value`.
-/

#check seriesIntegrable_value_of_flat
#check seriesSumRep_L1_value
#check seriesSumRep_L1_hsplit_value
#check add_absSeriesSum_left
#check add_absSeriesSum_right
#check row_seriesSum
#check G_m
#check tail_m
#check Nm

/--
A small constructor for the A1 bridge.  It is useful independently of the
exact internal API of `seriesSumRep_L1`.
-/
noncomputable def sec4_make_pointBridge_from_rows
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    (x : X)
    (hflatDom : (seriesSumRep_L1 F hsum).MemAt x)
    (hflatabs : RSeq.SeriesSum
      (fun n => COF.abs ((seriesSumRep_L1 F hsum).valueAt x hflatDom n)))
    (rowDom : ∀ m : Nat, (F m).MemAt x)
    (rowAbs : ∀ m : Nat,
      RSeq.SeriesSum (fun n => COF.abs ((F m).valueAt x (rowDom m) n)))
    (rows : RSeq.SeriesSum
      (fun m => (seriesSum_of_abs (rowAbs m)).sum))
    (value_eq : (seriesSum_of_abs hflatabs).sum = rows.sum) :
    { B : Sec4SeriesSumRepL1PointBridge (S := S) F hsum x //
      (seriesSum_of_abs hflatabs).sum = B.rows.sum } := ⟨{
  rowDom := rowDom
  rowAbs := rowAbs
  rowVal := fun m => seriesSum_of_abs (rowAbs m)
  rows := rows
}, value_eq⟩


/--
The concrete bridge for `seriesSumRep_L1`.

The only delicate line is the definition of `rowAbs`; if the local signature of
`seriesIntegrable_value_of_flat` has a different argument order, the kernel
loop should rewrite that call only.  The mathematical content is exactly the
one reported by the A1 kernel response.
-/
noncomputable def sec4_make_pointBridge
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    (x : X)
    (hflatDom : (seriesSumRep_L1 F hsum).MemAt x)
    (hflatabs : RSeq.SeriesSum
      (fun n => COF.abs ((seriesSumRep_L1 F hsum).valueAt x hflatDom n))) :
    { B : Sec4SeriesSumRepL1PointBridge (S := S) F hsum x //
      (seriesSum_of_abs hflatabs).sum = B.rows.sum } := by
  -- Technical note.
  -- Technical note.
  let rowDom : ∀ m : Nat, (F m).MemAt x :=
    fun m => seriesSumRep_L1_F_memAt F hsum hflatDom m
  let rowAbs : ∀ m : Nat,
      RSeq.SeriesSum (fun n => COF.abs ((F m).valueAt x (rowDom m) n)) :=
    fun m => seriesSumRep_L1_row_absConv F hsum (x := x)
      hflatDom hflatabs m
  let rowVal : ∀ m : Nat,
      RSeq.SeriesSum (fun n => (F m).valueAt x (rowDom m) n) :=
    fun m => seriesSum_of_abs (rowAbs m)
  -- Technical note.
  -- Technical note.
  -- Technical note.
  obtain ⟨hV, eV⟩ :=
    seriesSumRep_L1_value F hsum hflatDom hflatabs
  let rows : RSeq.SeriesSum (fun m => (rowVal m).sum) :=
    seriesSum_congr (fun m => by
      let hprefix := IntegrableRep.ofL_value (psi_m_mem F m) x
        (BFunR.seqSum_mem (F m).fn x (rowDom m) (Nm F m))
      let htail := IntegrableRep.tailFrom_value
        (F m) (Nm F m) x (rowDom m) (rowVal m)
      calc
        (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
          ((G_m F i).valueAt x
            (seriesSumRep_L1_Grow_memAt F hsum hflatDom i) j))
          (add_absSeriesSum_left hflatDom hflatabs) m)).sum
            + (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
              ((tail_m F i).valueAt x
                (seriesSumRep_L1_tailRow_memAt F hsum hflatDom i) j))
              (add_absSeriesSum_right hflatDom hflatabs) m)).sum
          = hprefix.val.sum + htail.val.sum := by
              rw [seriesSum_unique _ hprefix.val,
                seriesSum_unique _ htail.val]
        _ = (rowVal m).sum :=
          seriesSumRep_L1_hsplit_value F m (rowDom m) (rowVal m)) hV
  exact sec4_make_pointBridge_from_rows F hsum x hflatDom hflatabs
    rowDom rowAbs rows eV


/--
Unconditional `RepNonneg` preservation for `seriesSumRep_L1`, using the
concrete bridge above.
-/
noncomputable def sec4_seriesSumRep_L1_repNonneg
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    (hFnn : ∀ m : Nat, RepNonneg (F m)) :
    RepNonneg (seriesSumRep_L1 F hsum) :=
  sec4_seriesSumRep_L1_repNonneg_of_bridge F hsum hFnn
    (fun x hflatDom hflatabs =>
      sec4_make_pointBridge F hsum x hflatDom hflatabs)


/--
Specialized positive tail preservation, ready for the direct `I_B`
construction once the norm-majorant `H` has been supplied.
-/
noncomputable def sec4IB_tailRepNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) B hB f hnn)
    (hterm_nn : ∀ k : Nat, RepNonneg (sec4IB_termRep B hB f hnn k)) :
    RepNonneg (sec4IB_tailRep B hB f hnn H) := by
  dsimp [sec4IB_tailRep]
  exact sec4_seriesSumRep_L1_repNonneg
    (fun k => sec4IB_termRep B hB f hnn k) H hterm_nn


end BishopC
