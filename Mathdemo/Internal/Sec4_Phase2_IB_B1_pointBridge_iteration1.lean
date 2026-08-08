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
    (hflatabs : RSeq.SeriesSum
      (fun n => COF.abs (((seriesSumRep_L1 F hsum).fn n).toFun x)))
    (rowAbs : ∀ m : Nat,
      RSeq.SeriesSum (fun n => COF.abs (((F m).fn n).toFun x)))
    (rows : RSeq.SeriesSum
      (fun m => (seriesSum_of_abs (rowAbs m)).sum))
    (value_eq : (seriesSum_of_abs hflatabs).sum = rows.sum) :
    Sec4SeriesSumRepL1PointBridge (S := S) F hsum x hflatabs := {
  rowAbs := rowAbs
  rowVal := fun m => seriesSum_of_abs (rowAbs m)
  rows := rows
  value_eq := value_eq
}


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
    (hflatabs : RSeq.SeriesSum
      (fun n => COF.abs (((seriesSumRep_L1 F hsum).fn n).toFun x))) :
    Sec4SeriesSumRepL1PointBridge (S := S) F hsum x hflatabs := by
  -- Technical note.
  -- Technical note.
  let rowAbs : ∀ m : Nat,
      RSeq.SeriesSum (fun n => COF.abs (((F m).fn n).toFun x)) :=
    fun m => seriesSumRep_L1_row_absConv F hsum (x := x) hflatabs m
  -- Technical note.
  -- Technical note.
  -- Technical note.
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_value F hsum (x := x) hflatabs
  exact sec4_make_pointBridge_from_rows F hsum x hflatabs rowAbs
    (seriesSum_congr (fun m => by
        rw [show (seriesSum_of_abs (row_seriesSum
                (fun i j => abs_nonneg (((G_m F i).fn j).toFun x))
                (add_absSeriesSum_left hflatabs) m)).sum
              = (IntegrableRep.ofL_value (psi_m_mem F m) x).val.sum from seriesSum_unique _ _,
            show (seriesSum_of_abs (row_seriesSum
                (fun i j => abs_nonneg (((tail_m F i).fn j).toFun x))
                (add_absSeriesSum_right hflatabs) m)).sum
              = (IntegrableRep.tailFrom_value (F m) (Nm F m) x
                  (seriesSum_of_abs (rowAbs m))).val.sum from seriesSum_unique _ _]
        exact seriesSumRep_L1_hsplit_value F m (seriesSum_of_abs (rowAbs m)))
      hV)
    eV


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
    (fun x hflatabs => sec4_make_pointBridge F hsum x hflatabs)


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
