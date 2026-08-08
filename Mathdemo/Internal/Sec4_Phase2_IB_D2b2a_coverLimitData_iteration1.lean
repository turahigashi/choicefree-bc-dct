import Mathdemo.Internal.Sec4_Phase2_IB_D2b1_rowsLimitBridge_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2a: cover-limit data implies `Sec4GenIBRowsLimitData`

D2b1 was kernel-verified after two fixes: the tail row series is a direct
term-mode projection, and `Sec4GenIBRowsLimitData` is Type-valued because it
contains `TendstoHalf` data.

This chunk performs the next safe split.  Instead of proving the finite
telescope and cover limit in one large theorem, it packages them as
`Sec4GenIBCoverLimitData` and proves that they imply the exact
`Sec4GenIBRowsLimitData` required by D2b1.

The next chunk only has to build `Sec4GenIBCoverLimitData`:
finite telescope
`base + partialSum rows N = coverValue N`, then the two limits on `B.S1` and
`B.S2`.
-/

#check Sec4GenIBRowsLimitData
#check sec4_genIBValueBridge_of_rowsLimitData
#check sec4_genRelIntegral_eq_relIntegral_of_rowsLimitData
#check sec4_tendstoHalf_sub_const
#check RSeq.TendstoHalf
#check RSeq.partialSum

/-! ## 1. TendstoHalf transport helpers -/

/-- Transport a `TendstoHalf` proof along pointwise equality of sequences. -/
def sec4_tendstoHalf_congr_left
    {u v : Nat → R} {l : R}
    (h : RSeq.TendstoHalf u l)
    (hEq : ∀ n : Nat, v n = u n) :
    RSeq.TendstoHalf v l where
  mod := h.mod
  close := by
    intro k n hn
    simpa [hEq n] using h.close k n hn


/--
If `base + rowsPartial n = cover n`, then the row partial sums are
`cover n - base`.
-/
theorem sec4_rowsPartial_eq_cover_sub_base
    (base : R) (rows cover : Nat → R)
    (hTel : ∀ n : Nat, base + rows n = cover n) :
    ∀ n : Nat, rows n = cover n - base := by
  intro n
  calc
    rows n = (base + rows n) - base := by ring
    _ = cover n - base := by rw [hTel n]


/--
A cover-value limit plus the finite telescope gives a row-sum limit.
-/
def sec4_rows_tendsto_from_cover
    (base : R) (rows cover : Nat → R) (target : R)
    (hTel : ∀ n : Nat, base + rows n = cover n)
    (hCover : RSeq.TendstoHalf cover target) :
    RSeq.TendstoHalf rows (target - base) := by
  let hSub : RSeq.TendstoHalf (fun n => cover n - base) (target - base) :=
    sec4_tendstoHalf_sub_const hCover base
  exact sec4_tendstoHalf_congr_left hSub
    (sec4_rowsPartial_eq_cover_sub_base base rows cover hTel)


/-! ## 2. The remaining cover-value data -/

/--
The remaining finite-telescope and cover-limit data.

`coverValue x hgenabs N` is intended to be the point value of
`χ_{A_N ∧ B} · f` at `x`.  The field `finite_telescope` states the exact
finite identity connecting this value to the base plus the first `N+1` tail
rows, in the `RSeq.partialSum` convention used throughout the development.

The two limit fields are the two cases of the final value identification:
on `B.S1` the cover values tend to the value of `f`; on `B.S2` they tend to
zero.
-/
structure Sec4GenIBCoverLimitData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  coverValue :
    ∀ x : X,
      RSeq.SeriesSum
        (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x)) →
      Nat → R
  domain :
    ∀ x : X,
      RSeq.SeriesSum
        (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x)) →
      x ∈ B.S1 ∪ B.S2
  finite_telescope :
    ∀ x : X,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x)),
      ∀ N : Nat,
        sec4_genIB_baseValue B hB f hnn x hgenabs +
          RSeq.partialSum (sec4_genIB_tailRowSeq B hB f hnn x hgenabs) N =
        coverValue x hgenabs N
  cover_tendsto_s1 :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x)),
      ∀ hfabs :
        RSeq.SeriesSum (fun n => COF.abs (((f.fn n).toFun x))),
      RSeq.TendstoHalf (coverValue x hgenabs) (seriesSum_of_abs hfabs).sum
  cover_tendsto_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x)),
      RSeq.TendstoHalf (coverValue x hgenabs) 0


/-! ## 3. Cover-limit data gives the D2b1 row-limit data -/

/-- The `B.S1` row limit extracted from cover-limit data. -/
noncomputable def sec4_rows_tendsto_s1_of_coverLimitData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverLimitData (S := S) B hB f hnn)
    (x : X) (hxB : x ∈ B.S1)
    (hgenabs :
      RSeq.SeriesSum
        (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x)))
    (hfabs :
      RSeq.SeriesSum (fun n => COF.abs (((f.fn n).toFun x)))) :
    RSeq.TendstoHalf
      (RSeq.partialSum (sec4_genIB_tailRowSeq B hB f hnn x hgenabs))
      ((seriesSum_of_abs hfabs).sum -
        sec4_genIB_baseValue B hB f hnn x hgenabs) :=
  sec4_rows_tendsto_from_cover
    (sec4_genIB_baseValue B hB f hnn x hgenabs)
    (RSeq.partialSum (sec4_genIB_tailRowSeq B hB f hnn x hgenabs))
    (T.coverValue x hgenabs)
    (seriesSum_of_abs hfabs).sum
    (T.finite_telescope x hgenabs)
    (T.cover_tendsto_s1 x hxB hgenabs hfabs)


/-- The `B.S2` row limit extracted from cover-limit data. -/
noncomputable def sec4_rows_tendsto_s2_of_coverLimitData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverLimitData (S := S) B hB f hnn)
    (x : X) (hxB : x ∈ B.S2)
    (hgenabs :
      RSeq.SeriesSum
        (fun n => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn n).toFun x))) :
    RSeq.TendstoHalf
      (RSeq.partialSum (sec4_genIB_tailRowSeq B hB f hnn x hgenabs))
      (0 - sec4_genIB_baseValue B hB f hnn x hgenabs) :=
  sec4_rows_tendsto_from_cover
    (sec4_genIB_baseValue B hB f hnn x hgenabs)
    (RSeq.partialSum (sec4_genIB_tailRowSeq B hB f hnn x hgenabs))
    (T.coverValue x hgenabs)
    0
    (T.finite_telescope x hgenabs)
    (T.cover_tendsto_s2 x hxB hgenabs)


/--
Build the exact D2b1 row-limit data from finite telescope plus cover limits.
-/
noncomputable def sec4_rowsLimitData_of_coverLimitData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverLimitData (S := S) B hB f hnn) :
    Sec4GenIBRowsLimitData (S := S) B hB f hnn := {
  domain := T.domain
  rows_tendsto_s1 := by
    intro x hxB hgenabs hfabs
    exact sec4_rows_tendsto_s1_of_coverLimitData B hB f hnn T
      x hxB hgenabs hfabs
  rows_tendsto_s2 := by
    intro x hxB hgenabs
    exact sec4_rows_tendsto_s2_of_coverLimitData B hB f hnn T
      x hxB hgenabs
}


/-! ## 4. Value bridge and consistency from cover-limit data -/

/-- Full value bridge from finite telescope plus cover limits. -/
noncomputable def sec4_genIBValueBridge_of_coverLimitData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverLimitData (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_rowsLimitData B hB f hnn
    (sec4_rowsLimitData_of_coverLimitData B hB f hnn T)


/-- Consistency theorem from cover-limit data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_coverLimitData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverLimitData (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_rowsLimitData C hC f hnn
    (sec4_rowsLimitData_of_coverLimitData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from cover-limit data. -/
noncomputable def sec4_genIBConsistencyBridge_of_coverLimitData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4GenIBCoverLimitData (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_rowsLimitData C hC f hnn
    (sec4_rowsLimitData_of_coverLimitData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
