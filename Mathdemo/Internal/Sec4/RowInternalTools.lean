import Mathdemo.Internal.Sec4.InternalTools

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b7: row-level internal tools for `prop_4_2_chi_f_rep`

The b2b6 kernel response confirms that the external plumbing is complete after
the `Sec4ChiFZeroOnS2 : Prop` correction.  The only remaining object is
`Sec4ChiFInternalTools`.

This file pushes two of the three internal tools down to row-level facts about
`prop_4_2_lambda_k`:

* `χ_A` abs extraction from a `χ_A·f` abs witness is obtained by taking row 0
  of the `seriesSumRep_L1` construction and applying a row-level extractor.
* zero on `A.S2` is obtained by the B1 point bridge for `seriesSumRep_L1`;
  if every row value is zero on `A.S2`, the whole outer row sum is zero.

The remaining primitive data are packaged in
`Sec4Prop42RowInternalTools`.  The next kernel-loop chunk should prove those
row-level internal facts from the actual definition of `prop_4_2_lambda_k`.
-/

#check Sec4ChiFInternalTools
#check Sec4CoverChiFAbsSucc
#check Sec4SetChiAbsOfChiFAbs
#check Sec4ChiFZeroOnS2
#check sec4_genIBValueBridge_of_internalTools
#check sec4_genRelIntegral_eq_relIntegral_of_internalTools
#check sec4_genIBConsistencyBridge_of_internalTools
#check seriesSumRep_L1_row_absConv
#check sec4_make_pointBridge
#check prop_4_2_chi_f_rep
#check prop_4_2_lambda_k
#check prop_4_2_n_k

/-! ## 1. Row-level primitives -/

/--
Row-0 extraction of the characteristic representative from the internal
`prop_4_2_lambda_k` row.

This is the first genuinely internal fact about Proposition 4.2.  It is lower
level than `Sec4SetChiAbsOfChiFAbs`: it talks about the first row of the
`seriesSumRep_L1` construction, not the completed representative.
-/
def Sec4Lambda0ChiAbsOfAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
    ∀ hrowDom :
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f) 0).MemAt x,
    RSeq.SeriesSum
      (fun m => COF.abs
        ((prop_4_2_lambda_k A hA f (prop_4_2_n_k f) 0).valueAt
          x hrowDom m)) →
    Sec4RepAbsAt hA.rep x


/--
Row-level zero fact for every `prop_4_2_lambda_k` row on `A.S2`.

This is the second genuinely internal fact about Proposition 4.2.  It avoids
reading a characteristic value from an arbitrary signed witness; the input is
the row absolute convergence witness.
-/
def Sec4LambdaRowZeroOnS2
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S2 →
    ∀ k : Nat,
      ∀ hrowDom :
        (prop_4_2_lambda_k A hA f (prop_4_2_n_k f) k).MemAt x,
      ∀ hrowabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((prop_4_2_lambda_k A hA f (prop_4_2_n_k f) k).valueAt
              x hrowDom m)),
        (seriesSum_of_abs hrowabs).sum = 0


/--
The remaining primitive data for the final internal bridge.

The first field is still the finite-cover `χ·f` abs witness.  The other two
are row-level facts about `prop_4_2_lambda_k`, from which this file constructs
the generic `Sec4SetChiAbsOfChiFAbs` and `Sec4ChiFZeroOnS2`.
-/
def Sec4Prop42RowInternalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4CoverChiFAbsSucc (S := S) B hB f hnn)
    (PProd (Sec4Lambda0ChiAbsOfAbs (S := S) f hnn)
      (Sec4LambdaRowZeroOnS2 (S := S) f hnn))


namespace Sec4Prop42RowInternalTools



def cover_chiF_abs_succ
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowInternalTools (S := S) B hB f hnn) :
    Sec4CoverChiFAbsSucc (S := S) B hB f hnn :=
  T.1


def lambda0_chi_abs
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowInternalTools (S := S) B hB f hnn) :
    Sec4Lambda0ChiAbsOfAbs (S := S) f hnn :=
  T.2.1


def lambda_row_zero_on_s2
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowInternalTools (S := S) B hB f hnn) :
    Sec4LambdaRowZeroOnS2 (S := S) f hnn :=
  T.2.2


end Sec4Prop42RowInternalTools

/-! ## 2. Generic extraction from the completed `χ_A·f` representative -/

/--
Extract the characteristic abs witness from a completed `χ_A·f` abs witness,
using row 0 of the underlying `seriesSumRep_L1`.
-/
noncomputable def sec4_setChiAbsOfChiFAbs_of_rowTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowInternalTools (S := S) B hB f hnn) :
    Sec4SetChiAbsOfChiFAbs (S := S) f hnn := by
  intro A hA x hflatDom hflatabs
  unfold prop_4_2_chi_f_rep at hflatDom hflatabs
  let hrow0Dom :
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f) 0).MemAt x :=
    seriesSumRep_L1_F_memAt
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
      _ hflatDom 0
  let hrow0 :
      RSeq.SeriesSum
        (fun m => COF.abs
          ((prop_4_2_lambda_k A hA f (prop_4_2_n_k f) 0).valueAt
            x hrow0Dom m)) :=
    seriesSumRep_L1_row_absConv
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
      _
      (x := x)
      hflatDom
      hflatabs
      0
  exact Sec4Prop42RowInternalTools.lambda0_chi_abs T
    A hA x hrow0Dom hrow0


/-! ## 3. Zero of the completed `χ_A·f` representative on `A.S2` -/

/-- A transparent zero series, with `.sum = 0` by reduction. -/
noncomputable def sec4_zeroSeries_transparent :
    RSeq.SeriesSum (fun _ : Nat => (0 : R)) :=
  seriesSum_congr
    (fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn])
    (seriesSum_single (0 : R))


/--
If each internal row of `prop_4_2_chi_f_rep` has value zero on `A.S2`, then
the completed representative has value zero on `A.S2`.
-/
noncomputable def sec4_chiFZeroOnS2_of_rowTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowInternalTools (S := S) B hB f hnn) :
    Sec4ChiFZeroOnS2 (S := S) f hnn := by
  intro A hA x hxA hflatDom hflatabs
  unfold prop_4_2_chi_f_rep at hflatDom hflatabs
  let F : Nat → IntegrableRep S :=
    prop_4_2_lambda_k A hA f (prop_4_2_n_k f)
  let PBData := sec4_make_pointBridge F _ x hflatDom hflatabs
  let PB := PBData.val
  let hzeroRows : RSeq.SeriesSum (fun k => (PB.rowVal k).sum) :=
    seriesSum_congr
      (fun k => by
        -- Technical note.
        -- Technical note.
        change (0 : R) = (PB.rowVal k).sum
        exact (Sec4Prop42RowInternalTools.lambda_row_zero_on_s2 T
          A hA x hxA k (PB.rowDom k) (PB.rowAbs k)).symm)
      (sec4_zeroSeries_transparent (R := R))
  have hrows0 : PB.rows.sum = 0 :=
    (seriesSum_unique PB.rows hzeroRows).trans (by rfl)
  calc
    (seriesSum_of_abs hflatabs).sum = PB.rows.sum := PBData.property
    _ = 0 := hrows0


/-! ## 4. Assemble the b2b6 internal tools and final bridges -/

/-- The final `Sec4ChiFInternalTools` from row-level Proposition 4.2 tools. -/
noncomputable def sec4_chiFInternalTools_of_rowTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowInternalTools (S := S) B hB f hnn) :
    Sec4ChiFInternalTools (S := S) B hB f hnn :=
  Sec4ChiFInternalTools.mk
    (cover_chiF_abs_succ := Sec4Prop42RowInternalTools.cover_chiF_abs_succ T)
    (set_chi_abs_of_chiF_abs := sec4_setChiAbsOfChiFAbs_of_rowTools B hB f hnn T)
    (chiF_zero_on_s2 := sec4_chiFZeroOnS2_of_rowTools B hB f hnn T)


/-- Full value bridge from row-level Proposition 4.2 tools. -/
noncomputable def sec4_genIBValueBridge_of_rowTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowInternalTools (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_internalTools B hB f hnn
    (sec4_chiFInternalTools_of_rowTools B hB f hnn T)


/-- Consistency theorem from row-level Proposition 4.2 tools. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_rowTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowInternalTools
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_internalTools C hC f hnn
    (sec4_chiFInternalTools_of_rowTools
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from row-level Proposition 4.2 tools. -/
noncomputable def sec4_genIBConsistencyBridge_of_rowTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowInternalTools
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_internalTools C hC f hnn
    (sec4_chiFInternalTools_of_rowTools
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
