import Mathdemo.Internal.Sec4.Min2RowInternals

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b9: row≥1 switch, removing the impossible `n0_pos`

The b2b8 kernel response found the crucial gap: `prop_4_2_n_k f 0` is a
convergence modulus and may be zero, so `0 < prop_4_2_n_k f 0` is not a valid
primitive assumption.

This file switches the characteristic-abs extraction from row 0 to row 1.
For every `k`, the successor row coefficient

```
prop_4_2_n_k f (k+1) - prop_4_2_n_k f k
```

is strictly positive, because the definition of `prop_4_2_n_k` includes
`prop_4_2_n_k f k + 1` under a `Nat.max`.

Consequently the final external primitive data is reduced to a single field:

```
Sec4CoverChiFAbsSucc B hB f hnn
```

All other `prop_4_2` internals are supplied by the already verified b2b8 row
zero theorem and the row≥1 scalar cancellation below.
-/

#check Sec4Prop42AlmostFinalTools
#check Sec4Prop42RowInternalTools
#check Sec4ChiFInternalTools
#check Sec4CoverChiFAbsSucc
#check Sec4SetChiAbsOfChiFAbs
#check Sec4ChiFZeroOnS2
#check sec4_lambdaRowZeroOnS2
#check sec4_natSmuled_abs_cancel
#check prop_4_2_n_k
#check prop_4_2_lambda_k
#check seriesSumRep_L1_row_absConv
#check sec4_make_pointBridge
#check sec4_zeroSeries_transparent

/-! ## 1. Successor coefficients of `prop_4_2_n_k` are positive -/

/-- `prop_4_2_n_k` strictly increases at every successor step. -/
theorem sec4_prop42_nk_strict_succ
    (f : IntegrableRep S) (k : Nat) :
    prop_4_2_n_k f k < prop_4_2_n_k f (k + 1) := by
  change prop_4_2_n_k f k <
    Nat.max (f.cutNat_tendsto_rep.mod (k + 2)) (prop_4_2_n_k f k + 1)
  exact Nat.lt_of_lt_of_le
    (Nat.lt_succ_self (prop_4_2_n_k f k))
    (Nat.le_max_right (f.cutNat_tendsto_rep.mod (k + 2))
      (prop_4_2_n_k f k + 1))




/-- The successor row coefficient is positive. -/
theorem sec4_prop42_nk_diff_pos
    (f : IntegrableRep S) (k : Nat) :
    0 < prop_4_2_n_k f (k + 1) - prop_4_2_n_k f k :=
  Nat.sub_pos_of_lt (sec4_prop42_nk_strict_succ (S := S) f k)


/-! ## 2. Row≥1 characteristic abs extraction -/

/--
Characteristic abs extraction from a positive successor row of
`prop_4_2_lambda_k`.

This is the row≥1 replacement for `sec4_lambda0ChiAbs_of_n0_pos`.
-/
def Sec4LambdaSuccChiAbsOfAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ k : Nat,
    ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
      ∀ hrowDom :
        (prop_4_2_lambda_k A hA f (prop_4_2_n_k f) (k + 1)).MemAt x,
      RSeq.SeriesSum
        (fun m => COF.abs
          ((prop_4_2_lambda_k A hA f (prop_4_2_n_k f) (k + 1)).valueAt
            x hrowDom m)) →
      Sec4RepAbsAt hA.rep x


/--
Extract `χ_A` abs convergence from any successor row of `prop_4_2_lambda_k`.
-/
noncomputable def sec4_lambdaSuccChiAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4LambdaSuccChiAbsOfAbs (S := S) f hnn := by
  intro k A hA x hrowDom hrowabs
  dsimp [prop_4_2_lambda_k] at hrowDom hrowabs
  let coeff : Nat := prop_4_2_n_k f (k + 1) - prop_4_2_n_k f k
  let hleftDom := min2_dom_left hrowDom
  let hleftAbs :=
    min2_absSeriesSum_left hrowDom hrowabs
  exact sec4_natSmuled_abs_cancel (S := S)
    coeff (sec4_prop42_nk_diff_pos (S := S) f k)
      hA.rep x hleftDom hleftAbs


/--
Extract `χ_A` abs convergence from a completed `χ_A·f` representative, using
row 1 of the internal `seriesSumRep_L1`.
-/
noncomputable def sec4_setChiAbsOfChiFAbs_of_row1
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4SetChiAbsOfChiFAbs (S := S) f hnn := by
  intro A hA x hflatDom hflatabs
  unfold prop_4_2_chi_f_rep at hflatDom hflatabs
  let hrow1Dom :
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f) 1).MemAt x :=
    seriesSumRep_L1_F_memAt
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
      _ hflatDom 1
  let hrow1 :
      RSeq.SeriesSum
        (fun m => COF.abs
          ((prop_4_2_lambda_k A hA f (prop_4_2_n_k f) 1).valueAt
            x hrow1Dom m)) :=
    seriesSumRep_L1_row_absConv
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
      _
      (x := x)
      hflatDom
      hflatabs
      1
  exact sec4_lambdaSuccChiAbs (S := S) f hnn
    0 A hA x hrow1Dom hrow1


/-! ## 3. Generic zero on `A.S2` without any row-0 positivity -/

/--
The completed `χ_A·f` representative is zero on `A.S2`, using b2b8's
row-wise zero theorem.
-/
noncomputable def sec4_chiFZeroOnS2_from_lambdaRows
    (f : IntegrableRep S) (hnn : RepNonneg f) :
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
        change (0 : R) = (PB.rowVal k).sum
        exact (sec4_lambdaRowZeroOnS2 (S := S) f hnn
          A hA x hxA k (PB.rowDom k) (PB.rowAbs k)).symm)
      (sec4_zeroSeries_transparent (R := R))
  have hrows0 : PB.rows.sum = 0 :=
    (seriesSum_unique PB.rows hzeroRows).trans (by rfl)
  calc
    (seriesSum_of_abs hflatabs).sum = PB.rows.sum := PBData.property
    _ = 0 := hrows0


/-! ## 4. Final tools: only the finite-cover `χ·f` abs witness remains -/

/--
The true final primitive data for the measurable relative integral.

After the row≥1 switch, the row-0 positivity assumption is gone.  The only
remaining field is the finite-cover `χ·f` abs witness.
-/
def Sec4Prop42FinalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  Sec4CoverChiFAbsSucc (S := S) B hB f hnn


namespace Sec4Prop42FinalTools

/-- Constructor, kept for a stable final API. -/
def mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (cover_chiF_abs_succ : Sec4CoverChiFAbsSucc (S := S) B hB f hnn) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  cover_chiF_abs_succ


/-- The remaining finite-cover `χ·f` abs witness. -/
def cover_chiF_abs_succ
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42FinalTools (S := S) B hB f hnn) :
    Sec4CoverChiFAbsSucc (S := S) B hB f hnn :=
  T


end Sec4Prop42FinalTools

/--
Build the b2b6 `Sec4ChiFInternalTools` from the single final primitive.
-/
noncomputable def sec4_chiFInternalTools_of_finalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42FinalTools (S := S) B hB f hnn) :
    Sec4ChiFInternalTools (S := S) B hB f hnn :=
  Sec4ChiFInternalTools.mk
    (cover_chiF_abs_succ := Sec4Prop42FinalTools.cover_chiF_abs_succ T)
    (set_chi_abs_of_chiF_abs := sec4_setChiAbsOfChiFAbs_of_row1 f hnn)
    (chiF_zero_on_s2 := sec4_chiFZeroOnS2_from_lambdaRows f hnn)


/-- Full value bridge from the single final primitive. -/
noncomputable def sec4_genIBValueBridge_of_finalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42FinalTools (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_internalTools B hB f hnn
    (sec4_chiFInternalTools_of_finalTools B hB f hnn T)


/-- Consistency theorem from the single final primitive. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_finalTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42FinalTools
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_internalTools C hC f hnn
    (sec4_chiFInternalTools_of_finalTools
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from the single final primitive. -/
noncomputable def sec4_genIBConsistencyBridge_of_finalTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42FinalTools
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_internalTools C hC f hnn
    (sec4_chiFInternalTools_of_finalTools
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
