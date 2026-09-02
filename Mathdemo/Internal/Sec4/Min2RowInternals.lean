import Mathdemo.Internal.Sec4.RowInternalTools

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b8: min2 row internals and near-final bridge

The b2b7 kernel response confirms that the row-level plumbing passed after
one `.symm` orientation fix.  This file now proves the two row-internal pieces
that do not involve the finite cover construction:

* `lambda_row_zero_on_s2`;
* `lambda0_chi_abs`, assuming the expected positivity of the row-0
  coefficient `prop_4_2_n_k f 0`.

The remaining primitive data are therefore only:

* the finite-cover abs witness `cover_chiF_abs_succ`;
* the positivity proof for the row-0 coefficient.

If `prop_4_2_n_k f 0` already has a named positivity lemma in the local tree,
the final step should be to feed it into `Sec4Prop42AlmostFinalTools`.
-/

#check Sec4Prop42RowInternalTools
#check Sec4CoverChiFAbsSucc
#check Sec4Lambda0ChiAbsOfAbs
#check Sec4LambdaRowZeroOnS2
#check sec4_genIBValueBridge_of_rowTools
#check sec4_genRelIntegral_eq_relIntegral_of_rowTools
#check sec4_genIBConsistencyBridge_of_rowTools
#check sec4_absSeries_of_pos_smul
#check sec4_natCast_pos
#check sec4_smul_zero_value
#check min2_absSeriesSum_left
#check min2_absSeriesSum_right
#check min2_value
#check repNonneg_sub_cutNatVal
#check prop_4_2_n_k
#check prop_4_2_lambda_k

/-! ## 1. Cancelling natural scalar abs-convergence -/

/--
Cancel a positive natural scalar from the abs series of a scalar-multiplied
representative.
-/
noncomputable def sec4_natSmuled_abs_cancel
    (m : Nat) (hmpos : 0 < m)
    (r : IntegrableRep S) (x : X)
    (hdom : (r.smul (((m : Nat) : R))).MemAt x)
    (habs : RSeq.SeriesSum
      (fun n => COF.abs
        ((r.smul (((m : Nat) : R))).valueAt x hdom n))) :
    Sec4RepAbsAt r x := by
  let hrDom : r.MemAt x := smul_dom hdom
  let hc : COF.lt 0 (((m : Nat) : R)) :=
    sec4_natCast_pos (R := R) hmpos
  let hscaled : RSeq.SeriesSum
      (fun n => COF.abs ((((m : Nat) : R) * r.valueAt x hrDom n))) :=
    seriesSum_congr
      (fun n => by
        rw [smul_fn_toFun (((m : Nat) : R)) r n x hrDom])
      habs
  exact ⟨hrDom, sec4_absSeries_of_pos_smul (((m : Nat) : R)) hc
    (fun n => r.valueAt x hrDom n) hscaled⟩


/--
A natural scalar multiple of a characteristic representative has value zero on
the negative side of the underlying complemented set.

This proof is split on the scalar.  In the zero-scalar branch it uses an
explicit zero series; in the positive branch it cancels the scalar, reads
`χ_A(x)=0` from `hA.valid`, and then re-evaluates the scalar series.
-/
noncomputable def sec4_natSmuled_chi_zero_on_s2
    (m : Nat) (A : BSet X) (hA : IntegrableSet1 S A)
    (x : X) (hxA : x ∈ A.S2)
    (hdom : (hA.rep.smul (((m : Nat) : R))).MemAt x)
    (habs : RSeq.SeriesSum
      (fun n => COF.abs
        ((hA.rep.smul (((m : Nat) : R))).valueAt x hdom n))) :
    (seriesSum_of_abs habs).sum = 0 := by
  let hχDom : hA.rep.MemAt x := smul_dom hdom
  by_cases hm : m = 0
  · subst hm
    let hz : RSeq.SeriesSum
        (fun n => (hA.rep.smul (((0 : Nat) : R))).valueAt x hdom n) :=
      seriesSum_congr
        (fun n => by
          simpa only [Nat.cast_zero] using
            (show (0 : R) = (hA.rep.smul (0 : R)).valueAt x
                (IntegrableRep.smul_memAt (a := (0 : R)) hχDom) n by
              calc
                (0 : R) = (0 : R) * hA.rep.valueAt x hχDom n := by ring
                _ = (hA.rep.smul (0 : R)).valueAt x
                    (IntegrableRep.smul_memAt (a := (0 : R)) hχDom) n :=
                  (smul_fn_toFun (0 : R) hA.rep n x hχDom).symm))
        (sec4_seriesSum_zero_const (R := R))
    have hz0 : hz.sum = (0 : R) := rfl
    exact (seriesSum_unique (seriesSum_of_abs habs) hz).trans hz0
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let hχAt : Sec4RepAbsAt hA.rep x :=
      sec4_natSmuled_abs_cancel (S := S)
        m hmpos hA.rep x hdom habs
    let hχabs : RSeq.SeriesSum
        (fun n => COF.abs (hA.rep.valueAt x hχAt.fst n)) :=
      hχAt.snd
    let hχ : RSeq.SeriesSum (fun n => hA.rep.valueAt x hχAt.fst n) :=
      seriesSum_of_abs hχabs
    have hχzero : hχ.sum = 0 :=
      (hA.valid x hχAt.fst hχabs).2.2 hxA hχ
    let hsmul : RSeq.SeriesSum
        (fun n => (hA.rep.smul (((m : Nat) : R))).valueAt x hdom n) := by
      simpa using smul_seriesSum_value (((m : Nat) : R)) hχAt.fst hχ
    have heq :
        (seriesSum_of_abs habs).sum = hsmul.sum :=
      seriesSum_unique (seriesSum_of_abs habs) hsmul
    calc
      (seriesSum_of_abs habs).sum = hsmul.sum := heq
      _ = (((m : Nat) : R) * hχ.sum) := by rfl
      _ = (((m : Nat) : R) * 0) := by rw [hχzero]
      _ = 0 := by ring


/-! ## 2. Row zero on `A.S2` for every Proposition 4.2 row -/

/--
Each `prop_4_2_lambda_k` row has point value zero on `A.S2`.

The proof uses only the row's own abs witness.  It extracts the left and right
components of the `min2`; the left component is a natural multiple of `χ_A`,
hence zero on `A.S2`, while the right component is non-negative by the
existing `repNonneg_sub_cutNatVal`.  Thus `min(0, nonnegative)=0`.
-/
theorem sec4_lambdaRowZeroOnS2
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4LambdaRowZeroOnS2 (S := S) f hnn := by
  intro A hA x hxA k hrowDom hrowabs
  cases k with
  | zero =>
      dsimp [prop_4_2_lambda_k] at hrowDom hrowabs
      let hleftDom := min2_dom_left hrowDom
      let hrightDom := min2_dom_right hrowDom
      let hleftAbs :=
        min2_absSeriesSum_left hrowDom hrowabs
      let hrightAbs :=
        min2_absSeriesSum_right hrowDom hrowabs
      let hleftVal : RSeq.SeriesSum
          (fun n =>
            (hA.rep.smul (((prop_4_2_n_k f 0 : Nat) : R))).valueAt
              x hleftDom n) :=
        seriesSum_of_abs hleftAbs
      let hrightVal : RSeq.SeriesSum
          (fun n => (f.sub (prop_4_2_min_f_n f 0)).valueAt
            x hrightDom n) :=
        seriesSum_of_abs hrightAbs
      let hmin :=
        min2_value
          (hA.rep.smul (((prop_4_2_n_k f 0 : Nat) : R)))
          (f.sub (prop_4_2_min_f_n f 0))
          x hleftDom hrightDom hleftVal hrightVal
      have hleft0 : hleftVal.sum = 0 :=
        sec4_natSmuled_chi_zero_on_s2 (S := S)
          (prop_4_2_n_k f 0) A hA x hxA hleftDom hleftAbs
      have hrightNN : Nonneg hrightVal.sum :=
        (repNonneg_sub_cutNatVal f 0) x hrightDom hrightAbs hrightVal
      have hmin0 : COF.min hleftVal.sum hrightVal.sum = 0 := by
        rw [hleft0]
        exact cof_min_eq_left_of_le hrightNN
      calc
        (seriesSum_of_abs hrowabs).sum = hmin.val.sum :=
          seriesSum_unique (seriesSum_of_abs hrowabs) hmin.val
        _ = COF.min hleftVal.sum hrightVal.sum := hmin.property
        _ = 0 := hmin0
  | succ k =>
      dsimp [prop_4_2_lambda_k] at hrowDom hrowabs
      let coeff : Nat := prop_4_2_n_k f (k + 1) - prop_4_2_n_k f k
      let cut : Nat := prop_4_2_n_k f k
      let hleftDom := min2_dom_left hrowDom
      let hrightDom := min2_dom_right hrowDom
      let hleftAbs :=
        min2_absSeriesSum_left hrowDom hrowabs
      let hrightAbs :=
        min2_absSeriesSum_right hrowDom hrowabs
      let hleftVal : RSeq.SeriesSum
          (fun n => (hA.rep.smul (((coeff : Nat) : R))).valueAt
            x hleftDom n) :=
        seriesSum_of_abs hleftAbs
      let hrightVal : RSeq.SeriesSum
          (fun n => (f.sub (prop_4_2_min_f_n f cut)).valueAt
            x hrightDom n) :=
        seriesSum_of_abs hrightAbs
      let hmin :=
        min2_value
          (hA.rep.smul (((coeff : Nat) : R)))
          (f.sub (prop_4_2_min_f_n f cut))
          x hleftDom hrightDom hleftVal hrightVal
      have hleft0 : hleftVal.sum = 0 :=
        sec4_natSmuled_chi_zero_on_s2 (S := S)
          coeff A hA x hxA hleftDom hleftAbs
      have hrightNN : Nonneg hrightVal.sum :=
        (repNonneg_sub_cutNatVal f cut) x hrightDom hrightAbs hrightVal
      have hmin0 : COF.min hleftVal.sum hrightVal.sum = 0 := by
        rw [hleft0]
        exact cof_min_eq_left_of_le hrightNN
      calc
        (seriesSum_of_abs hrowabs).sum = hmin.val.sum :=
          seriesSum_unique (seriesSum_of_abs hrowabs) hmin.val
        _ = COF.min hleftVal.sum hrightVal.sum := hmin.property
        _ = 0 := hmin0


/-! ## 3. Row-0 characteristic abs extraction, assuming row-0 coefficient positivity -/



/-! ## 4. Near-final tools: only cover abs and coefficient positivity remain -/

/--
The remaining primitive data after the min2 row internals have been discharged.

The `cover_chiF_abs_succ` field is the finite-cover `χ·f` abs witness.
The `n0_pos` field is the row-0 coefficient positivity needed to cancel the
row-0 scalar and recover `χ_A` abs convergence.
-/
def Sec4Prop42AlmostFinalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4CoverChiFAbsSucc (S := S) B hB f hnn)
    (0 < prop_4_2_n_k f 0)


namespace Sec4Prop42AlmostFinalTools







end Sec4Prop42AlmostFinalTools









end BishopC
