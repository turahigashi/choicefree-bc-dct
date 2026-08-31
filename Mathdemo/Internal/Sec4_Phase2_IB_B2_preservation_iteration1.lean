import Mathdemo.Internal.Sec4_Phase2_IB_B1_pointBridge_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-B2: preservation chain for `χ_A·f`

This chunk uses the B1 result

```lean
sec4_seriesSumRep_L1_repNonneg
```

to prove that the Proposition 4.2 representative `prop_4_2_chi_f_rep`
preserves `RepNonneg`.

The only mildly delicate point is scalar multiplication.  The coefficients
appearing in `prop_4_2_lambda_k` are natural-number casts.  We therefore prove
the specialized natural-cast scalar preservation by splitting the natural
coefficient into `0` and positive cases.  In the positive case we recover the
original absolute convergence by cancelling the positive scalar; in the zero
case the scaled value series is identically zero.

Every declaration is followed by a dependency-audit command.
-/

#check prop_4_2_chi_f_rep
#check prop_4_2_lambda_k
#check prop_4_2_n_k
#check prop_4_2_lambda_sum
#check prop_4_2_min_f_n
#check repNonneg_sub_cutNatVal
#check natCast_nonneg
#check IntegrableSet1.repNonneg
#check smul_fn_toFun
#check smul_seriesSum_value
#check sec4_min2_repNonneg
#check sec4_seriesSumRep_L1_repNonneg

/-! ## 1. Scalar and additive preservation -/

/-- The constantly zero series. -/
noncomputable def sec4_seriesSum_zero_const :
    RSeq.SeriesSum (fun _ : Nat => (0 : R)) :=
  seriesSum_congr
    (fun n => by
      by_cases hn : n = 0
      · simp [hn]
      · simp [hn])
    (seriesSum_single (0 : R))


/-- Natural casts of positive naturals are positive in the constructive field. -/
theorem sec4_natCast_pos {m : Nat} (hm : 0 < m) :
    COF.lt 0 ((m : Nat) : R) := by
  cases m with
  | zero => cases hm
  | succ k =>
      rw [Nat.cast_succ]
      have hk : Nonneg ((k : Nat) : R) := natCast_nonneg k
      have hlt : COF.lt ((k : Nat) : R) (((k : Nat) : R) + 1) := by
        have h := COF.lt_add_left ((k : Nat) : R) (COFO.one_pos (R := R))
        simpa using h
      exact BishopC.lt_of_le_of_lt hk hlt


/--
Cancel a positive scalar from an absolutely convergent scaled scalar series.

This is the scalar-series version needed in the positive natural-cast branch.
-/
noncomputable def sec4_absSeries_of_pos_smul
    (c : R) (hc : COF.lt 0 c) (u : Nat → R)
    (hscaled : RSeq.SeriesSum (fun n => COF.abs (c * u n))) :
    RSeq.SeriesSum (fun n => COF.abs (u n)) := by
  let hc_nonneg : Nonneg c := le_of_lt hc
  let hmul : RSeq.SeriesSum (fun n => c * COF.abs (u n)) :=
    seriesSum_congr
      (fun n => by
        rw [COFO.abs_mul, COFO.abs_of_nonneg hc_nonneg])
      hscaled
  let hinv := seriesSum_smul (COFO.inv c) hmul
  exact seriesSum_congr
    (fun n => by
      calc
        COFO.inv c * (c * COF.abs (u n)) =
            (c * COFO.inv c) * COF.abs (u n) := by ring
        _ = 1 * COF.abs (u n) := by rw [COFO.mul_inv_cancel hc]
        _ = COF.abs (u n) := by ring)
    hinv


/-- The point-value series for a zero scalar multiple is the zero series. -/
noncomputable def sec4_smul_zero_value
    (r : IntegrableRep S) (x : X) (hdom : r.MemAt x) :
    RSeq.SeriesSum (fun n => (r.smul (0 : R)).valueAt x
      (IntegrableRep.smul_memAt (a := (0 : R)) hdom) n) :=
  seriesSum_congr
    (fun n => by
      change (0 : R) = (0 : R) * r.valueAt x hdom n
      ring)
    (sec4_seriesSum_zero_const (R := R))


/--
Natural-cast scalar multiplication preserves `RepNonneg`.

This is the exact scalar preservation needed by `prop_4_2_lambda_k`.
-/
noncomputable def sec4_nat_smul_repNonneg
    (m : Nat) (r : IntegrableRep S) (hrnn : RepNonneg r) :
    RepNonneg (r.smul ((m : Nat) : R)) := by
  intro x hdom habs hx
  let hrDom : r.MemAt x := smul_dom hdom
  by_cases hm : m = 0
  · subst hm
    -- Technical note.
    -- Technical note.
    -- Technical note.
    let hzero : RSeq.SeriesSum (fun _ : Nat => (0 : R)) :=
      sec4_seriesSum_zero_const (R := R)
    let hz : RSeq.SeriesSum (fun n =>
        (IntegrableRep.smul ((0 : Nat) : R) r).valueAt x hdom n) :=
      seriesSum_congr (fun n => by
        change (0 : R) = ((0 : Nat) : R) * r.valueAt x hrDom n
        rw [Nat.cast_zero, zero_mul]) hzero
    have hzero_sum : hzero.sum = 0 := by
      dsimp [hzero, sec4_seriesSum_zero_const, BishopC.seriesSum_congr,
        BishopC.seriesSum_single]
    have hz0 : hz.sum = 0 := by
      change hzero.sum = 0
      exact hzero_sum
    have hx0 : hx.sum = 0 := (seriesSum_unique hx hz).trans hz0
    rw [hx0]
    exact nonneg_zero
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hc : COF.lt 0 (((m : Nat) : R)) :=
      sec4_natCast_pos (R := R) hmpos
    let hscaled : RSeq.SeriesSum
        (fun n => COF.abs ((((m : Nat) : R) * r.valueAt x hrDom n))) :=
      seriesSum_congr
        (fun n => by
          rw [smul_fn_toFun (((m : Nat) : R)) r n x hrDom])
        habs
    let hrAbs : RSeq.SeriesSum
        (fun n => COF.abs (r.valueAt x hrDom n)) :=
      sec4_absSeries_of_pos_smul (((m : Nat) : R)) hc
        (fun n => r.valueAt x hrDom n) hscaled
    let hrVal : RSeq.SeriesSum (fun n => r.valueAt x hrDom n) :=
      seriesSum_of_abs hrAbs
    let hsmul : RSeq.SeriesSum
        (fun n => (r.smul (((m : Nat) : R))).valueAt x hdom n) :=
      smul_seriesSum_value (((m : Nat) : R)) hrDom hrVal
    have hx_eq : hx.sum = hsmul.sum := seriesSum_unique hx hsmul
    rw [hx_eq]
    show Nonneg ((((m : Nat) : R) * hrVal.sum))
    exact COFO.mul_nonneg (le_of_lt hc) (hrnn x hrDom hrAbs hrVal)


/-- Addition preserves representation non-negativity. -/
noncomputable def sec4_add_repNonneg
    (r s : IntegrableRep S) (hrnn : RepNonneg r) (hsnn : RepNonneg s) :
    RepNonneg (r.add s) := by
  intro x hdom habs hx
  let hrDom : r.MemAt x := add_dom_left hdom
  let hsDom : s.MemAt x := add_dom_right hdom
  let hrAbs : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hrDom n)) :=
    add_absSeriesSum_left hdom habs
  let hsAbs : RSeq.SeriesSum (fun n => COF.abs (s.valueAt x hsDom n)) :=
    add_absSeriesSum_right hdom habs
  let hrVal : RSeq.SeriesSum (fun n => r.valueAt x hrDom n) :=
    seriesSum_of_abs hrAbs
  let hsVal : RSeq.SeriesSum (fun n => s.valueAt x hsDom n) :=
    seriesSum_of_abs hsAbs
  let hadd : RSeq.SeriesSum (fun n => (r.add s).valueAt x hdom n) :=
    add_seriesSum_value hrDom hsDom hrVal hsVal
  have hx_eq : hx.sum = hadd.sum := seriesSum_unique hx hadd
  rw [hx_eq]
  show Nonneg (hrVal.sum + hsVal.sum)
  exact nonneg_add
    (hrnn x hrDom hrAbs hrVal) (hsnn x hsDom hsAbs hsVal)


/-! ## 2. Proposition 4.2 preservation chain -/

/-- Every `prop_4_2_lambda_k` summand is non-negative. -/
noncomputable def sec4_prop42_lambda_k_repNonneg
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (n_k : Nat → Nat) :
    ∀ k : Nat, RepNonneg (prop_4_2_lambda_k A hA f n_k k) := by
  intro k
  cases k with
  | zero =>
      dsimp [prop_4_2_lambda_k]
      exact sec4_min2_repNonneg
        (sec4_nat_smul_repNonneg (S := S) (n_k 0) hA.rep
          (IntegrableSet1.repNonneg hA))
        (repNonneg_sub_cutNatVal f 0)
  | succ k =>
      dsimp [prop_4_2_lambda_k]
      exact sec4_min2_repNonneg
        (sec4_nat_smul_repNonneg (S := S) (n_k (k + 1) - n_k k) hA.rep
          (IntegrableSet1.repNonneg hA))
        (repNonneg_sub_cutNatVal f (n_k k))


/--
`χ_A · f` as built in Proposition 4.2 is non-negative whenever `f` is
non-negative.
-/
noncomputable def sec4_chi_f_repNonneg
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    RepNonneg (prop_4_2_chi_f_rep A hA f hnn) := by
  unfold prop_4_2_chi_f_rep
  exact sec4_seriesSumRep_L1_repNonneg
    (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
    _
    (sec4_prop42_lambda_k_repNonneg A hA f hnn (prop_4_2_n_k f))


/-- The base piece `χ_{A₀∧B}·f` is non-negative. -/
noncomputable def sec4IB_baseRepNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    RepNonneg (sec4IB_baseRep B hB f hnn) := by
  unfold sec4IB_baseRep
  exact sec4_chi_f_repNonneg (sec4CoverAnd B f 0)
    (sec4CoverAnd_int B hB f 0) f hnn


/-- Each layer piece `χ_{D_k}·f` is non-negative. -/
noncomputable def sec4IB_termRepNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) :
    RepNonneg (sec4IB_termRep B hB f hnn k) := by
  unfold sec4IB_termRep
  exact sec4_chi_f_repNonneg (sec4CoverDiff B f k)
    (sec4CoverDiff_int B hB f k) f hnn


/--
The tail representative is non-negative, now with its term non-negativity
discharged by `sec4IB_termRepNonneg`.
-/
noncomputable def sec4IB_tailRepNonneg_closed
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) B hB f hnn) :
    RepNonneg (sec4IB_tailRep B hB f hnn H) :=
  sec4IB_tailRepNonneg B hB f hnn H
    (fun k => sec4IB_termRepNonneg B hB f hnn k)


/-- The direct `I_B` candidate is non-negative once the tail majorant exists. -/
noncomputable def genIB_rep_from_tailData_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) B hB f hnn) :
    RepNonneg (genIB_rep_from_tailData B hB f hnn H) := by
  unfold genIB_rep_from_tailData
  exact sec4_add_repNonneg
    (sec4IB_baseRep B hB f hnn)
    (sec4IB_tailRep B hB f hnn H)
    (sec4IB_baseRepNonneg B hB f hnn)
    (sec4IB_tailRepNonneg_closed B hB f hnn H)


end BishopC
