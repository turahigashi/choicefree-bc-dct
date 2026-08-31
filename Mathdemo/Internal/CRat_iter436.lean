import Mathdemo.Internal.CRat_iter435

set_option linter.style.longLine false

/-!
# Stage A15: close the 4.6 value target for fixed `A`

The MCT representative built from the cutoff sequence represents the pointwise
limit of `min (chi_A * |f|) n`, hence `DataPFunR.chiMulAbs hA f`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Generic point-value bridge for `seriesSumRep_L1`: the flattened value is the
outer row series of the original row representatives. -/
noncomputable def stageA15_seriesSumRep_L1_value_rows
    (F : Nat -> IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hflatDom : (seriesSumRep_L1 F hsum).MemAt x)
    (hflatabs : RSeq.SeriesSum
      (fun n => COF.abs
        ((seriesSumRep_L1 F hsum).valueAt x hflatDom n))) :
    { hser : RSeq.SeriesSum (fun m =>
        (seriesSum_of_abs
          (seriesSumRep_L1_row_absConv F hsum hflatDom hflatabs m)).sum) //
        (seriesSum_of_abs hflatabs).sum = hser.sum } := by
  let P := sec4_make_pointBridge F hsum x hflatDom hflatabs
  let hser : RSeq.SeriesSum (fun m =>
      (seriesSum_of_abs
        (seriesSumRep_L1_row_absConv F hsum hflatDom hflatabs m)).sum) :=
    seriesSum_congr
      (fun m => seriesSum_unique (P.val.rowVal m)
        (seriesSum_of_abs
          (seriesSumRep_L1_row_absConv F hsum hflatDom hflatabs m)))
      P.val.rows
  exact ⟨hser, P.property.trans (seriesSum_unique P.val.rows hser)⟩

/-- A cutoff-difference row has the expected point value:
`lambda_m(x) = min(v,m+1) - min(v,m)`, where `v = chi_A * |f|`. -/
theorem stageA15_lambda_value_eq_cutoff_diff
    {df : DataPFunR X R} (hm : IsMeasurableData S df)
    (A : BSet X) (hA : IntegrableSet1 S A) (m : Nat) {x : X}
    (hp : (DataPFunR.chiMulAbs (S := S) hA df).domData x)
    (hlamDom :
      (thm_4_13_lambda (thm46CutoffSeq hm A hA) m).MemAt x)
    (hlamabs : RSeq.SeriesSum (fun k =>
      COF.abs ((thm_4_13_lambda (thm46CutoffSeq hm A hA) m).valueAt
        x hlamDom k))) :
    (seriesSum_of_abs hlamabs).sum
      = COF.min ((DataPFunR.chiMulAbs (S := S) hA df).toFun x hp)
          ((m + 1 : Nat) : R)
        - COF.min ((DataPFunR.chiMulAbs (S := S) hA df).toFun x hp)
          (m : R) := by
  let p := DataPFunR.chiMulAbs (S := S) hA df
  let fn := thm46CutoffSeq hm A hA
  let hsubDom : ((fn (m + 1)).add (fn m).neg).MemAt x := by
    simpa [fn, thm_4_13_lambda, IntegrableRep.sub] using hlamDom
  have hsubabs : RSeq.SeriesSum (fun k =>
      COF.abs (((fn (m + 1)).add (fn m).neg).valueAt x hsubDom k)) := by
    simpa [fn, thm_4_13_lambda, IntegrableRep.sub] using hlamabs
  let hnextDom : (fn (m + 1)).MemAt x := add_dom_left hsubDom
  let hnegCurrDom : (fn m).neg.MemAt x := add_dom_right hsubDom
  let hcurrDom : (fn m).MemAt x := neg_dom hnegCurrDom
  have hnext_abs : RSeq.SeriesSum
      (fun k => COF.abs ((fn (m + 1)).valueAt x hnextDom k)) :=
    add_absSeriesSum_left hsubDom hsubabs
  have hcurr_abs : RSeq.SeriesSum
      (fun k => COF.abs ((fn m).valueAt x hcurrDom k)) :=
    neg_absSeriesSum hnegCurrDom
      (add_absSeriesSum_right hsubDom hsubabs)
  let hnext := seriesSum_of_abs hnext_abs
  let hcurr := seriesSum_of_abs hcurr_abs
  have hsub_sum :
      (seriesSum_of_abs hsubabs).sum = hnext.sum - hcurr.sum := by
    have heq :=
      seriesSum_unique (seriesSum_of_abs hsubabs)
        (add_seriesSum_value hnextDom hnegCurrDom hnext
          (neg_seriesSum_value hcurrDom hcurr))
    change (seriesSum_of_abs hsubabs).sum = hnext.sum + -hcurr.sum at heq
    rwa [sub_eq_add_neg]
  have hnext_val :
      hnext.sum = COF.min (p.toFun x hp) ((m + 1 : Nat) : R) := by
    have hv :=
      (hm.represents A hA (m + 1)).value x hp hnextDom hnext_abs
    simpa [p, DataPFunR.cutNat, DataPFunR.cutConst, hnext] using hv
  have hcurr_val :
      hcurr.sum = COF.min (p.toFun x hp) (m : R) := by
    have hv := (hm.represents A hA m).value x hp hcurrDom hcurr_abs
    simpa [p, DataPFunR.cutNat, DataPFunR.cutConst, hcurr] using hv
  have hsub_sum' :
      (seriesSum_of_abs hlamabs).sum = hnext.sum - hcurr.sum := by
    have hsame := seriesSum_unique
      (seriesSum_of_abs hlamabs) (seriesSum_of_abs hsubabs)
    change (seriesSum_of_abs hlamabs).sum = (seriesSum_of_abs hsubabs).sum at hsame
    exact hsame.trans hsub_sum
  rw [hsub_sum', hnext_val, hcurr_val]

/-- The MCT representative over the cutoff sequence represents the fixed
`chi_A * |f|` data-function. -/
noncomputable def thm46MCTRep_represents_chiMulAbs
    (df : DataPFunR X R) (hm : IsMeasurableData S df)
    (A : BSet X) (hA : IntegrableSet1 S A) (c : R)
    (hlim : RSeq.TendstoHalf
      (fun n => (thm46CutoffSeq hm A hA n).integral) c) :
    Lemma414RepresentsDataPFunR (S := S)
      (thm46MCTRep hm A hA c hlim)
      (DataPFunR.chiMulAbs (S := S) hA df) where
  value := by
    intro x hp hrDom hrabs
    dsimp [thm46MCTRep, thm_4_13_monotone_convergence_faithful,
      thm_4_13_monotone_convergence] at hrDom hrabs ⊢
    let p := DataPFunR.chiMulAbs (S := S) hA df
    let fn := thm46CutoffSeq hm A hA
    let lambda := thm_4_13_lambda fn
    let hmono := thm_4_13_h_mono_of_nonneg fn (thm46CutoffSeq_mono hm A hA)
    let hsum := thm_4_13_lambda_sum fn hmono c hlim
    let g := seriesSumRep_L1 lambda hsum
    let h0Dom : (fn 0).MemAt x := add_dom_left hrDom
    let hgDom : g.MemAt x := add_dom_right hrDom
    have h0abs : RSeq.SeriesSum
        (fun k => COF.abs ((fn 0).valueAt x h0Dom k)) :=
      add_absSeriesSum_left hrDom hrabs
    have hgabs : RSeq.SeriesSum
        (fun k => COF.abs (g.valueAt x hgDom k)) :=
      add_absSeriesSum_right hrDom hrabs
    let h0 := seriesSum_of_abs h0abs
    let hg := seriesSum_of_abs hgabs
    obtain ⟨hRows, hG_rows⟩ :=
      stageA15_seriesSumRep_L1_value_rows lambda hsum hgDom hgabs
    let v := p.toFun x hp
    have h0_val : h0.sum = COF.min v (0 : R) := by
      have hv := (hm.represents A hA 0).value x hp h0Dom h0abs
      simpa [p, v, fn, DataPFunR.cutNat, DataPFunR.cutConst, h0] using hv
    have hterm : forall m,
        (seriesSum_of_abs
          (seriesSumRep_L1_row_absConv lambda hsum hgDom hgabs m)).sum
          = COF.min v ((m + 1 : Nat) : R) - COF.min v (m : R) := by
      intro m
      simpa [lambda, fn, p, v] using
        stageA15_lambda_value_eq_cutoff_diff
          (S := S) hm A hA m hp
          (seriesSumRep_L1_F_memAt lambda hsum hgDom m)
          (seriesSumRep_L1_row_absConv lambda hsum hgDom hgabs m)
    have htelescope : forall N,
        RSeq.partialSum
          (fun m =>
            (seriesSum_of_abs
              (seriesSumRep_L1_row_absConv lambda hsum hgDom hgabs m)).sum) N
          = COF.min v ((N + 1 : Nat) : R) - COF.min v (0 : R) := by
      intro N
      induction N with
      | zero =>
          simpa [RSeq.partialSum] using hterm 0
      | succ N ih =>
          change
            RSeq.partialSum
                (fun m =>
                  (seriesSum_of_abs
                    (seriesSumRep_L1_row_absConv lambda hsum hgDom hgabs m)).sum) N
              + (seriesSum_of_abs
                  (seriesSumRep_L1_row_absConv lambda hsum hgDom hgabs
                    (N + 1))).sum
              = COF.min v (((N + 1) + 1 : Nat) : R) - COF.min v (0 : R)
          rw [ih, hterm (N + 1)]
          ring
    obtain ⟨N0, hN0⟩ := exists_nat_ge v
    have hRows_sum : hRows.sum = v - COF.min v (0 : R) := by
      refine seriesSum_of_eventually_const hRows N0 ?_
      intro N hN
      rw [htelescope N]
      have hvN : Le v ((N + 1 : Nat) : R) :=
        le_trans hN0 (natCast_le_of_le (Nat.le_trans hN (Nat.le_succ N)))
      rw [min_eq_left_of_le hvN]
    have htotal :
        (seriesSum_of_abs hrabs).sum = h0.sum + hg.sum := by
      exact seriesSum_unique (seriesSum_of_abs hrabs)
        (add_seriesSum_value h0Dom hgDom h0 hg)
    calc
      (seriesSum_of_abs hrabs).sum = h0.sum + hg.sum := htotal
      _ = COF.min v (0 : R) + hRows.sum := by
        rw [h0_val, hG_rows]
      _ = COF.min v (0 : R) + (v - COF.min v (0 : R)) := by
        rw [hRows_sum]
      _ = v := by ring

noncomputable def thm_4_6_measurable_integrable_closed
    (df : DataPFunR X R) (hm : IsMeasurableData S df)
    (A : BSet X) (hA : IntegrableSet1 S A) (c : R)
    (hlim : RSeq.TendstoHalf
      (fun n => (thm46CutoffSeq hm A hA n).integral) c) :
    Sigma (fun rep : IntegrableRep S =>
      Lemma414RepresentsDataPFunR (S := S) rep
        (DataPFunR.chiMulAbs (S := S) hA df)) :=
  ⟨thm46MCTRep hm A hA c hlim,
    thm46MCTRep_represents_chiMulAbs (S := S) df hm A hA c hlim⟩

/-- Corollary 4.7 with the same closed target.  The cutoff domination hypothesis
is retained at the interface; `cor_4_7_dominates_cutoffs_discharged` from
iter435 supplies it from point-order data. -/
noncomputable def cor_4_7_measurable_integrable_closed
    (df : DataPFunR X R) (hm : IsMeasurableData S df)
    (g : IntegrableRep S) (A : BSet X) (hA : IntegrableSet1 S A)
    (hg_dom : forall n, Le ((thm46CutoffSeq hm A hA n).integral) g.integral)
    (hlim : RSeq.TendstoHalf
      (fun n => (thm46CutoffSeq hm A hA n).integral) g.integral) :
    Sigma (fun rep : IntegrableRep S =>
      Lemma414RepresentsDataPFunR (S := S) rep
        (DataPFunR.chiMulAbs (S := S) hA df)) :=
  have _h_dom := hg_dom
  thm_4_6_measurable_integrable_closed (S := S) df hm A hA g.integral hlim

structure StageA15Audit where
  represents_limit_discharged : Nat
  target_is_chiMulAbs_not_f : Nat
  a_exhaustion_used : Nat
  archimedean_min_limit_used : Nat
  value_telescope_used : Nat

def stageA15Audit : StageA15Audit where
  represents_limit_discharged := 1
  target_is_chiMulAbs_not_f := 1
  a_exhaustion_used := 0
  archimedean_min_limit_used := 1
  value_telescope_used := 1


end BishopC
