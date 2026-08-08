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
    (hflatabs : RSeq.SeriesSum
      (fun n => COF.abs (((seriesSumRep_L1 F hsum).fn n).toFun x))) :
    { hser : RSeq.SeriesSum (fun m =>
        (seriesSum_of_abs
          (seriesSumRep_L1_row_absConv F hsum hflatabs m)).sum) //
        (seriesSum_of_abs hflatabs).sum = hser.sum } := by
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_value F hsum hflatabs
  refine ⟨seriesSum_congr (fun m => ?_) hV, eV⟩
  rw [show
        (seriesSum_of_abs
          (row_seriesSum
            (fun i j => abs_nonneg (((G_m F i).fn j).toFun x))
            (add_absSeriesSum_left hflatabs) m)).sum
          = (IntegrableRep.ofL_value (psi_m_mem F m) x).val.sum
        from seriesSum_unique _ _,
      show
        (seriesSum_of_abs
          (row_seriesSum
            (fun i j => abs_nonneg (((tail_m F i).fn j).toFun x))
            (add_absSeriesSum_right hflatabs) m)).sum
          = (IntegrableRep.tailFrom_value (F m) (Nm F m) x
              (seriesSum_of_abs
                (seriesSumRep_L1_row_absConv F hsum hflatabs m))).val.sum
        from seriesSum_unique _ _]
  exact seriesSumRep_L1_hsplit_value F m
    (seriesSum_of_abs (seriesSumRep_L1_row_absConv F hsum hflatabs m))

/-- A cutoff-difference row has the expected point value:
`lambda_m(x) = min(v,m+1) - min(v,m)`, where `v = chi_A * |f|`. -/
theorem stageA15_lambda_value_eq_cutoff_diff
    {df : DataPFunR X R} (hm : IsMeasurableData S df)
    (A : BSet X) (hA : IntegrableSet1 S A) (m : Nat) {x : X}
    (hp : (DataPFunR.chiMulAbs (S := S) hA df).domData x)
    (hlamabs : RSeq.SeriesSum (fun k =>
      COF.abs (((thm_4_13_lambda (thm46CutoffSeq hm A hA) m).fn k).toFun x))) :
    (seriesSum_of_abs hlamabs).sum
      = COF.min ((DataPFunR.chiMulAbs (S := S) hA df).toFun x hp)
          ((m + 1 : Nat) : R)
        - COF.min ((DataPFunR.chiMulAbs (S := S) hA df).toFun x hp)
          (m : R) := by
  let p := DataPFunR.chiMulAbs (S := S) hA df
  let fn := thm46CutoffSeq hm A hA
  have hsubabs : RSeq.SeriesSum (fun k =>
      COF.abs ((((fn (m + 1)).add (fn m).neg).fn k).toFun x)) := by
    simpa [fn, thm_4_13_lambda, IntegrableRep.sub] using hlamabs
  have hnext_abs : RSeq.SeriesSum (fun k => COF.abs (((fn (m + 1)).fn k).toFun x)) :=
    add_absSeriesSum_left hsubabs
  have hcurr_abs : RSeq.SeriesSum (fun k => COF.abs (((fn m).fn k).toFun x)) :=
    neg_absSeriesSum (add_absSeriesSum_right hsubabs)
  let hnext := seriesSum_of_abs hnext_abs
  let hcurr := seriesSum_of_abs hcurr_abs
  have hsub_sum :
      (seriesSum_of_abs hsubabs).sum = hnext.sum - hcurr.sum := by
    have heq :=
      seriesSum_unique (seriesSum_of_abs hsubabs)
        (add_seriesSum_value hnext (neg_seriesSum_value hcurr))
    change (seriesSum_of_abs hsubabs).sum = hnext.sum + -hcurr.sum at heq
    rwa [sub_eq_add_neg]
  have hnext_val :
      hnext.sum = COF.min (p.toFun x hp) ((m + 1 : Nat) : R) := by
    have hv := (hm.represents A hA (m + 1)).value x hp hnext_abs
    simpa [p, DataPFunR.cutNat, DataPFunR.cutConst, hnext] using hv
  have hcurr_val :
      hcurr.sum = COF.min (p.toFun x hp) (m : R) := by
    have hv := (hm.represents A hA m).value x hp hcurr_abs
    simpa [p, DataPFunR.cutNat, DataPFunR.cutConst, hcurr] using hv
  have hsub_sum' :
      (seriesSum_of_abs hlamabs).sum = hnext.sum - hcurr.sum := by
    let hsub_signed : RSeq.SeriesSum (fun k =>
        ((thm_4_13_lambda (thm46CutoffSeq hm A hA) m).fn k).toFun x) :=
      seriesSum_congr (fun k => by
        simp [fn, thm_4_13_lambda, IntegrableRep.sub])
        (seriesSum_of_abs hsubabs)
    have hsame := seriesSum_unique (seriesSum_of_abs hlamabs) hsub_signed
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
    intro x hp hrabs
    dsimp [thm46MCTRep, thm_4_13_monotone_convergence_faithful,
      thm_4_13_monotone_convergence] at hrabs ⊢
    let p := DataPFunR.chiMulAbs (S := S) hA df
    let fn := thm46CutoffSeq hm A hA
    let lambda := thm_4_13_lambda fn
    let hmono := thm_4_13_h_mono_of_nonneg fn (thm46CutoffSeq_mono hm A hA)
    let hsum := thm_4_13_lambda_sum fn hmono c hlim
    let g := seriesSumRep_L1 lambda hsum
    have h0abs : RSeq.SeriesSum (fun k => COF.abs (((fn 0).fn k).toFun x)) :=
      add_absSeriesSum_left hrabs
    have hgabs : RSeq.SeriesSum (fun k => COF.abs (((g).fn k).toFun x)) :=
      add_absSeriesSum_right hrabs
    let h0 := seriesSum_of_abs h0abs
    let hg := seriesSum_of_abs hgabs
    obtain ⟨hRows, hG_rows⟩ :=
      stageA15_seriesSumRep_L1_value_rows lambda hsum hgabs
    let v := p.toFun x hp
    have h0_val : h0.sum = COF.min v (0 : R) := by
      have hv := (hm.represents A hA 0).value x hp h0abs
      simpa [p, v, fn, DataPFunR.cutNat, DataPFunR.cutConst, h0] using hv
    have hterm : forall m,
        (seriesSum_of_abs
          (seriesSumRep_L1_row_absConv lambda hsum hgabs m)).sum
          = COF.min v ((m + 1 : Nat) : R) - COF.min v (m : R) := by
      intro m
      simpa [lambda, fn, p, v] using
        stageA15_lambda_value_eq_cutoff_diff
          (S := S) hm A hA m hp
          (seriesSumRep_L1_row_absConv lambda hsum hgabs m)
    have htelescope : forall N,
        RSeq.partialSum
          (fun m =>
            (seriesSum_of_abs
              (seriesSumRep_L1_row_absConv lambda hsum hgabs m)).sum) N
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
                    (seriesSumRep_L1_row_absConv lambda hsum hgabs m)).sum) N
              + (seriesSum_of_abs
                  (seriesSumRep_L1_row_absConv lambda hsum hgabs (N + 1))).sum
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
        (add_seriesSum_value h0 hg)
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
