import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b20_absOuterPack_iteration1

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Flatten row domains and row absolute convergence through `cellAt`. -/
noncomputable def sec4_seriesIntegrable_absAt_of_rows
    (H : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun i => (H i).absConv.sum))
    (x : X)
    (hrows : ∀ i : Nat, Sec4RepAbsAt (H i) x)
    (houter : RSeq.SeriesSum (fun i => (hrows i).snd.sum)) :
    Sec4RepAbsAt (seriesIntegrable H hsum) x := by
  let hflatDom : (seriesIntegrable H hsum).MemAt x :=
    fun k => (hrows (cellAt k).1).fst (cellAt k).2
  refine ⟨hflatDom, ?_⟩
  simpa only [seriesIntegrable, IntegrableRep.valueAt] using
    (cellAt_seriesSum
      (a := fun i j => COF.abs ((H i).valueAt x (hrows i).fst j))
      (fun i j => abs_nonneg _)
      (fun i => (hrows i).snd)
      houter)


/-- Absolute convergence is preserved when two pointwise representatives are interleaved. -/
noncomputable def sec4_repAbsAt_add
    (r s : IntegrableRep S) (x : X)
    (hr : Sec4RepAbsAt r x) (hs : Sec4RepAbsAt s x) :
    Sec4RepAbsAt (r.add s) x := by
  let hdom : (r.add s).MemAt x :=
    IntegrableRep.add_memAt hr.fst hs.fst
  refine ⟨hdom, seriesSum_congr (fun n => ?_)
    (seriesSum_interleave hr.snd hs.snd)⟩
  rw [add_fn_toFun r s n x hr.fst hs.fst]
  by_cases hn : n % 2 = 0
  · simp [seqInterleave, hn]
  · simp [seqInterleave, hn]


/-- A finite pointwise prefix is bounded by the sum of an absolute-value series. -/
theorem sec4_abs_seqSum_le_seriesSum
    (r : IntegrableRep S) (x : X) (hdom : r.MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hdom n)))
    (N : Nat) :
    Le (COF.abs ((BFunR.seqSum r.fn N).toFun x
          (BFunR.seqSum_mem r.fn x hdom N))) habs.sum := by
  refine le_trans
    (abs_seqSum_le (r := r) x N (BFunR.seqSum_mem r.fn x hdom N)) ?_
  have hvalue := BFunR.seqSum_toFun
    (fun k => BFunR.absf (r.fn k)) x (fun k => hdom k) N
  rw [hvalue]
  exact partialSum_le_sum (fun n => abs_nonneg _) habs N


set_option maxHeartbeats 500000 in
/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_rowToFlat_source :
    Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S) := by
  intro F hsum x hrows hrowsum
  let hFDom : ∀ i : Nat, (F i).MemAt x := fun i => (hrows i).fst
  let hFAbs : ∀ i : Nat,
      RSeq.SeriesSum (fun j => COF.abs ((F i).valueAt x (hFDom i) j)) :=
    fun i => (hrows i).snd

  -- The finite-prefix `G_m` rows.
  let hPsiDom : ∀ i : Nat, x ∈ (psi_m F i).dom :=
    fun i => BFunR.seqSum_mem (F i).fn x (hFDom i) (Nm F i)
  let hGDom : ∀ i : Nat, (G_m F i).MemAt x :=
    fun i => IntegrableRep.ofL_memAt (psi_m_mem F i) (hPsiDom i)
  have hGcongr : ∀ i j,
      (if j = 0 then COF.abs ((psi_m F i).toFun x (hPsiDom i))
        else (0 : R)) =
        COF.abs ((G_m F i).valueAt x (hGDom i) j) := by
    intro i j
    by_cases hj : j = 0
    · subst hj; rfl
    · simp only [hj, if_false, G_m, IntegrableRep.valueAt,
        IntegrableRep.ofL, BFunR.smul, zero_mul, COFO.abs_zero]
  let hGAbs : ∀ i, RSeq.SeriesSum
      (fun j => COF.abs ((G_m F i).valueAt x (hGDom i) j)) :=
    fun i => seriesSum_congr (hGcongr i)
      (seriesSum_single (COF.abs ((psi_m F i).toFun x (hPsiDom i))))
  let hGRows : ∀ i : Nat, Sec4RepAbsAt (G_m F i) x :=
    fun i => ⟨hGDom i, hGAbs i⟩
  have hboundG : ∀ i,
      Le (COF.abs ((psi_m F i).toFun x (hPsiDom i))) (hFAbs i).sum := by
    intro i
    change Le (COF.abs ((BFunR.seqSum (F i).fn (Nm F i)).toFun x
      (BFunR.seqSum_mem (F i).fn x (hrows i).fst (Nm F i)))) (hrows i).snd.sum
    exact sec4_abs_seqSum_le_seriesSum
      (F i) x (hrows i).fst (hrows i).snd (Nm F i)
  have hrowsumG : RSeq.SeriesSum (fun i => (hGRows i).snd.sum) :=
    seriesSum_comparison
      (a := fun i => (hGAbs i).sum) (b := fun i => (hFAbs i).sum)
      (fun i => by
        show Nonneg (COF.abs ((psi_m F i).toFun x (hPsiDom i)))
        exact abs_nonneg _)
      (fun i => by
        show Le (COF.abs ((psi_m F i).toFun x (hPsiDom i))) (hFAbs i).sum
        exact hboundG i)
      hrowsum
  let hflatG : Sec4RepAbsAt
      (seriesIntegrable (G_m F) (G_m_absConv_seriesSum F hsum)) x :=
    sec4_seriesIntegrable_absAt_of_rows
      (G_m F) (G_m_absConv_seriesSum F hsum) x hGRows hrowsumG

  -- The tail rows.
  let hTDom : ∀ i : Nat, (tail_m F i).MemAt x :=
    fun i => IntegrableRep.tailFrom_memAt (Nm F i) (hFDom i)
  let hTAbs : ∀ i, RSeq.SeriesSum
      (fun j => COF.abs ((tail_m F i).valueAt x (hTDom i) j)) :=
    fun i => by
      simpa only [tail_m, IntegrableRep.tailFrom, IntegrableRep.valueAt] using
        (seriesSum_tail (hFAbs i) (Nm F i))
  let hTRows : ∀ i : Nat, Sec4RepAbsAt (tail_m F i) x :=
    fun i => ⟨hTDom i, hTAbs i⟩
  have hrowsumT : RSeq.SeriesSum (fun i => (hTRows i).snd.sum) :=
    seriesSum_comparison
      (a := fun i => (hTAbs i).sum) (b := fun i => (hFAbs i).sum)
      (fun i => seriesSum_nonneg (fun j => abs_nonneg _) (hTAbs i))
      (fun i => by
        show Le ((hFAbs i).sum - RSeq.partialSum
              (fun m => COF.abs ((F i).valueAt x (hFDom i) m)) (Nm F i))
            (hFAbs i).sum
        refine le_of_nonneg_sub ?_
        rw [show (hFAbs i).sum - ((hFAbs i).sum - RSeq.partialSum
              (fun m => COF.abs ((F i).valueAt x (hFDom i) m)) (Nm F i)) =
            RSeq.partialSum
              (fun m => COF.abs ((F i).valueAt x (hFDom i) m)) (Nm F i)
          from by ring]
        exact partialSum_nonneg (fun n => abs_nonneg _) (Nm F i))
      hrowsum
  let hflatT : Sec4RepAbsAt
      (seriesIntegrable (tail_m F) (tail_m_absConv_seriesSum F)) x :=
    sec4_seriesIntegrable_absAt_of_rows
      (tail_m F) (tail_m_absConv_seriesSum F) x hTRows hrowsumT

  simpa only [seriesSumRep_L1] using
    (sec4_repAbsAt_add
      (seriesIntegrable (G_m F) (G_m_absConv_seriesSum F hsum))
      (seriesIntegrable (tail_m F) (tail_m_absConv_seriesSum F))
      x hflatG hflatT)


end BishopC
