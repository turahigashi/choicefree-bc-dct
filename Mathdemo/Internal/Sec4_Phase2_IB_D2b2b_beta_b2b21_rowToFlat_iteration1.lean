import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b20_absOuterPack_iteration1

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_rowToFlat_source :
    Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S) := by
  intro F hsum x hrows hrowsum
  -- seriesSumRep_L1 = Gint.add Tint
  set Gint : IntegrableRep S :=
    seriesIntegrable (G_m F) (G_m_absConv_seriesSum F hsum) with hGdef
  set Tint : IntegrableRep S :=
    seriesIntegrable (tail_m F) (tail_m_absConv_seriesSum F) with hTdef
  -- ===================== G side (head, ofL single term) =====================
  -- Technical note.
  -- Technical note.
  have hGcongr : ∀ i j,
      (if j = 0 then COF.abs ((psi_m F i).toFun x) else (0 : R))
        = COF.abs (((G_m F i).fn j).toFun x) := by
    intro i j
    by_cases hj : j = 0
    · subst hj; rfl
    · rw [if_neg hj]
      show (0 : R) = COF.abs (((G_m F i).fn j).toFun x)
      have hz : ((G_m F i).fn j).toFun x = (0 : R) := by
        show (if j = 0 then psi_m F i else BFunR.smul (0 : R) (psi_m F i)).toFun x = 0
        rw [if_neg hj]
        show (0 : R) * (psi_m F i).toFun x = 0
        ring
      rw [hz, COFO.abs_zero]
  let hrowG : ∀ i, RSeq.SeriesSum (fun j => COF.abs (((G_m F i).fn j).toFun x)) :=
    fun i => seriesSum_congr (hGcongr i) (seriesSum_single (COF.abs ((psi_m F i).toFun x)))
  -- Technical note.
  have hboundG : ∀ i, Le (COF.abs ((psi_m F i).toFun x)) ((hrows i).sum) := by
    intro i
    refine le_trans (abs_seqSum_le (r := F i) x (Nm F i)) ?_
    rw [BFunR.seqSum_toFun]
    exact partialSum_le_sum (fun n => abs_nonneg _) (hrows i) (Nm F i)
  -- Technical note.
  have hrowsumG : RSeq.SeriesSum (fun i => (hrowG i).sum) :=
    seriesSum_comparison
      (a := fun i => (hrowG i).sum) (b := fun i => (hrows i).sum)
      (fun i => by
        show Nonneg (COF.abs ((psi_m F i).toFun x)); exact abs_nonneg _)
      (fun i => by
        show Le (COF.abs ((psi_m F i).toFun x)) ((hrows i).sum); exact hboundG i)
      hrowsum
  -- flatten G。
  have hflatG : RSeq.SeriesSum (fun m => COF.abs ((Gint.fn m).toFun x)) :=
    cellAt_seriesSum
      (a := fun i j => COF.abs (((G_m F i).fn j).toFun x))
      (fun i j => abs_nonneg _) hrowG hrowsumG
  -- ===================== T side (tail) =====================
  -- Technical note.
  let hrowT : ∀ i, RSeq.SeriesSum (fun j => COF.abs (((tail_m F i).fn j).toFun x)) :=
    fun i => seriesSum_tail (hrows i) (Nm F i)
  -- Technical note.
  have hrowsumT : RSeq.SeriesSum (fun i => (hrowT i).sum) :=
    seriesSum_comparison
      (a := fun i => (hrowT i).sum) (b := fun i => (hrows i).sum)
      (fun i => seriesSum_nonneg (fun j => abs_nonneg _) (hrowT i))
      (fun i => by
        show Le ((hrows i).sum
              - RSeq.partialSum (fun m => COF.abs (((F i).fn m).toFun x)) (Nm F i))
            ((hrows i).sum)
        refine le_of_nonneg_sub ?_
        rw [show (hrows i).sum
              - ((hrows i).sum
                - RSeq.partialSum (fun m => COF.abs (((F i).fn m).toFun x)) (Nm F i))
            = RSeq.partialSum (fun m => COF.abs (((F i).fn m).toFun x)) (Nm F i) from by ring]
        exact partialSum_nonneg (fun n => abs_nonneg (((F i).fn n).toFun x)) (Nm F i))
      hrowsum
  -- flatten T。
  have hflatT : RSeq.SeriesSum (fun m => COF.abs ((Tint.fn m).toFun x)) :=
    cellAt_seriesSum
      (a := fun i j => COF.abs (((tail_m F i).fn j).toFun x))
      (fun i j => abs_nonneg _) hrowT hrowsumT
  -- ===================== reverse interleave =====================
  refine seriesSum_congr (fun m => ?_) (seriesSum_interleave hflatG hflatT)
  show seqInterleave (fun k => COF.abs ((Gint.fn k).toFun x))
        (fun k => COF.abs ((Tint.fn k).toFun x)) m
      = COF.abs (((Gint.add Tint).fn m).toFun x)
  rw [add_fn_toFun Gint Tint m x]
  by_cases hm : m % 2 = 0
  · show (if m % 2 = 0 then COF.abs ((Gint.fn (m / 2)).toFun x)
          else COF.abs ((Tint.fn (m / 2)).toFun x))
        = COF.abs (if m % 2 = 0 then (Gint.fn (m / 2)).toFun x
                    else (Tint.fn (m / 2)).toFun x)
    rw [if_pos hm, if_pos hm]
  · show (if m % 2 = 0 then COF.abs ((Gint.fn (m / 2)).toFun x)
          else COF.abs ((Tint.fn (m / 2)).toFun x))
        = COF.abs (if m % 2 = 0 then (Gint.fn (m / 2)).toFun x
                    else (Tint.fn (m / 2)).toFun x)
    rw [if_neg hm, if_neg hm]


end BishopC
