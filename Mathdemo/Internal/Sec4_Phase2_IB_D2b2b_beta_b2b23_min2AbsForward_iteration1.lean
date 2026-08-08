import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b22_remainingAtomsAssembly_iteration1

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_add_absSeriesSum_fwd {r r' : IntegrableRep S} {x : X}
    (hr : RSeq.SeriesSum (fun k => COF.abs ((r.fn k).toFun x)))
    (hr' : RSeq.SeriesSum (fun k => COF.abs ((r'.fn k).toFun x))) :
    RSeq.SeriesSum (fun n => COF.abs (((r.add r').fn n).toFun x)) := by
  refine seriesSum_congr (fun n => ?_) (seriesSum_interleave hr hr')
  show seqInterleave (fun k => COF.abs ((r.fn k).toFun x))
          (fun k => COF.abs ((r'.fn k).toFun x)) n
      = COF.abs (((r.add r').fn n).toFun x)
  rw [add_fn_toFun]
  by_cases hn : n % 2 = 0
  · show (if n % 2 = 0 then COF.abs ((r.fn (n / 2)).toFun x)
            else COF.abs ((r'.fn (n / 2)).toFun x))
        = COF.abs (if n % 2 = 0 then (r.fn (n / 2)).toFun x else (r'.fn (n / 2)).toFun x)
    rw [if_pos hn, if_pos hn]
  · show (if n % 2 = 0 then COF.abs ((r.fn (n / 2)).toFun x)
            else COF.abs ((r'.fn (n / 2)).toFun x))
        = COF.abs (if n % 2 = 0 then (r.fn (n / 2)).toFun x else (r'.fn (n / 2)).toFun x)
    rw [if_neg hn, if_neg hn]


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_neg_absSeriesSum_fwd {r : IntegrableRep S} {x : X}
    (hr : RSeq.SeriesSum (fun k => COF.abs ((r.fn k).toFun x))) :
    RSeq.SeriesSum (fun n => COF.abs (((r.neg).fn n).toFun x)) :=
  seriesSum_congr (fun n => by rw [neg_fn_toFun, COFO.abs_neg]) hr


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_sub_absSeriesSum_fwd {r s : IntegrableRep S} {x : X}
    (hr : RSeq.SeriesSum (fun k => COF.abs ((r.fn k).toFun x)))
    (hs : RSeq.SeriesSum (fun k => COF.abs ((s.fn k).toFun x))) :
    RSeq.SeriesSum (fun n => COF.abs (((r.sub s).fn n).toFun x)) :=
  sec4_add_absSeriesSum_fwd hr (sec4_neg_absSeriesSum_fwd hs)


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_min2_absSeriesSum {r s : IntegrableRep S} {x : X}
    (hr : RSeq.SeriesSum (fun k => COF.abs ((r.fn k).toFun x)))
    (hs : RSeq.SeriesSum (fun k => COF.abs ((s.fn k).toFun x))) :
    RSeq.SeriesSum (fun n => COF.abs (((IntegrableRep.min2 r s).fn n).toFun x)) := by
  -- (r.sub s) abs
  have hsub : RSeq.SeriesSum (fun n => COF.abs (((r.sub s).fn n).toFun x)) :=
    sec4_sub_absSeriesSum_fwd hr hs
  -- Technical note.
  have habsVal : RSeq.SeriesSum (fun n => COF.abs (((r.sub s).absVal.fn n).toFun x)) :=
    (r.sub s).absVal_absSeries hsub
  -- (r.add s) abs
  have hadd : RSeq.SeriesSum (fun n => COF.abs (((r.add s).fn n).toFun x)) :=
    sec4_add_absSeriesSum_fwd hr hs
  -- inner = (r.add s).sub ((r.sub s).absVal) abs
  have hinner :
      RSeq.SeriesSum
        (fun n => COF.abs ((((r.add s).sub ((r.sub s).absVal)).fn n).toFun x)) :=
    sec4_sub_absSeriesSum_fwd hadd habsVal
  -- half scale: |min2.fn n| = half * |inner.fn n|
  have hhalf_nonneg : Nonneg (COF.half : R) := le_of_lt COFO.half_pos
  refine seriesSum_congr (fun n => ?_) (seriesSum_smul (COF.half : R) hinner)
  show COF.half * COF.abs ((((r.add s).sub ((r.sub s).absVal)).fn n).toFun x)
      = COF.abs (((IntegrableRep.min2 r s).fn n).toFun x)
  show COF.half * COF.abs ((((r.add s).sub ((r.sub s).absVal)).fn n).toFun x)
      = COF.abs (((IntegrableRep.smul (COF.half : R)
            ((r.add s).sub ((r.sub s).absVal))).fn n).toFun x)
  rw [smul_fn_toFun, COFO.abs_mul, COFO.abs_of_nonneg hhalf_nonneg]


end BishopC
