import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b22_remainingAtomsAssembly_iteration1

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_add_absSeriesSum_fwd {r r' : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x)
    (hr' : Sec4RepAbsAt r' x) :
    Sec4RepAbsAt (r.add r') x :=
  sec4_repAbsAt_add r r' x hr hr'


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_neg_absSeriesSum_fwd {r : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x) :
    Sec4RepAbsAt r.neg x := by
  let hdom : r.neg.MemAt x := IntegrableRep.neg_memAt hr.fst
  exact ⟨hdom, seriesSum_congr
    (fun n => by rw [neg_fn_toFun r n x hr.fst, COFO.abs_neg]) hr.snd⟩


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_sub_absSeriesSum_fwd {r s : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x)
    (hs : Sec4RepAbsAt s x) :
    Sec4RepAbsAt (r.sub s) x :=
  sec4_add_absSeriesSum_fwd hr (sec4_neg_absSeriesSum_fwd hs)


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_min2_absSeriesSum {r s : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x)
    (hs : Sec4RepAbsAt s x) :
    Sec4RepAbsAt (IntegrableRep.min2 r s) x := by
  -- (r.sub s) abs
  let hsub : Sec4RepAbsAt (r.sub s) x :=
    sec4_sub_absSeriesSum_fwd hr hs
  -- Technical note.
  let habsValDom : (r.sub s).absVal.MemAt x :=
    (r.sub s).mem_absVal_dom hsub.fst
  let habsVal : Sec4RepAbsAt (r.sub s).absVal x :=
    ⟨habsValDom, by
      simpa only [IntegrableRep.valueAt] using
        ((r.sub s).absVal_absSeries hsub.fst hsub.snd)⟩
  -- (r.add s) abs
  let hadd : Sec4RepAbsAt (r.add s) x :=
    sec4_add_absSeriesSum_fwd hr hs
  -- inner = (r.add s).sub ((r.sub s).absVal) abs
  let hinner : Sec4RepAbsAt
      ((r.add s).sub ((r.sub s).absVal)) x :=
    sec4_sub_absSeriesSum_fwd hadd habsVal
  -- half scale: |min2.fn n| = half * |inner.fn n|
  have hhalf_nonneg : Nonneg (COF.half : R) := le_of_lt COFO.half_pos
  let hminDom : (IntegrableRep.min2 r s).MemAt x :=
    IntegrableRep.smul_memAt hinner.fst
  refine ⟨hminDom, seriesSum_congr (fun n => ?_)
    (seriesSum_smul (COF.half : R) hinner.snd)⟩
  show COF.half * COF.abs
      (((r.add s).sub ((r.sub s).absVal)).valueAt x hinner.fst n) =
    COF.abs ((IntegrableRep.min2 r s).valueAt x hminDom n)
  change COF.half * COF.abs
      (((r.add s).sub ((r.sub s).absVal)).valueAt x hinner.fst n) =
    COF.abs (COF.half *
      ((r.add s).sub ((r.sub s).absVal)).valueAt x hinner.fst n)
  rw [COFO.abs_mul, COFO.abs_of_nonneg hhalf_nonneg]


end BishopC
