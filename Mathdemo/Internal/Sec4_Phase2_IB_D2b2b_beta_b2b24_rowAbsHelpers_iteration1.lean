import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b23_min2AbsForward_iteration1

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_smul_absSeriesSum (c : R) {r : IntegrableRep S} {x : X}
    (hr : RSeq.SeriesSum (fun k => COF.abs ((r.fn k).toFun x))) :
    RSeq.SeriesSum (fun n => COF.abs (((IntegrableRep.smul c r).fn n).toFun x)) := by
  refine seriesSum_congr (fun n => ?_) (seriesSum_smul (COF.abs c) hr)
  show COF.abs c * COF.abs ((r.fn n).toFun x)
      = COF.abs (((IntegrableRep.smul c r).fn n).toFun x)
  rw [smul_fn_toFun, COFO.abs_mul]


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_fcut_absSeriesSum (n : Nat) {f : IntegrableRep S} {x : X}
    (hfabs : RSeq.SeriesSum (fun k => COF.abs ((f.fn k).toFun x))) :
    RSeq.SeriesSum (fun m => COF.abs (((f.sub (f.cutNatVal n)).fn m).toFun x)) :=
  sec4_sub_absSeriesSum_fwd hfabs
    (f.cutConstVal_absSeries (n : R) (natCast_nonneg n) hfabs)


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_lambdaRowAbs_of_chiF_fabs
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (n_k : Nat → Nat) (x : X)
    (hχabs : RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x)))
    (hfabs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))) :
    ∀ k, RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_lambda_k A hA f n_k k).fn m).toFun x)) := by
  intro k
  cases k with
  | zero =>
    show RSeq.SeriesSum
      (fun m => COF.abs
        ((((hA.rep.smul ((n_k 0 : R))).min2 (f.sub (prop_4_2_min_f_n f 0))).fn m).toFun x))
    exact sec4_min2_absSeriesSum
      (sec4_smul_absSeriesSum ((n_k 0 : R)) hχabs)
      (sec4_fcut_absSeriesSum 0 hfabs)
  | succ k =>
    show RSeq.SeriesSum
      (fun m => COF.abs
        ((((hA.rep.smul (((n_k (k + 1) - n_k k : Nat) : R))).min2
            (f.sub (prop_4_2_min_f_n f (n_k k)))).fn m).toFun x))
    exact sec4_min2_absSeriesSum
      (sec4_smul_absSeriesSum (((n_k (k + 1) - n_k k : Nat) : R)) hχabs)
      (sec4_fcut_absSeriesSum (n_k k) hfabs)


end BishopC
