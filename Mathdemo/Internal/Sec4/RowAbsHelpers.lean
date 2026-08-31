import Mathdemo.Internal.Sec4.Min2AbsForward

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_smul_absSeriesSum (c : R) {r : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x) :
    Sec4RepAbsAt (IntegrableRep.smul c r) x := by
  let hdom : (IntegrableRep.smul c r).MemAt x :=
    IntegrableRep.smul_memAt hr.fst
  refine ⟨hdom, seriesSum_congr (fun n => ?_)
    (seriesSum_smul (COF.abs c) hr.snd)⟩
  show COF.abs c * COF.abs (r.valueAt x hr.fst n) =
    COF.abs ((IntegrableRep.smul c r).valueAt x hdom n)
  rw [smul_fn_toFun c r n x hr.fst, COFO.abs_mul]


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_fcut_absSeriesSum (n : Nat) {f : IntegrableRep S} {x : X}
    (hfabs : Sec4RepAbsAt f x) :
    Sec4RepAbsAt (f.sub (f.cutNatVal n)) x :=
  let hcutDom : (f.cutNatVal n).MemAt x :=
    f.mem_cutConstVal_dom (n : R) (natCast_nonneg n) hfabs.fst
  let hcutAbs : Sec4RepAbsAt (f.cutNatVal n) x :=
    ⟨hcutDom, by
      simpa only [IntegrableRep.valueAt] using
        (f.cutConstVal_absSeries
          (n : R) (natCast_nonneg n) hfabs.fst hfabs.snd)⟩
  sec4_sub_absSeriesSum_fwd hfabs hcutAbs


/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_lambdaRowAbs_of_chiF_fabs
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (n_k : Nat → Nat) (x : X)
    (hχabs : Sec4RepAbsAt hA.rep x)
    (hfabs : Sec4RepAbsAt f x) :
    ∀ k, Sec4RepAbsAt (prop_4_2_lambda_k A hA f n_k k) x := by
  intro k
  cases k with
  | zero =>
    show Sec4RepAbsAt
      ((hA.rep.smul (n_k 0 : R)).min2
        (f.sub (prop_4_2_min_f_n f 0))) x
    exact sec4_min2_absSeriesSum
      (sec4_smul_absSeriesSum ((n_k 0 : R)) hχabs)
      (sec4_fcut_absSeriesSum 0 hfabs)
  | succ k =>
    show Sec4RepAbsAt
      ((hA.rep.smul (((n_k (k + 1) - n_k k : Nat) : R))).min2
        (f.sub (prop_4_2_min_f_n f (n_k k)))) x
    exact sec4_min2_absSeriesSum
      (sec4_smul_absSeriesSum (((n_k (k + 1) - n_k k : Nat) : R)) hχabs)
      (sec4_fcut_absSeriesSum (n_k k) hfabs)


end BishopC
