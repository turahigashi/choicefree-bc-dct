import Mathdemo.ChoiceFreeDCTExamples

/-!
# Concrete end-to-end examples for the public Bishop--Cheng DCT API

This module supplies a nonempty concrete smoke model.  The integration space is
the degenerate zero-integral space on an arbitrary type; the public example
specializes it to `PUnit`.  All bounded functions are integrable and every
integral is represented by `0`.  The example is intentionally minimal, but it is
not merely a theorem-name check: it constructs the required convergence and
majorant data and then invokes the automatic good-set public DCT wrapper.
-/

namespace ChoiceFreeMeasureDCT

universe u

noncomputable section

def zeroSeriesSumC :
    BishopSec1P.RepSeriesSum (fun _ : Nat => BishopCReal.CReal.zero) :=
  BishopSec1P.repSeriesSum_congr
    (BishopSec1P.repSeriesSum_single BishopCReal.CReal.zero)
    (fun n => by
      by_cases hn : n = 0
      · rw [if_pos hn]
        exact BishopCReal.relEventually_refl BishopCReal.CReal.zero
      · rw [if_neg hn]
        exact BishopCReal.relEventually_refl BishopCReal.CReal.zero)

def absZeroSeriesSumC :
    BishopSec1P.RepSeriesSum
      (fun _ : Nat => BishopCReal.CReal.abs BishopCReal.CReal.zero) :=
  BishopSec1P.repSeriesSum_congr zeroSeriesSumC
    (fun _ => BishopCReal.CReal.abs_zero)

theorem zeroSeriesSum_uniqueC
    (h : BishopSec1P.RepSeriesSum
      (fun _ : Nat => BishopCReal.CReal.zero)) :
    h.sum ≈ BishopCReal.CReal.zero :=
  BishopSec1P.repSeriesSum_unique h zeroSeriesSumC

def zeroIntSpaceC (X : Type u) : BishopSec1P.IntSpaceC X where
  L := Set.univ
  I := fun _ => BishopCReal.CReal.zero
  L_resp := by
    intro f g hf hfg
    trivial
  I_resp := by
    intro f g hf hfg
    exact Setoid.refl BishopCReal.CReal.zero
  add_mem := by
    intro f g hf hg
    trivial
  smul_mem := by
    intro a f hf
    trivial
  abs_mem := by
    intro f hf
    trivial
  cutConst_mem := by
    intro a f hf
    trivial
  I_add := by
    intro f g hf hg
    exact Setoid.symm (BishopCReal.CReal.add_zero BishopCReal.CReal.zero)
  I_smul := by
    intro a f hf
    have hmul0 : BishopCReal.CReal.mul a BishopCReal.CReal.zero ≈
        BishopCReal.CReal.zero :=
      Setoid.trans (BishopCReal.CReal.mul_comm a BishopCReal.CReal.zero)
        (BishopSec1P.zero_mul_equivC a)
    exact Setoid.symm hmul0
  cutNat_tendsto := by
    intro f hf
    exact BishopSec1P.repSeriesTendsto_constC BishopCReal.CReal.zero
  cutSmall_tendsto := by
    intro f hf
    exact BishopSec1P.repSeriesTendsto_constC BishopCReal.CReal.zero
  I_nonneg := by
    intro f hf hnn
    exact BishopCReal.regularSeqLe_refl BishopCReal.CReal.zero
  continuity := by
    intro f fs hf hfs hnn hI hlt
    have hsum0 : hI.sum ≈ BishopCReal.CReal.zero :=
      zeroSeriesSum_uniqueC hI
    have hbad : BishopCReal.CReal.ltE
        BishopCReal.CReal.zero BishopCReal.CReal.zero :=
      BishopSec1P.regularSeqLtProp_of_left_eventual
        (BishopCReal.relEventually_symm _ _ hsum0) hlt
    exact False.elim (BishopCReal.CReal.ltE_irrefl
      BishopCReal.CReal.zero hbad)

def constBFunC (X : Type u) (c : BishopCReal.CReal) :
    BishopSec1P.BFunC X where
  toFun := fun _ => c
  dom := Set.univ

def zeroBFunC (X : Type u) : BishopSec1P.BFunC X :=
  constBFunC X BishopCReal.CReal.zero

def oneBFunC (X : Type u) : BishopSec1P.BFunC X :=
  constBFunC X BishopCReal.CReal.one

def zeroRepC (X : Type u) :
    BishopSec1P.IntegrableRepC3 (zeroIntSpaceC X) where
  fn := fun _ => zeroBFunC X
  fn_mem := by
    intro n
    trivial
  abs_integral_sum := zeroSeriesSumC
  integral_sum := zeroSeriesSumC

def oneRepC (X : Type u) :
    BishopSec1P.IntegrableRepC3 (zeroIntSpaceC X) :=
  BishopSec1P.IntegrableRepC3.ofL
    (S := zeroIntSpaceC X) (g := oneBFunC X) (by trivial)

theorem zeroIntSpace_integral_zeroC {X : Type u}
    (r : BishopSec1P.IntegrableRepC3 (zeroIntSpaceC X)) :
    r.integral ≈ BishopCReal.CReal.zero :=
  BishopSec1P.repSeriesSum_unique r.integral_sum zeroSeriesSumC

def zeroRep_value_seriesC (X : Type u) (x : X) :
    BishopSec1P.RepSeriesSum
      (fun n => ((zeroRepC X).fn n).toFun x) :=
  zeroSeriesSumC

def zeroRep_abs_seriesC (X : Type u) (x : X) :
    BishopSec1P.RepSeriesSum
      (fun n => BishopCReal.CReal.abs (((zeroRepC X).fn n).toFun x)) :=
  absZeroSeriesSumC

theorem zeroRep_value_sum_zeroC {X : Type u} {x : X}
    (h : BishopSec1P.RepSeriesSum
      (fun n => ((zeroRepC X).fn n).toFun x)) :
    h.sum ≈ BishopCReal.CReal.zero :=
  BishopSec1P.repSeriesSum_unique h (zeroRep_value_seriesC X x)

theorem zeroRep_abs_value_sum_zeroC {X : Type u} {x : X}
    (h : BishopSec1P.RepSeriesSum
      (fun n => BishopCReal.CReal.abs (((zeroRepC X).fn n).toFun x))) :
    (BishopSec1P.seriesSum_of_absC h).sum ≈ BishopCReal.CReal.zero :=
  zeroRep_value_sum_zeroC (BishopSec1P.seriesSum_of_absC h)

theorem zeroRep_nonnegC (X : Type u) :
    BishopSec1P.RepNonnegC (zeroRepC X) := by
  intro x habs hx
  exact BishopCReal.regularSeqNonneg_of_eventual
    (zeroRep_value_sum_zeroC hx)
    BishopSec1P.regularSeqNonneg_zero

theorem zeroRep_abs_sub_sum_ltC {X : Type u} {x : X}
    (hfabs hfnabs : BishopSec1P.RepSeriesSum
      (fun n => BishopCReal.CReal.abs (((zeroRepC X).fn n).toFun x)))
    {eps : BishopCReal.CReal}
    (heps : BishopCReal.regularSeqLtProp
      BishopCReal.CReal.zero eps) :
    BishopCReal.regularSeqLtProp
      (BishopCReal.CReal.abs
        (BishopCReal.CReal.sub
          (BishopSec1P.seriesSum_of_absC hfabs).sum
          (BishopSec1P.seriesSum_of_absC hfnabs).sum)) eps := by
  have hf0 :
      (BishopSec1P.seriesSum_of_absC hfabs).sum ≈
        BishopCReal.CReal.zero :=
    zeroRep_abs_value_sum_zeroC hfabs
  have hfn0 :
      (BishopSec1P.seriesSum_of_absC hfnabs).sum ≈
        BishopCReal.CReal.zero :=
    zeroRep_abs_value_sum_zeroC hfnabs
  have hsub0 : BishopCReal.CReal.sub
      (BishopSec1P.seriesSum_of_absC hfabs).sum
      (BishopSec1P.seriesSum_of_absC hfnabs).sum ≈
        BishopCReal.CReal.zero :=
    BishopCReal.relEventually_trans _ _ _
      (BishopCReal.CReal.sub_respects_equiv _ _ _ _ hf0 hfn0)
      (BishopCReal.subSeq_self_eventually_law BishopCReal.CReal.zero)
  have habs0 : BishopCReal.CReal.abs
      (BishopCReal.CReal.sub
        (BishopSec1P.seriesSum_of_absC hfabs).sum
        (BishopSec1P.seriesSum_of_absC hfnabs).sum) ≈
        BishopCReal.CReal.zero :=
    BishopCReal.relEventually_trans _ _ _
      (BishopCReal.absSeq_respects_eventually _ _ hsub0)
      BishopCReal.CReal.abs_zero
  exact BishopSec1P.regularSeqLtProp_of_left_eventual habs0 heps

theorem zeroRep_boundC (X : Type u) :
    forall (n : Nat) (x : X)
      (hfnv : BishopSec1P.RepSeriesSum
        (fun k => (((fun _ : Nat => zeroRepC X) n).fn k).toFun x))
      (hgv : BishopSec1P.RepSeriesSum
        (fun k => ((zeroRepC X).fn k).toFun x)),
        BishopCReal.RegularSeqLe
          (BishopCReal.CReal.abs hfnv.sum) hgv.sum := by
  intro n x hfnv hgv
  have hfn0 : hfnv.sum ≈ BishopCReal.CReal.zero :=
    zeroRep_value_sum_zeroC hfnv
  have hg0 : hgv.sum ≈ BishopCReal.CReal.zero :=
    zeroRep_value_sum_zeroC hgv
  have habs0 : BishopCReal.CReal.abs hfnv.sum ≈
      BishopCReal.CReal.zero :=
    BishopCReal.relEventually_trans _ _ _
      (BishopCReal.absSeq_respects_eventually _ _ hfn0)
      BishopCReal.CReal.abs_zero
  exact BishopCReal.regularSeqLe_trans
    (BishopCReal.regularSeqLe_of_relEventually habs0)
    (BishopCReal.regularSeqLe_of_relEventually
      (BishopCReal.relEventually_symm _ _ hg0))

noncomputable def zeroRep_goodSetConvergeC (X : Type u) :
    BishopSec3P.Lemma415ConvergeInMeasureGoodSetDataC
      (fun _ : Nat => zeroRepC X) (zeroRepC X) where
  close := by
    intro A hA eps heps
    refine ⟨0, ?_⟩
    intro n hn
    refine ⟨A, hA, ?_⟩
    refine
      { subset_A := fun x hx => hx
        doms := ?_
        measure_small := ?_
        point_close := ?_ }
    · intro x hx
      exact ⟨zeroRep_abs_seriesC X x, zeroRep_abs_seriesC X x⟩
    · exact BishopSec1P.regularSeqLtProp_of_left_eventual
        (zeroIntSpace_integral_zeroC
          ((BishopSec1P.IntegrableSet1_subC hA hA).rep))
        heps
    · intro x hx hfabs hfnabs
      exact zeroRep_abs_sub_sum_ltC hfabs hfnabs heps

/-- A fully concrete nonempty end-to-end invocation of the automatic corrected
good-set DCT wrapper. -/
noncomputable def punit_zero_dct_application_autoC :
    BishopSec1P.RepSeriesTendsto
      (fun n => (((fun _ : Nat => zeroRepC PUnit) n).integral))
      (zeroRepC PUnit).integral :=
  dominated_convergence_from_pointwise_majorant_good_set_profile_autoC
    (fun _ : Nat => zeroRepC PUnit)
    (zeroRepC PUnit)
    (zeroRepC PUnit)
    (zeroRep_nonnegC PUnit)
    (zeroRep_boundC PUnit)
    (zeroRep_goodSetConvergeC PUnit)

#check ChoiceFreeMeasureDCT.punit_zero_dct_application_autoC
#print axioms ChoiceFreeMeasureDCT.punit_zero_dct_application_autoC

end

end ChoiceFreeMeasureDCT
