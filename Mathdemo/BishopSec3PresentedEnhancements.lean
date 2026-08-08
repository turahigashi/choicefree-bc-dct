import Mathdemo.BishopSec3Presented

/-!
# Public API enhancements for the Bishop--Cheng DCT artifact

This module adds paper-facing wrappers that separate the L1 error convergence
endpoint from the integral convergence endpoint.  The proofs are direct
compositions of the already audited Lemma 4.14, Lemma 4.3, and Theorem 4.15
implementation declarations.
-/

namespace BishopSec3P

universe u

/-- L1 error convergence from a nonnegative majorant, level-set data for that
majorant, domination of the absolute-error representatives, and measure
convergence of the absolute error to zero. -/
noncomputable def lemma414_l1_error_tendsto_zero_from_majorant_measure_convergeC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (D : Lemma43LevelSetSeqDataC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :
    BishopSec1P.RepSeriesTendsto
      (fun n => (BishopSec1P.thm_4_15_abs_errorC fn f n).integral)
      BishopCReal.CReal.zero :=
  BishopSec1P.lemma_4_14_tendsto_zero_from_uniform_and_rep_convergeC
    (BishopSec1P.thm_4_15_abs_errorC fn f) herr_nn
    (fun eps heps =>
      lemma43UniformComplementData_of_majorantC
        (BishopSec1P.thm_4_15_abs_errorC fn f)
        herr_nn g hgnn D hdom eps heps)
    (BishopSec1P.lemma_4_14_rep_converge_from_source_measure_converge_zeroC
      (BishopSec1P.thm_4_15_abs_errorC fn f) hconv)

/-- Smooth-level version of the L1 error convergence endpoint. -/
noncomputable def lemma414_l1_error_tendsto_zero_from_majorant_smooth_measure_convergeC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :
    BishopSec1P.RepSeriesTendsto
      (fun n => (BishopSec1P.thm_4_15_abs_errorC fn f n).integral)
      BishopCReal.CReal.zero :=
  lemma414_l1_error_tendsto_zero_from_majorant_measure_convergeC
    fn f herr_nn g hgnn
    (lemma43LevelSetSeqDataC_of_dyadicSmoothDataC g Dsmooth)
    hdom hconv

/-- Smooth-level L1 endpoint with the absolute-error nonnegativity supplied
canonically by the absolute-value construction. -/
noncomputable def lemma414_l1_error_tendsto_zero_from_majorant_smooth_measure_converge_autoNonnegC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :
    BishopSec1P.RepSeriesTendsto
      (fun n => (BishopSec1P.thm_4_15_abs_errorC fn f n).integral)
      BishopCReal.CReal.zero :=
  lemma414_l1_error_tendsto_zero_from_majorant_smooth_measure_convergeC
    fn f (thm_4_15_abs_error_nonnegC fn f) g hgnn Dsmooth hdom hconv

end BishopSec3P

namespace BishopSec1P

namespace IntegrableSet1C

/-- If an integrable characteristic representative has value `1` at a point,
then that point is in the positive side of the represented set. -/
theorem mem_s1_of_indicator_oneC
    {X : Type u} {S : IntSpaceC X} {C : BishopC.BSet X}
    (hC : IntegrableSet1C S C) {x : X}
    (hchi_abs : RepSeriesSum (fun n => BishopCReal.CReal.abs ((hC.rep.fn n).toFun x)))
    (hone : BishopCReal.relEventually (seriesSum_of_absC hchi_abs).sum
      BishopCReal.CReal.one) :
    x ∈ C.S1 := by
  have hvalid := hC.valid x hchi_abs
  rcases hvalid.1 with hxC1 | hxC2
  · exact hxC1
  · exfalso
    have hzero : BishopCReal.relEventually (seriesSum_of_absC hchi_abs).sum
        BishopCReal.CReal.zero :=
      hvalid.2.2 hxC2 (seriesSum_of_absC hchi_abs)
    have hone_zero : BishopCReal.relEventually
        BishopCReal.CReal.one BishopCReal.CReal.zero :=
      BishopCReal.relEventually_trans _ _ _
        (BishopCReal.relEventually_symm _ _ hone) hzero
    exact BishopSec3P.thm36A2_one_le_zero_falseC
      (BishopCReal.regularSeqLe_of_relEventually hone_zero)

end IntegrableSet1C

end BishopSec1P

namespace BishopSec3P

/-- Good-set close data for convergence in measure.  The pointwise estimate is
only required on the good set, and the domain witnesses are retained as data. -/
structure Lemma415GoodSetClosePackC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (A C : BishopC.BSet X)
    (hA : BishopSec1P.IntegrableSet1C S A)
    (hC : BishopSec1P.IntegrableSet1C S C)
    (eps : BishopCReal.CReal)
    (fn_n f : BishopSec1P.IntegrableRepC3 S) : Type u where
  subset_A : C.S1 ⊆ A.S1
  doms : forall x : X, x ∈ C.S1 ->
    BishopSec1P.RepSeriesSum (fun m => BishopCReal.CReal.abs ((f.fn m).toFun x)) ×
    BishopSec1P.RepSeriesSum (fun m => BishopCReal.CReal.abs ((fn_n.fn m).toFun x))
  measure_small :
    BishopCReal.regularSeqLtProp
      ((BishopSec1P.IntegrableSet1_subC hA hC).rep.integral) eps
  point_close : forall (x : X), x ∈ C.S1 ->
    forall
      (hfabs : BishopSec1P.RepSeriesSum
        (fun m => BishopCReal.CReal.abs ((f.fn m).toFun x)))
      (hfnabs : BishopSec1P.RepSeriesSum
        (fun m => BishopCReal.CReal.abs ((fn_n.fn m).toFun x))),
      BishopCReal.regularSeqLtProp
        (BishopCReal.CReal.abs
          (BishopCReal.CReal.sub
            (BishopSec1P.seriesSum_of_absC hfabs).sum
            (BishopSec1P.seriesSum_of_absC hfnabs).sum)) eps

/-- Good-set convergence-in-measure data for an integrable-representative
sequence. -/
structure Lemma415ConvergeInMeasureGoodSetDataC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S) : Type u where
  close : forall (A : BishopC.BSet X) (hA : BishopSec1P.IntegrableSet1C S A)
      (eps : BishopCReal.CReal),
      BishopCReal.regularSeqLtProp BishopCReal.CReal.zero eps ->
    Sigma (fun N : Nat =>
      forall n : Nat, N <= n ->
        Sigma (fun C : BishopC.BSet X =>
          Sigma (fun hC : BishopSec1P.IntegrableSet1C S C =>
            Lemma415GoodSetClosePackC A C hA hC eps (fn n) f)))

/-- Forget the data in good-set convergence and recover the Prop-valued
convergence-in-measure statement for the associated partial functions. -/
noncomputable def lemma415_goodSetData_to_convergeInMeasureC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (hconv : Lemma415ConvergeInMeasureGoodSetDataC fn f) :
    BishopSec1P.ConvergeInMeasureC S
      (fun n => (fn n).toDataPFunRC) f.toDataPFunRC := by
  intro A hA eps heps
  obtain ⟨N, hN⟩ := hconv.close A hA eps heps
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨C, hC, hpack⟩ := hN n hn
  refine ⟨C, hC, ?_, hpack.measure_small, ?_⟩
  · intro x hxC
    have hdom := hpack.doms x hxC
    exact ⟨⟨hpack.subset_A hxC, ⟨hdom.1⟩⟩, ⟨hdom.2⟩⟩
  · intro x hxC exf exfn
    exact hpack.point_close x hxC exf exfn

/-- Good-set convergence of `fn` to `f` gives convergence to zero for the
absolute-error representatives in the Lemma 4.14 input form. -/
noncomputable def lemma415_absError_convergeInMeasureToZeroData_goodSetC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (hconv : Lemma415ConvergeInMeasureGoodSetDataC fn f) :
    BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f) where
  close := by
    intro A hA eps heps
    obtain ⟨N, hN⟩ := hconv.close A hA eps heps
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hpack⟩ := hN n hn
    refine ⟨C, hC, hpack.subset_A, hpack.measure_small, ?_⟩
    intro x herrabs hchi_abs hchi_one
    have hxC : x ∈ C.S1 :=
      BishopSec1P.IntegrableSet1C.mem_s1_of_indicator_oneC hC hchi_abs hchi_one
    let r : BishopSec1P.IntegrableRepC3 S := (fn n).sub f
    let hsubabs : BishopSec1P.RepSeriesSum
        (fun m => BishopCReal.CReal.abs ((r.fn m).toFun x)) :=
      IntegrableRepC3_absVal_absSeriesSum_midC r x herrabs
    let hfnabs : BishopSec1P.RepSeriesSum
        (fun m => BishopCReal.CReal.abs (((fn n).fn m).toFun x)) :=
      BishopSec1P.add_absSeriesSum_leftC (r := fn n) (r' := f.neg) (x := x) hsubabs
    let hfnegabs : BishopSec1P.RepSeriesSum
        (fun m => BishopCReal.CReal.abs (((f.neg).fn m).toFun x)) :=
      BishopSec1P.add_absSeriesSum_rightC (r := fn n) (r' := f.neg) (x := x) hsubabs
    let hfabs : BishopSec1P.RepSeriesSum
        (fun m => BishopCReal.CReal.abs ((f.fn m).toFun x)) :=
      BishopSec1P.neg_absSeriesSumC (r := f) (x := x) hfnegabs
    let hfnv : BishopSec1P.RepSeriesSum (fun m => ((fn n).fn m).toFun x) :=
      BishopSec1P.seriesSum_of_absC hfnabs
    let hfv : BishopSec1P.RepSeriesSum (fun m => (f.fn m).toFun x) :=
      BishopSec1P.seriesSum_of_absC hfabs
    let herrv : BishopSec1P.RepSeriesSum (fun m => (r.fn m).toFun x) :=
      BishopSec1P.sub_seriesSum_valueC3 (r := fn n) (r' := f) (x := x) hfnv hfv
    obtain ⟨habsModel, habsModel_eq⟩ := r.absVal_signed_value x herrv
    let herrSigned : BishopSec1P.RepSeriesSum
        (fun m => (((BishopSec1P.thm_4_15_abs_errorC fn f n).fn m).toFun x)) :=
      BishopSec1P.seriesSum_of_absC herrabs
    have herr_to_abs : BishopCReal.relEventually herrSigned.sum
        (BishopCReal.CReal.abs (BishopCReal.CReal.sub hfnv.sum hfv.sum)) := by
      have huniq : BishopCReal.relEventually herrSigned.sum habsModel.sum := by
        simpa [BishopSec1P.thm_4_15_abs_errorC, r] using
          BishopSec1P.repSeriesSum_unique herrSigned habsModel
      have herrv_sub : BishopCReal.relEventually herrv.sum
          (BishopCReal.CReal.sub hfnv.sum hfv.sum) := by
        change BishopCReal.relEventually
          (BishopCReal.addSeq hfnv.sum (BishopCReal.negSeq hfv.sum))
          (BishopCReal.subSeq hfnv.sum hfv.sum)
        exact BishopCReal.relEventually_symm _ _
          (BishopCReal.subSeq_eq_add_neg_eventually hfnv.sum hfv.sum)
      exact BishopCReal.relEventually_trans _ _ _ huniq
        (BishopCReal.relEventually_trans _ _ _ habsModel_eq
          (BishopCReal.absSeq_respects_eventually herrv.sum
            (BishopCReal.CReal.sub hfnv.sum hfv.sum) herrv_sub))
    have houter : BishopCReal.relEventually
        (BishopCReal.CReal.abs herrSigned.sum)
        (BishopCReal.CReal.abs (BishopCReal.CReal.sub hfv.sum hfnv.sum)) := by
      have hnonneg_abs : BishopCReal.RegularSeqNonneg
          (BishopCReal.CReal.abs (BishopCReal.CReal.sub hfnv.sum hfv.sum)) :=
        BishopSec1P.regularSeqNonneg_of_zero_le
          (BishopCReal.absSeq_nonnegative_regularSeqLe
            (BishopCReal.CReal.sub hfnv.sum hfv.sum))
      have h1 : BishopCReal.relEventually
          (BishopCReal.CReal.abs herrSigned.sum)
          (BishopCReal.CReal.abs
            (BishopCReal.CReal.abs (BishopCReal.CReal.sub hfnv.sum hfv.sum))) :=
        BishopCReal.absSeq_respects_eventually herrSigned.sum
          (BishopCReal.CReal.abs (BishopCReal.CReal.sub hfnv.sum hfv.sum))
          herr_to_abs
      have h2 : BishopCReal.relEventually
          (BishopCReal.CReal.abs
            (BishopCReal.CReal.abs (BishopCReal.CReal.sub hfnv.sum hfv.sum)))
          (BishopCReal.CReal.abs (BishopCReal.CReal.sub hfnv.sum hfv.sum)) :=
        BishopCReal.CReal.abs_of_nonneg_E hnonneg_abs
      exact BishopCReal.relEventually_trans _ _ _ h1
        (BishopCReal.relEventually_trans _ _ _ h2
          (BishopSec1P.absSeq_subSeq_comm_eventually hfnv.sum hfv.sum))
    exact BishopSec1P.regularSeqLtProp_of_left_eventual houter
      (hpack.point_close x hxC hfabs hfnabs)

/-- Pointwise-majorant DCT wrapper using the corrected good-set convergence
data. -/
noncomputable def goalB_pointwise_majorant_goodSet_convergence_dataC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC (g.add f.absVal))
    (hfn_bound : forall (n : Nat) (x : X)
      (hfnv : BishopSec1P.RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (hgv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe (BishopCReal.CReal.abs hfnv.sum) hgv.sum)
    (hconv : Lemma415ConvergeInMeasureGoodSetDataC fn f) :
    BishopSec1P.RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  goalB_dominated_convergence_dataWithAbsC
    fn f (g.add f.absVal)
    (RepNonnegC_addC g f.absVal hgnn
      (IntegrableRepC3_absVal_repNonnegC f))
    Dsmooth
    (lemma415_absError_le_majorant_add_absLimitC fn f g hfn_bound)
    (lemma415_absError_convergeInMeasureToZeroData_goodSetC fn f hconv)

end BishopSec3P
