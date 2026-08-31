import Mathdemo.BishopChengTheorem415Prop

open BishopCReal BishopSec1P

namespace BishopSec1P

universe u

/-- Proof-relevant pointwise order on an explicitly supplied full set. -/
structure RepLeOnFullDataC
    {X : Type u} {S : IntSpaceC X}
    (u v : IntegrableRepC3 S) : Type u where
  carrier : Set X
  full : IsFullC S carrier
  bound : forall x : X, x ∈ carrier ->
    forall (hudom : u.MemAt x) (hvdom : v.MemAt x)
      (hu : RepSeriesSum (fun k => u.valueAt x hudom k))
      (hv : RepSeriesSum (fun k => v.valueAt x hvdom k)),
      RegularSeqLe hu.sum hv.sum

/-- Proof-relevant domination `|u| <= v` on an explicitly supplied full set. -/
structure RepAbsLeOnFullDataC
    {X : Type u} {S : IntSpaceC X}
    (u v : IntegrableRepC3 S) : Type u where
  carrier : Set X
  full : IsFullC S carrier
  bound : forall x : X, x ∈ carrier ->
    forall (hudom : u.MemAt x) (hvdom : v.MemAt x)
      (hu : RepSeriesSum (fun k => u.valueAt x hudom k))
      (hv : RepSeriesSum (fun k => v.valueAt x hvdom k)),
      RegularSeqLe (CReal.abs hu.sum) hv.sum

/-- A single majorant together with an explicit full-set witness for every index. -/
structure DominatedOnFullDataC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S)
    (g : IntegrableRepC3 S) : Type u where
  atIndex : forall n : Nat, RepAbsLeOnFullDataC (fn n) g

def RepLeOnFullDataC.toProp
    {X : Type u} {S : IntSpaceC X} {u v : IntegrableRepC3 S}
    (h : RepLeOnFullDataC u v) : RepLeOnFullC u v :=
  ⟨h.carrier, h.full, h.bound⟩

/-- Package a global pointwise bound as explicit full-set data.  The domain of
the right-hand representative supplies a canonical full carrier. -/
def RepLeOnFullDataC.ofGlobal
    {X : Type u} {S : IntSpaceC X} {u v : IntegrableRepC3 S}
    (h : forall x : X,
      forall (hudom : u.MemAt x) (hvdom : v.MemAt x)
        (hu : RepSeriesSum (fun k => u.valueAt x hudom k))
        (hv : RepSeriesSum (fun k => v.valueAt x hvdom k)),
        RegularSeqLe hu.sum hv.sum) : RepLeOnFullDataC u v :=
  {
    carrier := v.domain
    full := v.domain_isFull
    bound := fun x _ hudom hvdom hu hv => h x hudom hvdom hu hv
  }

def RepAbsLeOnFullDataC.toProp
    {X : Type u} {S : IntSpaceC X} {u v : IntegrableRepC3 S}
    (h : RepAbsLeOnFullDataC u v) : RepAbsLeOnFullC u v :=
  ⟨h.carrier, h.full, h.bound⟩

/-- Package global absolute domination as explicit full-set data. -/
def RepAbsLeOnFullDataC.ofGlobal
    {X : Type u} {S : IntSpaceC X} {u v : IntegrableRepC3 S}
    (h : forall x : X,
      forall (hudom : u.MemAt x) (hvdom : v.MemAt x)
        (hu : RepSeriesSum (fun k => u.valueAt x hudom k))
        (hv : RepSeriesSum (fun k => v.valueAt x hvdom k)),
        RegularSeqLe (CReal.abs hu.sum) hv.sum) :
    RepAbsLeOnFullDataC u v :=
  {
    carrier := v.domain
    full := v.domain_isFull
    bound := fun x _ hudom hvdom hu hv => h x hudom hvdom hu hv
  }

def DominatedOnFullDataC.toProp
    {X : Type u} {S : IntSpaceC X}
    {fn : Nat -> IntegrableRepC3 S} {g : IntegrableRepC3 S}
    (h : DominatedOnFullDataC fn g) : DominatedOnFullC fn g :=
  fun n => (h.atIndex n).toProp

/-- Every global pointwise domination family yields an explicit full-set
selector.  The converse is intentionally not asserted. -/
def DominatedOnFullDataC.ofGlobal
    {X : Type u} {S : IntSpaceC X}
    {fn : Nat -> IntegrableRepC3 S} {g : IntegrableRepC3 S}
    (h : forall n : Nat, forall x : X,
      forall (hfndom : (fn n).MemAt x) (hgdom : g.MemAt x)
        (hfn : RepSeriesSum (fun k => (fn n).valueAt x hfndom k))
        (hg : RepSeriesSum (fun k => g.valueAt x hgdom k)),
        RegularSeqLe (CReal.abs hfn.sum) hg.sum) :
    DominatedOnFullDataC fn g :=
  { atIndex := fun n => RepAbsLeOnFullDataC.ofGlobal (h n) }

end BishopSec1P

namespace BishopSec3P

universe u

/-- Dyadic uniform-complement data from explicit full-set domination. -/
noncomputable def lemma43UniformComplementData_of_majorantOnFullData_halfPowC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (hnn : forall n, RepNonnegC (fn n))
    (H : IntegrableRepC3 S) (hHnn : RepNonnegC H)
    (D : Lemma43LevelSetSeqDataC H)
    (hdom : forall n, RepLeOnFullDataC (fn n) H)
    (K : Nat) :
    Lemma414UniformComplementDataC fn hnn (halfPow K) := by
  let aData := lemma43ComplementIntegral_lt_halfPowDataC D hHnn (K + 1)
  let m : Nat := aData.1
  let d := relIntegral_abs_continuous_setdiff_halfPowDataC H hHnn (K + 1)
  refine {
    A := D.A m
    hA := D.hA m
    N := 0
    delta := d.1
    delta_pos := d.2.1
    small := ?_
  }
  intro n _hn C hC hmu
  let compFn : CReal :=
    ((fn n).sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC (fn n))).integral
  let compH_C : CReal :=
    (H.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC H)).integral
  let compH_A : CReal :=
    (H.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A m) (D.hA m) H)).integral
  let iAC : CReal :=
    relIntegralC ((D.A m).sub C) (IntegrableSet1_subC (D.hA m) hC) H
  let hnDom := hdom n
  have hle_dom : RegularSeqLe compFn compH_C := by
    simpa [compFn, compH_C] using
      lemma43ComplementIntegral_le_of_le_funWithAbsOnFullC hC (fn n) H
        (hnn n) hHnn hnDom.full
        (fun x hxF hfndom hHdom fvabs Hvabs fv Hv => by
          let fv0 : RepSeriesSum (fun k => (fn n).valueAt x hfndom k) :=
            seriesSum_of_absC fvabs
          let Hv0 : RepSeriesSum (fun k => H.valueAt x hHdom k) :=
            seriesSum_of_absC Hvabs
          have hle0 : RegularSeqLe fv0.sum Hv0.sum :=
            hnDom.bound x hxF hfndom hHdom fv0 Hv0
          have hfv : fv.sum ≈ fv0.sum := repSeriesSum_unique fv fv0
          have hHv : Hv.sum ≈ Hv0.sum := repSeriesSum_unique Hv Hv0
          exact regularSeqLe_of_left_eventual hfv
            (regularSeqLe_of_right_eventual (Setoid.symm hHv) hle0))
  have hle_split : RegularSeqLe compH_C (addSeq compH_A iAC) := by
    simpa [compH_C, compH_A, iAC] using
      lemma43ComplementIntegral_le_complement_plus_setdiffC (D.hA m) hC H hHnn
  have hcomp : regularSeqLtProp compH_A (halfPow (K + 1)) := by
    simpa [aData, m, compH_A] using aData.2
  have hdiff : regularSeqLtProp iAC (halfPow (K + 1)) := by
    simpa [d, m, iAC] using d.2.2 (D.A m) C (D.hA m) hC hmu
  have hsum : regularSeqLtProp (addSeq compH_A iAC)
      (addSeq (halfPow (K + 1)) (halfPow (K + 1))) :=
    regularSeqLtProp_add hcomp hdiff
  have hsumK : regularSeqLtProp (addSeq compH_A iAC) (halfPow K) :=
    regularSeqLtProp_of_right_eventual (halfPow_succ_add_self K) hsum
  exact regularSeqLtProp_of_le_of_lt
    (regularSeqLe_trans hle_dom hle_split) hsumK

/-- Uniform-complement data for arbitrary positive epsilon. -/
noncomputable def lemma43UniformComplementData_of_majorantOnFullDataC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (hnn : forall n, RepNonnegC (fn n))
    (H : IntegrableRepC3 S) (hHnn : RepNonnegC H)
    (D : Lemma43LevelSetSeqDataC H)
    (hdom : forall n, RepLeOnFullDataC (fn n) H)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps) :
    Lemma414UniformComplementDataC fn hnn eps := by
  let kData := halfPow_lt_of_posDataC (posEventuallyData_of_pos_zeroC heps)
  let U := lemma43UniformComplementData_of_majorantOnFullData_halfPowC
    fn hnn H hHnn D hdom kData.1
  exact {
    A := U.A
    hA := U.hA
    N := U.N
    delta := U.delta
    delta_pos := U.delta_pos
    small := by
      intro n hn C hC hmu
      exact regularSeqLtProp_trans _ _ _
        (U.small n hn C hC hmu) kData.2
  }

/-- Type-valued DCT from explicit full-set domination of the absolute error. -/
noncomputable def integralConvergence_from_errorMajorantOnFullDataC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (f H : IntegrableRepC3 S)
    (herr_nn : forall n, RepNonnegC (thm_4_15_abs_errorC fn f n))
    (hHnn : RepNonnegC H)
    (Dsmooth : Lemma43DyadicSmoothDataC H)
    (hdom : forall n,
      RepLeOnFullDataC (thm_4_15_abs_errorC fn f n) H)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC
      (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_uniform_and_measure_convergeC
    fn f herr_nn
    (fun eps heps =>
      lemma43UniformComplementData_of_majorantOnFullDataC
        (fun n => thm_4_15_abs_errorC fn f n) herr_nn
        H hHnn (lemma43LevelSetSeqDataC_of_dyadicSmoothDataC H Dsmooth)
        hdom eps heps)
    hconv

/-- Type-valued L1-error convergence from explicit full-set domination of the
absolute error.  The result retains the convergence modulus. -/
noncomputable def l1ErrorConvergence_from_errorMajorantOnFullDataC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (f H : IntegrableRepC3 S)
    (herr_nn : forall n, RepNonnegC (thm_4_15_abs_errorC fn f n))
    (hHnn : RepNonnegC H)
    (Dsmooth : Lemma43DyadicSmoothDataC H)
    (hdom : forall n,
      RepLeOnFullDataC (thm_4_15_abs_errorC fn f n) H)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC
      (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto
      (fun n => (thm_4_15_abs_errorC fn f n).integral) CReal.zero :=
  lemma_4_14_tendsto_zero_from_uniform_and_rep_convergeC
    (thm_4_15_abs_errorC fn f) herr_nn
    (fun eps heps =>
      lemma43UniformComplementData_of_majorantOnFullDataC
        (fun n => thm_4_15_abs_errorC fn f n) herr_nn
        H hHnn (lemma43LevelSetSeqDataC_of_dyadicSmoothDataC H Dsmooth)
        hdom eps heps)
    (lemma_4_14_rep_converge_from_source_measure_converge_zeroC
      (thm_4_15_abs_errorC fn f) hconv)

set_option maxHeartbeats 1000000 in
/-- Convert explicit full-set domination of `fn n` by `g` into explicit
full-set domination of `|fn n - f|` by `|g| + |f|`, retaining the carrier as
data instead of reopening a propositional existential. -/
noncomputable def absError_le_absMajorant_add_absLimit_onFullDataC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S)
    (f g : IntegrableRepC3 S)
    (n : Nat)
    (hdom : RepAbsLeOnFullDataC (fn n) g) :
    RepLeOnFullDataC
      (thm_4_15_abs_errorC fn f n)
      (g.absVal.add f.absVal) := by
  let err : IntegrableRepC3 S := thm_4_15_abs_errorC fn f n
  let H : IntegrableRepC3 S := g.absVal.add f.absVal
  refine {
    carrier := (hdom.carrier ∩ err.domain) ∩ H.domain
    full := isFull_interC
      (isFull_interC hdom.full err.domain_isFull) H.domain_isFull
    bound := ?_
  }
  intro x hx herrdom hHdom herrv hHv
  obtain ⟨⟨hxF, hxErrDom⟩, hxHDom⟩ := hx
  obtain ⟨_herrdom0, ⟨herrabs0⟩⟩ := hxErrDom
  obtain ⟨_hHdom0, ⟨hHabs0⟩⟩ := hxHDom
  let herrabs : RepSeriesSum
      (fun m => absSeq (err.valueAt x herrdom m)) := by
    simpa [IntegrableRepC3.valueAt, err] using herrabs0
  let hHabs : RepSeriesSum
      (fun m => absSeq (H.valueAt x hHdom m)) := by
    simpa [IntegrableRepC3.valueAt, H] using hHabs0
  let r : IntegrableRepC3 S := (fn n).sub f
  let hrdom : r.MemAt x := IntegrableRepC3_of_absVal_memAtC herrdom
  let herrAddDom : ((fn n).add f.neg).MemAt x := by
    simpa [r, IntegrableRepC3.sub] using hrdom
  let hfndom : (fn n).MemAt x := IntegrableRepC3.add_left_memAt herrAddDom
  let hfnegdom : f.neg.MemAt x := IntegrableRepC3.add_right_memAt herrAddDom
  let hfdomErr : f.MemAt x := IntegrableRepC3.of_neg_memAt hfnegdom
  let hgAbsValDom : g.absVal.MemAt x := IntegrableRepC3.add_left_memAt hHdom
  let hfAbsValDom : f.absVal.MemAt x := IntegrableRepC3.add_right_memAt hHdom
  let hgdom : g.MemAt x := IntegrableRepC3_of_absVal_memAtC hgAbsValDom
  let hfdomH : f.MemAt x := IntegrableRepC3_of_absVal_memAtC hfAbsValDom
  let hsubabs : RepSeriesSum (fun m => absSeq (r.valueAt x hrdom m)) :=
    IntegrableRepC3_absVal_absSeriesSum_midC r x herrdom herrabs
  let hfnabs : RepSeriesSum
      (fun m => absSeq ((fn n).valueAt x hfndom m)) :=
    add_absSeriesSum_leftC (r := fn n) (r' := f.neg) (x := x)
      herrAddDom hsubabs
  let hfnegabs : RepSeriesSum
      (fun m => absSeq (f.neg.valueAt x hfnegdom m)) :=
    add_absSeriesSum_rightC (r := fn n) (r' := f.neg) (x := x)
      herrAddDom hsubabs
  let hfabs_from_err : RepSeriesSum
      (fun m => absSeq (f.valueAt x hfdomErr m)) :=
    neg_absSeriesSumC (r := f) (x := x) hfdomErr hfnegabs
  let hfnv : RepSeriesSum (fun m => (fn n).valueAt x hfndom m) :=
    seriesSum_of_absC hfnabs
  let hfv_from_err : RepSeriesSum (fun m => f.valueAt x hfdomErr m) :=
    seriesSum_of_absC hfabs_from_err
  let hgAbsValAbs :
      RepSeriesSum (fun m => absSeq (g.absVal.valueAt x hgAbsValDom m)) :=
    add_absSeriesSum_leftC (r := g.absVal) (r' := f.absVal) (x := x)
      hHdom hHabs
  let hfAbsValAbs :
      RepSeriesSum (fun m => absSeq (f.absVal.valueAt x hfAbsValDom m)) :=
    add_absSeriesSum_rightC (r := g.absVal) (r' := f.absVal) (x := x)
      hHdom hHabs
  let hgvabs : RepSeriesSum (fun m => absSeq (g.valueAt x hgdom m)) :=
    IntegrableRepC3_absVal_absSeriesSum_midC g x hgAbsValDom hgAbsValAbs
  let hgv : RepSeriesSum (fun m => g.valueAt x hgdom m) :=
    seriesSum_of_absC hgvabs
  let hfabs_from_H : RepSeriesSum (fun m => absSeq (f.valueAt x hfdomH m)) :=
    IntegrableRepC3_absVal_absSeriesSum_midC f x hfAbsValDom hfAbsValAbs
  let hfv_from_H : RepSeriesSum (fun m => f.valueAt x hfdomH m) :=
    seriesSum_of_absC hfabs_from_H
  let hgAbsValV : RepSeriesSum
      (fun m => g.absVal.valueAt x hgAbsValDom m) :=
    seriesSum_of_absC hgAbsValAbs
  let hfAbsValV : RepSeriesSum
      (fun m => f.absVal.valueAt x hfAbsValDom m) :=
    seriesSum_of_absC hfAbsValAbs
  let hHmodel : RepSeriesSum (fun m => H.valueAt x hHdom m) :=
    add_seriesSum_valueC3 (r := g.absVal) (r' := f.absVal) (x := x)
      hgAbsValDom hfAbsValDom hgAbsValV hfAbsValV
  let herrSubV : RepSeriesSum (fun m => r.valueAt x hrdom m) :=
    sub_seriesSum_valueC3 (r := fn n) (r' := f) (x := x)
      hfndom hfdomErr hfnv hfv_from_err
  obtain ⟨herrAbsModel, herrAbs_eq⟩ :=
    r.absVal_signed_value x hrdom herrSubV
  obtain ⟨hgAbsModel, hgAbs_eq⟩ :=
    g.absVal_signed_value x hgdom hgv
  obtain ⟨hfAbsModel, hfAbs_eq⟩ :=
    f.absVal_signed_value x hfdomH hfv_from_H
  have herr_to_abs_sub :
      herrv.sum ≈ CReal.abs (CReal.sub hfnv.sum hfv_from_err.sum) := by
    have huniq : herrv.sum ≈ herrAbsModel.sum := by
      simpa [err, thm_4_15_abs_errorC, r] using
        repSeriesSum_unique herrv herrAbsModel
    have hsubeq : herrSubV.sum ≈ CReal.sub hfnv.sum hfv_from_err.sum := by
      change relEventually (addSeq hfnv.sum (negSeq hfv_from_err.sum))
        (subSeq hfnv.sum hfv_from_err.sum)
      exact relEventually_symm _ _
        (subSeq_eq_add_neg_eventually hfnv.sum hfv_from_err.sum)
    exact relEventually_trans _ _ _ huniq
      (relEventually_trans _ _ _ herrAbs_eq
        (absSeq_respects_eventually herrSubV.sum
          (CReal.sub hfnv.sum hfv_from_err.sum) hsubeq))
  have hH_to_sum : hHv.sum ≈ CReal.add hgAbsValV.sum hfAbsValV.sum := by
    simpa [H] using repSeriesSum_unique hHv hHmodel
  have hgAbsVal_to_abs_g : hgAbsValV.sum ≈ CReal.abs hgv.sum :=
    relEventually_trans _ _ _ (repSeriesSum_unique hgAbsValV hgAbsModel) hgAbs_eq
  have hfAbsVal_to_abs_f : hfAbsValV.sum ≈ CReal.abs hfv_from_H.sum :=
    relEventually_trans _ _ _ (repSeriesSum_unique hfAbsValV hfAbsModel) hfAbs_eq
  have hf_eq : hfv_from_err.sum ≈ hfv_from_H.sum :=
    repSeriesSum_unique hfv_from_err hfv_from_H
  have hfn_le_abs_g : RegularSeqLe (CReal.abs hfnv.sum) hgAbsValV.sum := by
    have hle_g : RegularSeqLe (CReal.abs hfnv.sum) hgv.sum :=
      hdom.bound x hxF hfndom hgdom hfnv hgv
    have hg_le_abs : RegularSeqLe hgv.sum (CReal.abs hgv.sum) :=
      base_le_abs_base_regularSeqLe hgv.sum
    exact regularSeqLe_trans hle_g
      (regularSeqLe_trans hg_le_abs
        (regularSeqLe_of_relEventually (Setoid.symm hgAbsVal_to_abs_g)))
  have hf_abs_le : RegularSeqLe (CReal.abs hfv_from_err.sum) hfAbsValV.sum := by
    have hleft : CReal.abs hfv_from_err.sum ≈ CReal.abs hfv_from_H.sum :=
      absSeq_respects_eventually hfv_from_err.sum hfv_from_H.sum hf_eq
    exact regularSeqLe_of_left_eventual hleft
      (regularSeqLe_of_right_eventual (Setoid.symm hfAbsVal_to_abs_f)
        (regularSeqLe_refl (CReal.abs hfv_from_H.sum)))
  have htri : RegularSeqLe
      (CReal.abs (CReal.sub hfnv.sum hfv_from_err.sum))
      (CReal.add (CReal.abs hfnv.sum) (CReal.abs hfv_from_err.sum)) :=
    regularSeqLe_abs_sub_le_add_absC hfnv.sum hfv_from_err.sum
  have hsum_le : RegularSeqLe
      (CReal.add (CReal.abs hfnv.sum) (CReal.abs hfv_from_err.sum))
      (CReal.add hgAbsValV.sum hfAbsValV.sum) :=
    regularSeqLe_add hfn_le_abs_g hf_abs_le
  exact regularSeqLe_of_left_eventual herr_to_abs_sub
    (regularSeqLe_of_right_eventual (Setoid.symm hH_to_sum)
      (regularSeqLe_trans htri hsum_le))

/-- Fully data-carrying DCT with an explicit full-set selector for domination. -/
noncomputable def dominatedConvergence_from_pointwiseMajorantOnFullDataC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (f g : IntegrableRepC3 S)
    (Dsmooth : Lemma43DyadicSmoothDataC (g.absVal.add f.absVal))
    (hdom : DominatedOnFullDataC fn g)
    (hconv : Lemma415ConvergeInMeasureDataC fn f) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  integralConvergence_from_errorMajorantOnFullDataC
    fn f (g.absVal.add f.absVal)
    (fun n => thm_4_15_abs_error_nonnegC fn f n)
    (RepNonnegC_addC g.absVal f.absVal
      (IntegrableRepC3_absVal_repNonnegC g)
      (IntegrableRepC3_absVal_repNonnegC f))
    Dsmooth
    (fun n => absError_le_absMajorant_add_absLimit_onFullDataC
      fn f g n (hdom.atIndex n))
    (lemma415_absError_convergeInMeasureToZeroDataC fn f hconv)

/-- The same explicit full-set DCT with internally constructed smooth-level data. -/
noncomputable def dominatedConvergence_from_pointwiseMajorantOnFullData_autoC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (f g : IntegrableRepC3 S)
    (hdom : DominatedOnFullDataC fn g)
    (hconv : Lemma415ConvergeInMeasureDataC fn f) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  dominatedConvergence_from_pointwiseMajorantOnFullDataC
    fn f g (lemma43DyadicSmoothDataC_construct (g.absVal.add f.absVal))
    hdom hconv

/-- Explicit full-set DCT using good-set convergence data.  The good sets used
for convergence and the full sets used for domination remain distinct data. -/
noncomputable def dominatedConvergence_from_pointwiseMajorantOnFullGoodSetDataC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (f g : IntegrableRepC3 S)
    (Dsmooth : Lemma43DyadicSmoothDataC (g.absVal.add f.absVal))
    (hdom : DominatedOnFullDataC fn g)
    (hconv : Lemma415ConvergeInMeasureGoodSetDataC fn f) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  integralConvergence_from_errorMajorantOnFullDataC
    fn f (g.absVal.add f.absVal)
    (fun n => thm_4_15_abs_error_nonnegC fn f n)
    (RepNonnegC_addC g.absVal f.absVal
      (IntegrableRepC3_absVal_repNonnegC g)
      (IntegrableRepC3_absVal_repNonnegC f))
    Dsmooth
    (fun n => absError_le_absMajorant_add_absLimit_onFullDataC
      fn f g n (hdom.atIndex n))
    (lemma415_absError_convergeInMeasureToZeroData_goodSetC fn f hconv)

/-- Automatic smooth-level wrapper for explicit domination and good-set
convergence data. -/
noncomputable def dominatedConvergence_from_pointwiseMajorantOnFullGoodSetData_autoC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (f g : IntegrableRepC3 S)
    (hdom : DominatedOnFullDataC fn g)
    (hconv : Lemma415ConvergeInMeasureGoodSetDataC fn f) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  dominatedConvergence_from_pointwiseMajorantOnFullGoodSetDataC
    fn f g (lemma43DyadicSmoothDataC_construct (g.absVal.add f.absVal))
    hdom hconv

#check BishopSec1P.RepLeOnFullDataC
#check BishopSec1P.RepAbsLeOnFullDataC
#check BishopSec1P.DominatedOnFullDataC
#check BishopSec1P.RepLeOnFullDataC.ofGlobal
#check BishopSec1P.RepAbsLeOnFullDataC.ofGlobal
#check BishopSec1P.DominatedOnFullDataC.ofGlobal
#check lemma43UniformComplementData_of_majorantOnFullDataC
#check integralConvergence_from_errorMajorantOnFullDataC
#check l1ErrorConvergence_from_errorMajorantOnFullDataC
#check absError_le_absMajorant_add_absLimit_onFullDataC
#check dominatedConvergence_from_pointwiseMajorantOnFullDataC
#check dominatedConvergence_from_pointwiseMajorantOnFullData_autoC
#check dominatedConvergence_from_pointwiseMajorantOnFullGoodSetDataC
#check dominatedConvergence_from_pointwiseMajorantOnFullGoodSetData_autoC

#print axioms BishopSec1P.RepLeOnFullDataC
#print axioms BishopSec1P.RepAbsLeOnFullDataC
#print axioms BishopSec1P.DominatedOnFullDataC
#print axioms BishopSec1P.RepLeOnFullDataC.ofGlobal
#print axioms BishopSec1P.RepAbsLeOnFullDataC.ofGlobal
#print axioms BishopSec1P.DominatedOnFullDataC.ofGlobal
#print axioms lemma43UniformComplementData_of_majorantOnFullDataC
#print axioms integralConvergence_from_errorMajorantOnFullDataC
#print axioms l1ErrorConvergence_from_errorMajorantOnFullDataC
#print axioms absError_le_absMajorant_add_absLimit_onFullDataC
#print axioms dominatedConvergence_from_pointwiseMajorantOnFullDataC
#print axioms dominatedConvergence_from_pointwiseMajorantOnFullData_autoC
#print axioms dominatedConvergence_from_pointwiseMajorantOnFullGoodSetDataC
#print axioms dominatedConvergence_from_pointwiseMajorantOnFullGoodSetData_autoC

end BishopSec3P
