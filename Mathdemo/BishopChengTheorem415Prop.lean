import Mathdemo.BishopSec3PresentedEnhancementsC

/-!
# Propositional Bishop--Cheng theorem 4.15 interface

This module starts the Prop-facing route corresponding to Bishop--Cheng
definition 4.11 and theorem 4.15.  The public-facing hypotheses are ordinary
propositions; proof-relevant witnesses are opened only inside propositional
proof goals.
-/

open BishopCReal BishopSec1P

namespace BishopSec1P

universe u

/-- Ordinary epsilon-style propositional convergence of a sequence of presented
reals. -/
def RepSeriesTendstoEpsPropC
    (u : Nat -> CReal) (l : CReal) : Prop :=
  forall eps : CReal, regularSeqLtProp CReal.zero eps ->
    exists N : Nat, forall n : Nat, N <= n ->
      regularSeqLtProp (CReal.abs (CReal.sub (u n) l)) eps

/-- Pointwise order on some full set. -/
def RepLeOnFullC
    {X : Type u} {S : IntSpaceC X}
    (u v : IntegrableRepC3 S) : Prop :=
  exists F : Set X, IsFullC S F /\
    forall x : X, x ∈ F ->
      forall (hudom : u.MemAt x) (hvdom : v.MemAt x)
        (hu : RepSeriesSum (fun k => u.valueAt x hudom k))
        (hv : RepSeriesSum (fun k => v.valueAt x hvdom k)),
        RegularSeqLe hu.sum hv.sum

/-- Bishop--Cheng style domination `|u| <= v` on some full set. -/
def RepAbsLeOnFullC
    {X : Type u} {S : IntSpaceC X}
    (u v : IntegrableRepC3 S) : Prop :=
  exists F : Set X, IsFullC S F /\
    forall x : X, x ∈ F ->
      forall (hudom : u.MemAt x) (hvdom : v.MemAt x)
        (hu : RepSeriesSum (fun k => u.valueAt x hudom k))
        (hv : RepSeriesSum (fun k => v.valueAt x hvdom k)),
        RegularSeqLe (CReal.abs hu.sum) hv.sum

/-- A sequence dominated on full sets by a single integrable representative. -/
def DominatedOnFullC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S)
    (g : IntegrableRepC3 S) : Prop :=
  forall n : Nat, RepAbsLeOnFullC (fn n) g

end BishopSec1P

namespace BishopSec3P

universe u

set_option maxHeartbeats 1000000 in
/-- Complement-integral monotonicity when pointwise domination is available on
an additional full set. -/
theorem lemma43ComplementIntegral_le_of_le_funWithAbsOnFullC
    {X : Type u} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C)
    (u v : IntegrableRepC3 S) (hunn : RepNonnegC u) (hvnn : RepNonnegC v)
    {F : Set X} (hF : IsFullC S F)
    (hle : forall (x : X), x ∈ F ->
      forall
        (hudom : u.MemAt x) (hvdom : v.MemAt x)
        (huabs : RepSeriesSum (fun k => CReal.abs (u.valueAt x hudom k)))
        (hvabs : RepSeriesSum (fun k => CReal.abs (v.valueAt x hvdom k)))
        (huv : RepSeriesSum (fun k => u.valueAt x hudom k))
        (hvv : RepSeriesSum (fun k => v.valueAt x hvdom k)),
        RegularSeqLe huv.sum hvv.sum) :
    RegularSeqLe
      (u.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC u)).integral
      (v.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC v)).integral := by
  let chiU := IntegrableRepC3.prop_4_2_chi_f_repC C hC u
  let chiV := IntegrableRepC3.prop_4_2_chi_f_repC C hC v
  let rL := u.sub chiU
  let rR := v.sub chiV
  change RegularSeqLe rL.integral rR.integral
  refine prop_1_11C
    (isFull_interC
      (isFull_interC (isFull_interC (isFull_interC (isFull_interC
        (isFull_interC rL.domain_isFull rR.domain_isFull) u.domain_isFull)
        v.domain_isFull) chiU.domain_isFull)
        (isFull_interC chiV.domain_isFull hC.rep.domain_isFull))
      hF)
    rL rR ?_
  intro x hx hrLDom hrRDom hr hr'
  obtain ⟨hx_main, hxF⟩ := hx
  obtain ⟨⟨⟨⟨⟨hxL, hxR⟩, hxu⟩, hxv⟩, hxchiU⟩, hxchiV_hC⟩ := hx_main
  obtain ⟨hxchiV, hxCchi⟩ := hxchiV_hC
  obtain ⟨_hrLDom, ⟨_hLabs⟩⟩ := hxL
  obtain ⟨_hrRDom, ⟨_hRabs⟩⟩ := hxR
  obtain ⟨hudom, ⟨huabs⟩⟩ := hxu
  obtain ⟨hvdom, ⟨hvabs⟩⟩ := hxv
  obtain ⟨hchiUdom, ⟨hchiUabs⟩⟩ := hxchiU
  obtain ⟨hchiVdom, ⟨hchiVabs⟩⟩ := hxchiV
  obtain ⟨hCdom, ⟨hCchiabs⟩⟩ := hxCchi
  let uv : RepSeriesSum (fun k => u.valueAt x hudom k) := seriesSum_of_absC huabs
  let vv : RepSeriesSum (fun k => v.valueAt x hvdom k) := seriesSum_of_absC hvabs
  let chiVal : RepSeriesSum (fun k => hC.rep.valueAt x hCdom k) :=
    seriesSum_of_absC hCchiabs
  let chiUVal : RepSeriesSum (fun k => chiU.valueAt x hchiUdom k) :=
    seriesSum_of_absC hchiUabs
  let chiVVal : RepSeriesSum (fun k => chiV.valueAt x hchiVdom k) :=
    seriesSum_of_absC hchiVabs
  have hchiU_value : chiUVal.sum ≈ CReal.mul chiVal.sum uv.sum := by
    exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC u hunn
      hchiUdom hchiUabs hCdom hCchiabs hudom huabs
  have hchiV_value : chiVVal.sum ≈ CReal.mul chiVal.sum vv.sum := by
    exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC v hvnn
      hchiVdom hchiVabs hCdom hCchiabs hvdom hvabs
  let hsubL := sub_seriesSum_valueC3 (r := u) (r' := chiU) (x := x)
    hudom hchiUdom uv chiUVal
  let hsubR := sub_seriesSum_valueC3 (r := v) (r' := chiV) (x := x)
    hvdom hchiVdom vv chiVVal
  have hmodelL_to_sub : hsubL.sum ≈ CReal.sub uv.sum chiUVal.sum := by
    change relEventually (addSeq uv.sum (negSeq chiUVal.sum))
      (subSeq uv.sum chiUVal.sum)
    exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually uv.sum chiUVal.sum)
  have hmodelR_to_sub : hsubR.sum ≈ CReal.sub vv.sum chiVVal.sum := by
    change relEventually (addSeq vv.sum (negSeq chiVVal.sum))
      (subSeq vv.sum chiVVal.sum)
    exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually vv.sum chiVVal.sum)
  have hLcanon : hr.sum ≈ CReal.sub uv.sum (CReal.mul chiVal.sum uv.sum) := by
    have htransport : CReal.sub uv.sum chiUVal.sum ≈
        CReal.sub uv.sum (CReal.mul chiVal.sum uv.sum) :=
      subSeq_respects_eventually uv.sum uv.sum chiUVal.sum
        (CReal.mul chiVal.sum uv.sum) (relEventually_refl uv.sum) hchiU_value
    exact Setoid.trans (Setoid.trans (repSeriesSum_unique hr hsubL) hmodelL_to_sub)
      htransport
  have hRcanon : hr'.sum ≈ CReal.sub vv.sum (CReal.mul chiVal.sum vv.sum) := by
    have htransport : CReal.sub vv.sum chiVVal.sum ≈
        CReal.sub vv.sum (CReal.mul chiVal.sum vv.sum) :=
      subSeq_respects_eventually vv.sum vv.sum chiVVal.sum
        (CReal.mul chiVal.sum vv.sum) (relEventually_refl vv.sum) hchiV_value
    exact Setoid.trans (Setoid.trans (repSeriesSum_unique hr' hsubR) hmodelR_to_sub)
      htransport
  have hvalid := hC.valid x hCdom hCchiabs
  have hchi01 : chiVal.sum ≈ CReal.zero \/ chiVal.sum ≈ CReal.one := by
    rcases hvalid.1 with hxS1 | hxS2
    · exact Or.inr (hvalid.2.1 hxS1 chiVal)
    · exact Or.inl (hvalid.2.2 hxS2 chiVal)
  have hmid : RegularSeqLe
      (CReal.sub uv.sum (CReal.mul chiVal.sum uv.sum))
      (CReal.sub vv.sum (CReal.mul chiVal.sum vv.sum)) :=
    lemma43SubMulChi_monoC hchi01
      (hle x hxF hudom hvdom huabs hvabs uv vv)
  exact regularSeqLe_of_left_eventual hLcanon
    (regularSeqLe_of_right_eventual (Setoid.symm hRcanon) hmid)

/-- Propositional shadow of the uniform-complement input used in Lemma 4.14. -/
def Lemma414UniformComplementPropC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (eps : CReal) : Prop :=
  exists A : BishopC.BSet X, exists hA : IntegrableSet1C S A,
  exists N : Nat, exists delta : CReal,
    regularSeqLtProp CReal.zero delta /\
    forall n : Nat, N <= n ->
      forall C : BishopC.BSet X, forall hC : IntegrableSet1C S C,
        regularSeqLtProp
          ((IntegrableSet1_subC hA hC).rep.integral) delta ->
        regularSeqLtProp
          ((fn n).sub
            (IntegrableRepC3.prop_4_2_chi_f_repC C hC (fn n))).integral
          eps

/-- Dyadic Prop uniform-complement bridge from full-set domination. -/
noncomputable def lemma43UniformComplementProp_of_majorantWithAbsOnFull_halfPowC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (hnn : forall n, RepNonnegC (fn n))
    (H : IntegrableRepC3 S) (hHnn : RepNonnegC H)
    (D : Lemma43LevelSetSeqDataC H)
    (hdom : forall n, RepLeOnFullC (fn n) H)
    (K : Nat) :
    Lemma414UniformComplementPropC fn (halfPow K) := by
  let aData := lemma43ComplementIntegral_lt_halfPowDataC D hHnn (K + 1)
  let m : Nat := aData.1
  let d := relIntegral_abs_continuous_setdiff_halfPowDataC H hHnn (K + 1)
  refine ⟨D.A m, D.hA m, 0, d.1, d.2.1, ?_⟩
  intro n _hn C hC hmu
  let compFn : CReal :=
    ((fn n).sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC (fn n))).integral
  let compH_C : CReal :=
    (H.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC H)).integral
  let compH_A : CReal :=
    (H.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A m) (D.hA m) H)).integral
  let iAC : CReal :=
    relIntegralC ((D.A m).sub C) (IntegrableSet1_subC (D.hA m) hC) H
  rcases hdom n with ⟨F, hF, hpoint⟩
  have hle_dom : RegularSeqLe compFn compH_C := by
    simpa [compFn, compH_C] using
      lemma43ComplementIntegral_le_of_le_funWithAbsOnFullC hC (fn n) H
        (hnn n) hHnn hF
        (fun x hxF hfndom hHdom fvabs Hvabs fv Hv => by
          let fv0 : RepSeriesSum (fun k => (fn n).valueAt x hfndom k) :=
            seriesSum_of_absC fvabs
          let Hv0 : RepSeriesSum (fun k => H.valueAt x hHdom k) :=
            seriesSum_of_absC Hvabs
          have hle0 : RegularSeqLe fv0.sum Hv0.sum :=
            hpoint x hxF hfndom hHdom fv0 Hv0
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

/-- Arbitrary-epsilon Prop uniform-complement bridge from full-set
domination. -/
noncomputable def lemma43UniformComplementProp_of_majorantWithAbsOnFullC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (hnn : forall n, RepNonnegC (fn n))
    (H : IntegrableRepC3 S) (hHnn : RepNonnegC H)
    (D : Lemma43LevelSetSeqDataC H)
    (hdom : forall n, RepLeOnFullC (fn n) H)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps) :
    Lemma414UniformComplementPropC fn eps := by
  let kData := halfPow_lt_of_posDataC (posEventuallyData_of_pos_zeroC heps)
  let U := lemma43UniformComplementProp_of_majorantWithAbsOnFull_halfPowC
    fn hnn H hHnn D hdom kData.1
  rcases U with ⟨A, hA, N, delta, hdelta, hsmall⟩
  refine ⟨A, hA, N, delta, hdelta, ?_⟩
  intro n hn C hC hmu
  exact regularSeqLtProp_trans _ _ _
    (hsmall n hn C hC hmu) kData.2

set_option maxHeartbeats 1000000 in
/-- Full-set error domination using the internal majorant `|g| + |f|`. -/
theorem absError_le_absMajorant_add_absLimit_onFullC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S)
    (f g : IntegrableRepC3 S)
    (n : Nat)
    (hdom : RepAbsLeOnFullC (fn n) g) :
    RepLeOnFullC
      (thm_4_15_abs_errorC fn f n)
      (g.absVal.add f.absVal) := by
  rcases hdom with ⟨F, hF, hpoint⟩
  let err : IntegrableRepC3 S := thm_4_15_abs_errorC fn f n
  let H : IntegrableRepC3 S := g.absVal.add f.absVal
  refine ⟨(F ∩ err.domain) ∩ H.domain, ?_, ?_⟩
  · exact isFull_interC (isFull_interC hF err.domain_isFull) H.domain_isFull
  · intro x hx herrdom hHdom herrv hHv
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
        hpoint x hxF hfndom hgdom hfnv hgv
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

set_option maxHeartbeats 1000000 in
/-- Prop-facing Lemma 4.14 endpoint for the absolute error representatives.

The convergence-in-measure hypothesis is opened only inside this Prop proof.
The selected good set is not stored in any Type-valued structure. -/
theorem bishop_cheng_l1_error_tends_zero_propC_with_majorant
    {X : Type u} (S : IntSpaceC X)
    (fn : Nat -> IntegrableRepC3 S) (f g : IntegrableRepC3 S)
    (hconv : ConvergeInMeasureC S (fun n => (fn n).toDataPFunRC) f.toDataPFunRC)
    (hdom : DominatedOnFullC fn g) :
    forall eps : CReal, regularSeqLtProp CReal.zero eps ->
      exists N : Nat, forall n : Nat, N <= n ->
        regularSeqLtProp (thm_4_15_abs_errorC fn f n).integral eps := by
  intro eps heps
  obtain ⟨K, hKeps⟩ :=
    halfPow_lt_of_posDataC (posEventuallyData_of_pos_zeroC heps)
  let eta : CReal := halfPow (K + 1)
  have heta : regularSeqLtProp CReal.zero eta :=
    regularSeqLtProp_zero_halfPow (K + 1)
  let H : IntegrableRepC3 S := g.absVal.add f.absVal
  have hHnn : RepNonnegC H :=
    RepNonnegC_addC g.absVal f.absVal
      (IntegrableRepC3_absVal_repNonnegC g)
      (IntegrableRepC3_absVal_repNonnegC f)
  have hD : Lemma43DyadicSmoothDataC H :=
    lemma43DyadicSmoothDataC_construct H
  have hlevels : Lemma43LevelSetSeqDataC H :=
    lemma43LevelSetSeqDataC_of_dyadicSmoothDataC H hD
  have herrdom : forall n : Nat,
      RepLeOnFullC (thm_4_15_abs_errorC fn f n) H := by
    intro n
    exact absError_le_absMajorant_add_absLimit_onFullC fn f g n (hdom n)
  obtain ⟨A, hA, Nuc, delta, hdelta, hsmall⟩ :=
    lemma43UniformComplementProp_of_majorantWithAbsOnFullC
      (fun n => thm_4_15_abs_errorC fn f n)
      (fun n => thm_4_15_abs_error_nonnegC fn f n)
      H hHnn hlevels herrdom eta heta
  let rho : CReal := CReal.min delta (goodSetBoundC hA eta)
  have hrho : regularSeqLtProp CReal.zero rho :=
    min_posC hdelta (goodSetBoundC_pos hA heta)
  obtain ⟨Ncm, hNcm⟩ :=
    hconv A hA rho hrho
  refine ⟨Nat.max Nuc Ncm, ?_⟩
  intro n hn
  have hnuc : Nuc <= n := Nat.le_trans (Nat.le_max_left Nuc Ncm) hn
  have hncm : Ncm <= n := Nat.le_trans (Nat.le_max_right Nuc Ncm) hn
  obtain ⟨C, hC, hsubset, hmeasure, hclose⟩ := hNcm n hncm
  have hsub1 : C.S1 ⊆ A.S1 := by
    intro x hx
    exact (hsubset hx).1.1
  have hbad :
      regularSeqLtProp
        (((thm_4_15_abs_errorC fn f n).sub
          (IntegrableRepC3.prop_4_2_chi_f_repC C hC
            (thm_4_15_abs_errorC fn f n))).integral) eta := by
    exact hsmall n hnuc C hC
      (regularSeqLtProp_of_lt_of_le hmeasure
        (CReal.min_le_leftC delta (goodSetBoundC hA eta)))
  have hbound :
      forall (x : X)
        (herrdom : (thm_4_15_abs_errorC fn f n).MemAt x)
        (hchiDom : hC.rep.MemAt x)
        (herrabs : RepSeriesSum
          (fun k => absSeq
            ((thm_4_15_abs_errorC fn f n).valueAt x herrdom k)))
        (hchiabs : RepSeriesSum
          (fun k => absSeq (hC.rep.valueAt x hchiDom k))),
        relEventually (seriesSum_of_absC hchiabs).sum CReal.one ->
          RegularSeqLe (seriesSum_of_absC herrabs).sum (goodSetBoundC hA eta) := by
    intro x herrdom hchiDom herrabs hchiabs hchione
    have hxC : x ∈ C.S1 :=
      IntegrableSet1C.mem_s1_of_indicator_oneC hC hchiDom hchiabs hchione
    let r : IntegrableRepC3 S := (fn n).sub f
    let hrdom : r.MemAt x := IntegrableRepC3_of_absVal_memAtC herrdom
    let haddDom : ((fn n).add f.neg).MemAt x := by
      simpa [r, IntegrableRepC3.sub] using hrdom
    let hfndom : (fn n).MemAt x := IntegrableRepC3.add_left_memAt haddDom
    let hfnegdom : f.neg.MemAt x := IntegrableRepC3.add_right_memAt haddDom
    let hfdom : f.MemAt x := IntegrableRepC3.of_neg_memAt hfnegdom
    let hsubabs : RepSeriesSum
        (fun m => CReal.abs (r.valueAt x hrdom m)) :=
      IntegrableRepC3_absVal_absSeriesSum_midC r x herrdom herrabs
    let hfnabs : RepSeriesSum
        (fun m => CReal.abs ((fn n).valueAt x hfndom m)) :=
      add_absSeriesSum_leftC (r := fn n) (r' := f.neg) (x := x)
        haddDom hsubabs
    let hfnegabs : RepSeriesSum
        (fun m => CReal.abs (f.neg.valueAt x hfnegdom m)) :=
      add_absSeriesSum_rightC (r := fn n) (r' := f.neg) (x := x)
        haddDom hsubabs
    let hfabs0 : RepSeriesSum
        (fun m => CReal.abs (f.valueAt x hfdom m)) :=
      neg_absSeriesSumC (r := f) (x := x) hfdom hfnegabs
    let hfnv : RepSeriesSum (fun m => (fn n).valueAt x hfndom m) :=
      seriesSum_of_absC hfnabs
    let hfv : RepSeriesSum (fun m => f.valueAt x hfdom m) :=
      seriesSum_of_absC hfabs0
    let herrv : RepSeriesSum (fun m => r.valueAt x hrdom m) :=
      sub_seriesSum_valueC3 (r := fn n) (r' := f) (x := x)
        hfndom hfdom hfnv hfv
    obtain ⟨habsModel, habsModel_eq⟩ :=
      r.absVal_signed_value x hrdom herrv
    let herrSigned : RepSeriesSum
        (fun m => (thm_4_15_abs_errorC fn f n).valueAt x herrdom m) :=
      seriesSum_of_absC herrabs
    have herr_to_abs : relEventually herrSigned.sum
        (CReal.abs (CReal.sub hfnv.sum hfv.sum)) := by
      have huniq : relEventually herrSigned.sum habsModel.sum := by
        simpa [thm_4_15_abs_errorC, r] using
          repSeriesSum_unique herrSigned habsModel
      have herrv_sub : relEventually herrv.sum
          (CReal.sub hfnv.sum hfv.sum) := by
        change relEventually
          (addSeq hfnv.sum (negSeq hfv.sum))
          (subSeq hfnv.sum hfv.sum)
        exact relEventually_symm _ _
          (subSeq_eq_add_neg_eventually hfnv.sum hfv.sum)
      exact relEventually_trans _ _ _ huniq
        (relEventually_trans _ _ _ habsModel_eq
          (absSeq_respects_eventually herrv.sum
            (CReal.sub hfnv.sum hfv.sum) herrv_sub))
    have hpt :
        regularSeqLtProp
          (CReal.abs (seriesSum_of_absC herrabs).sum) rho := by
      have hnonneg_abs : RegularSeqNonneg
          (CReal.abs (CReal.sub hfnv.sum hfv.sum)) :=
        regularSeqNonneg_of_zero_le
          (absSeq_nonnegative_regularSeqLe
            (CReal.sub hfnv.sum hfv.sum))
      have h1 : relEventually
          (CReal.abs herrSigned.sum)
          (CReal.abs (CReal.abs (CReal.sub hfnv.sum hfv.sum))) :=
        absSeq_respects_eventually herrSigned.sum
          (CReal.abs (CReal.sub hfnv.sum hfv.sum)) herr_to_abs
      have h2 : relEventually
          (CReal.abs (CReal.abs (CReal.sub hfnv.sum hfv.sum)))
          (CReal.abs (CReal.sub hfnv.sum hfv.sum)) :=
        CReal.abs_of_nonneg_E hnonneg_abs
      have houter : relEventually
          (CReal.abs herrSigned.sum)
          (CReal.abs (CReal.sub hfv.sum hfnv.sum)) :=
        relEventually_trans _ _ _ h1
          (relEventually_trans _ _ _ h2
            (absSeq_subSeq_comm_eventually hfnv.sum hfv.sum))
      exact regularSeqLtProp_of_left_eventual houter
        (hclose x hxC
          { mem := hfdom, absWitness := hfabs0 }
          { mem := hfndom, absWitness := hfnabs })
    have hlt :
        regularSeqLtProp
          (seriesSum_of_absC herrabs).sum
          (goodSetBoundC hA eta) :=
      regularSeqLtProp_of_le_of_lt
        (base_le_abs_base_regularSeqLe (seriesSum_of_absC herrabs).sum)
        (regularSeqLtProp_of_lt_of_le hpt
          (CReal.min_le_rightC delta (goodSetBoundC hA eta)))
    exact regularSeqLe_of_ltPropC hlt
  have htwo :
      regularSeqLtProp
        (thm_4_15_abs_errorC fn f n).integral
        (CReal.add eta eta) :=
    lemma_4_14_local_two_epsilonC C A hC hA hsub1
      (thm_4_15_abs_errorC fn f n)
      (thm_4_15_abs_error_nonnegC fn f n)
      eta heta hbound hbad
  have hhalf :
      regularSeqLtProp
        (thm_4_15_abs_errorC fn f n).integral
        (halfPow K) :=
    regularSeqLtProp_of_right_eventual
      (halfPow_succ_add_self K) htwo
  exact regularSeqLtProp_trans
    (thm_4_15_abs_errorC fn f n).integral (halfPow K) eps hhalf hKeps

/-- The integral of the absolute error bounds the absolute difference of
integrals. -/
theorem integral_diff_lt_of_abs_error_integral_ltC
    {X : Type u} {S : IntSpaceC X}
    (fn : Nat -> IntegrableRepC3 S) (f : IntegrableRepC3 S) (n : Nat)
    {eps : CReal}
    (herr : regularSeqLtProp (thm_4_15_abs_errorC fn f n).integral eps) :
    regularSeqLtProp
      (CReal.abs (CReal.sub (fn n).integral f.integral)) eps := by
  change regularSeqLtProp
    (absSeq (subSeq (fn n).integral f.integral)) eps
  have hleft :
      relEventually
        (absSeq (subSeq (fn n).integral f.integral))
        (CReal.abs ((fn n).sub f).integral) := by
    exact absSeq_respects_eventually _ _
      (subSeq_eq_add_neg_eventually (fn n).integral f.integral)
  have htri :
      RegularSeqLe
        (CReal.abs ((fn n).sub f).integral)
        (((fn n).sub f).absVal.integral) :=
    IntegrableRepC3.abs_integral_le_normL1C ((fn n).sub f)
  have hle :
      RegularSeqLe
        (absSeq (subSeq (fn n).integral f.integral))
        (thm_4_15_abs_errorC fn f n).integral := by
    simpa [thm_4_15_abs_errorC]
      using regularSeqLe_of_left_eventual hleft htri
  exact regularSeqLtProp_of_le_of_lt hle herr

/-- A one-step stronger representative gauge bound gives a strict dyadic
bound on the absolute difference. -/
theorem regularSeqLtProp_abs_sub_of_repCloseAtGauge_succC
    {x y : CReal} {K : Nat}
    (hclose : RepCloseAtGauge (K + 1) x y) :
    regularSeqLtProp (CReal.abs (CReal.sub x y)) (halfPow K) := by
  rcases hclose with ⟨N, hN⟩
  have hlt : regularSeqLtData (absSeq (subSeq x y)) (constSeq (eps K)) := by
    refine ⟨K + 2, N, ?_⟩
    intro n hn
    have hle_point : BishopCReal.Le
        (BishopC.COF_core.abs (x.val (n + 2) - y.val (n + 2))) (eps (K + 1)) :=
      hN (n + 2) (Nat.le_trans hn (Nat.le_add_right n 2))
    have hgap := scalar_eps_gap_of_le_succ
      (a := BishopC.COF_core.abs (x.val (n + 2) - y.val (n + 2))) K hle_point
    simpa [subSeq, subVal, constSeq, constVal, absSeq, absVal, addIndex]
      using hgap
  simpa [CReal.abs, CReal.sub, halfPow, CReal.epsSeq] using hlt.toProp

/-- Forgetful bridge from the existing Type-valued convergence datum to the
ordinary epsilon-style Prop convergence statement. -/
theorem repSeriesTendsto_to_epsPropC {u : Nat -> CReal} {l : CReal}
    (h : RepSeriesTendsto u l) :
    RepSeriesTendstoEpsPropC u l := by
  intro eps heps
  obtain ⟨K, hKeps⟩ :=
    halfPow_lt_of_posDataC (posEventuallyData_of_pos_zeroC heps)
  refine ⟨h.mod K, ?_⟩
  intro n hn
  have hdyadic :
      regularSeqLtProp (CReal.abs (CReal.sub (u n) l)) (halfPow K) :=
    regularSeqLtProp_abs_sub_of_repCloseAtGauge_succC (h.close K n hn)
  exact regularSeqLtProp_trans
    (CReal.abs (CReal.sub (u n) l)) (halfPow K) eps hdyadic hKeps

/-- Bishop--Cheng Theorem 4.15 in Prop epsilon form, with an explicit
full-set majorant. -/
theorem bishop_cheng_thm_4_15_propC_with_majorant
    {X : Type u} (S : IntSpaceC X)
    (fn : Nat -> IntegrableRepC3 S) (f g : IntegrableRepC3 S)
    (hconv : ConvergeInMeasureC S (fun n => (fn n).toDataPFunRC) f.toDataPFunRC)
    (hdom : DominatedOnFullC fn g) :
    RepSeriesTendstoEpsPropC (fun n => (fn n).integral) f.integral := by
  intro eps heps
  obtain ⟨N, hN⟩ :=
    bishop_cheng_l1_error_tends_zero_propC_with_majorant S fn f g hconv hdom eps heps
  refine ⟨N, ?_⟩
  intro n hn
  exact integral_diff_lt_of_abs_error_integral_ltC fn f n (hN n hn)

/-- Bishop--Cheng Theorem 4.15 in its Prop-facing dominated-convergence form.

The full-set majorant is existential at the outer interface. The proof opens
that existential only inside the final Prop proof and does not build a
Type-valued convergence selector. -/
theorem bishop_cheng_thm_4_15_propC
    {X : Type u} (S : IntSpaceC X)
    (fn : Nat -> IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (hconv : ConvergeInMeasureC S (fun n => (fn n).toDataPFunRC) f.toDataPFunRC)
    (hdom : exists g : IntegrableRepC3 S, DominatedOnFullC fn g) :
    RepSeriesTendstoEpsPropC (fun n => (fn n).integral) f.integral := by
  rcases hdom with ⟨g, hg⟩
  exact bishop_cheng_thm_4_15_propC_with_majorant S fn f g hconv hg

end BishopSec3P
