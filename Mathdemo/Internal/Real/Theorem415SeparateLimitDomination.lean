import Mathdemo.Internal.Real.LocalTheorem415SourcePFun

set_option linter.style.longLine false

/-!
# G235: Theorem 4.15 without a separate limit-domination input

G234 removed the direct abs-error convergence-in-measure input.  This file
removes the separate `|f| <= g` endpoint input from the local PFun route.

The source proof writes the error domination as `|f_n - f| <= 2g`.  In Lean that
requires a representative-level datum `|f| <= g`.  Rather than silently adding
that datum, this file uses the theorem statement's already integrable limit
`f` to form the constructive majorant `g + |f|`:

`|f_n - f| <= |f_n| + |f| <= g + |f|`.

This is a Bishop-valid variant of the displayed domination step and introduces
no Prop-to-data selector.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- The alternative theorem-4.15 majorant `g + |f|` is non-negative from
`g >= 0` and the automatic non-negativity of `|f|`. -/
noncomputable def theorem415_g_add_absf_majorant_nonneg
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (f g : BishopC.IntegrableRep S)
    (g_nonneg : BishopC.RepNonneg g) :
    BishopC.RepNonneg (g.add f.absVal) :=
  BishopC.sec4_add_repNonneg
    (S := S) g f.absVal g_nonneg (BishopC.repNonneg_absVal f)

/-- The error domination used by the no-limit-domination route:
`|f_n - f| <= g + |f|`, derived from the theorem hypothesis
`|f_n| <= g`. -/
theorem theorem415_abs_error_dominated_by_g_add_absf
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S)
    (hfn_dom : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)) :
  forall n,
      BishopC.RepNonneg
        ((g.add f.absVal).sub
          (BishopC.thm_4_15_abs_error (S := S) fn f n)) := by
  intro n x htotalDom habs hx
  let err : BishopC.IntegrableRep S :=
    BishopC.thm_4_15_abs_error (S := S) fn f n
  let subRep : BishopC.IntegrableRep S := (fn n).sub f
  let hmajorantDom : (g.add f.absVal).MemAt x :=
    BishopC.add_dom_left htotalDom
  let herrNegDom : err.neg.MemAt x := BishopC.add_dom_right htotalDom
  let herrDom : err.MemAt x := BishopC.neg_dom herrNegDom
  have hmajorant_abs :
      RSeq.SeriesSum
        (fun k => COF.abs ((g.add f.absVal).valueAt x hmajorantDom k)) := by
    simpa only [hmajorantDom] using
      BishopC.add_absSeriesSum_left htotalDom habs
  have herr_neg_abs :
      RSeq.SeriesSum
        (fun k => COF.abs (err.neg.valueAt x herrNegDom k)) := by
    simpa only [herrNegDom] using
      BishopC.add_absSeriesSum_right htotalDom habs
  have herr_abs :
      RSeq.SeriesSum (fun k => COF.abs (err.valueAt x herrDom k)) := by
    simpa only [herrDom] using
      BishopC.neg_absSeriesSum herrNegDom herr_neg_abs
  let hgDom : g.MemAt x := BishopC.add_dom_left hmajorantDom
  let hfAbsDom : f.absVal.MemAt x := BishopC.add_dom_right hmajorantDom
  have hg_abs :
      RSeq.SeriesSum (fun k => COF.abs (g.valueAt x hgDom k)) := by
    simpa only [hgDom] using
      BishopC.add_absSeriesSum_left hmajorantDom hmajorant_abs
  have hfAbs_abs :
      RSeq.SeriesSum
        (fun k => COF.abs (f.absVal.valueAt x hfAbsDom k)) := by
    simpa only [hfAbsDom] using
      BishopC.add_absSeriesSum_right hmajorantDom hmajorant_abs
  let hg_sum : RSeq.SeriesSum (fun k => g.valueAt x hgDom k) :=
    BishopC.seriesSum_of_abs hg_abs
  let hfAbs_sum :
      RSeq.SeriesSum (fun k => f.absVal.valueAt x hfAbsDom k) :=
    BishopC.seriesSum_of_abs hfAbs_abs
  let herr_sum : RSeq.SeriesSum (fun k => err.valueAt x herrDom k) :=
    BishopC.seriesSum_of_abs herr_abs
  let hmajorant_sum :
      RSeq.SeriesSum
        (fun k => (g.add f.absVal).valueAt x hmajorantDom k) := by
    simpa only [hmajorantDom] using
      BishopC.add_seriesSum_value hgDom hfAbsDom hg_sum hfAbs_sum
  let htotal :
      RSeq.SeriesSum
        (fun k => ((g.add f.absVal).sub err).valueAt x htotalDom k) := by
    simpa only [BishopC.IntegrableRep.sub] using
      BishopC.add_seriesSum_value hmajorantDom herrNegDom hmajorant_sum
        (BishopC.neg_seriesSum_value herrDom herr_sum)
  have hx_eq : hx.sum = htotal.sum := BishopC.seriesSum_unique hx htotal
  let hsubAt : BishopC.Sec4RepAbsAt subRep x :=
    _root_.BishopCReal.BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.prop412_absVal_absSeries_to_inner_absSeries subRep
        (by simpa only [err, subRep, BishopC.thm_4_15_abs_error] using herrDom)
        (by simpa only [err, subRep, BishopC.thm_4_15_abs_error] using herr_abs)
  let hsubDom : subRep.MemAt x := hsubAt.fst
  have hsub_abs :
      RSeq.SeriesSum (fun k => COF.abs (subRep.valueAt x hsubDom k)) :=
    hsubAt.snd
  let hfnDom : (fn n).MemAt x := BishopC.add_dom_left hsubDom
  let hfNegDom : f.neg.MemAt x := BishopC.add_dom_right hsubDom
  let hfDom : f.MemAt x := BishopC.neg_dom hfNegDom
  have hfn_abs :
      RSeq.SeriesSum (fun k => COF.abs ((fn n).valueAt x hfnDom k)) := by
    simpa only [hfnDom] using
      BishopC.add_absSeriesSum_left hsubDom hsub_abs
  have hf_neg_abs :
      RSeq.SeriesSum (fun k => COF.abs (f.neg.valueAt x hfNegDom k)) := by
    simpa only [hfNegDom] using
      BishopC.add_absSeriesSum_right hsubDom hsub_abs
  have hf_abs :
      RSeq.SeriesSum (fun k => COF.abs (f.valueAt x hfDom k)) := by
    simpa only [hfDom] using BishopC.neg_absSeriesSum hfNegDom hf_neg_abs
  let hfn_sum : RSeq.SeriesSum (fun k => (fn n).valueAt x hfnDom k) :=
    BishopC.seriesSum_of_abs hfn_abs
  let hf_sum : RSeq.SeriesSum (fun k => f.valueAt x hfDom k) :=
    BishopC.seriesSum_of_abs hf_abs
  let hsub_sum : RSeq.SeriesSum (fun k => subRep.valueAt x hsubDom k) :=
    BishopC.seriesSum_of_abs hsub_abs
  have hsub_eq : hsub_sum.sum = hfn_sum.sum - hf_sum.sum := by
    have heq :=
      BishopC.seriesSum_unique hsub_sum
        (BishopC.add_seriesSum_value hfnDom hfNegDom hfn_sum
          (BishopC.neg_seriesSum_value hfDom hf_sum))
    change hsub_sum.sum = hfn_sum.sum + -hf_sum.sum at heq
    rwa [sub_eq_add_neg]
  obtain ⟨herr_alt, herr_alt_eq⟩ :=
    subRep.absVal_pointSum x hsubDom hsub_sum
  have herr_eq :
      herr_sum.sum = COF.abs (hfn_sum.sum - hf_sum.sum) := by
    have heq : herr_sum.sum = herr_alt.sum :=
      BishopC.seriesSum_unique herr_sum herr_alt
    rw [heq, herr_alt_eq, hsub_eq]
  let hfnAbsValDom : (fn n).absVal.MemAt x :=
    (fn n).mem_absVal_dom hfnDom
  have hfn_absVal_abs :
      RSeq.SeriesSum
        (fun k => COF.abs ((fn n).absVal.valueAt x hfnAbsValDom k)) := by
    simpa only [BishopC.IntegrableRep.valueAt, hfnAbsValDom] using
      (fn n).absVal_absSeries hfnDom hfn_abs
  let hfn_absVal_sum :
      RSeq.SeriesSum (fun k => (fn n).absVal.valueAt x hfnAbsValDom k) :=
    BishopC.seriesSum_of_abs hfn_absVal_abs
  obtain ⟨hfn_absVal_alt, hfn_absVal_alt_eq⟩ :=
    (fn n).absVal_pointSum x hfnDom hfn_sum
  have hfn_absVal_sum_eq :
      hfn_absVal_sum.sum = COF.abs hfn_sum.sum := by
    rw [BishopC.seriesSum_unique hfn_absVal_sum hfn_absVal_alt,
      hfn_absVal_alt_eq]
  let hfnSubAt : BishopC.Sec4RepAbsAt (g.sub (fn n).absVal) x :=
    BishopC.sec4_sub_absSeriesSum_fwd
      (r := g) (s := (fn n).absVal)
      ⟨hgDom, hg_abs⟩ ⟨hfnAbsValDom, hfn_absVal_abs⟩
  have hfn_sub_abs :
      RSeq.SeriesSum (fun k => COF.abs
        ((g.sub (fn n).absVal).valueAt x hfnSubAt.fst k)) :=
    hfnSubAt.snd
  let hfnAbsValNegDom : (fn n).absVal.neg.MemAt x :=
    BishopC.IntegrableRep.neg_memAt hfnAbsValDom
  let hfn_sub_sum : RSeq.SeriesSum
      (fun k => (g.sub (fn n).absVal).valueAt x hfnSubAt.fst k) := by
    simpa only [BishopC.IntegrableRep.sub] using
      BishopC.add_seriesSum_value hgDom hfnAbsValNegDom hg_sum
        (BishopC.neg_seriesSum_value hfnAbsValDom hfn_absVal_sum)
  have hfn_nonneg :=
    hfn_dom n x hfnSubAt.fst hfn_sub_abs hfn_sub_sum
  have hfn_abs_le_g : BishopC.Le (COF.abs hfn_sum.sum) hg_sum.sum := by
    have hle_absVal : BishopC.Le hfn_absVal_sum.sum hg_sum.sum :=
      BishopC.le_of_nonneg_sub (by
        rw [show hg_sum.sum - hfn_absVal_sum.sum =
            hg_sum.sum + -hfn_absVal_sum.sum from by ring]
        exact hfn_nonneg)
    rwa [← hfn_absVal_sum_eq]
  let hfAbsValDom : f.absVal.MemAt x := f.mem_absVal_dom hfDom
  have hf_absVal_abs :
      RSeq.SeriesSum
        (fun k => COF.abs (f.absVal.valueAt x hfAbsValDom k)) := by
    simpa only [BishopC.IntegrableRep.valueAt, hfAbsValDom] using
      f.absVal_absSeries hfDom hf_abs
  let hf_absVal_sum :
      RSeq.SeriesSum (fun k => f.absVal.valueAt x hfAbsValDom k) :=
    BishopC.seriesSum_of_abs hf_absVal_abs
  obtain ⟨hf_absVal_alt, hf_absVal_alt_eq⟩ :=
    f.absVal_pointSum x hfDom hf_sum
  have hf_absVal_sum_eq :
      hf_absVal_sum.sum = COF.abs hf_sum.sum := by
    rw [BishopC.seriesSum_unique hf_absVal_sum hf_absVal_alt,
      hf_absVal_alt_eq]
  have hf_abs_le_absf : BishopC.Le (COF.abs hf_sum.sum) hfAbs_sum.sum := by
    rw [← hf_absVal_sum_eq]
    have heq : hf_absVal_sum.sum = hfAbs_sum.sum :=
      BishopC.seriesSum_unique hf_absVal_sum hfAbs_sum
    rw [heq]
    exact BishopC.le_refl hfAbs_sum.sum
  have herr_le_abs_sum :
      BishopC.Le herr_sum.sum (COF.abs hfn_sum.sum + COF.abs hf_sum.sum) := by
    rw [herr_eq]
    exact BishopC.abs_sub_le hfn_sum.sum hf_sum.sum
  have herr_le_majorant :
      BishopC.Le herr_sum.sum (hg_sum.sum + hfAbs_sum.sum) :=
    BishopC.le_trans herr_le_abs_sum
      (BishopC.le_add hfn_abs_le_g hf_abs_le_absf)
  rw [hx_eq]
  change BishopC.Nonneg ((hg_sum.sum + hfAbs_sum.sum) + -herr_sum.sum)
  rw [show (hg_sum.sum + hfAbs_sum.sum) + -herr_sum.sum =
      (hg_sum.sum + hfAbs_sum.sum) - herr_sum.sum from by ring]
  exact BishopC.nonneg_sub_of_le herr_le_majorant

/-- The local theorem-4.15 PFun source data without a separate
`|f| <= g` field. -/
structure Theorem415LocalPFunSourceDataNoLimitDomination
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S) : Type _ where
  g_nonneg : BishopC.RepNonneg g
  dominated_fn : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

noncomputable def theorem415_noLimitDom_rowSeedProvider_of_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g) :
    BishopC.Lemma415Prop42RowSeedToolsProvider (S := S) :=
  BishopC.Lemma415Prop42RowSeedToolsProvider.of_generalIBDomainResidualProvider
    (S := S) D.domainResidualProvider

noncomputable def theorem415_noLimitDom_local_complement_bridges
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g) :
    forall (n : Nat) (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n C hC =>
    let P := theorem415_noLimitDom_rowSeedProvider_of_sourceData (S := S) D
    BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S)
      (BishopC.BSet.neg C)
      (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
      (BishopC.sec4_genIBValueBridge_of_rowSeedTools
        (S := S)
        (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
        (P.rowSeeds
          (BishopC.thm_4_15_abs_error (S := S) fn f n)
          (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)))

/-- Build majorant-choice data for the alternative majorant `g + |f|`. -/
noncomputable def theorem415_noLimitDom_majorant_choice_from_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantChoiceSourceData
      (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg)
      eps :=
  let P := theorem415_noLimitDom_rowSeedProvider_of_sourceData (S := S) D
  let majorant := g.add f.absVal
  let majorant_nonneg :=
    theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg
  let budget : BishopC.Lemma415TailBudgetSourceData (R := R) eps :=
    BishopC.lemma_4_15_default_tail_budget (R := R) eps heps
  let majorantComp :
      BishopC.Lemma415GComplementTailRelChoiceSourceData
        (S := S) majorant majorant_nonneg eps :=
    BishopC.lemma_4_15_g_complement_tail_rel_choice_data_from_coverSetBudget
      (S := S) majorant majorant_nonneg eps
      (P.rowSeeds majorant majorant_nonneg)
      budget
  let majorantTail :
      BishopC.Lemma415GSingleTailRelChoiceSourceData
        (S := S) majorant majorant_nonneg eps :=
    BishopC.lemma_4_15_g_single_tail_rel_choice_source_data_from_g_complement_tail_data
      (S := S) majorant majorant_nonneg eps majorantComp
  {
    majorantSeeds := majorantTail.gSeeds
    A := majorantTail.A
    hA := majorantTail.hA
    N := majorantTail.N
    N_ge_one := majorantTail.N_ge_one
    epsAB := budget.epsAB
    epsNeg := budget.epsNeg
    epsAB_pos := budget.epsAB_pos
    pieces_sum_lt := budget.pieces_sum_lt
    dominatesError :=
      theorem415_abs_error_dominated_by_g_add_absf
        (S := S) fn f g D.dominated_fn
    majorantNegSmall := by
      have h_epsG_nonneg : BishopC.Nonneg budget.epsG :=
        BishopC.le_of_lt budget.epsG_pos
      have h_epsG_le_double :
          BishopC.Le budget.epsG (budget.epsG + budget.epsG) := by
        apply BishopC.le_of_nonneg_sub
        rw [show (budget.epsG + budget.epsG) - budget.epsG =
            budget.epsG from by ring]
        exact h_epsG_nonneg
      have h_epsG_lt_epsNeg : COF.lt budget.epsG budget.epsNeg :=
        BishopC.lt_of_le_of_lt h_epsG_le_double budget.gTailBudget
      exact COFO.lt_trans majorantTail.gNegSmall h_epsG_lt_epsNeg
  }

noncomputable def theorem415_noLimitDom_majorant_split_from_sourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg)
      eps :=
  BishopC.lemma_4_15_majorant_split_uniform_source_data_from_choice_data
    (S := S) fn f (g.add f.absVal)
    (theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg)
    eps
    (theorem415_noLimitDom_majorant_choice_from_sourceData
      (S := S) D eps heps)

noncomputable def theorem415_noLimitDom_uniform_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma414UniformIBSourceData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
        (theorem415_noLimitDom_local_complement_bridges (S := S) D))
      eps :=
  let P := theorem415_noLimitDom_rowSeedProvider_of_sourceData (S := S) D
  let hSeeds : forall n,
      BishopC.Sec4Prop42RowSeedTools (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
    fun n =>
      P.rowSeeds
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  let localSplit :
      BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
    BishopC.lemma_4_15_local_split_uniform_source_data_from_majorant_data
      (S := S) fn f hSeeds (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg)
      eps
      (theorem415_noLimitDom_majorant_split_from_sourceData
        (S := S) D eps heps)
  BishopC.lemma_4_15_uniform_ib_source_data_from_local_split_data
    (S := S) fn f
    (theorem415_noLimitDom_local_complement_bridges (S := S) D)
    eps localSplit

/-- Abs-error convergence of integrals without a separate `|f| <= g` input. -/
noncomputable def theorem415_abs_error_tendsto_from_noLimitDom_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  let IB :=
    BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (theorem415_noLimitDom_local_complement_bridges (S := S) D)
  BishopC.lemma_4_14_tendsto_zero_from_ib_and_pfun_converge
    (S := S)
    (BishopC.thm_4_15_abs_error (S := S) fn f)
    (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
    (BishopC.thm_4_15_pfun_abs_error D.pfnsrc D.pf)
    (BishopC.thm_4_15_pfun_zero (X := Y) (R := R))
    IB
    (BishopC.lemma_4_14_uniform_ib_data_from_source
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      IB
      (theorem415_noLimitDom_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

/-- Theorem 4.15 from source PFun convergence data, without the separate
limit-domination field. -/
noncomputable def theorem415_integral_convergence_from_noLimitDom_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (theorem415_abs_error_tendsto_from_noLimitDom_source_data
      (S := S) D)

structure Theorem415NoLimitDomRouteAuditAfterG235 : Type where
  separate_limit_domination_input_removed : Nat
  substitute_majorant_g_plus_abs_f_used : Nat
  direct_abs_error_convergence_input_removed : Nat
  source_pfun_convergence_input_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def theorem415NoLimitDomRouteAuditAfterG235 :
    Theorem415NoLimitDomRouteAuditAfterG235 where
  separate_limit_domination_input_removed := 1
  substitute_majorant_g_plus_abs_f_used := 1
  direct_abs_error_convergence_input_removed := 1
  source_pfun_convergence_input_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 2
  remaining_plain_prop_415_bridge_steps := 3

structure Chapter4G235Theorem415NoLimitDomPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g234 : Chapter4G234Theorem415PFunSourcePackage S
  audit : Theorem415NoLimitDomRouteAuditAfterG235
  theorem415_noLimitDom_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def chapter4G235Theorem415NoLimitDomPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G235Theorem415NoLimitDomPackage S where
  g234 := chapter4G234Theorem415PFunSourcePackage S
  audit := theorem415NoLimitDomRouteAuditAfterG235
  theorem415_noLimitDom_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 2
  remaining_plain_prop_415_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G235. -/
def bishopRegularSeqChapter4Theorem415NoLimitDomProgressAfterG235 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G235: removed the separate |f| <= g endpoint input from the local 4.15 \
    PFun source route by using the constructive majorant g + |f| for \
    |f_n - f|. This avoids a hidden limit-domination witness. Remaining \
    source-data bridges are g-nonnegativity/equivalence conventions and the \
    domain-residual provider; the completely plain Prop statement remains 3."


end BishopCReal
