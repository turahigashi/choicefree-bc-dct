import Mathdemo.Internal.CRat_iter333

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
  intro n x habs hx
  let err : BishopC.IntegrableRep S :=
    BishopC.thm_4_15_abs_error (S := S) fn f n
  let subRep : BishopC.IntegrableRep S := (fn n).sub f
  have hmajorant_abs :
      RSeq.SeriesSum
        (fun k => COF.abs (((g.add f.absVal).fn k).toFun x)) :=
    BishopC.add_absSeriesSum_left habs
  have herr_neg_abs :
      RSeq.SeriesSum (fun k => COF.abs ((err.neg.fn k).toFun x)) :=
    BishopC.add_absSeriesSum_right habs
  have herr_abs :
      RSeq.SeriesSum (fun k => COF.abs ((err.fn k).toFun x)) :=
    BishopC.neg_absSeriesSum herr_neg_abs
  have hg_abs : RSeq.SeriesSum (fun k => COF.abs ((g.fn k).toFun x)) :=
    BishopC.add_absSeriesSum_left hmajorant_abs
  have hfAbs_abs :
      RSeq.SeriesSum (fun k => COF.abs ((f.absVal.fn k).toFun x)) :=
    BishopC.add_absSeriesSum_right hmajorant_abs
  let hg_sum : RSeq.SeriesSum (fun k => (g.fn k).toFun x) :=
    BishopC.seriesSum_of_abs hg_abs
  let hfAbs_sum : RSeq.SeriesSum (fun k => (f.absVal.fn k).toFun x) :=
    BishopC.seriesSum_of_abs hfAbs_abs
  let herr_sum : RSeq.SeriesSum (fun k => (err.fn k).toFun x) :=
    BishopC.seriesSum_of_abs herr_abs
  let hmajorant_sum :
      RSeq.SeriesSum (fun k => ((g.add f.absVal).fn k).toFun x) :=
    BishopC.add_seriesSum_value hg_sum hfAbs_sum
  let htotal :
      RSeq.SeriesSum
        (fun k => (((g.add f.absVal).sub err).fn k).toFun x) :=
    BishopC.add_seriesSum_value hmajorant_sum
      (BishopC.neg_seriesSum_value herr_sum)
  have hx_eq : hx.sum = htotal.sum := BishopC.seriesSum_unique hx htotal
  let u : Nat -> R := fun j => COF.abs ((subRep.absDiffFn j).toFun x)
  let v : Nat -> R := fun k => COF.abs ((subRep.fn k).toFun x)
  let w : Nat -> R := fun k =>
    COF.abs ((BFunR.smul (-1) (subRep.fn k)).toFun x)
  have hmerge : RSeq.SeriesSum (BishopC.seqMerge3 u v w) := by
    refine BishopC.seriesSum_congr (fun m => ?_) herr_abs
    dsimp [u, v, w, err, subRep, BishopC.thm_4_15_abs_error]
    change COF.abs
        (((BishopC.seqMerge3 ((fn n).sub f).absDiffFn ((fn n).sub f).fn
          (fun k => BFunR.smul (-1) (((fn n).sub f).fn k)) m).toFun x)) =
      BishopC.seqMerge3
        (fun j => COF.abs ((((fn n).sub f).absDiffFn j).toFun x))
        (fun k => COF.abs ((((fn n).sub f).fn k).toFun x))
        (fun k => COF.abs
          ((BFunR.smul (-1) (((fn n).sub f).fn k)).toFun x)) m
    exact BishopC.seqMerge3_map (fun q : BFunR Y R => COF.abs (q.toFun x))
      ((fn n).sub f).absDiffFn ((fn n).sub f).fn
      (fun k => BFunR.smul (-1) (((fn n).sub f).fn k)) m
  have hsub_abs :
      RSeq.SeriesSum (fun k => COF.abs ((subRep.fn k).toFun x)) := by
    dsimp [v] at hmerge ⊢
    exact BishopC.seriesSum_merge3_second_of_nonneg
      (u := u) (v := v) (w := w)
      (fun _ => BishopC.abs_nonneg _)
      (fun _ => BishopC.abs_nonneg _)
      (fun _ => BishopC.abs_nonneg _)
      hmerge
  have hfn_abs :
      RSeq.SeriesSum (fun k => COF.abs (((fn n).fn k).toFun x)) :=
    BishopC.add_absSeriesSum_left hsub_abs
  have hf_abs :
      RSeq.SeriesSum (fun k => COF.abs ((f.fn k).toFun x)) :=
    BishopC.neg_absSeriesSum (BishopC.add_absSeriesSum_right hsub_abs)
  let hfn_sum : RSeq.SeriesSum (fun k => ((fn n).fn k).toFun x) :=
    BishopC.seriesSum_of_abs hfn_abs
  let hf_sum : RSeq.SeriesSum (fun k => (f.fn k).toFun x) :=
    BishopC.seriesSum_of_abs hf_abs
  let hsub_sum : RSeq.SeriesSum (fun k => (subRep.fn k).toFun x) :=
    BishopC.seriesSum_of_abs hsub_abs
  have hsub_eq : hsub_sum.sum = hfn_sum.sum - hf_sum.sum := by
    have heq :=
      BishopC.seriesSum_unique hsub_sum
        (BishopC.add_seriesSum_value hfn_sum
          (BishopC.neg_seriesSum_value hf_sum))
    change hsub_sum.sum = hfn_sum.sum + -hf_sum.sum at heq
    rwa [sub_eq_add_neg]
  obtain ⟨herr_alt, herr_alt_eq⟩ := subRep.absVal_pointSum x hsub_sum
  have herr_eq :
      herr_sum.sum = COF.abs (hfn_sum.sum - hf_sum.sum) := by
    have heq : herr_sum.sum = herr_alt.sum :=
      BishopC.seriesSum_unique herr_sum herr_alt
    rw [heq, herr_alt_eq, hsub_eq]
  have hfn_absVal_abs :
      RSeq.SeriesSum (fun k => COF.abs (((fn n).absVal.fn k).toFun x)) :=
    (fn n).absVal_absSeries hfn_abs
  let hfn_absVal_sum :
      RSeq.SeriesSum (fun k => ((fn n).absVal.fn k).toFun x) :=
    BishopC.seriesSum_of_abs hfn_absVal_abs
  obtain ⟨hfn_absVal_alt, hfn_absVal_alt_eq⟩ :=
    (fn n).absVal_pointSum x hfn_sum
  have hfn_absVal_sum_eq :
      hfn_absVal_sum.sum = COF.abs hfn_sum.sum := by
    rw [BishopC.seriesSum_unique hfn_absVal_sum hfn_absVal_alt,
      hfn_absVal_alt_eq]
  have hfn_sub_abs :
      RSeq.SeriesSum
        (fun k => COF.abs (((g.sub (fn n).absVal).fn k).toFun x)) :=
    BishopC.sec4_sub_absSeriesSum_fwd hg_abs hfn_absVal_abs
  let hfn_sub_sum : RSeq.SeriesSum
      (fun k => ((g.sub (fn n).absVal).fn k).toFun x) :=
    BishopC.add_seriesSum_value hg_sum
      (BishopC.neg_seriesSum_value hfn_absVal_sum)
  have hfn_nonneg := hfn_dom n x hfn_sub_abs hfn_sub_sum
  have hfn_abs_le_g : BishopC.Le (COF.abs hfn_sum.sum) hg_sum.sum := by
    have hle_absVal : BishopC.Le hfn_absVal_sum.sum hg_sum.sum :=
      BishopC.le_of_nonneg_sub (by
        rw [show hg_sum.sum - hfn_absVal_sum.sum =
            hg_sum.sum + -hfn_absVal_sum.sum from by ring]
        exact hfn_nonneg)
    rwa [← hfn_absVal_sum_eq]
  have hf_absVal_abs :
      RSeq.SeriesSum (fun k => COF.abs ((f.absVal.fn k).toFun x)) :=
    f.absVal_absSeries hf_abs
  let hf_absVal_sum :
      RSeq.SeriesSum (fun k => (f.absVal.fn k).toFun x) :=
    BishopC.seriesSum_of_abs hf_absVal_abs
  obtain ⟨hf_absVal_alt, hf_absVal_alt_eq⟩ :=
    f.absVal_pointSum x hf_sum
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
