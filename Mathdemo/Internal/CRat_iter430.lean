import Mathdemo.Internal.CRat_iter429
import Mathdemo.Internal.CRat_iter425
import Mathdemo.Internal.CRat_iter334

set_option linter.style.longLine false

/-!
# Stage A10: DataPFunR-carrying DCT route

This additive node restates the theorem-4.15 source route over `DataPFunR`.
The public theorem below uses only witness-carrying partial functions in its
source convergence and representation inputs.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

def thm_4_15_data_pfun_zero : DataPFunR X R where
  domData := fun _ => Unit
  toFun := fun _ _ => 0

structure Lemma414ZeroDataPFunR (p : DataPFunR X R) : Type _ where
  value_zero : forall (x : X) (hp : p.domData x), p.toFun x hp = 0

def thm_4_15_data_pfun_zero_is_zero :
    Lemma414ZeroDataPFunR (thm_4_15_data_pfun_zero (X := X) (R := R)) where
  value_zero := by
    intro _x _hx
    rfl

def DataPFunR.sub (p q : DataPFunR X R) : DataPFunR X R where
  domData := fun x => p.domData x × q.domData x
  toFun := fun x hx => p.toFun x hx.1 - q.toFun x hx.2

def DataPFunR.absVal (p : DataPFunR X R) : DataPFunR X R where
  domData := p.domData
  toFun := fun x hx => COF.abs (p.toFun x hx)

def thm_4_15_data_pfun_abs_error
    (pfn : Nat -> DataPFunR X R) (pf : DataPFunR X R) :
    Nat -> DataPFunR X R :=
  fun n => (DataPFunR.sub (pfn n) pf).absVal

structure Lemma415DataPFunClosePack {S : IntSpaceRC X R}
    (A C : BSet X) (hA : IntegrableSet1 S A) (hC : IntegrableSet1 S C)
    (eps : R) (pfn pf : DataPFunR X R) : Type _ where
  subset_A : C.S1 ⊆ A.S1
  doms : forall x, x ∈ C.S1 -> pf.domData x × pfn.domData x
  measure_small : COF.lt (measure1 S (IntegrableSet1_sub hA hC)) eps
  point_close : forall (x : X) (_hxC : x ∈ C.S1)
      (hxpf : pf.domData x) (hxfn : pfn.domData x),
    COF.lt (COF.abs (pf.toFun x hxpf - pfn.toFun x hxfn)) eps

structure Lemma415DataPFunConvergeData {S : IntSpaceRC X R}
    (pfn : Nat -> DataPFunR X R) (pf : DataPFunR X R) : Type _ where
  close : forall (A : BSet X) (hA : IntegrableSet1 S A)
      (eps : R), COF.lt 0 eps ->
    Sigma (fun N : Nat =>
      forall n, N <= n ->
        Sigma (fun C : BSet X =>
          Sigma (fun hC : IntegrableSet1 S C =>
            Lemma415DataPFunClosePack (S := S) A C hA hC eps (pfn n) pf)))

abbrev Lemma414DataPFunConvergeToZeroData {S : IntSpaceRC X R}
    (pfn : Nat -> DataPFunR X R) (zero : DataPFunR X R) : Type _ :=
  Lemma415DataPFunConvergeData (S := S) pfn zero

structure Lemma414RepresentsDataPFunR {S : IntSpaceRC X R}
    (r : IntegrableRep S) (p : DataPFunR X R) : Type _ where
  value : forall (x : X) (hp : p.domData x)
    (hrDom : r.MemAt x)
    (hrabs : RSeq.SeriesSum (fun m => COF.abs (r.valueAt x hrDom m))),
      (seriesSum_of_abs hrabs).sum = p.toFun x hp

def lemma414RepresentsDataPFunR_toDataPFunRSeries (r : IntegrableRep S) :
    Lemma414RepresentsDataPFunR (S := S) r (r.toDataPFunRSeries) where
  value := by
    intro x hp _hrDom hrabs
    exact IntegrableRep.toDataPFunRSeries_represents r x hp hrabs

def lemma_4_15_data_pfun_abs_error_converge_to_zero
    (pfn : Nat -> DataPFunR X R) (pf : DataPFunR X R)
    (hconv : Lemma415DataPFunConvergeData (S := S) pfn pf) :
    Lemma414DataPFunConvergeToZeroData (S := S)
      (thm_4_15_data_pfun_abs_error pfn pf)
      (thm_4_15_data_pfun_zero (X := X) (R := R)) where
  close := by
    intro A hA eps heps
    obtain ⟨N, hN⟩ := hconv.close A hA eps heps
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hpack⟩ := hN n hn
    refine ⟨C, hC, ?_⟩
    refine
      { subset_A := hpack.subset_A
        doms := ?_
        measure_small := hpack.measure_small
        point_close := ?_ }
    · intro x hxC
      let hdom := hpack.doms x hxC
      exact ⟨(), ⟨hdom.2, hdom.1⟩⟩
    · intro x hxC _hxzero hxerr
      rcases hxerr with ⟨hxfn, hxpf⟩
      have hpt := hpack.point_close x hxC hxpf hxfn
      change COF.lt
        (COF.abs ((0 : R) -
          COF.abs ((pfn n).toFun x hxfn - pf.toFun x hxpf))) eps
      have hzero_abs :
          (0 : R) - COF.abs ((pfn n).toFun x hxfn - pf.toFun x hxpf) =
            -COF.abs ((pfn n).toFun x hxfn - pf.toFun x hxpf) := by
        ring
      rw [hzero_abs, COFO.abs_neg,
        COFO.abs_of_nonneg
          (abs_nonneg ((pfn n).toFun x hxfn - pf.toFun x hxpf))]
      have hsym :
          (pfn n).toFun x hxfn - pf.toFun x hxpf =
            -(pf.toFun x hxpf - (pfn n).toFun x hxfn) := by
        ring
      rw [hsym, COFO.abs_neg]
      exact hpt

noncomputable def lemma_4_15_data_abs_error_represents_from_sources
    (r s : IntegrableRep S) (p q : DataPFunR X R)
    (hr : Lemma414RepresentsDataPFunR (S := S) r p)
    (hs : Lemma414RepresentsDataPFunR (S := S) s q) :
    Lemma414RepresentsDataPFunR (S := S)
      ((r.sub s).absVal) ((DataPFunR.sub p q).absVal) where
  value := by
    intro x hp habsAbsValDom habsAbsVal
    let subRep : IntegrableRep S := r.sub s
    let hsubDom : subRep.MemAt x := fun k => by
      have hk := habsAbsValDom (3 * k + 1)
      simpa only [IntegrableRep.absVal, seqMerge3_one] using hk
    let hrDom : r.MemAt x := add_dom_left hsubDom
    let hnegSDom : s.neg.MemAt x := add_dom_right hsubDom
    let hsDom : s.MemAt x := neg_dom hnegSDom
    let u : Nat -> R := fun j =>
      COF.abs ((subRep.absDiffFn j).toFun x
        (subRep.absDiffFn_memAt hsubDom j))
    let v : Nat -> R := fun k =>
      COF.abs (subRep.valueAt x hsubDom k)
    let w : Nat -> R := fun k =>
      COF.abs ((BFunR.smul (-1) (subRep.fn k)).toFun x (hsubDom k))
    have hmerge : RSeq.SeriesSum (seqMerge3 u v w) := by
      refine seriesSum_congr (fun n => ?_) habsAbsVal
      dsimp [u, v, w, subRep]
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_zero]
      · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_one]
      · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_two]
    have hsub_abs :
        RSeq.SeriesSum (fun k => COF.abs
          ((r.sub s).valueAt x hsubDom k)) := by
      dsimp [v] at hmerge ⊢
      exact seriesSum_merge3_second_of_nonneg
        (u := u) (v := v) (w := w)
        (fun _ => abs_nonneg _)
        (fun _ => abs_nonneg _)
        (fun _ => abs_nonneg _)
        hmerge
    have hr_abs : RSeq.SeriesSum
        (fun k => COF.abs (r.valueAt x hrDom k)) :=
      add_absSeriesSum_left hsubDom hsub_abs
    have hs_abs : RSeq.SeriesSum
        (fun k => COF.abs (s.valueAt x hsDom k)) :=
      neg_absSeriesSum hnegSDom (add_absSeriesSum_right hsubDom hsub_abs)
    let hsub_sum : RSeq.SeriesSum
        (fun k => (r.sub s).valueAt x hsubDom k) :=
      seriesSum_of_abs hsub_abs
    let hr_sum : RSeq.SeriesSum (fun k => r.valueAt x hrDom k) :=
      seriesSum_of_abs hr_abs
    let hs_sum : RSeq.SeriesSum (fun k => s.valueAt x hsDom k) :=
      seriesSum_of_abs hs_abs
    have hsub_eq : hsub_sum.sum = hr_sum.sum - hs_sum.sum := by
      have heq :=
        seriesSum_unique hsub_sum
          (add_seriesSum_value hrDom hnegSDom hr_sum
            (neg_seriesSum_value hsDom hs_sum))
      change hsub_sum.sum = hr_sum.sum + -hs_sum.sum at heq
      rwa [sub_eq_add_neg]
    obtain ⟨habsValSum, habsValEq⟩ :=
      (r.sub s).absVal_signed_value x hsubDom hsub_sum
    have habs_eq :
        (seriesSum_of_abs habsAbsVal).sum = COF.abs hsub_sum.sum := by
      rw [seriesSum_unique (seriesSum_of_abs habsAbsVal) habsValSum, habsValEq]
    let hp_dom : p.domData x := hp.1
    let hq_dom : q.domData x := hp.2
    have hr_val := hr.value x hp_dom hrDom hr_abs
    have hs_val := hs.value x hq_dom hsDom hs_abs
    calc
      (seriesSum_of_abs habsAbsVal).sum = COF.abs hsub_sum.sum := habs_eq
      _ = COF.abs (hr_sum.sum - hs_sum.sum) := by rw [hsub_eq]
      _ = COF.abs (p.toFun x hp_dom - q.toFun x hq_dom) := by
        rw [hr_val, hs_val]
      _ = ((DataPFunR.sub p q).absVal).toFun x hp := by
        dsimp [DataPFunR.absVal, DataPFunR.sub, hp_dom, hq_dom]

noncomputable def lemma_4_14_rep_converge_from_data_pfun_converge_zero
    (fn : Nat -> IntegrableRep S) (hnn : forall n, RepNonneg (fn n))
    (pfn : Nat -> DataPFunR X R) (zero : DataPFunR X R)
    (hconv : Lemma414DataPFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroDataPFunR zero)
    (hrep : forall n, Lemma414RepresentsDataPFunR (S := S) (fn n) (pfn n)) :
    Lemma414RepConvergeToZeroData (S := S) fn where
  close := by
    intro A hA delta eta hdelta heta
    let rho : R := COF.min delta eta
    have hrho : COF.lt 0 rho := by
      dsimp [rho]
      exact lemma34_min_pos hdelta heta
    obtain ⟨N, hN⟩ := hconv.close A hA rho hrho
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hpack⟩ := hN n hn
    refine ⟨C, hC, ?_⟩
    refine ⟨?_, ?_⟩
    · intro x hxC
      exact hpack.subset_A hxC
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le hpack.measure_small (cof_min_le_left delta eta)
    · intro x hfDom hchiDom hfabs hchiabs hchione
      have hvalid := hC.valid x hchiDom hchiabs
      rcases hvalid.1 with hxC | hxC2
      · let hdom := hpack.doms x hxC
        have hxzero : zero.domData x := hdom.1
        have hxfn : (pfn n).domData x := hdom.2
        have hpt := hpack.point_close x hxC hxzero hxfn
        have hrepv := (hrep n).value x hxfn hfDom hfabs
        have hzv := hzero.value_zero x hxzero
        rw [hzv, <- hrepv] at hpt
        have hnon : Nonneg (seriesSum_of_abs hfabs).sum :=
          hnn n x hfDom hfabs (seriesSum_of_abs hfabs)
        rw [show (0 : R) - (seriesSum_of_abs hfabs).sum =
              -(seriesSum_of_abs hfabs).sum from by ring,
            COFO.abs_neg, COFO.abs_of_nonneg hnon] at hpt
        exact le_of_lt (lt_of_lt_of_le hpt (cof_min_le_right delta eta))
      · exfalso
        have hzerochi : (seriesSum_of_abs hchiabs).sum = 0 :=
          hvalid.2.2 hxC2 (seriesSum_of_abs hchiabs)
        have h01 : (0 : R) = 1 := by
          rw [<- hzerochi, hchione]
        have hbad : COF.lt (0 : R) 0 := by
          have hone := COFO.one_pos (R := R)
          rwa [<- h01] at hone
        exact COF.lt_irrefl 0 hbad

noncomputable def lemma_4_14_tendsto_zero_from_ib_and_data_pfun_converge
    (fn : Nat -> IntegrableRep S) (hnn : forall n, RepNonneg (fn n))
    (pfn : Nat -> DataPFunR X R) (zero : DataPFunR X R)
    (IB : Lemma414IBInterface (S := S) fn hnn)
    (hui : forall eps, COF.lt 0 eps -> Lemma414UniformIBData (S := S) fn hnn IB eps)
    (hconv : Lemma414DataPFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroDataPFunR zero)
    (hrep : forall n, Lemma414RepresentsDataPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_rep_converge fn hnn IB hui
    (lemma_4_14_rep_converge_from_data_pfun_converge_zero
      fn hnn pfn zero hconv hzero hrep)

end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqChapter4
namespace Theorem415Route

universe uR uD

structure Theorem415LocalDataPFunSourceDataNoLimitDomination
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S) : Type _ where
  g_nonneg : BishopC.RepNonneg g
  dominated_fn : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  pfnsrc : Nat -> BishopC.DataPFunR.{0, uR, uD} Y R
  pf : BishopC.DataPFunR.{0, uR, uD} Y R
  pfun_converges :
    BishopC.Lemma415DataPFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsDataPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsDataPFunR (S := S) f pf

noncomputable def theorem415_data_noLimitDom_rowSeedProvider_of_sourceData
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalDataPFunSourceDataNoLimitDomination fn f g) :
    BishopC.Lemma415Prop42RowSeedToolsProvider (S := S) :=
  BishopC.Lemma415Prop42RowSeedToolsProvider.of_generalIBDomainResidualProvider
    (S := S) D.domainResidualProvider

noncomputable def theorem415_data_noLimitDom_local_complement_bridges
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalDataPFunSourceDataNoLimitDomination fn f g) :
    forall (n : Nat) (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n C hC =>
    let P := theorem415_data_noLimitDom_rowSeedProvider_of_sourceData (S := S) D
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

noncomputable def theorem415_data_noLimitDom_majorant_choice_from_sourceData
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalDataPFunSourceDataNoLimitDomination fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantChoiceSourceData
      (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg)
      eps :=
  let P := theorem415_data_noLimitDom_rowSeedProvider_of_sourceData (S := S) D
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

noncomputable def theorem415_data_noLimitDom_majorant_split_from_sourceData
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalDataPFunSourceDataNoLimitDomination fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg)
      eps :=
  BishopC.lemma_4_15_majorant_split_uniform_source_data_from_choice_data
    (S := S) fn f (g.add f.absVal)
    (theorem415_g_add_absf_majorant_nonneg (S := S) f g D.g_nonneg)
    eps
    (theorem415_data_noLimitDom_majorant_choice_from_sourceData
      (S := S) D eps heps)

noncomputable def theorem415_data_noLimitDom_uniform_source_data
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalDataPFunSourceDataNoLimitDomination fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma414UniformIBSourceData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
        (theorem415_data_noLimitDom_local_complement_bridges (S := S) D))
      eps :=
  let P := theorem415_data_noLimitDom_rowSeedProvider_of_sourceData (S := S) D
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
      (theorem415_data_noLimitDom_majorant_split_from_sourceData
        (S := S) D eps heps)
  BishopC.lemma_4_15_uniform_ib_source_data_from_local_split_data
    (S := S) fn f
    (theorem415_data_noLimitDom_local_complement_bridges (S := S) D)
    eps localSplit

noncomputable def theorem415_abs_error_tendsto_from_noLimitDom_dataCarrying
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415LocalDataPFunSourceDataNoLimitDomination fn f g) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  let IB :=
    BishopC.lemma_4_14_ib_interface_from_genIB_localComplements
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (theorem415_data_noLimitDom_local_complement_bridges (S := S) D)
  BishopC.lemma_4_14_tendsto_zero_from_ib_and_data_pfun_converge
    (S := S)
    (BishopC.thm_4_15_abs_error (S := S) fn f)
    (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
    (BishopC.thm_4_15_data_pfun_abs_error D.pfnsrc D.pf)
    (BishopC.thm_4_15_data_pfun_zero (X := Y) (R := R))
    IB
    (BishopC.lemma_4_14_uniform_ib_data_from_source
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      IB
      (theorem415_data_noLimitDom_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_data_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_data_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_data_abs_error_represents_from_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

noncomputable def theorem415_localDataPFun_source_data_from_witnesses
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S)
    (pfnsrc : Nat -> BishopC.DataPFunR.{0, uR, uD} Y R)
    (pf : BishopC.DataPFunR.{0, uR, uD} Y R)
    (h_conv : BishopC.Lemma415DataPFunConvergeData (S := S) pfnsrc pf)
    (h_represents_fn : forall n,
      BishopC.Lemma414RepresentsDataPFunR (S := S) (fn n) (pfnsrc n))
    (h_represents_limit :
      BishopC.Lemma414RepresentsDataPFunR (S := S) f pf)
    (h_domain : BishopC.Sec4GeneralIBDomainResidualProvider (S := S))
    (h_g_nonneg : BishopC.RepNonneg g)
    (h_bound : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)) :
    Theorem415LocalDataPFunSourceDataNoLimitDomination fn f g where
  g_nonneg := h_g_nonneg
  dominated_fn := h_bound
  domainResidualProvider := h_domain
  pfnsrc := pfnsrc
  pf := pf
  pfun_converges := h_conv
  represents_fn := h_represents_fn
  represents_limit := h_represents_limit

noncomputable def thm_4_15_dominated_convergence_dataCarrying
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S) (f g : BishopC.IntegrableRep S)
    (pfnsrc : Nat -> BishopC.DataPFunR.{0, uR, uD} Y R)
    (pf : BishopC.DataPFunR.{0, uR, uD} Y R)
    (h_conv : BishopC.Lemma415DataPFunConvergeData (S := S) pfnsrc pf)
    (h_represents_fn : forall n,
      BishopC.Lemma414RepresentsDataPFunR (S := S) (fn n) (pfnsrc n))
    (h_represents_limit :
      BishopC.Lemma414RepresentsDataPFunR (S := S) f pf)
    (h_domain : BishopC.Sec4GeneralIBDomainResidualProvider (S := S))
    (h_g_nonneg : BishopC.RepNonneg g)
    (h_bound : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  theorem415_abs_error_tendsto_from_noLimitDom_dataCarrying
    (S := S)
    (theorem415_localDataPFun_source_data_from_witnesses
      (S := S) fn f g pfnsrc pf h_conv h_represents_fn
      h_represents_limit h_domain h_g_nonneg h_bound)

noncomputable def thm_4_15_dominated_convergence_toDataPFunRSeries
    {R : Type uR} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S) (f g : BishopC.IntegrableRep S)
    (h_conv : BishopC.Lemma415DataPFunConvergeData (S := S)
      (fun n => (fn n).toDataPFunRSeries) f.toDataPFunRSeries)
    (h_domain : BishopC.Sec4GeneralIBDomainResidualProvider (S := S))
    (h_g_nonneg : BishopC.RepNonneg g)
    (h_bound : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_15_dominated_convergence_dataCarrying
    (S := S) fn f g
    (fun n => (fn n).toDataPFunRSeries) f.toDataPFunRSeries
    h_conv
    (fun n => BishopC.lemma414RepresentsDataPFunR_toDataPFunRSeries
      (S := S) (fn n))
    (BishopC.lemma414RepresentsDataPFunR_toDataPFunRSeries
      (S := S) f)
    h_domain h_g_nonneg h_bound

end Theorem415Route
end BishopRegularSeqChapter4
end BishopCReal
