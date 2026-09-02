import Mathdemo.Internal.BishopB

namespace BishopC
variable {X R : Type*} [COFOC R] {S : IntSpaceRC X R}

/-- Technical lemma used in the public import closure. -/
def Nm (F : Nat → IntegrableRep S) (m : Nat) : Nat :=
  max ((lemma_1_8 (F m)).mod m) ((F m).absConv.tends.mod m)

/-- Technical lemma used in the public import closure. -/
def tail_m (F : Nat → IntegrableRep S) (m : Nat) : IntegrableRep S :=
  (F m).tailFrom (Nm F m)

/-- Technical lemma used in the public import closure. -/
def psi_m (F : Nat → IntegrableRep S) (m : Nat) : BFunR X R :=
  BFunR.seqSum (F m).fn (Nm F m)

/-- Technical lemma used in the public import closure. -/
theorem psi_m_mem (F : Nat → IntegrableRep S) (m : Nat) : psi_m F m ∈ S.L :=
  S.toIntSpaceR.seqSum_mem (F m).mem (Nm F m)

/-- Technical lemma used in the public import closure. -/
def G_m (F : Nat → IntegrableRep S) (m : Nat) : IntegrableRep S :=
  IntegrableRep.ofL (psi_m_mem F m)

/-- Technical lemma used in the public import closure. -/
theorem tail_m_absConv_sum_lt (F : Nat → IntegrableRep S) (m : Nat) :
    COF.lt (tail_m F m).absConv.sum (COF.halfPow m) := by
  have h := (F m).absConv.tends.close m (Nm F m) (Nat.le_max_right _ _)
  show COF.lt ((F m).absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf ((F m).fn n))) (Nm F m))
              (COF.halfPow m)
  refine lt_of_le_of_lt (COFO.le_abs_self _) ?_
  rw [show COF.abs ((F m).absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf ((F m).fn n))) (Nm F m))
        = COF.abs (RSeq.partialSum (fun n => S.I (BFunR.absf ((F m).fn n))) (Nm F m) - (F m).absConv.sum) from by
        rw [show (F m).absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf ((F m).fn n))) (Nm F m)
              = -(RSeq.partialSum (fun n => S.I (BFunR.absf ((F m).fn n))) (Nm F m) - (F m).absConv.sum)
              from by ring, COFO.abs_neg]]
  exact h

/-- Technical lemma used in the public import closure. -/
theorem G_m_absConv_sum_lt (F : Nat → IntegrableRep S) (m : Nat) :
    COF.lt (G_m F m).absConv.sum ((F m).normL1 + COF.halfPow m) := by
  -- G_m.absConv.sum = S.I (BFunR.absf (psi_m F m))。
  -- Technical note.
  -- Technical note.
  have e_sum : (G_m F m).absConv.sum = S.I (BFunR.absf (psi_m F m)) := by
    refine seriesSum_sum_congr ?_ (G_m F m).absConv
      (seriesSum_single (S.I (BFunR.absf (psi_m F m))))
    intro n
    show S.I (BFunR.absf ((IntegrableRep.ofL (psi_m_mem F m)).fn n))
        = if n = 0 then S.I (BFunR.absf (psi_m F m)) else (0:R)
    by_cases hn : n = 0
    · rw [if_pos hn]
      show S.I (BFunR.absf (if n = 0 then psi_m F m else BFunR.smul (0:R) (psi_m F m)))
          = S.I (BFunR.absf (psi_m F m))
      rw [if_pos hn]
    · rw [if_neg hn]
      show S.I (BFunR.absf (if n = 0 then psi_m F m else BFunR.smul (0:R) (psi_m F m))) = (0:R)
      rw [if_neg hn]
      exact I_abs_smul_zero (psi_m_mem F m)
  rw [e_sum]
  have hc := (lemma_1_8 (F m)).close m (Nm F m) (Nat.le_max_left _ _)
  have e1 : COF.lt (S.I (BFunR.absf (psi_m F m)) - (F m).normL1) (COF.halfPow m) :=
    lt_of_le_of_lt (COFO.le_abs_self _) hc
  have := COF.lt_add_left ((F m).normL1) e1
  rwa [show (F m).normL1 + (S.I (BFunR.absf (psi_m F m)) - (F m).normL1)
        = S.I (BFunR.absf (psi_m F m)) from by ring] at this

/-- Technical lemma used in the public import closure. -/
def tail_m_absConv_seriesSum (F : Nat → IntegrableRep S) :
    RSeq.SeriesSum (fun m => (tail_m F m).absConv.sum) :=
  seriesSum_comparison
    (fun m => IntegrableRep.absSum_nonneg (tail_m F m))
    (fun m => le_of_lt (tail_m_absConv_sum_lt F m))
    seriesSum_halfPow

/-- Technical lemma used in the public import closure. -/
def G_m_absConv_seriesSum (F : Nat → IntegrableRep S) (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) :
    RSeq.SeriesSum (fun m => (G_m F m).absConv.sum) :=
  seriesSum_comparison
    (fun m => IntegrableRep.absSum_nonneg (G_m F m))
    (fun m => le_of_lt (G_m_absConv_sum_lt F m))
    (seriesSum_add hsum seriesSum_halfPow)

/-- Technical lemma used in the public import closure. -/
def seriesSumRep_L1 (F : Nat → IntegrableRep S) (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) : IntegrableRep S :=
  let G_sum := seriesIntegrable (G_m F) (G_m_absConv_seriesSum F hsum)
  let tail_sum := seriesIntegrable (tail_m F) (tail_m_absConv_seriesSum F)
  G_sum.add tail_sum

/-! Technical auxiliary material for the public import closure. -/
namespace RSeq


/-- Technical lemma used in the public import closure. -/
def seriesSum_congr {R : Type*} [COFOC R] {u v : Nat → R} (h : ∀ n, u n = v n)
    (hu : SeriesSum u) : SeriesSum v where
  sum := hu.sum
  tends :=
    { mod := hu.tends.mod
      close := fun k n hn => by
        rw [← partialSum_congr h n]; exact hu.tends.close k n hn }

end RSeq

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def tendstoHalf_squeeze_zero {a b : Nat → R} (hb : RSeq.TendstoHalf b 0)
    (hnn : ∀ n, ¬ COF.lt (a n) 0) (hle : ∀ n, ¬ COF.lt (b n) (a n)) :
    RSeq.TendstoHalf a 0 where
  mod := hb.mod
  close := fun k n hn => by
    have hbn_nonneg : ¬ COF.lt (b n) 0 := fun h => hnn n (lt_of_le_of_lt (hle n) h)
    have hbclose : COF.lt (COF.abs (b n - 0)) (COF.halfPow k) := hb.close k n hn
    rw [sub_zero, COFO.abs_of_nonneg hbn_nonneg] at hbclose
    show COF.lt (COF.abs (a n - 0)) (COF.halfPow k)
    rw [sub_zero, COFO.abs_of_nonneg (hnn n)]
    exact lt_of_le_of_lt (hle n) hbclose

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.integral_mono_of_repNonneg_sub {u v : IntegrableRep S}
    (h : RepNonneg (v.sub u)) : Le u.integral v.integral := by
  have hnn : Nonneg (v.sub u).integral :=
    ((v.sub u).normL1_eq_integral_of_nonneg h) ▸ (v.sub u).normL1_nonneg
  rw [IntegrableRep.integral_sub] at hnn
  exact le_of_nonneg_sub hnn

/-- Technical lemma used in the public import closure. -/
theorem cof_min_le_min_right (s a b : R) (h : Le a b) :
    Le (COF.min s a) (COF.min s b) := by
  apply le_of_nonneg_sub
  rw [COF.min_halfsum s a, COF.min_halfsum s b,
      show COF.half * (s + b - COF.abs (s - b)) - COF.half * (s + a - COF.abs (s - a))
        = COF.half * ((b - a) - (COF.abs (s - b) - COF.abs (s - a))) from by ring]
  have hrt : Le (COF.abs (s - b) - COF.abs (s - a)) (b - a) := by
    have h1 : Le (COF.abs (s - b) - COF.abs (s - a))
                 (COF.abs ((s - b) - (s - a))) :=
      le_trans (COFO.le_abs_self (COF.abs (s - b) - COF.abs (s - a)))
        (abs_abs_sub_abs_le (s - b) (s - a))
    rwa [show (s - b) - (s - a) = -(b - a) from by ring, COFO.abs_neg,
         COFO.abs_of_nonneg (nonneg_sub_of_le h)] at h1
  exact COFO.mul_nonneg (le_of_lt COFO.half_pos) (nonneg_sub_of_le hrt)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def seriesSum_mid_of_merge3_abs {u v w : Nat → R}
    (h : RSeq.SeriesSum (fun n => COF.abs (seqMerge3 u v w n))) :
    RSeq.SeriesSum (fun k => COF.abs (v k)) :=
  seriesSum_congr (fun k => by rw [seqMerge3_one])
    (seriesSum_of_partialCauchy
      (isCauchy_of_inj (fun _ => abs_nonneg _) (e := fun k => 3 * k + 1)
        (fun l => by show 3 * l + 1 < 3 * (l + 1) + 1; omega) (fun l => by show l ≤ 3 * l + 1; omega)
        (isCauchy_of_tendsto h.tends)))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.cutConstVal_base_memAt {r : IntegrableRep S} {x : X}
    (a : R) (ha : ¬ COF.lt a 0) (hdom : (r.cutConstVal a ha).MemAt x) :
    r.MemAt x := by
  intro k
  have hk := hdom (3 * k + 1)
  simpa only [IntegrableRep.cutConstVal, seqMerge3_one] using hk

/-- Extract the middle component of the absolute three-way merge while retaining
the domain witness required by a genuine partial function. -/
def cutConstVal_absSeriesSum_mid {r : IntegrableRep S} {x : X} (a : R)
    (ha : ¬ COF.lt a 0) (hdom : (r.cutConstVal a ha).MemAt x)
    (habs : RSeq.SeriesSum (fun n =>
      COF.abs ((r.cutConstVal a ha).valueAt x hdom n))) :
    RSeq.SeriesSum (fun k => COF.abs
      (r.valueAt x (r.cutConstVal_base_memAt a ha hdom) k)) := by
  let hbase : r.MemAt x := r.cutConstVal_base_memAt a ha hdom
  apply seriesSum_mid_of_merge3_abs
    (u := fun j => (r.cutConstDiffFn a j).toFun x
      (r.mem_cutConstDiffFn_dom a hbase j))
    (v := fun k => r.valueAt x hbase k)
    (w := fun k => (BFunR.smul (-1) (r.fn k)).toFun x (hbase k))
  refine RSeq.seriesSum_congr (fun n => ?_) habs
  rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simp only [IntegrableRep.valueAt, IntegrableRep.cutConstVal, seqMerge3_zero]
  · simp only [IntegrableRep.valueAt, IntegrableRep.cutConstVal, seqMerge3_one]
  · simp only [IntegrableRep.valueAt, IntegrableRep.cutConstVal, BFunR.smul,
      seqMerge3_two]

/-- Technical lemma used in the public import closure. -/
theorem min_nonneg {a b : R} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (COF.min a b) := by
  rw [COF.min_halfsum a b]
  refine COFO.mul_nonneg (le_of_lt COFO.half_pos) (nonneg_sub_of_le ?_)
  have h := COFO.abs_add_le a (-b)
  rw [show a + (-b) = a - b from by ring, COFO.abs_neg] at h
  rwa [COFO.abs_of_nonneg ha, COFO.abs_of_nonneg hb] at h

/-- Technical lemma used in the public import closure. -/
theorem repNonneg_cutConstVal (f : IntegrableRep S) (hf : RepNonneg f) (a : R) (ha : ¬ COF.lt a 0) :
    RepNonneg (f.cutConstVal a ha) := by
  intro x hdom hx_abs hx
  let hbase : f.MemAt x := f.cutConstVal_base_memAt a ha hdom
  have hf_abs := cutConstVal_absSeriesSum_mid a ha hdom hx_abs
  have hfx := seriesSum_of_abs hf_abs
  have hfx_nn : Nonneg hfx.sum := hf x hbase hf_abs hfx
  obtain ⟨hs, hseq⟩ := f.cutConstVal_signed_value a ha x hbase hfx
  rw [seriesSum_unique hx hs, hseq]
  exact min_nonneg hfx_nn ha

/-- Technical lemma used in the public import closure. -/
theorem repNonneg_cutSmall_sub_cutConst (f : IntegrableRep S) (hf : RepNonneg f) (n : Nat)
    (a : R) (ha : ¬ COF.lt a 0) (hle : ¬ COF.lt (COF.halfPow n) a) :
    RepNonneg ((f.cutSmallVal n).sub (f.cutConstVal a ha)) := by
  intro x hsubDom hx_abs hx
  let haddDom : ((f.cutSmallVal n).add (f.cutConstVal a ha).neg).MemAt x := by
    simpa only [IntegrableRep.sub] using hsubDom
  let haddAbs : RSeq.SeriesSum (fun k => COF.abs
      (((f.cutSmallVal n).add (f.cutConstVal a ha).neg).valueAt x haddDom k)) := by
    simpa only [IntegrableRep.sub] using hx_abs
  -- de-interleave (sub = add ∘ neg): cutSmall abs / cutConst abs
  let hsmallDom : (f.cutSmallVal n).MemAt x := add_dom_left haddDom
  let hnegDom : (f.cutConstVal a ha).neg.MemAt x := add_dom_right haddDom
  let hcutDom : (f.cutConstVal a ha).MemAt x := neg_dom hnegDom
  have hcs_abs := add_absSeriesSum_left haddDom haddAbs
  have hcc_neg_abs := add_absSeriesSum_right haddDom haddAbs
  have hcc_abs := neg_absSeriesSum hnegDom hcc_neg_abs
  -- Technical note.
  let hbase : f.MemAt x := f.cutConstVal_base_memAt a ha hcutDom
  have hf_abs := cutConstVal_absSeriesSum_mid a ha hcutDom hcc_abs
  have hfx := seriesSum_of_abs hf_abs
  have hfx_nn : Nonneg hfx.sum := hf x hbase hf_abs hfx
  -- Technical note.
  let habsValDom : f.absVal.MemAt x :=
    f.absVal.cutConstVal_base_memAt (COF.halfPow n) (halfPow_nonneg n) hsmallDom
  have hg_abs := cutConstVal_absSeriesSum_mid
    (COF.halfPow n) (halfPow_nonneg n) hsmallDom hcs_abs
  have hgx := seriesSum_of_abs hg_abs
  -- hg.sum = |hf.sum| = hf.sum (f≥0)
  obtain ⟨hav, haveq⟩ := f.absVal_signed_value x hbase hfx
  have hg_eq : hgx.sum = hfx.sum := by
    rw [seriesSum_unique hgx hav, haveq, COFO.abs_of_nonneg hfx_nn]
  -- Technical note.
  obtain ⟨hcs, hcseq⟩ := f.absVal.cutConstVal_signed_value
    (COF.halfPow n) (halfPow_nonneg n) x habsValDom hgx
  obtain ⟨hcc, hcceq⟩ := f.cutConstVal_signed_value a ha x hbase hfx
  let hcsDom := f.absVal.mem_cutConstVal_dom
    (COF.halfPow n) (halfPow_nonneg n) habsValDom
  let hccDom := f.mem_cutConstVal_dom a ha hbase
  let hnegSeries := neg_seriesSum_value hccDom hcc
  rw [seriesSum_unique hx
    (add_seriesSum_value hcsDom (IntegrableRep.neg_memAt hccDom) hcs hnegSeries)]
  show Nonneg (hcs.sum + (- hcc.sum))
  rw [hcseq, hcceq, hg_eq,
      show COF.min hfx.sum (COF.halfPow n) + (- COF.min hfx.sum a)
        = COF.min hfx.sum (COF.halfPow n) - COF.min hfx.sum a from by ring]
  exact nonneg_sub_of_le (cof_min_le_min_right hfx.sum a (COF.halfPow n) hle)

end BishopC
