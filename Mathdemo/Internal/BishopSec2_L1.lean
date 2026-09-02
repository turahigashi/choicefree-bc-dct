import Mathdemo.Internal.BishopB
import Mathdemo.Internal.BishopB_Completeness
import Mathlib.Data.Set.Basic

namespace BishopC
variable {X R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
structure BSet (X : Type*) where
  S1 : Set X
  S2 : Set X
  disj : ∀ x, x ∈ S1 → ∀ y, y ∈ S2 → x ≠ y

namespace BSet


def Subset (A B : BSet X) : Prop :=
  A.S1 ⊆ B.S1 ∧ B.S2 ⊆ A.S2

def neg (A : BSet X) : BSet X where
  S1 := A.S2
  S2 := A.S1
  disj := fun x hx y hy heq => A.disj y hy x hx heq.symm

def and (A B : BSet X) : BSet X where
  S1 := A.S1 ∩ B.S1
  S2 := (A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1) ∪ (A.S2 ∩ B.S2)
  disj := by
    intro x hx y hy heq
    subst heq
    rcases hy with (h1 | h2) | h3
    · exact B.disj x hx.2 x h1.2 rfl
    · exact A.disj x hx.1 x h2.1 rfl
    · exact A.disj x hx.1 x h3.1 rfl

def or (A B : BSet X) : BSet X where
  S1 := (A.S1 ∩ B.S1) ∪ (A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1)
  S2 := A.S2 ∩ B.S2
  disj := by
    intro x hx y hy heq
    subst heq
    rcases hx with (h1 | h2) | h3
    · exact A.disj x h1.1 x hy.1 rfl
    · exact A.disj x h2.1 x hy.1 rfl
    · exact B.disj x h3.2 x hy.2 rfl

def sub (A B : BSet X) : BSet X := and A (neg B)



end BSet

/-- Technical lemma used in the public import closure. -/
structure IntegrableSet1 (S : IntSpaceRC X R) (A : BSet X) where
  full : IsFull S (A.S1 ∪ A.S2)
  rep : IntegrableRep S
  valid : ∀ x (hdom : rep.MemAt x),
      RSeq.SeriesSum (fun n => COF.abs (rep.valueAt x hdom n)) →
      (x ∈ A.S1 ∪ A.S2) ∧
      (x ∈ A.S1 → ∀ (h : RSeq.SeriesSum (fun n => rep.valueAt x hdom n)), h.sum = 1) ∧
      (x ∈ A.S2 → ∀ (h : RSeq.SeriesSum (fun n => rep.valueAt x hdom n)), h.sum = 0)

noncomputable def measure1 (S : IntSpaceRC X R) {A : BSet X} (hA : IntegrableSet1 S A) : R :=
  hA.rep.integral

/-- Technical lemma used in the public import closure. -/
theorem IntegrableSet1.repNonneg {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A) :
    RepNonneg hA.rep := by
  intro x hdom habs hx
  rcases (hA.valid x hdom habs).1 with hx1 | hx2
  · rw [(hA.valid x hdom habs).2.1 hx1 hx]; exact le_of_lt COFO.one_pos
  · rw [(hA.valid x hdom habs).2.2 hx2 hx]; exact le_refl (0 : R)


/-! Technical auxiliary material for the public import closure. -/

def IntegrableRep.min2 {S : IntSpaceRC X R} (r s : IntegrableRep S) : IntegrableRep S :=
  (r.add s).sub ((r.sub s).absVal) |>.smul (COF.half : R)

/-- Domain transport into the representative of the pointwise minimum. -/
theorem IntegrableRep.min2_memAt {S : IntSpaceRC X R} {r s : IntegrableRep S} {x : X}
    (hrdom : r.MemAt x) (hsdom : s.MemAt x) : (r.min2 s).MemAt x :=
  IntegrableRep.smul_memAt
    (IntegrableRep.add_memAt (IntegrableRep.add_memAt hrdom hsdom)
      (IntegrableRep.neg_memAt
        ((r.sub s).mem_absVal_dom
          (IntegrableRep.add_memAt hrdom (IntegrableRep.neg_memAt hsdom)))))

/-- Recover the left input domain from a minimum representative. -/
theorem min2_dom_left {S : IntSpaceRC X R} {r s : IntegrableRep S} {x : X}
    (hdom : (r.min2 s).MemAt x) : r.MemAt x :=
  add_dom_left (add_dom_left (smul_dom hdom))

/-- Recover the right input domain from a minimum representative. -/
theorem min2_dom_right {S : IntSpaceRC X R} {r s : IntegrableRep S} {x : X}
    (hdom : (r.min2 s).MemAt x) : s.MemAt x :=
  add_dom_right (add_dom_left (smul_dom hdom))

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def min2_value {S : IntSpaceRC X R} (r s : IntegrableRep S) (x : X)
    (hrdom : r.MemAt x) (hsdom : s.MemAt x)
    (hr : RSeq.SeriesSum (fun n => r.valueAt x hrdom n))
    (hs : RSeq.SeriesSum (fun n => s.valueAt x hsdom n)) :
    { hm : RSeq.SeriesSum (fun n => (IntegrableRep.min2 r s).valueAt x
        (IntegrableRep.min2_memAt hrdom hsdom) n) //
        hm.sum = COF.min hr.sum hs.sum } := by
  let haddDom : (r.add s).MemAt x := IntegrableRep.add_memAt hrdom hsdom
  let hnegSDom : s.neg.MemAt x := IntegrableRep.neg_memAt hsdom
  let hsubDom : (r.sub s).MemAt x := IntegrableRep.add_memAt hrdom hnegSDom
  let hadd := add_seriesSum_value hrdom hsdom hr hs
  let hnegS := neg_seriesSum_value hsdom hs
  let hsub := add_seriesSum_value hrdom hnegSDom hr hnegS
  obtain ⟨habsv, habsveq⟩ := (r.sub s).absVal_signed_value x hsubDom hsub
  let habsvDom : (r.sub s).absVal.MemAt x := (r.sub s).mem_absVal_dom hsubDom
  let hnegAbsDom : (r.sub s).absVal.neg.MemAt x := IntegrableRep.neg_memAt habsvDom
  let hinnerDom : ((r.add s).sub ((r.sub s).absVal)).MemAt x :=
    IntegrableRep.add_memAt haddDom hnegAbsDom
  let hnegAbs := neg_seriesSum_value habsvDom habsv
  let hd := add_seriesSum_value haddDom hnegAbsDom hadd hnegAbs
  refine ⟨smul_seriesSum_value COF.half hinnerDom hd, ?_⟩
  show COF.half * hd.sum = COF.min hr.sum hs.sum
  have e : hd.sum = (hr.sum + hs.sum) - COF.abs (hr.sum - hs.sum) := by
    show (hr.sum + hs.sum) + (- habsv.sum) = (hr.sum + hs.sum) - COF.abs (hr.sum - hs.sum)
    rw [habsveq]
    show (hr.sum + hs.sum) + (- COF.abs (hr.sum + (- hs.sum)))
        = (hr.sum + hs.sum) - COF.abs (hr.sum - hs.sum)
    rw [show hr.sum + (- hs.sum) = hr.sum - hs.sum from by ring]
    ring
  rw [e, COF.min_halfsum]

/-- Technical lemma used in the public import closure. -/
def min2_absSeriesSum_inner {S : IntSpaceRC X R} {r s : IntegrableRep S} {x : X}
    (hdom : (IntegrableRep.min2 r s).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((IntegrableRep.min2 r s).valueAt x hdom n))) :
    RSeq.SeriesSum (fun n => COF.abs
      (((r.add s).sub ((r.sub s).absVal)).valueAt x (smul_dom hdom) n)) := by
  refine seriesSum_congr (fun n => ?_) (seriesSum_smul (2 : R) habs)
  show (2 : R) * COF.abs ((IntegrableRep.min2 r s).valueAt x hdom n)
      = COF.abs (((r.add s).sub ((r.sub s).absVal)).valueAt x (smul_dom hdom) n)
  have hp : (IntegrableRep.min2 r s).valueAt x hdom n
          = COF.half * (((r.add s).sub ((r.sub s).absVal)).valueAt x (smul_dom hdom) n) := rfl
  rw [hp, COFO.abs_mul, COFO.abs_of_nonneg (le_of_lt COFO.half_pos),
      show (2 : R) * (COF.half * COF.abs
          (((r.add s).sub ((r.sub s).absVal)).valueAt x (smul_dom hdom) n))
        = ((2 : R) * COF.half) * COF.abs
          (((r.add s).sub ((r.sub s).absVal)).valueAt x (smul_dom hdom) n) from by ring,
      two_mul_half, one_mul]

/-- Technical lemma used in the public import closure. -/
def min2_absSeriesSum_left {S : IntSpaceRC X R} {r s : IntegrableRep S} {x : X}
    (hdom : (IntegrableRep.min2 r s).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((IntegrableRep.min2 r s).valueAt x hdom n))) :
    RSeq.SeriesSum (fun k => COF.abs (r.valueAt x (min2_dom_left hdom) k)) :=
  add_absSeriesSum_left (add_dom_left (smul_dom hdom))
    (add_absSeriesSum_left (smul_dom hdom) (min2_absSeriesSum_inner hdom habs))

/-- Technical lemma used in the public import closure. -/
def min2_absSeriesSum_right {S : IntSpaceRC X R} {r s : IntegrableRep S} {x : X}
    (hdom : (IntegrableRep.min2 r s).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((IntegrableRep.min2 r s).valueAt x hdom n))) :
    RSeq.SeriesSum (fun k => COF.abs (s.valueAt x (min2_dom_right hdom) k)) :=
  add_absSeriesSum_right (add_dom_left (smul_dom hdom))
    (add_absSeriesSum_left (smul_dom hdom) (min2_absSeriesSum_inner hdom habs))

/-- Technical lemma used in the public import closure. -/
theorem min_self (a : R) : COF.min a a = a := by
  rw [COF.min_halfsum, show a - a = (0 : R) from by ring, COFO.abs_of_nonneg (le_refl (0 : R)),
      show COF.half * (a + a - 0) = (COF.half + COF.half) * a from by ring, COF.half_add_half, one_mul]

/-- 0≤a ⟹ min(a,0)=0。 -/
theorem min_zero_right {a : R} (ha : Nonneg a) : COF.min a 0 = 0 := by
  rw [COF.min_halfsum, sub_zero, COFO.abs_of_nonneg ha]; ring

/-- 0≤a ⟹ min(0,a)=0。 -/
theorem min_zero_left {a : R} (ha : Nonneg a) : COF.min 0 a = 0 := by
  rw [COF.min_halfsum, show (0 : R) - a = - a from by ring, COFO.abs_neg, COFO.abs_of_nonneg ha]; ring

/-- Technical lemma used in the public import closure. -/
theorem cof_min_le_right (a b : R) : Le (COF.min a b) b := by
  have e : b - COF.min a b = COF.half * (COF.abs (a - b) - (a - b)) := by
    rw [COF.min_halfsum]
    calc
      b - COF.half * (a + b - COF.abs (a - b))
        = 1 * b - COF.half * (a + b - COF.abs (a - b)) := by ring
      _ = (COF.half + COF.half) * b - COF.half * (a + b - COF.abs (a - b)) := by rw [COF.half_add_half]
      _ = COF.half * (COF.abs (a - b) - (a - b)) := by ring
  have hkey : Nonneg (b - COF.min a b) := by
    rw [e]
    exact COFO.mul_nonneg (le_of_lt COFO.half_pos) (nonneg_sub_of_le (COFO.le_abs_self (a - b)))
  exact fun hlt => hkey (sub_neg_of_lt hlt)

/-- Technical lemma used in the public import closure. -/
theorem cof_min_le_left (a b : R) : Le (COF.min a b) a := by
  have e : a - COF.min a b = COF.half * (COF.abs (a - b) - (-(a - b))) := by
    rw [COF.min_halfsum]
    calc
      a - COF.half * (a + b - COF.abs (a - b))
        = 1 * a - COF.half * (a + b - COF.abs (a - b)) := by ring
      _ = (COF.half + COF.half) * a - COF.half * (a + b - COF.abs (a - b)) := by rw [COF.half_add_half]
      _ = COF.half * (COF.abs (a - b) - (-(a - b))) := by ring
  have hkey : Nonneg (a - COF.min a b) := by
    rw [e]
    exact COFO.mul_nonneg (le_of_lt COFO.half_pos) (nonneg_sub_of_le (COFO.neg_le_abs (a - b)))
  exact fun hlt => hkey (sub_neg_of_lt hlt)


/-- Technical lemma used in the public import closure. -/
def tendstoHalf_of_eventually_const {u : Nat → R} {c : R} (k : Nat)
    (h : ∀ N, k ≤ N → RSeq.partialSum u N = c) :
    RSeq.TendstoHalf (RSeq.partialSum u) c where
  mod := fun _ => k
  close := fun k' N hN => by
    show COF.lt (COF.abs (RSeq.partialSum u N - c)) (COF.halfPow k')
    rw [h N hN, show c - c = (0 : R) from by ring, COFO.abs_zero]
    exact halfPow_pos k'

/-- Technical lemma used in the public import closure. -/
theorem seriesSum_of_eventually_const {u : Nat → R} {c : R} (h : RSeq.SeriesSum u) (k : Nat)
    (hev : ∀ N, k ≤ N → RSeq.partialSum u N = c) : h.sum = c :=
  tendstoHalf_unique h.tends (tendstoHalf_of_eventually_const k hev)





noncomputable def IntegrableSet1_or {S : IntSpaceRC X R} {A B : BSet X} (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B) :
    IntegrableSet1 S (BSet.or A B) where
  full := by
    have h : (BSet.or A B).S1 ∪ (BSet.or A B).S2 = (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
      ext x
      change (x ∈ (A.S1 ∩ B.S1) ∪ (A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1)) ∨ x ∈ (A.S2 ∩ B.S2) ↔ (x ∈ A.S1 ∨ x ∈ A.S2) ∧ (x ∈ B.S1 ∨ x ∈ B.S2)
      constructor
      · rintro (((⟨a1, b1⟩ | ⟨a1, b2⟩) | ⟨a2, b1⟩) | ⟨a2, b2⟩)
        · exact ⟨Or.inl a1, Or.inl b1⟩
        · exact ⟨Or.inl a1, Or.inr b2⟩
        · exact ⟨Or.inr a2, Or.inl b1⟩
        · exact ⟨Or.inr a2, Or.inr b2⟩
      · rintro ⟨a1 | a2, b1 | b2⟩
        · exact Or.inl (Or.inl (Or.inl ⟨a1, b1⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨a1, b2⟩))
        · exact Or.inl (Or.inr ⟨a2, b1⟩)
        · exact Or.inr ⟨a2, b2⟩
    rw [h]
    exact isFull_inter hA.full hB.full
  rep := hA.rep.add hB.rep |>.sub (IntegrableRep.min2 hA.rep hB.rep)
  valid := by
    intro x hdom habs
    let haddDom : (hA.rep.add hB.rep).MemAt x := add_dom_left hdom
    let hnegMinDom : (hA.rep.min2 hB.rep).neg.MemAt x := add_dom_right hdom
    let hminDom : (hA.rep.min2 hB.rep).MemAt x := neg_dom hnegMinDom
    let hrADom : hA.rep.MemAt x := add_dom_left haddDom
    let hrBDom : hB.rep.MemAt x := add_dom_right haddDom
    have hadd_abs := add_absSeriesSum_left hdom habs
    have hrA_abs := add_absSeriesSum_left haddDom hadd_abs
    have hrB_abs := add_absSeriesSum_right haddDom hadd_abs
    have hrA := seriesSum_of_abs hrA_abs
    have hrB := seriesSum_of_abs hrB_abs
    have hvA := hA.valid x hrADom hrA_abs
    have hvB := hB.valid x hrBDom hrB_abs
    let hadd := add_seriesSum_value hrADom hrBDom hrA hrB
    obtain ⟨hm, hmeq⟩ := min2_value hA.rep hB.rep x hrADom hrBDom hrA hrB
    let hminDom' : (hA.rep.min2 hB.rep).MemAt x :=
      IntegrableRep.min2_memAt hrADom hrBDom
    let hnegMinDom' : (hA.rep.min2 hB.rep).neg.MemAt x :=
      IntegrableRep.neg_memAt hminDom'
    let hnegMin := neg_seriesSum_value hminDom' hm
    let hor := add_seriesSum_value haddDom hnegMinDom' hadd hnegMin
    refine ⟨?_, ?_, ?_⟩
    · rcases hvA.1 with hxA1 | hxA2 <;> rcases hvB.1 with hxB1 | hxB2
      · exact Or.inl (Or.inl (Or.inl ⟨hxA1, hxB1⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hxA1, hxB2⟩))
      · exact Or.inl (Or.inr ⟨hxA2, hxB1⟩)
      · exact Or.inr ⟨hxA2, hxB2⟩
    · intro hx_S1 h_sum
      rw [seriesSum_unique h_sum hor]
      show hrA.sum + hrB.sum + (- hm.sum) = 1
      rw [hmeq]
      rcases hx_S1 with (⟨hxA1, hxB1⟩ | ⟨hxA1, hxB2⟩) | ⟨hxA2, hxB1⟩
      · rw [hvA.2.1 hxA1 hrA, hvB.2.1 hxB1 hrB, min_self 1]; ring
      · rw [hvA.2.1 hxA1 hrA, hvB.2.2 hxB2 hrB, min_zero_right (le_of_lt COFO.one_pos)]; ring
      · rw [hvA.2.2 hxA2 hrA, hvB.2.1 hxB1 hrB, min_zero_left (le_of_lt COFO.one_pos)]; ring
    · intro hx_S2 h_sum
      rw [seriesSum_unique h_sum hor]
      show hrA.sum + hrB.sum + (- hm.sum) = 0
      rw [hmeq]
      obtain ⟨hxA2, hxB2⟩ := hx_S2
      rw [hvA.2.2 hxA2 hrA, hvB.2.2 hxB2 hrB, min_zero_right (le_refl (0 : R))]; ring















-- Technical note.

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem cellAt_seriesSum_eq {a : Nat → Nat → R} (ha : ∀ i j, Nonneg (a i j))
    (hrow : ∀ i, RSeq.SeriesSum (a i)) (hrowsum : RSeq.SeriesSum (fun i => (hrow i).sum)) :
    (cellAt_seriesSum ha hrow hrowsum).sum = hrowsum.sum := by
  refine le_antisymm (cellAt_seriesSum_le ha hrow hrowsum) ?_
  intro hlt
  have hpos : COF.lt 0 (hrowsum.sum - (cellAt_seriesSum ha hrow hrowsum).sum) := by
    have t := neg_pos_of_neg (sub_neg_of_lt hlt); rwa [neg_sub] at t
  obtain ⟨k, hk⟩ := COFO.archimedean_pos _ hpos
  obtain ⟨M, hM⟩ := gridSum_gap ha hrow hrowsum k
  have hgle : Le (gridSum a M) (cellAt_seriesSum ha hrow hrowsum).sum := by
    rw [← partialSum_cellAt_eq_gridSum a M]
    exact partialSum_le_sum (fun m => ha (cellAt m).1 (cellAt m).2)
      (cellAt_seriesSum ha hrow hrowsum) (M * M + 2 * M)
  have hle2 : Le (hrowsum.sum - (cellAt_seriesSum ha hrow hrowsum).sum)
                 (hrowsum.sum - gridSum a M) := by
    apply le_of_nonneg_sub
    rw [show (hrowsum.sum - gridSum a M) - (hrowsum.sum - (cellAt_seriesSum ha hrow hrowsum).sum)
          = (cellAt_seriesSum ha hrow hrowsum).sum - gridSum a M from by ring]
    exact nonneg_sub_of_le hgle
  exact COF.lt_irrefl _ (COFO.lt_trans hk (lt_of_le_of_lt hle2 hM))

/-- Technical lemma used in the public import closure. -/
def seriesIntegrable_integral {S : IntSpaceRC X R} (H : Nat → IntegrableRep S)
    (hs : RSeq.SeriesSum (fun m => (H m).absConv.sum)) :
    { hI : RSeq.SeriesSum (fun m => (H m).integral) //
        (seriesIntegrable H hs).integral = hI.sum } := by
  let hRowAbs : ∀ i, RSeq.SeriesSum (fun j => COF.abs (S.I ((H i).fn j))) :=
    fun i => seriesSum_comparison (fun _ => abs_nonneg _) (fun j => S.I_abs_ge ((H i).mem j)) (H i).absConv
  let hRowPos : ∀ i, RSeq.SeriesSum (fun j => COF.max (S.I ((H i).fn j)) 0) :=
    fun i => seriesSum_comparison (fun _ => COFO.max_zero_nonneg _) (fun _ => COFO.max_le_abs _) (hRowAbs i)
  let hRowNeg : ∀ i, RSeq.SeriesSum (fun j => - COF.min (S.I ((H i).fn j)) 0) :=
    fun i => seriesSum_comparison (fun _ => COFO.neg_min_zero_nonneg _) (fun _ => COFO.neg_min_le_abs _) (hRowAbs i)
  let hRowSumPos : RSeq.SeriesSum (fun i => (hRowPos i).sum) :=
    seriesSum_comparison (fun i => seriesSum_nonneg (fun _ => COFO.max_zero_nonneg _) (hRowPos i))
      (fun i => le_trans (seriesSum_comparison_le _ _ _) (seriesSum_comparison_le _ _ _)) hs
  let hRowSumNeg : RSeq.SeriesSum (fun i => (hRowNeg i).sum) :=
    seriesSum_comparison (fun i => seriesSum_nonneg (fun _ => COFO.neg_min_zero_nonneg _) (hRowNeg i))
      (fun i => le_trans (seriesSum_comparison_le _ _ _) (seriesSum_comparison_le _ _ _)) hs
  have eqPos : (cellAt_seriesSum (fun i j => COFO.max_zero_nonneg (S.I ((H i).fn j))) hRowPos hRowSumPos).sum
             = hRowSumPos.sum := cellAt_seriesSum_eq _ hRowPos hRowSumPos
  have eqNeg : (cellAt_seriesSum (fun i j => COFO.neg_min_zero_nonneg (S.I ((H i).fn j))) hRowNeg hRowSumNeg).sum
             = hRowSumNeg.sum := cellAt_seriesSum_eq _ hRowNeg hRowSumNeg
  have hrowdecomp : ∀ m, (H m).integral = (hRowPos m).sum - (hRowNeg m).sum := fun m =>
    seriesSum_unique (H m).seriesSum_I
      (seriesSum_congr (fun j => by rw [sub_neg_eq_add, COF.max_add_min_eq_self])
        (seriesSum_sub (hRowPos m) (hRowNeg m)))
  refine ⟨seriesSum_congr (fun m => (hrowdecomp m).symm) (seriesSum_sub hRowSumPos hRowSumNeg), ?_⟩
  have hflat_eq : (seriesIntegrable H hs).seriesSum_I.sum
      = (cellAt_seriesSum (fun i j => COFO.max_zero_nonneg (S.I ((H i).fn j))) hRowPos hRowSumPos).sum
        - (cellAt_seriesSum (fun i j => COFO.neg_min_zero_nonneg (S.I ((H i).fn j))) hRowNeg hRowSumNeg).sum :=
    seriesSum_unique (seriesIntegrable H hs).seriesSum_I
      (seriesSum_congr (fun k => by rw [sub_neg_eq_add, COF.max_add_min_eq_self]; rfl)
        (seriesSum_sub
          (cellAt_seriesSum (fun i j => COFO.max_zero_nonneg (S.I ((H i).fn j))) hRowPos hRowSumPos)
          (cellAt_seriesSum (fun i j => COFO.neg_min_zero_nonneg (S.I ((H i).fn j))) hRowNeg hRowSumNeg)))
  show (seriesIntegrable H hs).seriesSum_I.sum = hRowSumPos.sum - hRowSumNeg.sum
  rw [hflat_eq, eqPos, eqNeg]

/-- Recover a row domain from the domain of the flattened double series. -/
theorem seriesIntegrable_row_memAt {S : IntSpaceRC X R} (H : Nat → IntegrableRep S)
    (hs : RSeq.SeriesSum (fun m => (H m).absConv.sum)) {x : X}
    (hflatDom : (seriesIntegrable H hs).MemAt x) (i : Nat) : (H i).MemAt x := by
  intro j
  obtain ⟨k, hk⟩ := cellAt_surj i j
  have hd := hflatDom k
  change x ∈ ((H (cellAt k).1).fn (cellAt k).2).dom at hd
  rw [hk] at hd
  exact hd

/-- Technical lemma used in the public import closure. -/
def seriesIntegrable_value {S : IntSpaceRC X R} (H : Nat → IntegrableRep S)
    (hs : RSeq.SeriesSum (fun m => (H m).absConv.sum)) {x : X}
    (hflatDom : (seriesIntegrable H hs).MemAt x)
    (hRowAbsX : ∀ i, RSeq.SeriesSum (fun j => COF.abs
      ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)))
    (hRowSumAbsX : RSeq.SeriesSum (fun i => (hRowAbsX i).sum))
    (hflatX : RSeq.SeriesSum (fun k =>
      (seriesIntegrable H hs).valueAt x hflatDom k)) :
    { hV : RSeq.SeriesSum (fun m => (seriesSum_of_abs (hRowAbsX m)).sum) // hflatX.sum = hV.sum } := by
  let hRowPos : ∀ i, RSeq.SeriesSum (fun j => COF.max
      ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j) 0) :=
    fun i => seriesSum_comparison (fun _ => COFO.max_zero_nonneg _) (fun _ => COFO.max_le_abs _) (hRowAbsX i)
  let hRowNeg : ∀ i, RSeq.SeriesSum (fun j => - COF.min
      ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j) 0) :=
    fun i => seriesSum_comparison (fun _ => COFO.neg_min_zero_nonneg _) (fun _ => COFO.neg_min_le_abs _) (hRowAbsX i)
  let hRowSumPos : RSeq.SeriesSum (fun i => (hRowPos i).sum) :=
    seriesSum_comparison (fun i => seriesSum_nonneg (fun _ => COFO.max_zero_nonneg _) (hRowPos i))
      (fun i => seriesSum_comparison_le _ _ _) hRowSumAbsX
  let hRowSumNeg : RSeq.SeriesSum (fun i => (hRowNeg i).sum) :=
    seriesSum_comparison (fun i => seriesSum_nonneg (fun _ => COFO.neg_min_zero_nonneg _) (hRowNeg i))
      (fun i => seriesSum_comparison_le _ _ _) hRowSumAbsX
  have eqPos : (cellAt_seriesSum (fun i j => COFO.max_zero_nonneg
      ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hRowPos hRowSumPos).sum
             = hRowSumPos.sum := cellAt_seriesSum_eq _ hRowPos hRowSumPos
  have eqNeg : (cellAt_seriesSum (fun i j => COFO.neg_min_zero_nonneg
      ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hRowNeg hRowSumNeg).sum
             = hRowSumNeg.sum := cellAt_seriesSum_eq _ hRowNeg hRowSumNeg
  have hrowdecomp : ∀ m, (seriesSum_of_abs (hRowAbsX m)).sum = (hRowPos m).sum - (hRowNeg m).sum := fun m =>
    seriesSum_unique (seriesSum_of_abs (hRowAbsX m))
      (seriesSum_congr (fun j => by rw [sub_neg_eq_add, COF.max_add_min_eq_self])
        (seriesSum_sub (hRowPos m) (hRowNeg m)))
  refine ⟨seriesSum_congr (fun m => (hrowdecomp m).symm) (seriesSum_sub hRowSumPos hRowSumNeg), ?_⟩
  have hflat_eq : hflatX.sum
      = (cellAt_seriesSum (fun i j => COFO.max_zero_nonneg
          ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hRowPos hRowSumPos).sum
        - (cellAt_seriesSum (fun i j => COFO.neg_min_zero_nonneg
          ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hRowNeg hRowSumNeg).sum :=
    seriesSum_unique hflatX
      (seriesSum_congr (fun k => by rw [sub_neg_eq_add, COF.max_add_min_eq_self]; rfl)
        (seriesSum_sub
          (cellAt_seriesSum (fun i j => COFO.max_zero_nonneg
            ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hRowPos hRowSumPos)
          (cellAt_seriesSum (fun i j => COFO.neg_min_zero_nonneg
            ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hRowNeg hRowSumNeg)))
  show hflatX.sum = hRowSumPos.sum - hRowSumNeg.sum
  rw [hflat_eq, eqPos, eqNeg]

/-- Technical lemma used in the public import closure. -/
def seriesIntegrable_value_of_flat {S : IntSpaceRC X R} (H : Nat → IntegrableRep S)
    (hs : RSeq.SeriesSum (fun m => (H m).absConv.sum)) {x : X}
    (hflatDom : (seriesIntegrable H hs).MemAt x)
    (hflatabs : RSeq.SeriesSum (fun k => COF.abs
      ((seriesIntegrable H hs).valueAt x hflatDom k))) :
    { hV : RSeq.SeriesSum (fun m =>
        (seriesSum_of_abs (row_seriesSum (fun (i j : Nat) => abs_nonneg
          ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j))
          (hflatabs) m)).sum) //
        (seriesSum_of_abs hflatabs).sum = hV.sum } :=
  seriesIntegrable_value H hs hflatDom
    (fun i => row_seriesSum (fun i j => abs_nonneg
      ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hflatabs i)
    (cellAt_rowsum (fun i j => abs_nonneg
      ((H i).valueAt x (seriesIntegrable_row_memAt H hs hflatDom i) j)) hflatabs)
    (seriesSum_of_abs hflatabs)


/-- Domain of the flattened finite-prefix representatives. -/
def seriesSumRep_L1_Gflat_memAt {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hdom : (seriesSumRep_L1 F hsum).MemAt x) :
    (seriesIntegrable (G_m F) (G_m_absConv_seriesSum F hsum)).MemAt x :=
  add_dom_left hdom

/-- Domain of the flattened tail representatives. -/
def seriesSumRep_L1_tailFlat_memAt {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hdom : (seriesSumRep_L1 F hsum).MemAt x) :
    (seriesIntegrable (tail_m F) (tail_m_absConv_seriesSum F)).MemAt x :=
  add_dom_right hdom

/-- Domain of one finite-prefix row. -/
def seriesSumRep_L1_Grow_memAt {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hdom : (seriesSumRep_L1 F hsum).MemAt x) (m : Nat) : (G_m F m).MemAt x :=
  seriesIntegrable_row_memAt (G_m F) (G_m_absConv_seriesSum F hsum)
    (seriesSumRep_L1_Gflat_memAt F hsum hdom) m

/-- Domain of one tail row. -/
def seriesSumRep_L1_tailRow_memAt {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hdom : (seriesSumRep_L1 F hsum).MemAt x) (m : Nat) : (tail_m F m).MemAt x :=
  seriesIntegrable_row_memAt (tail_m F) (tail_m_absConv_seriesSum F)
    (seriesSumRep_L1_tailFlat_memAt F hsum hdom) m

/-- Recover every source component domain from the prefix/tail split. -/
theorem seriesSumRep_L1_F_memAt {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hdom : (seriesSumRep_L1 F hsum).MemAt x) (m : Nat) : (F m).MemAt x := by
  let hGrow := seriesSumRep_L1_Grow_memAt F hsum hdom m
  let hTail := seriesSumRep_L1_tailRow_memAt F hsum hdom m
  let hPsi : x ∈ (psi_m F m).dom := IntegrableRep.ofL_dom (psi_m_mem F m) hGrow
  intro n
  by_cases hn : n ≤ Nm F m
  · exact mem_seqSum_dom_le hPsi n hn
  · have ht := hTail (n - (Nm F m) - 1)
    change x ∈ ((F m).fn (Nm F m + 1 + (n - Nm F m - 1))).dom at ht
    rwa [show Nm F m + 1 + (n - Nm F m - 1) = n by omega] at ht

/-- Technical lemma used in the public import closure. -/
def seriesSumRep_L1_hsplit_value {S : IntSpaceRC X R} (F : Nat → IntegrableRep S) (m : Nat) {x : X}
    (hFdom : (F m).MemAt x)
    (hFv : RSeq.SeriesSum (fun n => (F m).valueAt x hFdom n)) :
    (IntegrableRep.ofL_value (psi_m_mem F m) x
      (BFunR.seqSum_mem (F m).fn x hFdom (Nm F m))).1.sum
      + (IntegrableRep.tailFrom_value (F m) (Nm F m) x hFdom hFv).1.sum = hFv.sum := by
  rw [(IntegrableRep.ofL_value (psi_m_mem F m) x
        (BFunR.seqSum_mem (F m).fn x hFdom (Nm F m))).2,
      (IntegrableRep.tailFrom_value (F m) (Nm F m) x hFdom hFv).2]
  show (BFunR.seqSum (F m).fn (Nm F m)).toFun x
        (BFunR.seqSum_mem (F m).fn x hFdom (Nm F m))
        + (hFv.sum - (BFunR.seqSum (F m).fn (Nm F m)).toFun x
          (BFunR.seqSum_mem (F m).fn x hFdom (Nm F m))) = hFv.sum
  ring

/-- Technical lemma used in the public import closure. -/
def seriesSumRep_L1_value {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hflatDom : (seriesSumRep_L1 F hsum).MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((seriesSumRep_L1 F hsum).valueAt x hflatDom n))) :
    { hV : RSeq.SeriesSum (fun m =>
        (seriesSum_of_abs (row_seriesSum (fun (i j : Nat) => abs_nonneg
          ((G_m F i).valueAt x (seriesSumRep_L1_Grow_memAt F hsum hflatDom i) j))
          (add_absSeriesSum_left hflatDom hflatabs) m)).sum
        + (seriesSum_of_abs (row_seriesSum (fun (i j : Nat) => abs_nonneg
          ((tail_m F i).valueAt x (seriesSumRep_L1_tailRow_memAt F hsum hflatDom i) j))
          (add_absSeriesSum_right hflatDom hflatabs) m)).sum) //
        (seriesSum_of_abs hflatabs).sum = hV.sum } := by
  obtain ⟨hVG, eG⟩ := seriesIntegrable_value_of_flat (G_m F) (G_m_absConv_seriesSum F hsum)
    (seriesSumRep_L1_Gflat_memAt F hsum hflatDom)
    (add_absSeriesSum_left hflatDom hflatabs)
  obtain ⟨hVT, eT⟩ := seriesIntegrable_value_of_flat (tail_m F) (tail_m_absConv_seriesSum F)
    (seriesSumRep_L1_tailFlat_memAt F hsum hflatDom)
    (add_absSeriesSum_right hflatDom hflatabs)
  refine ⟨seriesSum_add hVG hVT, ?_⟩
  show (seriesSum_of_abs hflatabs).sum = hVG.sum + hVT.sum
  rw [← eG, ← eT]
  exact seriesSum_unique (seriesSum_of_abs hflatabs)
    (add_seriesSum_value (seriesSumRep_L1_Gflat_memAt F hsum hflatDom)
      (seriesSumRep_L1_tailFlat_memAt F hsum hflatDom)
      (seriesSum_of_abs (add_absSeriesSum_left hflatDom hflatabs))
      (seriesSum_of_abs (add_absSeriesSum_right hflatDom hflatabs)))

/-! Technical auxiliary material for the public import closure. -/














/-- Technical lemma used in the public import closure. -/
noncomputable def seriesSumRep_L1_row_absConv {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) {x : X}
    (hflatDom : (seriesSumRep_L1 F hsum).MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((seriesSumRep_L1 F hsum).valueAt x hflatDom n))) (m : Nat) :
    RSeq.SeriesSum (fun k => COF.abs ((F m).valueAt x
      (seriesSumRep_L1_F_memAt F hsum hflatDom m) k)) := by
  let htailFlatDom := seriesSumRep_L1_tailFlat_memAt F hsum hflatDom
  have htail_flat :
      RSeq.SeriesSum (fun n => COF.abs
        ((seriesIntegrable (tail_m F) (tail_m_absConv_seriesSum F)).valueAt x
          htailFlatDom n)) :=
    add_absSeriesSum_right hflatDom hflatabs
  let htailRowDom := seriesSumRep_L1_tailRow_memAt F hsum hflatDom m
  have htail_m : RSeq.SeriesSum (fun j => COF.abs
      ((tail_m F m).valueAt x htailRowDom j)) :=
    row_seriesSum (fun i j => abs_nonneg ((tail_m F i).valueAt x
      (seriesSumRep_L1_tailRow_memAt F hsum hflatDom i) j)) htail_flat m
  exact seriesSum_of_tail (Nm F m) htail_m




noncomputable def IntegrableSet1_and {S : IntSpaceRC X R} {A B : BSet X} (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B) :
    IntegrableSet1 S (BSet.and A B) where
  full := by
    have h : (BSet.and A B).S1 ∪ (BSet.and A B).S2 = (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
      ext x
      change x ∈ (A.S1 ∩ B.S1) ∨ x ∈ ((A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1) ∪ (A.S2 ∩ B.S2)) ↔ (x ∈ A.S1 ∨ x ∈ A.S2) ∧ (x ∈ B.S1 ∨ x ∈ B.S2)
      constructor
      · rintro (⟨a1, b1⟩ | (⟨a1, b2⟩ | ⟨a2, b1⟩) | ⟨a2, b2⟩)
        · exact ⟨Or.inl a1, Or.inl b1⟩
        · exact ⟨Or.inl a1, Or.inr b2⟩
        · exact ⟨Or.inr a2, Or.inl b1⟩
        · exact ⟨Or.inr a2, Or.inr b2⟩
      · rintro ⟨a1 | a2, b1 | b2⟩
        · exact Or.inl ⟨a1, b1⟩
        · exact Or.inr (Or.inl (Or.inl ⟨a1, b2⟩))
        · exact Or.inr (Or.inl (Or.inr ⟨a2, b1⟩))
        · exact Or.inr (Or.inr ⟨a2, b2⟩)
    rw [h]
    exact isFull_inter hA.full hB.full
  rep := IntegrableRep.min2 hA.rep hB.rep
  valid := by
    intro x hdom habs
    let hrADom : hA.rep.MemAt x := min2_dom_left hdom
    let hrBDom : hB.rep.MemAt x := min2_dom_right hdom
    have hrA_abs := min2_absSeriesSum_left hdom habs
    have hrB_abs := min2_absSeriesSum_right hdom habs
    have hrA := seriesSum_of_abs hrA_abs
    have hrB := seriesSum_of_abs hrB_abs
    have hvA := hA.valid x hrADom hrA_abs
    have hvB := hB.valid x hrBDom hrB_abs
    obtain ⟨hm, hmeq⟩ := min2_value hA.rep hB.rep x hrADom hrBDom hrA hrB
    refine ⟨?_, ?_, ?_⟩
    · rcases hvA.1 with hxA1 | hxA2 <;> rcases hvB.1 with hxB1 | hxB2
      · exact Or.inl ⟨hxA1, hxB1⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hxA1, hxB2⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨hxA2, hxB1⟩))
      · exact Or.inr (Or.inr ⟨hxA2, hxB2⟩)
    · intro hx_S1 h_sum
      rw [seriesSum_unique h_sum hm, hmeq, hvA.2.1 hx_S1.1 hrA, hvB.2.1 hx_S1.2 hrB]
      exact min_self 1
    · intro hx_S2 h_sum
      rw [seriesSum_unique h_sum hm, hmeq]
      rcases hx_S2 with (⟨hxA1, hxB2⟩ | ⟨hxA2, hxB1⟩) | ⟨hxA2, hxB2⟩
      · rw [hvA.2.1 hxA1 hrA, hvB.2.2 hxB2 hrB]; exact min_zero_right (le_of_lt COFO.one_pos)
      · rw [hvA.2.2 hxA2 hrA, hvB.2.1 hxB1 hrB]; exact min_zero_left (le_of_lt COFO.one_pos)
      · rw [hvA.2.2 hxA2 hrA, hvB.2.2 hxB2 hrB]; exact min_zero_right (le_refl (0 : R))

/-! Technical auxiliary material for the public import closure. -/









/-- Technical lemma used in the public import closure. -/
noncomputable def IntegrableSet1_sub {S : IntSpaceRC X R} {A B : BSet X}
    (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B) :
    IntegrableSet1 S (BSet.sub A B) where
  full := by
    have h : (BSet.sub A B).S1 ∪ (BSet.sub A B).S2 = (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
      ext x
      change x ∈ (A.S1 ∩ B.S2) ∨ x ∈ ((A.S1 ∩ B.S1) ∪ (A.S2 ∩ B.S2) ∪ (A.S2 ∩ B.S1)) ↔ (x ∈ A.S1 ∨ x ∈ A.S2) ∧ (x ∈ B.S1 ∨ x ∈ B.S2)
      constructor
      · rintro (⟨a1, b2⟩ | (⟨a1, b1⟩ | ⟨a2, b2⟩) | ⟨a2, b1⟩)
        · exact ⟨Or.inl a1, Or.inr b2⟩
        · exact ⟨Or.inl a1, Or.inl b1⟩
        · exact ⟨Or.inr a2, Or.inr b2⟩
        · exact ⟨Or.inr a2, Or.inl b1⟩
      · rintro ⟨a1 | a2, b1 | b2⟩
        · exact Or.inr (Or.inl (Or.inl ⟨a1, b1⟩))
        · exact Or.inl ⟨a1, b2⟩
        · exact Or.inr (Or.inr ⟨a2, b1⟩)
        · exact Or.inr (Or.inl (Or.inr ⟨a2, b2⟩))
    rw [h]
    exact isFull_inter hA.full hB.full
  rep := hA.rep.sub (IntegrableRep.min2 hA.rep hB.rep)
  valid := by
    intro x hdom habs
    let hrADom : hA.rep.MemAt x := add_dom_left hdom
    let hnegMinDom : (hA.rep.min2 hB.rep).neg.MemAt x := add_dom_right hdom
    let hminDom : (hA.rep.min2 hB.rep).MemAt x := neg_dom hnegMinDom
    let hrBDom : hB.rep.MemAt x := min2_dom_right hminDom
    have hrA_abs := add_absSeriesSum_left hdom habs
    have hmin_abs := neg_absSeriesSum hnegMinDom
      (add_absSeriesSum_right hdom habs)
    have hrB_abs := min2_absSeriesSum_right hminDom hmin_abs
    have hrA := seriesSum_of_abs hrA_abs
    have hrB := seriesSum_of_abs hrB_abs
    have hvA := hA.valid x hrADom hrA_abs
    have hvB := hB.valid x hrBDom hrB_abs
    obtain ⟨hm, hmeq⟩ := min2_value hA.rep hB.rep x hrADom hrBDom hrA hrB
    let hminDom' : (hA.rep.min2 hB.rep).MemAt x :=
      IntegrableRep.min2_memAt hrADom hrBDom
    let hnegMinDom' : (hA.rep.min2 hB.rep).neg.MemAt x :=
      IntegrableRep.neg_memAt hminDom'
    let hsub := add_seriesSum_value hrADom hnegMinDom' hrA
      (neg_seriesSum_value hminDom' hm)
    refine ⟨?_, ?_, ?_⟩
    · rcases hvA.1 with hxA1 | hxA2 <;> rcases hvB.1 with hxB1 | hxB2
      · exact Or.inr (Or.inl (Or.inl ⟨hxA1, hxB1⟩))
      · exact Or.inl ⟨hxA1, hxB2⟩
      · exact Or.inr (Or.inr ⟨hxA2, hxB1⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨hxA2, hxB2⟩))
    · intro hx_S1 h_sum
      rw [seriesSum_unique h_sum hsub]
      show hrA.sum + (- hm.sum) = 1
      rw [hmeq, hvA.2.1 hx_S1.1 hrA, hvB.2.2 hx_S1.2 hrB, min_zero_right (le_of_lt COFO.one_pos)]
      ring
    · intro hx_S2 h_sum
      rw [seriesSum_unique h_sum hsub]
      show hrA.sum + (- hm.sum) = 0
      rw [hmeq]
      rcases hx_S2 with (⟨hxA1, hxB⟩ | ⟨hxA2, hxB⟩) | ⟨hxA2, hxB⟩
      · rw [hvA.2.1 hxA1 hrA, hvB.2.1 hxB hrB, min_self 1]; ring
      · rw [hvA.2.2 hxA2 hrA, hvB.2.2 hxB hrB, min_zero_right (le_refl (0 : R))]; ring
      · rw [hvA.2.2 hxA2 hrA, hvB.2.1 hxB hrB, min_zero_left (le_of_lt COFO.one_pos)]; ring





























/- Additive clean characteristic representatives for Section 2.
The representative is carried together with termwise nonnegativity, pointwise
binary values, and bridges back to the ordinary `IntegrableSet1` witness. -/
/-- A signed representative series together with the domain on which it is evaluated. -/
structure RepSummableAtSec2 {S : IntSpaceRC X R} (r : IntegrableRep S) (x : X) where
  dom : r.MemAt x
  series : RSeq.SeriesSum (fun k => r.valueAt x dom k)

structure CleanCharRepSec2 {S : IntSpaceRC X R} (A : BSet X) where
  existing_chi : IntegrableSet1 S A
  rep : IntegrableRep S
  term_nonneg : ∀ k x (hx : x ∈ (rep.fn k).dom), Nonneg ((rep.fn k).toFun x hx)
  term_zero_or_one : ∀ k x (hx : x ∈ (rep.fn k).dom),
    PSum ((rep.fn k).toFun x hx = 0) ((rep.fn k).toFun x hx = 1)
  value_one :
    ∀ x, x ∈ A.S1 →
      { h : RepSummableAtSec2 rep x // h.series.sum = 1 }
  value_zero :
    ∀ x, x ∈ A.S2 →
      { h : RepSummableAtSec2 rep x // h.series.sum = 0 }
  bridge_value_existing :
    ∀ x
      (h_clean_dom : rep.MemAt x) (h_existing_dom : existing_chi.rep.MemAt x)
      (h_clean_abs : RSeq.SeriesSum (fun k => COF.abs
        (rep.valueAt x h_clean_dom k)))
      (h_existing_abs : RSeq.SeriesSum (fun k => COF.abs
        (existing_chi.rep.valueAt x h_existing_dom k)))
      (h_clean : RSeq.SeriesSum (fun k => rep.valueAt x h_clean_dom k))
      (h_existing : RSeq.SeriesSum (fun k =>
        existing_chi.rep.valueAt x h_existing_dom k)),
        h_clean.sum = h_existing.sum
  bridge_integral_existing : rep.integral = existing_chi.rep.integral

namespace CleanCharRepSec2

variable {S : IntSpaceRC X R} {A : BSet X}








end CleanCharRepSec2

/-- Data for a clean representative of the complement side, constructed directly
as a nonnegative side indicator rather than by subtracting from the constant one. -/
structure CleanComplementSideSec2 {S : IntSpaceRC X R} {A : BSet X}
    (C : CleanCharRepSec2 (S := S) A) where
  out : CleanCharRepSec2 (S := S) (BSet.neg A)
  direct_side_indicator : Nat
  subtractive_constant_constructor_count : direct_side_indicator = 0

/-- Data for the clean intersection/minimum constructor. -/
structure CleanInterSec2 {S : IntSpaceRC X R} {A B : BSet X}
    (CA : CleanCharRepSec2 (S := S) A) (CB : CleanCharRepSec2 (S := S) B) where
  out : CleanCharRepSec2 (S := S) (BSet.and A B)
  term_nonneg_preserved : Nat
  binary_value_preserved : Nat

/-- Data for the clean union/maximum constructor. -/
structure CleanUnionSec2 {S : IntSpaceRC X R} {A B : BSet X}
    (CA : CleanCharRepSec2 (S := S) A) (CB : CleanCharRepSec2 (S := S) B) where
  out : CleanCharRepSec2 (S := S) (BSet.or A B)
  term_nonneg_preserved : Nat
  binary_value_preserved : Nat

/-- Section 2 clean Boolean surface: clean min, clean max, and direct side complement. -/
structure CleanBooleanSec2Ops (S : IntSpaceRC X R) where
  clean_min :
    ∀ {A B : BSet X} (CA : CleanCharRepSec2 (S := S) A)
      (CB : CleanCharRepSec2 (S := S) B),
      CleanInterSec2 (S := S) CA CB
  clean_max :
    ∀ {A B : BSet X} (CA : CleanCharRepSec2 (S := S) A)
      (CB : CleanCharRepSec2 (S := S) B),
      CleanUnionSec2 (S := S) CA CB
  clean_complement_side :
    ∀ {A : BSet X} (CA : CleanCharRepSec2 (S := S) A),
      CleanComplementSideSec2 (S := S) CA













namespace Prop210BaseCleanRepSec2

variable {S : IntSpaceRC X R} {Ops : CleanBooleanSec2Ops (X := X) (R := R) S}
variable {A : Nat → BSet X}



end Prop210BaseCleanRepSec2


end BishopC
