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

def Equiv (A B : BSet X) : Prop :=
  A.S1 = B.S1 ∧ A.S2 = B.S2

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

/-- Technical lemma used in the public import closure. -/
def bigAnd (A : Nat → BSet X) : BSet X where
  S1 := ⋂ k, (A k).S1
  S2 := (⋂ k, (A k).S1 ∪ (A k).S2) ∩ (⋃ k, (A k).S2)
  disj := by
    intro x hx y hy heq
    subst heq
    have h1 : ∀ k, x ∈ (A k).S1 := by
      intro k
      exact Set.mem_iInter.mp hx k
    have h2 : ∃ k, x ∈ (A k).S2 := by
      exact Set.mem_iUnion.mp hy.2
    rcases h2 with ⟨k, hk⟩
    exact (A k).disj x (h1 k) x hk rfl

/-- Technical lemma used in the public import closure. -/
def bigOr (A : Nat → BSet X) : BSet X where
  S1 := (⋂ k, (A k).S1 ∪ (A k).S2) ∩ (⋃ k, (A k).S1)
  S2 := ⋂ k, (A k).S2
  disj := by
    intro x hx y hy heq
    subst heq
    have h2 : ∀ k, x ∈ (A k).S2 := by
      intro k
      exact Set.mem_iInter.mp hy k
    have h1 : ∃ k, x ∈ (A k).S1 := by
      exact Set.mem_iUnion.mp hx.2
    rcases h1 with ⟨k, hk⟩
    exact (A k).disj x hk x (h2 k) rfl

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

/-- Technical lemma used in the public import closure. -/
theorem measure1_eq_normL1 {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A) :
    hA.rep.normL1 = measure1 S hA :=
  IntegrableRep.normL1_eq_integral_of_nonneg hA.rep hA.repNonneg

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
def tendstoHalf_const_sub {u : Nat → R} {s : R} (c : R) (h : RSeq.TendstoHalf u s) :
    RSeq.TendstoHalf (fun n => c - u n) (c - s) where
  mod := h.mod
  close := fun k n hn => by
    have hc := h.close k n hn
    show COF.lt (COF.abs ((c - u n) - (c - s))) (COF.halfPow k)
    rw [show (c - u n) - (c - s) = -(u n - s) from by ring, COFO.abs_neg]
    exact hc

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

/-- Technical lemma used in the public import closure. -/
theorem seriesSum_binary_dichotomy {u : Nat → R} (hnn : ∀ n, Nonneg (u n)) (h : RSeq.SeriesSum u)
    (hbin : ∀ N, RSeq.partialSum u N = 0 ∨ RSeq.partialSum u N = 1) :
    (∃ M, RSeq.partialSum u M = 1) ∨ (∀ N, RSeq.partialSum u N = 0) := by
  rcases hbin (h.tends.mod 2) with h0 | h1
  · refine Or.inr (fun N => ?_)
    rcases hbin N with hN0 | hN1
    · exact hN0
    · exfalso
      have hle : Le (1 : R) h.sum := by rw [← hN1]; exact partialSum_le_sum hnn h N
      have hclose : COF.lt (COF.abs (RSeq.partialSum u (h.tends.mod 2) - h.sum)) (COF.halfPow 2) :=
        h.tends.close 2 (h.tends.mod 2) (Nat.le_refl _)
      rw [h0, show (0 : R) - h.sum = -h.sum from by ring, COFO.abs_neg] at hclose
      have hsum_lt : COF.lt h.sum 1 :=
        lt_of_le_of_lt (COFO.le_abs_self h.sum)
          (lt_of_lt_of_le hclose (by
            have hat := halfPow_antitone (R := R) (show 0 ≤ 2 by omega)
            rwa [show COF.halfPow (R := R) 0 = (1 : R) from rfl] at hat))
      exact hle hsum_lt
  · exact Or.inl ⟨h.tends.mod 2, h1⟩

/-- Technical lemma used in the public import closure. -/
theorem or_value_dichotomy {a b : R} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a + b - COF.min a b = 0 ∨ a + b - COF.min a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl (by rw [min_zero_right (le_refl (0 : R))]; ring)
  · exact Or.inr (by rw [min_zero_left (le_of_lt COFO.one_pos)]; ring)
  · exact Or.inr (by rw [min_zero_right (le_of_lt COFO.one_pos)]; ring)
  · exact Or.inr (by rw [min_self]; ring)

def bigOrFin (A : Nat → BSet X) : Nat → BSet X
| 0 => A 0
| n + 1 => BSet.or (bigOrFin A n) (A (n + 1))

noncomputable def phi_rep {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) : Nat → IntegrableRep S
| 0 => (hA 0).rep
| n + 1 =>
  let prev := phi_rep A hA n
  let cur := (hA (n + 1)).rep
  prev.add cur |>.sub (IntegrableRep.min2 prev cur)

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

noncomputable def bigOrFin_int {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) :
    ∀ n, IntegrableSet1 S (bigOrFin A n)
| 0 => hA 0
| n + 1 => IntegrableSet1_or (bigOrFin_int A hA n) (hA (n + 1))

/-- Technical lemma used in the public import closure. -/
theorem phi_rep_eq {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) :
    ∀ n, phi_rep A hA n = (bigOrFin_int A hA n).rep
  | 0 => rfl
  | n + 1 => by
      show ((phi_rep A hA n).add (hA (n + 1)).rep).sub (IntegrableRep.min2 (phi_rep A hA n) (hA (n + 1)).rep)
         = ((bigOrFin_int A hA n).rep.add (hA (n + 1)).rep).sub
             (IntegrableRep.min2 (bigOrFin_int A hA n).rep (hA (n + 1)).rep)
      rw [phi_rep_eq A hA n]

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_F {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) :
    Nat → IntegrableRep S
| 0 => (hA 0).rep
| n + 1 => (phi_rep A hA (n + 1)).sub (phi_rep A hA n)

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_F_nonneg {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) :
    ∀ m, RepNonneg (prop_2_10_F A hA m)
  | 0 => (hA 0).repNonneg
  | n + 1 => by
      intro x hdom habs hx
      -- F_{n+1}=phi_{n+1}.sub phi_n、phi_{n+1}=(phi_n.add c).sub(min2 phi_n c)、c=(hA(n+1)).rep
      let hphi1Dom : (phi_rep A hA (n + 1)).MemAt x := add_dom_left hdom
      let hnegPhinDom : (phi_rep A hA n).neg.MemAt x := add_dom_right hdom
      let hphinDom : (phi_rep A hA n).MemAt x := neg_dom hnegPhinDom
      let hpcDom : ((phi_rep A hA n).add (hA (n + 1)).rep).MemAt x :=
        add_dom_left hphi1Dom
      let hphinDom' : (phi_rep A hA n).MemAt x := add_dom_left hpcDom
      let hcDom : (hA (n + 1)).rep.MemAt x := add_dom_right hpcDom
      have hphi1_abs := add_absSeriesSum_left hdom habs
      have hpc_abs := add_absSeriesSum_left hphi1Dom hphi1_abs
      have hphin_abs := add_absSeriesSum_left hpcDom hpc_abs
      have hc_abs := add_absSeriesSum_right hpcDom hpc_abs
      have hphin := seriesSum_of_abs hphin_abs
      have hc := seriesSum_of_abs hc_abs
      obtain ⟨hmin, hmineq⟩ := min2_value (phi_rep A hA n) (hA (n + 1)).rep x
        hphinDom' hcDom hphin hc
      let hpc := add_seriesSum_value hphinDom' hcDom hphin hc
      let hminDom : ((phi_rep A hA n).min2 (hA (n + 1)).rep).MemAt x :=
        IntegrableRep.min2_memAt hphinDom' hcDom
      let hnegMinDom : ((phi_rep A hA n).min2 (hA (n + 1)).rep).neg.MemAt x :=
        IntegrableRep.neg_memAt hminDom
      let hnegMin := neg_seriesSum_value hminDom hmin
      let hphi1 := add_seriesSum_value hpcDom hnegMinDom hpc hnegMin
      let hnegPhin := neg_seriesSum_value hphinDom hphin
      let hF := add_seriesSum_value hphi1Dom hnegPhinDom hphi1 hnegPhin
      rw [seriesSum_unique hx hF]
      show Nonneg (hphi1.sum + (- hphin.sum))
      have e : hphi1.sum + (- hphin.sum) = hc.sum - hmin.sum := by
        show ((hphin.sum + hc.sum) + (- hmin.sum)) + (- hphin.sum) = hc.sum - hmin.sum
        ring
      rw [e, hmineq]
      exact nonneg_sub_of_le (cof_min_le_right hphin.sum hc.sum)

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_F_norm_sum {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) :
    RSeq.SeriesSum (fun m => (prop_2_10_F A hA m).normL1) :=
  { sum := h_lim.fst
    tends := by
      have h_eq : ∀ N, RSeq.partialSum (fun m => (prop_2_10_F A hA m).normL1) N = measure1 S (bigOrFin_int A hA N) := by
        intro N
        induction N with
        | zero =>
            -- partialSum 0 = (F_0).normL1 = (A_0).rep.normL1 = (A_0).rep.integral = measure1(bigOrFin 0)
            exact measure1_eq_normL1 (hA 0)
        | succ N ih =>
            -- partialSum(N+1) = partialSum N + (F_{N+1}).normL1
            --   = measure1(bigOrFin N) + (F_{N+1}).integral  [ih + normL1=integral(F_{N+1}≥0)]
            --   = measure1(bigOrFin N) + (measure1(bigOrFin(N+1)) − measure1(bigOrFin N))  [integral_sub + phi_rep_eq]
            --   = measure1(bigOrFin(N+1))
            show RSeq.partialSum (fun m => (prop_2_10_F A hA m).normL1) N
                  + (prop_2_10_F A hA (N + 1)).normL1
                = measure1 S (bigOrFin_int A hA (N + 1))
            rw [ih, IntegrableRep.normL1_eq_integral_of_nonneg (prop_2_10_F A hA (N + 1))
                  (prop_2_10_F_nonneg A hA (N + 1))]
            show measure1 S (bigOrFin_int A hA N)
                  + ((phi_rep A hA (N + 1)).sub (phi_rep A hA N)).integral
                = measure1 S (bigOrFin_int A hA (N + 1))
            rw [IntegrableRep.integral_sub, phi_rep_eq A hA (N + 1), phi_rep_eq A hA N]
            show measure1 S (bigOrFin_int A hA N)
                  + (measure1 S (bigOrFin_int A hA (N + 1)) - measure1 S (bigOrFin_int A hA N))
                = measure1 S (bigOrFin_int A hA (N + 1))
            ring
      have heq2 : (RSeq.partialSum (fun m => (prop_2_10_F A hA m).normL1))
                = (fun N => measure1 S (bigOrFin_int A hA N)) := funext h_eq
      rw [heq2]
      exact h_lim.snd }

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_rep {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) : IntegrableRep S :=
  seriesSumRep_L1 (prop_2_10_F A hA) (prop_2_10_F_norm_sum A hA h_lim)

/-- Domain transport from the finite-union representatives to their increments. -/
theorem prop_2_10_F_memAt {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k)) {x : X}
    (hphiDom : ∀ n, (phi_rep A hA n).MemAt x) :
    ∀ m, (prop_2_10_F A hA m).MemAt x
  | 0 => hphiDom 0
  | n + 1 => IntegrableRep.add_memAt (hphiDom (n + 1))
      (IntegrableRep.neg_memAt (hphiDom n))

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_Fvalue {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) {x : X}
    (hphiDom : ∀ n, (phi_rep A hA n).MemAt x)
    (hphiv : ∀ n, RSeq.SeriesSum (fun k => (phi_rep A hA n).valueAt x (hphiDom n) k)) :
    ∀ m, RSeq.SeriesSum (fun k => (prop_2_10_F A hA m).valueAt x
      (prop_2_10_F_memAt A hA hphiDom m) k)
  | 0 => hphiv 0
  | n + 1 => add_seriesSum_value (hphiDom (n + 1))
      (IntegrableRep.neg_memAt (hphiDom n)) (hphiv (n + 1))
      (neg_seriesSum_value (hphiDom n) (hphiv n))

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_F_partialSum_value {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    {x : X} (hphiDom : ∀ n, (phi_rep A hA n).MemAt x)
    (hphiv : ∀ n, RSeq.SeriesSum (fun k => (phi_rep A hA n).valueAt x (hphiDom n) k)) :
    ∀ N, RSeq.partialSum (fun m => (prop_2_10_Fvalue A hA hphiDom hphiv m).sum) N =
      (hphiv N).sum
  | 0 => rfl
  | n + 1 => by
      show RSeq.partialSum (fun m => (prop_2_10_Fvalue A hA hphiDom hphiv m).sum) n
            + (prop_2_10_Fvalue A hA hphiDom hphiv (n + 1)).sum = (hphiv (n + 1)).sum
      rw [prop_2_10_F_partialSum_value A hA hphiDom hphiv n]
      show (hphiv n).sum + ((hphiv (n + 1)).sum + (- (hphiv n).sum)) = (hphiv (n + 1)).sum
      ring

/-- Technical lemma used in the public import closure. -/
theorem bigOrFin_mem_domain (A : Nat → BSet X) {x : X}
    (hd : ∀ j, x ∈ (A j).S1 ∪ (A j).S2) :
    ∀ N, x ∈ (bigOrFin A N).S1 ∪ (bigOrFin A N).S2
  | 0 => hd 0
  | n + 1 => by
      have hP := bigOrFin_mem_domain A hd n
      rcases hP with hP1 | hP2 <;> rcases hd (n + 1) with hQ1 | hQ2
      · exact Or.inl (Or.inl (Or.inl ⟨hP1, hQ1⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hP1, hQ2⟩))
      · exact Or.inl (Or.inr ⟨hP2, hQ1⟩)
      · exact Or.inr ⟨hP2, hQ2⟩

/-- Technical lemma used in the public import closure. -/
theorem bigOrFin_mem_S1 (A : Nat → BSet X) {x : X}
    (hd : ∀ j, x ∈ (A j).S1 ∪ (A j).S2) :
    ∀ N k, k ≤ N → x ∈ (A k).S1 → x ∈ (bigOrFin A N).S1
  | 0, k, hk0, hxk => by
      have hk : k = 0 := Nat.le_zero.mp hk0
      subst hk; exact hxk
  | n + 1, k, hk, hxk => by
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · have hPn : x ∈ (bigOrFin A n).S1 := bigOrFin_mem_S1 A hd n k (Nat.lt_succ_iff.mp hlt) hxk
        rcases hd (n + 1) with hQ1 | hQ2
        · exact Or.inl (Or.inl ⟨hPn, hQ1⟩)
        · exact Or.inl (Or.inr ⟨hPn, hQ2⟩)
      · have hk' : k = n + 1 := Nat.le_antisymm hk hge
        subst hk'
        rcases bigOrFin_mem_domain A hd n with hP1 | hP2
        · exact Or.inl (Or.inl ⟨hP1, hxk⟩)
        · exact Or.inr ⟨hP2, hxk⟩

/-- Technical lemma used in the public import closure. -/
theorem bigOrFin_mem_S2 (A : Nat → BSet X) {x : X}
    (hd : ∀ j, x ∈ (A j).S2) :
    ∀ N, x ∈ (bigOrFin A N).S2
  | 0 => hd 0
  | n + 1 => ⟨bigOrFin_mem_S2 A hd n, hd (n + 1)⟩

/-- Technical lemma used in the public import closure. -/
theorem bigOrFin_S1_imp (A : Nat → BSet X) {x : X} :
    ∀ N, x ∈ (bigOrFin A N).S1 → ∃ k, k ≤ N ∧ x ∈ (A k).S1
  | 0, hx => ⟨0, Nat.le_refl 0, hx⟩
  | n + 1, hx => by
      rcases hx with (⟨hP1, _⟩ | ⟨hP1, _⟩) | ⟨_, hQ1⟩
      · obtain ⟨k, hk, hxk⟩ := bigOrFin_S1_imp A n hP1; exact ⟨k, Nat.le_succ_of_le hk, hxk⟩
      · obtain ⟨k, hk, hxk⟩ := bigOrFin_S1_imp A n hP1; exact ⟨k, Nat.le_succ_of_le hk, hxk⟩
      · exact ⟨n + 1, Nat.le_refl _, hQ1⟩

/-- Technical lemma used in the public import closure. -/
theorem bigOrFin_S2_imp (A : Nat → BSet X) {x : X} :
    ∀ N k, k ≤ N → x ∈ (bigOrFin A N).S2 → x ∈ (A k).S2
  | 0, k, hk, hx => by
      have : k = 0 := Nat.le_zero.mp hk
      subst this; exact hx
  | n + 1, k, hk, hx => by
      obtain ⟨hP2, hQ2⟩ := hx
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact bigOrFin_S2_imp A n k (Nat.lt_succ_iff.mp hlt) hP2
      · have : k = n + 1 := Nat.le_antisymm hk hge
        subst this; exact hQ2

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

/-- Technical lemma used in the public import closure. -/
def seriesSumRep_L1_integral {S : IntSpaceRC X R} (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1)) :
    { hI : RSeq.SeriesSum (fun m => (F m).integral) //
        (seriesSumRep_L1 F hsum).integral = hI.sum } := by
  obtain ⟨hIG, eG⟩ := seriesIntegrable_integral (G_m F) (G_m_absConv_seriesSum F hsum)
  obtain ⟨hIT, eT⟩ := seriesIntegrable_integral (tail_m F) (tail_m_absConv_seriesSum F)
  have hsplit : ∀ m, (G_m F m).integral + (tail_m F m).integral = (F m).integral := fun m => by
    show (IntegrableRep.ofL (psi_m_mem F m)).integral + ((F m).tailFrom (Nm F m)).integral = (F m).integral
    rw [IntegrableRep.ofL_integral, IntegrableRep.tailFrom_integral]
    show S.I (BFunR.seqSum (F m).fn (Nm F m))
          + ((F m).integral - S.I (BFunR.seqSum (F m).fn (Nm F m))) = (F m).integral
    ring
  refine ⟨seriesSum_congr (fun m => hsplit m) (seriesSum_add hIG hIT), ?_⟩
  show ((seriesIntegrable (G_m F) (G_m_absConv_seriesSum F hsum)).add
        (seriesIntegrable (tail_m F) (tail_m_absConv_seriesSum F))).integral = hIG.sum + hIT.sum
  rw [IntegrableRep.integral_add, eG, eT]

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
/-- Domain of an increment, recovered from the final flattened representative. -/
def prop_2_10_F_memAt_of_flat {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α)
    {x : X} (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x) (m : Nat) :
    (prop_2_10_F A hA m).MemAt x :=
  seriesSumRep_L1_F_memAt (prop_2_10_F A hA)
    (prop_2_10_F_norm_sum A hA h_lim) hflatDom m

/-- Domain of a finite-union representative, recovered from an increment domain. -/
def prop_2_10_phi_memAt_of_flat {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α)
    {x : X} (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x) :
    ∀ N, (phi_rep A hA N).MemAt x
  | 0 => prop_2_10_F_memAt_of_flat A hA h_lim hflatDom 0
  | n + 1 => add_dom_left
      (prop_2_10_F_memAt_of_flat A hA h_lim hflatDom (n + 1))

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_F_absConv_of_flatabs {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) {x : X}
    (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_rep A hA h_lim).valueAt x hflatDom n))) (m : Nat) :
    RSeq.SeriesSum (fun k => COF.abs ((prop_2_10_F A hA m).valueAt x
      (prop_2_10_F_memAt_of_flat A hA h_lim hflatDom m) k)) := by
  have hflat :
      RSeq.SeriesSum (fun n => COF.abs ((seriesSumRep_L1 (prop_2_10_F A hA)
        (prop_2_10_F_norm_sum A hA h_lim)).valueAt x hflatDom n)) := hflatabs
  let htailFlatDom := seriesSumRep_L1_tailFlat_memAt (prop_2_10_F A hA)
    (prop_2_10_F_norm_sum A hA h_lim) hflatDom
  have htail_flat :
      RSeq.SeriesSum (fun n => COF.abs ((seriesIntegrable (tail_m (prop_2_10_F A hA))
        (tail_m_absConv_seriesSum (prop_2_10_F A hA))).valueAt x htailFlatDom n)) :=
    add_absSeriesSum_right hflatDom hflat
  let htailRowDom := seriesSumRep_L1_tailRow_memAt (prop_2_10_F A hA)
    (prop_2_10_F_norm_sum A hA h_lim) hflatDom m
  have htail_m :
      RSeq.SeriesSum (fun j => COF.abs ((tail_m (prop_2_10_F A hA) m).valueAt x
        htailRowDom j)) :=
    row_seriesSum (fun i j => abs_nonneg ((tail_m (prop_2_10_F A hA) i).valueAt x
      (seriesSumRep_L1_tailRow_memAt (prop_2_10_F A hA)
        (prop_2_10_F_norm_sum A hA h_lim) hflatDom i) j)) htail_flat m
  exact seriesSum_of_tail (Nm (prop_2_10_F A hA) m) htail_m

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_phi_absConv_of_flatabs {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) {x : X}
    (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_rep A hA h_lim).valueAt x hflatDom n))) (N : Nat) :
    RSeq.SeriesSum (fun k => COF.abs ((phi_rep A hA N).valueAt x
      (prop_2_10_phi_memAt_of_flat A hA h_lim hflatDom N) k)) := by
  have hF := prop_2_10_F_absConv_of_flatabs A hA h_lim hflatDom hflatabs
  cases N with
  | zero => exact hF 0
  | succ n =>
      exact add_absSeriesSum_left
        (r := phi_rep A hA (n + 1)) (r' := (phi_rep A hA n).neg)
        (prop_2_10_F_memAt_of_flat A hA h_lim hflatDom (n + 1)) (hF (n + 1))

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_rep_value_series {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) {x : X}
    (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_rep A hA h_lim).valueAt x hflatDom n)))
    (hphiv : ∀ n, RSeq.SeriesSum (fun k => (phi_rep A hA n).valueAt x
      (prop_2_10_phi_memAt_of_flat A hA h_lim hflatDom n) k)) :
    { hser : RSeq.SeriesSum (fun m => (prop_2_10_Fvalue A hA
        (prop_2_10_phi_memAt_of_flat A hA h_lim hflatDom) hphiv m).sum) //
        (seriesSum_of_abs hflatabs).sum = hser.sum } := by
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_value (prop_2_10_F A hA)
    (prop_2_10_F_norm_sum A hA h_lim) hflatDom hflatabs
  refine ⟨seriesSum_congr (fun m => ?_) hV, eV⟩
  let hFDom : (prop_2_10_F A hA m).MemAt x :=
    prop_2_10_F_memAt_of_flat A hA h_lim hflatDom m
  let hPsiDom : x ∈ (psi_m (prop_2_10_F A hA) m).dom :=
    BFunR.seqSum_mem (prop_2_10_F A hA m).fn x hFDom
      (Nm (prop_2_10_F A hA) m)
  let hFv := prop_2_10_Fvalue A hA
    (prop_2_10_phi_memAt_of_flat A hA h_lim hflatDom) hphiv m
  rw [show (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
              ((G_m (prop_2_10_F A hA) i).valueAt x
                (seriesSumRep_L1_Grow_memAt (prop_2_10_F A hA)
                  (prop_2_10_F_norm_sum A hA h_lim) hflatDom i) j))
            (add_absSeriesSum_left hflatDom hflatabs) m)).sum
          = (IntegrableRep.ofL_value (psi_m_mem (prop_2_10_F A hA) m) x hPsiDom).val.sum from
          seriesSum_unique _ _,
      show (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
              ((tail_m (prop_2_10_F A hA) i).valueAt x
                (seriesSumRep_L1_tailRow_memAt (prop_2_10_F A hA)
                  (prop_2_10_F_norm_sum A hA h_lim) hflatDom i) j))
            (add_absSeriesSum_right hflatDom hflatabs) m)).sum
          = (IntegrableRep.tailFrom_value (prop_2_10_F A hA m) (Nm (prop_2_10_F A hA) m) x
              hFDom hFv).val.sum from
          seriesSum_unique _ _]
  exact seriesSumRep_L1_hsplit_value (prop_2_10_F A hA) m hFDom hFv

/-- 0 ≠ 1。 -/
theorem zero_ne_one_R {R : Type*} [COFOC R] : (0:R) ≠ 1 := by
  intro h; have hp : COF.lt (0:R) 1 := COFO.one_pos; rw [← h] at hp; exact COF.lt_irrefl 0 hp

/-- Technical lemma used in the public import closure. -/
def absSeriesSum_rep_congr {S : IntSpaceRC X R} {r r' : IntegrableRep S} {x : X} (heq : r = r')
    (hrdom : r.MemAt x) (hr'dom : r'.MemAt x)
    (h : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hrdom n))) :
    RSeq.SeriesSum (fun n => COF.abs (r'.valueAt x hr'dom n)) := by
  cases heq
  exact h

/-- Technical lemma used in the public import closure. -/
theorem seriesSum_sum_rep_congr {S : IntSpaceRC X R} {r r' : IntegrableRep S} {x : X} (heq : r = r')
    (hrdom : r.MemAt x) (hr'dom : r'.MemAt x)
    (h : RSeq.SeriesSum (fun n => r.valueAt x hrdom n))
    (h' : RSeq.SeriesSum (fun n => r'.valueAt x hr'dom n)) :
    h.sum = h'.sum := by cases heq; exact seriesSum_unique h h'

/-- Technical lemma used in the public import closure. -/
theorem bigOrFin_domain_imp {X : Type*} (A : Nat → BSet X) {x : X} :
    ∀ N k, k ≤ N → x ∈ (bigOrFin A N).S1 ∪ (bigOrFin A N).S2 → x ∈ (A k).S1 ∪ (A k).S2
  | 0, k, hk, hx => by have : k = 0 := Nat.le_zero.mp hk; subst this; exact hx
  | n + 1, k, hk, hx => by
      have hPQ : x ∈ (bigOrFin A n).S1 ∪ (bigOrFin A n).S2 ∧ x ∈ (A (n + 1)).S1 ∪ (A (n + 1)).S2 := by
        rcases hx with (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)) | ⟨h1, h2⟩
        · exact ⟨Or.inl h1, Or.inl h2⟩
        · exact ⟨Or.inl h1, Or.inr h2⟩
        · exact ⟨Or.inr h1, Or.inl h2⟩
        · exact ⟨Or.inr h1, Or.inr h2⟩
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact bigOrFin_domain_imp A n k (Nat.lt_succ_iff.mp hlt) hPQ.1
      · have : k = n + 1 := Nat.le_antisymm hk hge; subst this; exact hPQ.2

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_phi_value {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) (N : Nat) {x : X}
    (hphiDom : (phi_rep A hA N).MemAt x)
    (hphiabs_N : RSeq.SeriesSum (fun k => COF.abs
      ((phi_rep A hA N).valueAt x hphiDom k)))
    (hphiv_N : RSeq.SeriesSum (fun k => (phi_rep A hA N).valueAt x hphiDom k)) :
    (x ∈ (bigOrFin A N).S1 ∪ (bigOrFin A N).S2)
    ∧ (x ∈ (bigOrFin A N).S1 → hphiv_N.sum = 1)
    ∧ (x ∈ (bigOrFin A N).S2 → hphiv_N.sum = 0) := by
  let hbofDom : (bigOrFin_int A hA N).rep.MemAt x := by
    rw [← phi_rep_eq A hA N]
    exact hphiDom
  have hbofAbs : RSeq.SeriesSum (fun n => COF.abs
      ((bigOrFin_int A hA N).rep.valueAt x hbofDom n)) :=
    absSeriesSum_rep_congr (phi_rep_eq A hA N) hphiDom hbofDom hphiabs_N
  have hval := (bigOrFin_int A hA N).valid x hbofDom hbofAbs
  have hbofV : RSeq.SeriesSum (fun n =>
      (bigOrFin_int A hA N).rep.valueAt x hbofDom n) := seriesSum_of_abs hbofAbs
  refine ⟨hval.1, fun hx1 => ?_, fun hx2 => ?_⟩
  · rw [seriesSum_sum_rep_congr (phi_rep_eq A hA N) hphiDom hbofDom hphiv_N hbofV]
    exact hval.2.1 hx1 hbofV
  · rw [seriesSum_sum_rep_congr (phi_rep_eq A hA N) hphiDom hbofDom hphiv_N hbofV]
    exact hval.2.2 hx2 hbofV

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_a_mem {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) {x : X}
    (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_rep A hA h_lim).valueAt x hflatDom n))) :
    x ∈ (BSet.bigOr A).S1 ∪ (BSet.bigOr A).S2 := by
  let hphiDom := prop_2_10_phi_memAt_of_flat A hA h_lim hflatDom
  have hFabs := prop_2_10_F_absConv_of_flatabs A hA h_lim hflatDom habs
  have hphiabs := prop_2_10_phi_absConv_of_flatabs A hA h_lim hflatDom habs
  have hphiv : ∀ N, RSeq.SeriesSum (fun k =>
      (phi_rep A hA N).valueAt x (hphiDom N) k) :=
    fun N => seriesSum_of_abs (hphiabs N)
  obtain ⟨hser, _⟩ := prop_2_10_rep_value_series A hA h_lim hflatDom habs hphiv
  have hphival := fun N => prop_2_10_phi_value A hA N (hphiDom N) (hphiabs N) (hphiv N)
  have hpartial : ∀ N, RSeq.partialSum
      (fun m => (prop_2_10_Fvalue A hA hphiDom hphiv m).sum) N = (hphiv N).sum :=
    prop_2_10_F_partialSum_value A hA hphiDom hphiv
  have hnn : ∀ m, Nonneg ((prop_2_10_Fvalue A hA hphiDom hphiv m).sum) := fun m =>
    prop_2_10_F_nonneg A hA m x (prop_2_10_F_memAt A hA hphiDom m)
      (hFabs m) (prop_2_10_Fvalue A hA hphiDom hphiv m)
  have hbin : ∀ N, RSeq.partialSum
      (fun m => (prop_2_10_Fvalue A hA hphiDom hphiv m).sum) N = 0
      ∨ RSeq.partialSum (fun m => (prop_2_10_Fvalue A hA hphiDom hphiv m).sum) N = 1 := fun N => by
    rw [hpartial N]
    rcases (hphival N).1 with hx1 | hx2
    · exact Or.inr ((hphival N).2.1 hx1)
    · exact Or.inl ((hphival N).2.2 hx2)
  rcases seriesSum_binary_dichotomy hnn hser hbin with ⟨M, hM⟩ | hAll
  · rw [hpartial M] at hM
    have hxM1 : x ∈ (bigOrFin A M).S1 := by
      rcases (hphival M).1 with hx1 | hx2
      · exact hx1
      · exact absurd (((hphival M).2.2 hx2).symm.trans hM) zero_ne_one_R
    obtain ⟨k, _, hxk⟩ := bigOrFin_S1_imp A M hxM1
    have hdom : ∀ j, x ∈ (A j).S1 ∪ (A j).S2 := fun j =>
      bigOrFin_domain_imp A j j (Nat.le_refl j) (hphival j).1
    exact Or.inl ⟨Set.mem_iInter.mpr hdom, Set.mem_iUnion.mpr ⟨k, hxk⟩⟩
  · have hxS2 : ∀ j, x ∈ (A j).S2 := fun j => by
      have hj0 : (hphiv j).sum = 0 := by rw [← hpartial j]; exact hAll j
      have hxjS2 : x ∈ (bigOrFin A j).S2 := by
        rcases (hphival j).1 with hx1 | hx2
        · exact absurd (((hphival j).2.1 hx1).symm.trans hj0) zero_ne_one_R.symm
        · exact hx2
      exact bigOrFin_S2_imp A j j (Nat.le_refl j) hxjS2
    exact Or.inr (Set.mem_iInter.mpr hxS2)

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_a_val1 {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) {x : X}
    (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_rep A hA h_lim).valueAt x hflatDom n)))
    (hxS1 : x ∈ (BSet.bigOr A).S1)
    (h : RSeq.SeriesSum (fun n =>
      (prop_2_10_rep A hA h_lim).valueAt x hflatDom n)) :
    h.sum = 1 := by
  obtain ⟨hInter, hUnion⟩ := hxS1
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hUnion
  have hdom : ∀ j, x ∈ (A j).S1 ∪ (A j).S2 := fun j => Set.mem_iInter.mp hInter j
  let hphiDom := prop_2_10_phi_memAt_of_flat A hA h_lim hflatDom
  have hphiabs := prop_2_10_phi_absConv_of_flatabs A hA h_lim hflatDom habs
  have hphiv : ∀ N, RSeq.SeriesSum (fun k =>
      (phi_rep A hA N).valueAt x (hphiDom N) k) := fun N => seriesSum_of_abs (hphiabs N)
  obtain ⟨hser, eser⟩ := prop_2_10_rep_value_series A hA h_lim hflatDom habs hphiv
  have hphival := fun N => prop_2_10_phi_value A hA N (hphiDom N) (hphiabs N) (hphiv N)
  have hpartial := prop_2_10_F_partialSum_value A hA hphiDom hphiv
  have hev : ∀ N, k ≤ N → RSeq.partialSum
      (fun m => (prop_2_10_Fvalue A hA hphiDom hphiv m).sum) N = 1 := fun N hN => by
    rw [hpartial N]; exact (hphival N).2.1 (bigOrFin_mem_S1 A hdom N k hN hxk)
  rw [seriesSum_unique h (seriesSum_of_abs habs), eser]
  exact seriesSum_of_eventually_const hser k hev

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_a_val0 {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) {x : X}
    (hflatDom : (prop_2_10_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_rep A hA h_lim).valueAt x hflatDom n)))
    (hxS2 : x ∈ (BSet.bigOr A).S2)
    (h : RSeq.SeriesSum (fun n =>
      (prop_2_10_rep A hA h_lim).valueAt x hflatDom n)) :
    h.sum = 0 := by
  have hS2 : ∀ j, x ∈ (A j).S2 := fun j => Set.mem_iInter.mp hxS2 j
  let hphiDom := prop_2_10_phi_memAt_of_flat A hA h_lim hflatDom
  have hphiabs := prop_2_10_phi_absConv_of_flatabs A hA h_lim hflatDom habs
  have hphiv : ∀ N, RSeq.SeriesSum (fun k =>
      (phi_rep A hA N).valueAt x (hphiDom N) k) := fun N => seriesSum_of_abs (hphiabs N)
  obtain ⟨hser, eser⟩ := prop_2_10_rep_value_series A hA h_lim hflatDom habs hphiv
  have hphival := fun N => prop_2_10_phi_value A hA N (hphiDom N) (hphiabs N) (hphiv N)
  have hpartial := prop_2_10_F_partialSum_value A hA hphiDom hphiv
  have hev : ∀ N, 0 ≤ N → RSeq.partialSum
      (fun m => (prop_2_10_Fvalue A hA hphiDom hphiv m).sum) N = 0 := fun N _ => by
    rw [hpartial N]; exact (hphival N).2.2 (bigOrFin_mem_S2 A hS2 N)
  rw [seriesSum_unique h (seriesSum_of_abs habs), eser]
  exact seriesSum_of_eventually_const hser 0 hev

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_a {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) :
    IntegrableSet1 S (BSet.bigOr A) where
  full := ⟨fun _ => prop_2_10_rep A hA h_lim, fun x hx => by
    obtain ⟨hdom, ⟨habs⟩⟩ := hx 0
    exact prop_2_10_a_mem A hA h_lim hdom habs⟩
  rep := prop_2_10_rep A hA h_lim
  valid := by
    intro x hdom habs
    exact ⟨prop_2_10_a_mem A hA h_lim hdom habs,
      fun hxS1 h => prop_2_10_a_val1 A hA h_lim hdom habs hxS1 h,
      fun hxS2 h => prop_2_10_a_val0 A hA h_lim hdom habs hxS2 h⟩

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


theorem prop_2_10_a_measure {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α) :
    measure1 S (prop_2_10_a A hA h_lim) = h_lim.fst := by
  obtain ⟨hI, e⟩ := seriesSumRep_L1_integral (prop_2_10_F A hA) (prop_2_10_F_norm_sum A hA h_lim)
  show (seriesSumRep_L1 (prop_2_10_F A hA) (prop_2_10_F_norm_sum A hA h_lim)).integral = h_lim.fst
  rw [e]
  have heq : hI.sum = (prop_2_10_F_norm_sum A hA h_lim).sum :=
    seriesSum_unique hI
      (seriesSum_congr (fun m => IntegrableRep.normL1_eq_integral_of_nonneg
          (prop_2_10_F A hA m) (prop_2_10_F_nonneg A hA m))
        (prop_2_10_F_norm_sum A hA h_lim))
  rw [heq]
  rfl

def bigAndFin (A : Nat → BSet X) : Nat → BSet X
| 0 => A 0
| n + 1 => BSet.and (bigAndFin A n) (A (n + 1))

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
theorem measure1_nonneg {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A) :
    Nonneg (measure1 S hA) := by
  rw [← measure1_eq_normL1 hA]
  exact hA.rep.normL1_nonneg

/-- Technical lemma used in the public import closure. -/
theorem IntegrableSet1_or_measure {S : IntSpaceRC X R} {A B : BSet X}
    (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B) :
    measure1 S (IntegrableSet1_or hA hB) + measure1 S (IntegrableSet1_and hA hB)
      = measure1 S hA + measure1 S hB := by
  show ((hA.rep.add hB.rep).sub (IntegrableRep.min2 hA.rep hB.rep)).integral
      + (IntegrableRep.min2 hA.rep hB.rep).integral
      = hA.rep.integral + hB.rep.integral
  rw [IntegrableRep.integral_sub, IntegrableRep.integral_add]
  ring

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_partialSum_eq_measure {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k)) :
    ∀ N, RSeq.partialSum (fun m => (prop_2_10_F A hA m).normL1) N = measure1 S (bigOrFin_int A hA N)
  | 0 => measure1_eq_normL1 (hA 0)
  | N + 1 => by
      show RSeq.partialSum (fun m => (prop_2_10_F A hA m).normL1) N
            + (prop_2_10_F A hA (N + 1)).normL1
          = measure1 S (bigOrFin_int A hA (N + 1))
      rw [prop_2_10_partialSum_eq_measure A hA N,
          IntegrableRep.normL1_eq_integral_of_nonneg (prop_2_10_F A hA (N + 1))
            (prop_2_10_F_nonneg A hA (N + 1))]
      show measure1 S (bigOrFin_int A hA N)
            + ((phi_rep A hA (N + 1)).sub (phi_rep A hA N)).integral
          = measure1 S (bigOrFin_int A hA (N + 1))
      rw [IntegrableRep.integral_sub, phi_rep_eq A hA (N + 1), phi_rep_eq A hA N]
      show measure1 S (bigOrFin_int A hA N)
            + (measure1 S (bigOrFin_int A hA (N + 1)) - measure1 S (bigOrFin_int A hA N))
          = measure1 S (bigOrFin_int A hA (N + 1))
      ring

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_F_normL1_le {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k)) :
    ∀ m, Le ((prop_2_10_F A hA m).normL1) (measure1 S (hA m))
  | 0 => by
      rw [show (prop_2_10_F A hA 0) = (hA 0).rep from rfl, measure1_eq_normL1 (hA 0)]
      exact le_refl _
  | n + 1 => by
      rw [IntegrableRep.normL1_eq_integral_of_nonneg (prop_2_10_F A hA (n + 1))
            (prop_2_10_F_nonneg A hA (n + 1))]
      show Le (((phi_rep A hA (n + 1)).sub (phi_rep A hA n)).integral) (measure1 S (hA (n + 1)))
      rw [IntegrableRep.integral_sub, phi_rep_eq A hA (n + 1), phi_rep_eq A hA n]
      show Le (measure1 S (bigOrFin_int A hA (n + 1)) - measure1 S (bigOrFin_int A hA n))
              (measure1 S (hA (n + 1)))
      have hom : measure1 S (bigOrFin_int A hA (n + 1))
                  + measure1 S (IntegrableSet1_and (bigOrFin_int A hA n) (hA (n + 1)))
               = measure1 S (bigOrFin_int A hA n) + measure1 S (hA (n + 1)) :=
        IntegrableSet1_or_measure (bigOrFin_int A hA n) (hA (n + 1))
      apply le_of_nonneg_sub
      rw [show measure1 S (hA (n + 1))
              - (measure1 S (bigOrFin_int A hA (n + 1)) - measure1 S (bigOrFin_int A hA n))
            = (measure1 S (bigOrFin_int A hA n) + measure1 S (hA (n + 1)))
              - measure1 S (bigOrFin_int A hA (n + 1)) from by ring, ← hom,
          show measure1 S (bigOrFin_int A hA (n + 1))
                + measure1 S (IntegrableSet1_and (bigOrFin_int A hA n) (hA (n + 1)))
                - measure1 S (bigOrFin_int A hA (n + 1))
              = measure1 S (IntegrableSet1_and (bigOrFin_int A hA n) (hA (n + 1))) from by ring]
      exact measure1_nonneg _

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_measure_ccond {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k)) (h_conv : RSeq.SeriesSum (fun k => measure1 S (hA k))) :
    ∀ k m n : Nat, (isCauchy_of_tendsto h_conv.tends).cmod k ≤ m
      → (isCauchy_of_tendsto h_conv.tends).cmod k ≤ n
      → COF.lt (COF.abs (measure1 S (bigOrFin_int A hA m) - measure1 S (bigOrFin_int A hA n)))
               (COF.halfPow k) := by
  intro k m n hm hn
  rw [← prop_2_10_partialSum_eq_measure A hA m, ← prop_2_10_partialSum_eq_measure A hA n]
  exact lt_of_le_of_lt
    (partialSum_absdiff_le (fun j => (prop_2_10_F A hA j).normL1_nonneg)
      (fun j => prop_2_10_F_normL1_le A hA j) m n)
    ((isCauchy_of_tendsto h_conv.tends).ccond k m n hm hn)

/-- Technical lemma used in the public import closure. -/
noncomputable def measure_limit_of_sum {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (hA k))) :
    Σ α : R, RSeq.TendstoHalf (fun n => measure1 S (bigOrFin_int A hA n)) α :=
  let hc : IsCauchy (fun n => measure1 S (bigOrFin_int A hA n)) := {
    cmod := fun k => (isCauchy_of_tendsto h_conv.tends).cmod k
    ccond := prop_2_10_measure_ccond A hA h_conv
  }
  let lim := COFOC.complete hc
  ⟨lim.val, lim.tends⟩

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_b {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (hA k))) :
    IntegrableSet1 S (BSet.bigOr A) :=
  prop_2_10_a A hA (measure_limit_of_sum A hA h_conv)

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_b_measure {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (hA k))) :
    Le (measure1 S (prop_2_10_b A hA h_conv)) h_conv.sum := by
  let hFsum := seriesSum_comparison (fun m => (prop_2_10_F A hA m).normL1_nonneg)
    (fun m => prop_2_10_F_normL1_le A hA m) h_conv
  have hαeq : (measure_limit_of_sum A hA h_conv).fst = hFsum.sum := by
    refine tendstoHalf_unique (measure_limit_of_sum A hA h_conv).snd ?_
    rw [show (fun n => measure1 S (bigOrFin_int A hA n))
          = (fun n => RSeq.partialSum (fun m => (prop_2_10_F A hA m).normL1) n) from
        funext (fun n => (prop_2_10_partialSum_eq_measure A hA n).symm)]
    exact hFsum.tends
  rw [show measure1 S (prop_2_10_b A hA h_conv) = (measure_limit_of_sum A hA h_conv).fst from
        prop_2_10_a_measure A hA (measure_limit_of_sum A hA h_conv), hαeq]
  exact seriesSum_comparison_le _ _ _

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

/-- Technical lemma used in the public import closure. -/
theorem IntegrableSet1_sub_measure {S : IntSpaceRC X R} {A B : BSet X}
    (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B) :
    measure1 S (IntegrableSet1_sub hA hB)
      = measure1 S hA - measure1 S (IntegrableSet1_and hA hB) := by
  show (hA.rep.sub (IntegrableRep.min2 hA.rep hB.rep)).integral
      = hA.rep.integral - (IntegrableRep.min2 hA.rep hB.rep).integral
  rw [IntegrableRep.integral_sub]

noncomputable def bigAndFin_int {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) :
    ∀ n, IntegrableSet1 S (bigAndFin A n)
| 0 => hA 0
| n + 1 => IntegrableSet1_and (bigAndFin_int A hA n) (hA (n + 1))

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_G {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) :
    Nat → IntegrableRep S
| 0 => (hA 0).rep.sub (hA 0).rep
| n + 1 => (bigAndFin_int A hA n).rep.sub (bigAndFin_int A hA (n + 1)).rep

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_G_nonneg {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) :
    ∀ m, RepNonneg (prop_2_10_G A hA m)
  | 0 => by
      intro x hdom habs hx
      let hrDom : (hA 0).rep.MemAt x := add_dom_left hdom
      let hnegRDom : (hA 0).rep.neg.MemAt x := add_dom_right hdom
      let hr2Dom : (hA 0).rep.MemAt x := neg_dom hnegRDom
      have hr_abs := add_absSeriesSum_left hdom habs
      have hr2_abs := neg_absSeriesSum hnegRDom
        (add_absSeriesSum_right hdom habs)
      have hr := seriesSum_of_abs hr_abs
      have hr2 := seriesSum_of_abs hr2_abs
      let hG := add_seriesSum_value hrDom hnegRDom hr
        (neg_seriesSum_value hr2Dom hr2)
      rw [seriesSum_unique hx hG]
      show Nonneg (hr.sum + (- hr2.sum))
      rw [seriesSum_unique hr hr2, show hr2.sum + (- hr2.sum) = 0 from by ring]
      exact le_refl 0
  | n + 1 => by
      intro x hdom habs hx
      let hrcDom : (bigAndFin_int A hA n).rep.MemAt x := add_dom_left hdom
      let hnegNextDom : (bigAndFin_int A hA (n + 1)).rep.neg.MemAt x :=
        add_dom_right hdom
      let hnextDom : (bigAndFin_int A hA (n + 1)).rep.MemAt x :=
        neg_dom hnegNextDom
      let hraDom : (hA (n + 1)).rep.MemAt x := min2_dom_right hnextDom
      have hrc_abs := add_absSeriesSum_left hdom habs
      have hmin_abs := neg_absSeriesSum hnegNextDom
        (add_absSeriesSum_right hdom habs)
      have hra_abs := min2_absSeriesSum_right hnextDom hmin_abs
      have hrc := seriesSum_of_abs hrc_abs
      have hra := seriesSum_of_abs hra_abs
      obtain ⟨hm, hmeq⟩ := min2_value (bigAndFin_int A hA n).rep
        (hA (n + 1)).rep x hrcDom hraDom hrc hra
      let hminDom' : ((bigAndFin_int A hA n).rep.min2 (hA (n + 1)).rep).MemAt x :=
        IntegrableRep.min2_memAt hrcDom hraDom
      let hnegMinDom' : ((bigAndFin_int A hA n).rep.min2
          (hA (n + 1)).rep).neg.MemAt x := IntegrableRep.neg_memAt hminDom'
      let hG := add_seriesSum_value hrcDom hnegMinDom' hrc
        (neg_seriesSum_value hminDom' hm)
      rw [seriesSum_unique hx hG]
      show Nonneg (hrc.sum + (- hm.sum))
      have e : hrc.sum + (- hm.sum) = hrc.sum - hm.sum := by ring
      rw [e, hmeq]
      exact nonneg_sub_of_le (cof_min_le_left hrc.sum hra.sum)

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_G_norm_sum {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) :
    RSeq.SeriesSum (fun m => (prop_2_10_G A hA m).normL1) :=
  { sum := measure1 S (hA 0) - h_lim.fst
    tends := by
      have h_eq : ∀ N, RSeq.partialSum (fun m => (prop_2_10_G A hA m).normL1) N
            = measure1 S (hA 0) - measure1 S (bigAndFin_int A hA N) := by
        intro N
        induction N with
        | zero =>
            show (prop_2_10_G A hA 0).normL1 = measure1 S (hA 0) - measure1 S (bigAndFin_int A hA 0)
            rw [IntegrableRep.normL1_eq_integral_of_nonneg (prop_2_10_G A hA 0)
                  (prop_2_10_G_nonneg A hA 0)]
            show ((hA 0).rep.sub (hA 0).rep).integral = (hA 0).rep.integral - (hA 0).rep.integral
            rw [IntegrableRep.integral_sub]
        | succ N ih =>
            show RSeq.partialSum (fun m => (prop_2_10_G A hA m).normL1) N
                  + (prop_2_10_G A hA (N + 1)).normL1
                = measure1 S (hA 0) - measure1 S (bigAndFin_int A hA (N + 1))
            rw [ih, IntegrableRep.normL1_eq_integral_of_nonneg (prop_2_10_G A hA (N + 1))
                  (prop_2_10_G_nonneg A hA (N + 1))]
            show (measure1 S (hA 0) - measure1 S (bigAndFin_int A hA N))
                  + ((bigAndFin_int A hA N).rep.sub (bigAndFin_int A hA (N + 1)).rep).integral
                = measure1 S (hA 0) - measure1 S (bigAndFin_int A hA (N + 1))
            rw [IntegrableRep.integral_sub]
            show (measure1 S (hA 0) - measure1 S (bigAndFin_int A hA N))
                  + (measure1 S (bigAndFin_int A hA N) - measure1 S (bigAndFin_int A hA (N + 1)))
                = measure1 S (hA 0) - measure1 S (bigAndFin_int A hA (N + 1))
            ring
      have heq2 : (RSeq.partialSum (fun m => (prop_2_10_G A hA m).normL1))
                = (fun N => measure1 S (hA 0) - measure1 S (bigAndFin_int A hA N)) := funext h_eq
      rw [heq2]
      exact tendstoHalf_const_sub (measure1 S (hA 0)) h_lim.snd }

noncomputable def prop_2_10_c_rep {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) : IntegrableRep S :=
  (hA 0).rep.sub (seriesSumRep_L1 (prop_2_10_G A hA) (prop_2_10_G_norm_sum A hA h_lim))

/-- Domain transport from the decreasing finite intersections to their drops. -/
theorem prop_2_10_G_memAt {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k)) {x : X}
    (hpsiDom : ∀ n, (bigAndFin_int A hA n).rep.MemAt x) :
    ∀ m, (prop_2_10_G A hA m).MemAt x
  | 0 => IntegrableRep.add_memAt (hpsiDom 0)
      (IntegrableRep.neg_memAt (hpsiDom 0))
  | n + 1 => IntegrableRep.add_memAt (hpsiDom n)
      (IntegrableRep.neg_memAt (hpsiDom (n + 1)))

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_Gvalue {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) {x : X}
    (hpsiDom : ∀ n, (bigAndFin_int A hA n).rep.MemAt x)
    (hpsiv : ∀ n, RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA n).rep.valueAt x (hpsiDom n) k)) :
    ∀ m, RSeq.SeriesSum (fun k => (prop_2_10_G A hA m).valueAt x
      (prop_2_10_G_memAt A hA hpsiDom m) k)
  | 0 => add_seriesSum_value (hpsiDom 0) (IntegrableRep.neg_memAt (hpsiDom 0))
      (hpsiv 0) (neg_seriesSum_value (hpsiDom 0) (hpsiv 0))
  | n + 1 => add_seriesSum_value (hpsiDom n)
      (IntegrableRep.neg_memAt (hpsiDom (n + 1))) (hpsiv n)
      (neg_seriesSum_value (hpsiDom (n + 1)) (hpsiv (n + 1)))

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_G_partialSum_value {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    {x : X} (hpsiDom : ∀ n, (bigAndFin_int A hA n).rep.MemAt x)
    (hpsiv : ∀ n, RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA n).rep.valueAt x (hpsiDom n) k)) :
    ∀ N, RSeq.partialSum (fun m => (prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) N =
      (hpsiv 0).sum - (hpsiv N).sum
  | 0 => by
      show (prop_2_10_Gvalue A hA hpsiDom hpsiv 0).sum = (hpsiv 0).sum - (hpsiv 0).sum
      show (hpsiv 0).sum + (- (hpsiv 0).sum) = (hpsiv 0).sum - (hpsiv 0).sum
      ring
  | n + 1 => by
      show RSeq.partialSum (fun m => (prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) n
            + (prop_2_10_Gvalue A hA hpsiDom hpsiv (n + 1)).sum =
              (hpsiv 0).sum - (hpsiv (n + 1)).sum
      rw [prop_2_10_G_partialSum_value A hA hpsiDom hpsiv n]
      show ((hpsiv 0).sum - (hpsiv n).sum) + ((hpsiv n).sum + (- (hpsiv (n + 1)).sum))
            = (hpsiv 0).sum - (hpsiv (n + 1)).sum
      ring

/-- Domain of the summed drop representative inside the final intersection witness. -/
def prop_2_10_c_R_memAt {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β)
    {x : X} (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x) :
    (seriesSumRep_L1 (prop_2_10_G A hA)
      (prop_2_10_G_norm_sum A hA h_lim)).MemAt x :=
  neg_dom (add_dom_right hcDom)

/-- Domain of a drop row recovered from the final intersection witness. -/
def prop_2_10_G_memAt_of_c {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β)
    {x : X} (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x) (m : Nat) :
    (prop_2_10_G A hA m).MemAt x :=
  seriesSumRep_L1_F_memAt (prop_2_10_G A hA)
    (prop_2_10_G_norm_sum A hA h_lim)
    (prop_2_10_c_R_memAt A hA h_lim hcDom) m

/-- Domain of every decreasing finite-intersection representative. -/
def prop_2_10_psi_memAt_of_c {S : IntSpaceRC X R} (A : Nat → BSet X)
    (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β)
    {x : X} (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x) :
    ∀ N, (bigAndFin_int A hA N).rep.MemAt x
  | 0 => add_dom_left (prop_2_10_G_memAt_of_c A hA h_lim hcDom 0)
  | n + 1 => neg_dom (add_dom_right
      (prop_2_10_G_memAt_of_c A hA h_lim hcDom (n + 1)))

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_c_psi_absConv_of_flatabs {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) {x : X}
    (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_c_rep A hA h_lim).valueAt x hcDom n))) (N : Nat) :
    RSeq.SeriesSum (fun k => COF.abs ((bigAndFin_int A hA N).rep.valueAt x
      (prop_2_10_psi_memAt_of_c A hA h_lim hcDom N) k)) := by
  let hnegRDom := add_dom_right hcDom
  let hRDom := prop_2_10_c_R_memAt A hA h_lim hcDom
  have hRabs : RSeq.SeriesSum (fun n => COF.abs
      ((seriesSumRep_L1 (prop_2_10_G A hA)
        (prop_2_10_G_norm_sum A hA h_lim)).valueAt x hRDom n)) :=
    neg_absSeriesSum hnegRDom (add_absSeriesSum_right hcDom habs)
  have hGabs := seriesSumRep_L1_row_absConv (prop_2_10_G A hA)
    (prop_2_10_G_norm_sum A hA h_lim) hRDom hRabs
  exact add_absSeriesSum_left
    (r := (bigAndFin_int A hA N).rep)
    (r' := (bigAndFin_int A hA (N + 1)).rep.neg)
    (prop_2_10_G_memAt_of_c A hA h_lim hcDom (N + 1)) (hGabs (N + 1))

/-- Technical lemma used in the public import closure. -/
theorem bigAndFin_mem_domain {X : Type*} (A : Nat → BSet X) {x : X}
    (hd : ∀ j, x ∈ (A j).S1 ∪ (A j).S2) :
    ∀ N, x ∈ (bigAndFin A N).S1 ∪ (bigAndFin A N).S2
  | 0 => hd 0
  | n + 1 => by
      rcases bigAndFin_mem_domain A hd n with hP1 | hP2 <;> rcases hd (n + 1) with hQ1 | hQ2
      · exact Or.inl ⟨hP1, hQ1⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hP1, hQ2⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨hP2, hQ1⟩))
      · exact Or.inr (Or.inr ⟨hP2, hQ2⟩)

/-- Technical lemma used in the public import closure. -/
theorem bigAndFin_mem_S1 {X : Type*} (A : Nat → BSet X) {x : X} (hd : ∀ j, x ∈ (A j).S1) :
    ∀ N, x ∈ (bigAndFin A N).S1
  | 0 => hd 0
  | n + 1 => ⟨bigAndFin_mem_S1 A hd n, hd (n + 1)⟩

/-- Technical lemma used in the public import closure. -/
theorem bigAndFin_mem_S2 {X : Type*} (A : Nat → BSet X) {x : X}
    (hd : ∀ j, x ∈ (A j).S1 ∪ (A j).S2) :
    ∀ N k, k ≤ N → x ∈ (A k).S2 → x ∈ (bigAndFin A N).S2
  | 0, k, hk, hxk => by have : k = 0 := Nat.le_zero.mp hk; subst this; exact hxk
  | n + 1, k, hk, hxk => by
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · have hP2 : x ∈ (bigAndFin A n).S2 := bigAndFin_mem_S2 A hd n k (Nat.lt_succ_iff.mp hlt) hxk
        rcases hd (n + 1) with hQ1 | hQ2
        · exact Or.inl (Or.inr ⟨hP2, hQ1⟩)
        · exact Or.inr ⟨hP2, hQ2⟩
      · have hk' : k = n + 1 := Nat.le_antisymm hk hge
        subst hk'
        rcases bigAndFin_mem_domain A hd n with hP1 | hP2
        · exact Or.inl (Or.inl ⟨hP1, hxk⟩)
        · exact Or.inr ⟨hP2, hxk⟩

/-- Technical lemma used in the public import closure. -/
theorem bigAndFin_S1_imp {X : Type*} (A : Nat → BSet X) {x : X} :
    ∀ N k, k ≤ N → x ∈ (bigAndFin A N).S1 → x ∈ (A k).S1
  | 0, k, hk, hx => by have : k = 0 := Nat.le_zero.mp hk; subst this; exact hx
  | n + 1, k, hk, hx => by
      obtain ⟨hP, hQ⟩ := hx
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact bigAndFin_S1_imp A n k (Nat.lt_succ_iff.mp hlt) hP
      · have : k = n + 1 := Nat.le_antisymm hk hge; subst this; exact hQ

/-- Technical lemma used in the public import closure. -/
theorem bigAndFin_S2_imp {X : Type*} (A : Nat → BSet X) {x : X} :
    ∀ N, x ∈ (bigAndFin A N).S2 → ∃ k, k ≤ N ∧ x ∈ (A k).S2
  | 0, hx => ⟨0, Nat.le_refl 0, hx⟩
  | n + 1, hx => by
      rcases hx with (⟨_, hQ2⟩ | ⟨hP2, _⟩) | ⟨hP2, _⟩
      · exact ⟨n + 1, Nat.le_refl _, hQ2⟩
      · obtain ⟨k, hk, hxk⟩ := bigAndFin_S2_imp A n hP2; exact ⟨k, Nat.le_succ_of_le hk, hxk⟩
      · obtain ⟨k, hk, hxk⟩ := bigAndFin_S2_imp A n hP2; exact ⟨k, Nat.le_succ_of_le hk, hxk⟩

/-- Technical lemma used in the public import closure. -/
theorem bigAndFin_domain_imp {X : Type*} (A : Nat → BSet X) {x : X} :
    ∀ N k, k ≤ N → x ∈ (bigAndFin A N).S1 ∪ (bigAndFin A N).S2 → x ∈ (A k).S1 ∪ (A k).S2
  | 0, k, hk, hx => by have : k = 0 := Nat.le_zero.mp hk; subst this; exact hx
  | n + 1, k, hk, hx => by
      have hPQ : x ∈ (bigAndFin A n).S1 ∪ (bigAndFin A n).S2 ∧ x ∈ (A (n + 1)).S1 ∪ (A (n + 1)).S2 := by
        rcases hx with ⟨h1, h2⟩ | (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
        · exact ⟨Or.inl h1, Or.inl h2⟩
        · exact ⟨Or.inl h1, Or.inr h2⟩
        · exact ⟨Or.inr h1, Or.inl h2⟩
        · exact ⟨Or.inr h1, Or.inr h2⟩
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact bigAndFin_domain_imp A n k (Nat.lt_succ_iff.mp hlt) hPQ.1
      · have : k = n + 1 := Nat.le_antisymm hk hge; subst this; exact hPQ.2

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_G_rep_value_series {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) {x : X}
    (hRDom : (seriesSumRep_L1 (prop_2_10_G A hA)
      (prop_2_10_G_norm_sum A hA h_lim)).MemAt x)
    (hRabs : RSeq.SeriesSum (fun n => COF.abs ((seriesSumRep_L1 (prop_2_10_G A hA)
      (prop_2_10_G_norm_sum A hA h_lim)).valueAt x hRDom n)))
    (hpsiDom : ∀ n, (bigAndFin_int A hA n).rep.MemAt x)
    (hpsiv : ∀ n, RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA n).rep.valueAt x (hpsiDom n) k)) :
    { hser : RSeq.SeriesSum (fun m =>
        (prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) //
        (seriesSum_of_abs hRabs).sum = hser.sum } := by
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_value (prop_2_10_G A hA)
    (prop_2_10_G_norm_sum A hA h_lim) hRDom hRabs
  refine ⟨seriesSum_congr (fun m => ?_) hV, eV⟩
  let hGDom : (prop_2_10_G A hA m).MemAt x :=
    seriesSumRep_L1_F_memAt (prop_2_10_G A hA)
      (prop_2_10_G_norm_sum A hA h_lim) hRDom m
  let hPsiSumDom : x ∈ (psi_m (prop_2_10_G A hA) m).dom :=
    BFunR.seqSum_mem (prop_2_10_G A hA m).fn x hGDom
      (Nm (prop_2_10_G A hA) m)
  let hGv := prop_2_10_Gvalue A hA hpsiDom hpsiv m
  rw [show (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
              ((G_m (prop_2_10_G A hA) i).valueAt x
                (seriesSumRep_L1_Grow_memAt (prop_2_10_G A hA)
                  (prop_2_10_G_norm_sum A hA h_lim) hRDom i) j))
            (add_absSeriesSum_left hRDom hRabs) m)).sum
          = (IntegrableRep.ofL_value (psi_m_mem (prop_2_10_G A hA) m) x
              hPsiSumDom).val.sum from
          seriesSum_unique _ _,
      show (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
              ((tail_m (prop_2_10_G A hA) i).valueAt x
                (seriesSumRep_L1_tailRow_memAt (prop_2_10_G A hA)
                  (prop_2_10_G_norm_sum A hA h_lim) hRDom i) j))
            (add_absSeriesSum_right hRDom hRabs) m)).sum
          = (IntegrableRep.tailFrom_value (prop_2_10_G A hA m) (Nm (prop_2_10_G A hA) m) x
              hGDom hGv).val.sum from
          seriesSum_unique _ _]
  exact seriesSumRep_L1_hsplit_value (prop_2_10_G A hA) m hGDom hGv

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_psi_value {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) (N : Nat) {x : X}
    (hpsiDom : (bigAndFin_int A hA N).rep.MemAt x)
    (hpsiabs_N : RSeq.SeriesSum (fun k => COF.abs
      ((bigAndFin_int A hA N).rep.valueAt x hpsiDom k)))
    (hpsiv_N : RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA N).rep.valueAt x hpsiDom k)) :
    (x ∈ (bigAndFin A N).S1 ∪ (bigAndFin A N).S2)
    ∧ (x ∈ (bigAndFin A N).S1 → hpsiv_N.sum = 1)
    ∧ (x ∈ (bigAndFin A N).S2 → hpsiv_N.sum = 0) := by
  have hval := (bigAndFin_int A hA N).valid x hpsiDom hpsiabs_N
  exact ⟨hval.1, fun hx1 => hval.2.1 hx1 hpsiv_N, fun hx2 => hval.2.2 hx2 hpsiv_N⟩

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_c_decide {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) {x : X}
    (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_c_rep A hA h_lim).valueAt x hcDom n))) :
    (∃ M, x ∈ (bigAndFin A M).S2) ∨ (∀ N, x ∈ (bigAndFin A N).S1) := by
  let hnegRDom := add_dom_right hcDom
  let hRDom := prop_2_10_c_R_memAt A hA h_lim hcDom
  have hRabs : RSeq.SeriesSum (fun n => COF.abs
      ((seriesSumRep_L1 (prop_2_10_G A hA)
        (prop_2_10_G_norm_sum A hA h_lim)).valueAt x hRDom n)) :=
    neg_absSeriesSum hnegRDom (add_absSeriesSum_right hcDom habs)
  have hGabs := seriesSumRep_L1_row_absConv (prop_2_10_G A hA)
    (prop_2_10_G_norm_sum A hA h_lim) hRDom hRabs
  let hpsiDom := prop_2_10_psi_memAt_of_c A hA h_lim hcDom
  have hpsiabs := prop_2_10_c_psi_absConv_of_flatabs A hA h_lim hcDom habs
  have hpsiv : ∀ N, RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA N).rep.valueAt x (hpsiDom N) k) :=
    fun N => seriesSum_of_abs (hpsiabs N)
  obtain ⟨hser, _⟩ := prop_2_10_G_rep_value_series A hA h_lim hRDom hRabs
    hpsiDom hpsiv
  have hpsival := fun N => prop_2_10_psi_value A hA N (hpsiDom N)
    (hpsiabs N) (hpsiv N)
  have hpsi01 : ∀ N, (hpsiv N).sum = 0 ∨ (hpsiv N).sum = 1 := fun N => by
    rcases (hpsival N).1 with h1 | h2
    · exact Or.inr ((hpsival N).2.1 h1)
    · exact Or.inl ((hpsival N).2.2 h2)
  have hnn : ∀ m, Nonneg ((prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) := fun m =>
    prop_2_10_G_nonneg A hA m x (prop_2_10_G_memAt A hA hpsiDom m)
      (hGabs m) (prop_2_10_Gvalue A hA hpsiDom hpsiv m)
  have hbin : ∀ N, RSeq.partialSum
      (fun m => (prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) N = 0
      ∨ RSeq.partialSum (fun m => (prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) N = 1 := fun N => by
    have hps := prop_2_10_G_partialSum_value A hA hpsiDom hpsiv N
    have hnonneg := partialSum_nonneg hnn N
    rcases hpsi01 0 with h00 | h01 <;> rcases hpsi01 N with hN0 | hN1
    · left; rw [hps, h00, hN0]; ring
    · exfalso; rw [hps, h00, hN1] at hnonneg; exact hnonneg (BishopC.sub_neg_of_lt COFO.one_pos)
    · right; rw [hps, h01, hN0]; ring
    · left; rw [hps, h01, hN1]; ring
  rcases seriesSum_binary_dichotomy hnn hser hbin with ⟨M, hM⟩ | hAll
  · left; refine ⟨M, ?_⟩
    rw [prop_2_10_G_partialSum_value A hA hpsiDom hpsiv M] at hM
    rcases (hpsival M).1 with hx1 | hx2
    · exfalso
      rw [(hpsival M).2.1 hx1] at hM
      rcases hpsi01 0 with h00 | h01
      · rw [h00] at hM
        exact COF.lt_irrefl 0 (COFO.lt_trans COFO.one_pos (hM ▸ BishopC.sub_neg_of_lt COFO.one_pos))
      · rw [h01] at hM
        have : (1 : R) - 1 = 0 := by ring
        rw [this] at hM; exact zero_ne_one_R hM
    · exact hx2
  · rcases hpsi01 0 with h00 | h01
    · left; refine ⟨0, ?_⟩
      rcases (hpsival 0).1 with hx1 | hx2
      · exfalso; rw [(hpsival 0).2.1 hx1] at h00; exact zero_ne_one_R h00.symm
      · exact hx2
    · right; intro N
      have hN := hAll N
      rw [prop_2_10_G_partialSum_value A hA hpsiDom hpsiv N, h01] at hN
      have hψN1 : (hpsiv N).sum = 1 := by rw [sub_eq_zero] at hN; exact hN.symm
      rcases (hpsival N).1 with hx1 | hx2
      · exact hx1
      · exfalso; rw [(hpsival N).2.2 hx2] at hψN1; exact zero_ne_one_R hψN1

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_c_mem {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) {x : X}
    (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_c_rep A hA h_lim).valueAt x hcDom n))) :
    x ∈ (BSet.bigAnd A).S1 ∪ (BSet.bigAnd A).S2 := by
  let hpsiDom := prop_2_10_psi_memAt_of_c A hA h_lim hcDom
  have hpsiabs := prop_2_10_c_psi_absConv_of_flatabs A hA h_lim hcDom habs
  have hpsiv : ∀ N, RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA N).rep.valueAt x (hpsiDom N) k) :=
    fun N => seriesSum_of_abs (hpsiabs N)
  have hpsival := fun N => prop_2_10_psi_value A hA N (hpsiDom N)
    (hpsiabs N) (hpsiv N)
  have hdom : ∀ j, x ∈ (A j).S1 ∪ (A j).S2 := fun j =>
    bigAndFin_domain_imp A j j (Nat.le_refl j) (hpsival j).1
  rcases prop_2_10_c_decide A hA h_lim hcDom habs with ⟨M, hxM2⟩ | hAll
  · obtain ⟨k, _, hxk⟩ := bigAndFin_S2_imp A M hxM2
    exact Or.inr ⟨Set.mem_iInter.mpr hdom, Set.mem_iUnion.mpr ⟨k, hxk⟩⟩
  · exact Or.inl (Set.mem_iInter.mpr (fun k => bigAndFin_S1_imp A k k (Nat.le_refl k) (hAll k)))

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_c_val1 {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) {x : X}
    (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_c_rep A hA h_lim).valueAt x hcDom n)))
    (hxS1 : x ∈ (BSet.bigAnd A).S1)
    (h : RSeq.SeriesSum (fun n =>
      (prop_2_10_c_rep A hA h_lim).valueAt x hcDom n)) :
    h.sum = 1 := by
  have hd1 : ∀ j, x ∈ (A j).S1 := fun j => Set.mem_iInter.mp hxS1 j
  let h0Dom : (hA 0).rep.MemAt x := add_dom_left hcDom
  let hnegRDom := add_dom_right hcDom
  let hRDom := prop_2_10_c_R_memAt A hA h_lim hcDom
  have h0 : RSeq.SeriesSum (fun n => (hA 0).rep.valueAt x h0Dom n) :=
    seriesSum_of_abs (add_absSeriesSum_left hcDom habs)
  have hRabs : RSeq.SeriesSum (fun n => COF.abs
      ((seriesSumRep_L1 (prop_2_10_G A hA)
        (prop_2_10_G_norm_sum A hA h_lim)).valueAt x hRDom n)) :=
    neg_absSeriesSum hnegRDom (add_absSeriesSum_right hcDom habs)
  let hpsiDom := prop_2_10_psi_memAt_of_c A hA h_lim hcDom
  have hpsiabs := prop_2_10_c_psi_absConv_of_flatabs A hA h_lim hcDom habs
  have hpsiv : ∀ N, RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA N).rep.valueAt x (hpsiDom N) k) :=
    fun N => seriesSum_of_abs (hpsiabs N)
  obtain ⟨hser, eser⟩ := prop_2_10_G_rep_value_series A hA h_lim hRDom hRabs
    hpsiDom hpsiv
  have hpsival := fun N => prop_2_10_psi_value A hA N (hpsiDom N)
    (hpsiabs N) (hpsiv N)
  have hpsi0_1 : (hpsiv 0).sum = 1 := (hpsival 0).2.1 (hd1 0)
  have hh0 : h0.sum = (hpsiv 0).sum := seriesSum_unique h0 (hpsiv 0)
  have hev : ∀ N, 0 ≤ N → RSeq.partialSum
      (fun m => (prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) N = 0 := fun N _ => by
    rw [prop_2_10_G_partialSum_value A hA hpsiDom hpsiv N, hpsi0_1,
        (hpsival N).2.1 (bigAndFin_mem_S1 A hd1 N)]; ring
  have hser0 : hser.sum = 0 := seriesSum_of_eventually_const hser 0 hev
  rw [seriesSum_unique h (add_seriesSum_value h0Dom hnegRDom h0
    (neg_seriesSum_value hRDom (seriesSum_of_abs hRabs)))]
  show h0.sum + (- (seriesSum_of_abs hRabs).sum) = 1
  rw [hh0, hpsi0_1, eser, hser0]; ring

/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_c_val0 {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) {x : X}
    (hcDom : (prop_2_10_c_rep A hA h_lim).MemAt x)
    (habs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_2_10_c_rep A hA h_lim).valueAt x hcDom n)))
    (hxS2 : x ∈ (BSet.bigAnd A).S2)
    (h : RSeq.SeriesSum (fun n =>
      (prop_2_10_c_rep A hA h_lim).valueAt x hcDom n)) :
    h.sum = 0 := by
  obtain ⟨hInter, hUnion⟩ := hxS2
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hUnion
  have hdom : ∀ j, x ∈ (A j).S1 ∪ (A j).S2 := fun j => Set.mem_iInter.mp hInter j
  let h0Dom : (hA 0).rep.MemAt x := add_dom_left hcDom
  let hnegRDom := add_dom_right hcDom
  let hRDom := prop_2_10_c_R_memAt A hA h_lim hcDom
  have h0 : RSeq.SeriesSum (fun n => (hA 0).rep.valueAt x h0Dom n) :=
    seriesSum_of_abs (add_absSeriesSum_left hcDom habs)
  have hRabs : RSeq.SeriesSum (fun n => COF.abs
      ((seriesSumRep_L1 (prop_2_10_G A hA)
        (prop_2_10_G_norm_sum A hA h_lim)).valueAt x hRDom n)) :=
    neg_absSeriesSum hnegRDom (add_absSeriesSum_right hcDom habs)
  let hpsiDom := prop_2_10_psi_memAt_of_c A hA h_lim hcDom
  have hpsiabs := prop_2_10_c_psi_absConv_of_flatabs A hA h_lim hcDom habs
  have hpsiv : ∀ N, RSeq.SeriesSum (fun k =>
      (bigAndFin_int A hA N).rep.valueAt x (hpsiDom N) k) :=
    fun N => seriesSum_of_abs (hpsiabs N)
  obtain ⟨hser, eser⟩ := prop_2_10_G_rep_value_series A hA h_lim hRDom hRabs
    hpsiDom hpsiv
  have hpsival := fun N => prop_2_10_psi_value A hA N (hpsiDom N)
    (hpsiabs N) (hpsiv N)
  have hh0 : h0.sum = (hpsiv 0).sum := seriesSum_unique h0 (hpsiv 0)
  have hev : ∀ N, k ≤ N → RSeq.partialSum
      (fun m => (prop_2_10_Gvalue A hA hpsiDom hpsiv m).sum) N =
        (hpsiv 0).sum := fun N hN => by
    rw [prop_2_10_G_partialSum_value A hA hpsiDom hpsiv N,
      (hpsival N).2.2 (bigAndFin_mem_S2 A hdom N k hN hxk)]; ring
  have hserψ0 : hser.sum = (hpsiv 0).sum := seriesSum_of_eventually_const hser k hev
  rw [seriesSum_unique h (add_seriesSum_value h0Dom hnegRDom h0
    (neg_seriesSum_value hRDom (seriesSum_of_abs hRabs)))]
  show h0.sum + (- (seriesSum_of_abs hRabs).sum) = 0
  rw [hh0, eser, hserψ0]; ring

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_2_10_c {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) :
    IntegrableSet1 S (BSet.bigAnd A) where
  full := ⟨fun _ => prop_2_10_c_rep A hA h_lim, fun x hx => by
    obtain ⟨hdom, ⟨habs⟩⟩ := hx 0
    exact prop_2_10_c_mem A hA h_lim hdom habs⟩
  rep := prop_2_10_c_rep A hA h_lim
  valid := by
    intro x hdom habs
    exact ⟨prop_2_10_c_mem A hA h_lim hdom habs,
      fun hxS1 h => prop_2_10_c_val1 A hA h_lim hdom habs hxS1 h,
      fun hxS2 h => prop_2_10_c_val0 A hA h_lim hdom habs hxS2 h⟩


/-- Technical lemma used in the public import closure. -/
theorem prop_2_10_c_measure {S : IntSpaceRC X R} (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k))
    (h_lim : Σ β : R, RSeq.TendstoHalf (fun n => measure1 S (bigAndFin_int A hA n)) β) :
    measure1 S (prop_2_10_c A hA h_lim) = h_lim.fst := by
  obtain ⟨hI, e⟩ := seriesSumRep_L1_integral (prop_2_10_G A hA) (prop_2_10_G_norm_sum A hA h_lim)
  show ((hA 0).rep.sub
      (seriesSumRep_L1 (prop_2_10_G A hA) (prop_2_10_G_norm_sum A hA h_lim))).integral = h_lim.fst
  rw [IntegrableRep.integral_sub, e]
  have heq : hI.sum = (prop_2_10_G_norm_sum A hA h_lim).sum :=
    seriesSum_unique hI
      (seriesSum_congr (fun m => IntegrableRep.normL1_eq_integral_of_nonneg
          (prop_2_10_G A hA m) (prop_2_10_G_nonneg A hA m))
        (prop_2_10_G_norm_sum A hA h_lim))
  rw [heq]
  show (hA 0).rep.integral - (measure1 S (hA 0) - h_lim.fst) = h_lim.fst
  show (hA 0).rep.integral - ((hA 0).rep.integral - h_lim.fst) = h_lim.fst
  ring

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

/-- The absolute series of a clean representative is the same as its value series. -/
def absSeries_of_value (C : CleanCharRepSec2 (S := S) A) {x : X}
    (h : RepSummableAtSec2 C.rep x) :
    RSeq.SeriesSum (fun k => COF.abs (C.rep.valueAt x h.dom k)) := by
  refine seriesSum_congr (fun k => ?_) h.series
  exact (COFO.abs_of_nonneg (C.term_nonneg k x (h.dom k))).symm

/-- Termwise nonnegativity turns absolute sums into value sums. -/
theorem abs_eq_value (C : CleanCharRepSec2 (S := S) A) {x : X}
    (h : RepSummableAtSec2 C.rep x) :
    (C.absSeries_of_value h).sum = h.series.sum :=
  seriesSum_unique (C.absSeries_of_value h)
    (seriesSum_congr (fun k =>
      (COFO.abs_of_nonneg (C.term_nonneg k x (h.dom k))).symm) h.series)

/-- On the inactive side of a clean indicator, the absolute mass is zero. -/
theorem inactive_abs_zero (C : CleanCharRepSec2 (S := S) A) {x : X} (hx : x ∈ A.S2) :
    ((C.absSeries_of_value (C.value_zero x hx).val)).sum = 0 := by
  rw [C.abs_eq_value (C.value_zero x hx).val, (C.value_zero x hx).property]

/-- On the active side of a clean indicator, the absolute mass is one. -/
theorem active_abs_one (C : CleanCharRepSec2 (S := S) A) {x : X} (hx : x ∈ A.S1) :
    ((C.absSeries_of_value (C.value_one x hx).val)).sum = 1 := by
  rw [C.abs_eq_value (C.value_one x hx).val, (C.value_one x hx).property]

/-- Forget the clean layer and recover the ordinary Section 2 integrable set witness. -/
def toIntegrableSet1 (C : CleanCharRepSec2 (S := S) A) : IntegrableSet1 S A :=
  C.existing_chi

/-- Value bridge to the ordinary representative carried by `existing_chi`. -/
theorem bridge_value_with_existing (C : CleanCharRepSec2 (S := S) A) {x : X}
    (h_clean_dom : C.rep.MemAt x) (h_existing_dom : C.existing_chi.rep.MemAt x)
    (h_clean_abs : RSeq.SeriesSum (fun k => COF.abs
      (C.rep.valueAt x h_clean_dom k)))
    (h_existing_abs : RSeq.SeriesSum (fun k => COF.abs
      (C.existing_chi.rep.valueAt x h_existing_dom k)))
    (h_clean : RSeq.SeriesSum (fun k => C.rep.valueAt x h_clean_dom k))
    (h_existing : RSeq.SeriesSum (fun k =>
      C.existing_chi.rep.valueAt x h_existing_dom k)) :
    h_clean.sum = h_existing.sum :=
  C.bridge_value_existing x h_clean_dom h_existing_dom h_clean_abs h_existing_abs
    h_clean h_existing

/-- Integral bridge to the ordinary representative carried by `existing_chi`. -/
theorem bridge_integral_with_existing (C : CleanCharRepSec2 (S := S) A) :
    C.rep.integral = C.existing_chi.rep.integral :=
  C.bridge_integral_existing

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

/-- Clean intersection from the Section 2 primitive clean-min surface. -/
def cleanMinSec2 {S : IntSpaceRC X R} (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    {A B : BSet X} (CA : CleanCharRepSec2 (S := S) A)
    (CB : CleanCharRepSec2 (S := S) B) :
    CleanCharRepSec2 (S := S) (BSet.and A B) :=
  (Ops.clean_min CA CB).out

/-- Clean union from the Section 2 primitive clean-max surface. -/
def cleanMaxSec2 {S : IntSpaceRC X R} (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    {A B : BSet X} (CA : CleanCharRepSec2 (S := S) A)
    (CB : CleanCharRepSec2 (S := S) B) :
    CleanCharRepSec2 (S := S) (BSet.or A B) :=
  (Ops.clean_max CA CB).out

/-- Direct clean representative of the opposite side. -/
def cleanComplementSideSec2 {S : IntSpaceRC X R}
    (Ops : CleanBooleanSec2Ops (X := X) (R := R) S) {A : BSet X}
    (CA : CleanCharRepSec2 (S := S) A) :
    CleanCharRepSec2 (S := S) (BSet.neg A) :=
  (Ops.clean_complement_side CA).out

/-- Clean set difference as clean-min with the direct clean complement side. -/
def cleanDiffSec2 {S : IntSpaceRC X R} (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    {A B : BSet X} (CA : CleanCharRepSec2 (S := S) A)
    (CB : CleanCharRepSec2 (S := S) B) :
    CleanCharRepSec2 (S := S) (BSet.sub A B) :=
  cleanMinSec2 (S := S) Ops CA (cleanComplementSideSec2 (S := S) Ops CB)

/-- The inactive side of clean difference has zero absolute mass, without any
per-call clean-difference witness. -/
theorem cleanDiffSec2_inactive_abs_zero {S : IntSpaceRC X R}
    (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    {A B : BSet X} (CA : CleanCharRepSec2 (S := S) A)
    (CB : CleanCharRepSec2 (S := S) B) {x : X}
    (hx : x ∈ (BSet.sub A B).S2) :
    (((cleanDiffSec2 (S := S) Ops CA CB).absSeries_of_value
      (((cleanDiffSec2 (S := S) Ops CA CB).value_zero x hx).val))).sum = 0 :=
  (cleanDiffSec2 (S := S) Ops CA CB).inactive_abs_zero hx

/-- Finite union increment sets used by the clean Prop. 2.10 row surface. -/
def cleanBigOrFinIncrementSetSec2 (A : Nat → BSet X) : Nat → BSet X
  | 0 => A 0
  | n + 1 => BSet.sub (bigOrFin A (n + 1)) (bigOrFin A n)

/-- Finite intersection drop sets used by the clean Prop. 2.10 row surface. -/
def cleanBigAndFinDropSetSec2 (A : Nat → BSet X) : Nat → BSet X
  | 0 => BSet.sub (A 0) (A 0)
  | n + 1 => BSet.sub (bigAndFin A n) (bigAndFin A (n + 1))

/-- Clean finite unions obtained from base clean indicators and clean max. -/
noncomputable def cleanBigOrFinSec2 {S : IntSpaceRC X R}
    (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    (A : Nat → BSet X) (C : ∀ k, CleanCharRepSec2 (S := S) (A k)) :
    ∀ n, CleanCharRepSec2 (S := S) (bigOrFin A n)
  | 0 => C 0
  | n + 1 => cleanMaxSec2 (S := S) Ops (cleanBigOrFinSec2 (S := S) Ops A C n) (C (n + 1))

/-- Clean finite intersections obtained from base clean indicators and clean min. -/
noncomputable def cleanBigAndFinSec2 {S : IntSpaceRC X R}
    (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    (A : Nat → BSet X) (C : ∀ k, CleanCharRepSec2 (S := S) (A k)) :
    ∀ n, CleanCharRepSec2 (S := S) (bigAndFin A n)
  | 0 => C 0
  | n + 1 => cleanMinSec2 (S := S) Ops (cleanBigAndFinSec2 (S := S) Ops A C n) (C (n + 1))

/-- Clean Prop. 2.10 union-increment rows, built only from base clean indicators
and clean Boolean primitives. -/
noncomputable def cleanBigOrFinIncrementSec2 {S : IntSpaceRC X R}
    (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    (A : Nat → BSet X) (C : ∀ k, CleanCharRepSec2 (S := S) (A k)) :
    ∀ n, CleanCharRepSec2 (S := S) (cleanBigOrFinIncrementSetSec2 A n)
  | 0 => C 0
  | n + 1 =>
      cleanDiffSec2 (S := S) Ops
        (cleanBigOrFinSec2 (S := S) Ops A C (n + 1))
        (cleanBigOrFinSec2 (S := S) Ops A C n)

/-- Clean Prop. 2.10 intersection-drop rows, built only from base clean indicators
and clean Boolean primitives. -/
noncomputable def cleanBigAndFinDropSec2 {S : IntSpaceRC X R}
    (Ops : CleanBooleanSec2Ops (X := X) (R := R) S)
    (A : Nat → BSet X) (C : ∀ k, CleanCharRepSec2 (S := S) (A k)) :
    ∀ n, CleanCharRepSec2 (S := S) (cleanBigAndFinDropSetSec2 A n)
  | 0 => cleanDiffSec2 (S := S) Ops (C 0) (C 0)
  | n + 1 =>
      cleanDiffSec2 (S := S) Ops
        (cleanBigAndFinSec2 (S := S) Ops A C n)
        (cleanBigAndFinSec2 (S := S) Ops A C (n + 1))

/-- Base clean data for the Prop. 2.10 clean row generators. -/
structure Prop210BaseCleanRepSec2 {S : IntSpaceRC X R}
    (Ops : CleanBooleanSec2Ops (X := X) (R := R) S) (A : Nat → BSet X) where
  base_clean : ∀ k, CleanCharRepSec2 (S := S) (A k)

namespace Prop210BaseCleanRepSec2

variable {S : IntSpaceRC X R} {Ops : CleanBooleanSec2Ops (X := X) (R := R) S}
variable {A : Nat → BSet X}

/-- Prop. 2.10 finite union-increment clean rows supplied from base clean data. -/
noncomputable def unionIncrementClean (P : Prop210BaseCleanRepSec2 (S := S) Ops A) :
    ∀ n, CleanCharRepSec2 (S := S) (cleanBigOrFinIncrementSetSec2 A n) :=
  cleanBigOrFinIncrementSec2 (S := S) Ops A P.base_clean

/-- Prop. 2.10 finite intersection-drop clean rows supplied from base clean data. -/
noncomputable def intersectionDropClean (P : Prop210BaseCleanRepSec2 (S := S) Ops A) :
    ∀ n, CleanCharRepSec2 (S := S) (cleanBigAndFinDropSetSec2 A n) :=
  cleanBigAndFinDropSec2 (S := S) Ops A P.base_clean

end Prop210BaseCleanRepSec2


end BishopC
