import Mathdemo.CRealPresented
import Mathdemo.Internal.CRat_iter138

namespace BishopSec1P
open BishopCReal

-- <<<v7:I.1
private theorem add_congr {a a' b b' : CReal}
    (ha : a ≈ a') (hb : b ≈ b') :
    CReal.add a b ≈ CReal.add a' b' :=
  CReal.add_respects_equiv a a' b b' ha hb

#print axioms add_congr

private theorem mul_congr {a a' b b' : CReal}
    (ha : a ≈ a') (hb : b ≈ b') :
    CReal.mul a b ≈ CReal.mul a' b' :=
  CReal.mul_respects_equiv a a' b b' ha hb

#print axioms mul_congr

private theorem neg_congr {a b : CReal} (h : a ≈ b) :
    CReal.neg a ≈ CReal.neg b :=
  CReal.neg_respects_equiv a b h

#print axioms neg_congr

private theorem abs_congr {a b : CReal} (h : a ≈ b) :
    CReal.abs a ≈ CReal.abs b := by
  change absSeq a ≈ absSeq b
  exact absSeq_respects_eventually a b h

#print axioms abs_congr

private theorem neg_zero_equiv : CReal.neg CReal.zero ≈ CReal.zero := by
  exact Setoid.trans (Setoid.symm (CReal.add_zero (CReal.neg CReal.zero)))
    (CReal.add_left_neg CReal.zero)

#print axioms neg_zero_equiv

private theorem add_right_neg_equiv (a : CReal) :
    CReal.add a (CReal.neg a) ≈ CReal.zero := by
  change addSeq a (negSeq a) ≈ zeroSeq
  exact addSeq_neg_right_eventually a

#print axioms add_right_neg_equiv

private theorem neg_neg_equiv (a : CReal) : CReal.neg (CReal.neg a) ≈ a := by
  change negSeq (negSeq a) ≈ a
  exact negSeq_negSeq_eventually a

#print axioms neg_neg_equiv

private theorem mul_neg_right_equiv (a b : CReal) :
    CReal.mul a (CReal.neg b) ≈ CReal.neg (CReal.mul a b) := by
  change mulSeqConcreteWith cRatScalarMulArch a (negSeq b) ≈
    negSeq (mulSeqConcreteWith cRatScalarMulArch a b)
  exact bounded_mul_neg_right_eventually_with cRatScalarMulArch a b

#print axioms mul_neg_right_equiv

private theorem neg_one_mul_equiv (a : CReal) :
    CReal.mul (CReal.neg CReal.one) a ≈ CReal.neg a := by
  change mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq) a ≈ negSeq a
  exact mulSeq_neg_one_left_eventually_neg cRatScalarMulArch a

#print axioms neg_one_mul_equiv

theorem zero_mul_equivC (a : CReal) :
    CReal.mul CReal.zero a ≈ CReal.zero := by
  change relEventually (mulSeqConcreteWith cRatScalarMulArch zeroSeq a) zeroSeq
  exact mulSeqConcrete_zero_left_eventually cRatScalarMulArch a

#print axioms BishopSec1P.zero_mul_equivC

private theorem add_neg_one_mul_right_sub_equiv (a b : CReal) :
    CReal.add a (CReal.mul (CReal.neg CReal.one) b) ≈ CReal.sub a b := by
  change addSeq a (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq) b) ≈ subSeq a b
  exact addSeq_negOneMul_right_eventually_subSeq cRatScalarMulArch a b

#print axioms add_neg_one_mul_right_sub_equiv

private theorem add_sub_right_equiv (a b : CReal) :
    CReal.add a (CReal.neg b) ≈ CReal.sub a b := by
  exact Setoid.symm (subSeq_eq_add_neg_eventually a b)

#print axioms add_sub_right_equiv

private theorem sub_add_neg_equiv (a b : CReal) :
    CReal.sub a b ≈ CReal.add a (CReal.neg b) := by
  exact subSeq_eq_add_neg_eventually a b

#print axioms sub_add_neg_equiv

private theorem neg_add_neg_right_equiv (a b : CReal) :
    CReal.neg (CReal.add a (CReal.neg b)) ≈ CReal.add (CReal.neg a) b := by
  calc
    CReal.neg (CReal.add a (CReal.neg b))
        ≈ CReal.neg (CReal.sub a b) := neg_congr (add_sub_right_equiv a b)
    _ ≈ CReal.neg (CReal.neg (CReal.sub b a)) :=
        neg_congr (subSeq_comm_neg_eventually a b)
    _ ≈ CReal.sub b a := neg_neg_equiv (CReal.sub b a)
    _ ≈ CReal.add b (CReal.neg a) := sub_add_neg_equiv b a
    _ ≈ CReal.add (CReal.neg a) b := CReal.add_comm b (CReal.neg a)

#print axioms neg_add_neg_right_equiv

private theorem add_pair_swap (p q r s : CReal) :
    CReal.add (CReal.add p q) (CReal.add r s) ≈
      CReal.add (CReal.add p r) (CReal.add q s) := by
  have hinner : CReal.add q (CReal.add r s) ≈ CReal.add r (CReal.add q s) := by
    calc
      CReal.add q (CReal.add r s)
          ≈ CReal.add (CReal.add q r) s := Setoid.symm (CReal.add_assoc q r s)
      _ ≈ CReal.add (CReal.add r q) s := add_congr (CReal.add_comm q r) (Setoid.refl s)
      _ ≈ CReal.add r (CReal.add q s) := CReal.add_assoc r q s
  calc
    CReal.add (CReal.add p q) (CReal.add r s)
        ≈ CReal.add p (CReal.add q (CReal.add r s)) := CReal.add_assoc p q (CReal.add r s)
    _ ≈ CReal.add p (CReal.add r (CReal.add q s)) := add_congr (Setoid.refl p) hinner
    _ ≈ CReal.add (CReal.add p r) (CReal.add q s) :=
        Setoid.symm (CReal.add_assoc p r (CReal.add q s))

#print axioms add_pair_swap

private theorem half_add_self_equiv (a : CReal) :
    CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half a) ≈ a := by
  calc
    CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half a)
        ≈ CReal.mul (CReal.add CReal.half CReal.half) a :=
          Setoid.symm (CReal.right_distrib CReal.half CReal.half a)
    _ ≈ CReal.mul CReal.one a := mul_congr CReal.half_add_half (Setoid.refl a)
    _ ≈ a := CReal.one_mul a

#print axioms half_add_self_equiv

private theorem half_neg_cancel_equiv (a : CReal) :
    CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half (CReal.neg a)) ≈
      CReal.zero := by
  calc
    CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half (CReal.neg a))
        ≈ CReal.add (CReal.mul CReal.half a) (CReal.neg (CReal.mul CReal.half a)) :=
          add_congr (Setoid.refl (CReal.mul CReal.half a))
            (mul_neg_right_equiv CReal.half a)
    _ ≈ CReal.zero := add_right_neg_equiv (CReal.mul CReal.half a)

#print axioms half_neg_cancel_equiv

theorem max_zero_halfsum (a : CReal) :
    CReal.max a CReal.zero ≈ CReal.mul CReal.half (CReal.add a (CReal.abs a)) := by
  have hdiff : CReal.add a (CReal.neg CReal.zero) ≈ a := by
    exact Setoid.trans (add_congr (Setoid.refl a) neg_zero_equiv) (CReal.add_zero a)
  have habs : CReal.abs (CReal.add a (CReal.neg CReal.zero)) ≈ CReal.abs a :=
    abs_congr hdiff
  have hbody :
      CReal.add (CReal.add a CReal.zero)
          (CReal.abs (CReal.add a (CReal.neg CReal.zero))) ≈
        CReal.add a (CReal.abs a) :=
    add_congr (CReal.add_zero a) habs
  exact Setoid.trans (CReal.max_halfsum a CReal.zero)
    (mul_congr (Setoid.refl CReal.half) hbody)

#print axioms BishopSec1P.max_zero_halfsum

theorem min_zero_halfsum (a : CReal) :
    CReal.min a CReal.zero ≈
      CReal.mul CReal.half (CReal.add a (CReal.neg (CReal.abs a))) := by
  have hdiff : CReal.add a (CReal.neg CReal.zero) ≈ a := by
    exact Setoid.trans (add_congr (Setoid.refl a) neg_zero_equiv) (CReal.add_zero a)
  have hnegabs :
      CReal.neg (CReal.abs (CReal.add a (CReal.neg CReal.zero))) ≈
        CReal.neg (CReal.abs a) :=
    neg_congr (abs_congr hdiff)
  have hbody :
      CReal.add (CReal.add a CReal.zero)
          (CReal.neg (CReal.abs (CReal.add a (CReal.neg CReal.zero)))) ≈
        CReal.add a (CReal.neg (CReal.abs a)) :=
    add_congr (CReal.add_zero a) hnegabs
  exact Setoid.trans (CReal.min_halfsum a CReal.zero)
    (mul_congr (Setoid.refl CReal.half) hbody)

#print axioms BishopSec1P.min_zero_halfsum

private theorem neg_min_zero_halfsum (a : CReal) :
    CReal.neg (CReal.min a CReal.zero) ≈
      CReal.mul CReal.half (CReal.add (CReal.neg a) (CReal.abs a)) := by
  let u := CReal.abs a
  calc
    CReal.neg (CReal.min a CReal.zero)
        ≈ CReal.neg (CReal.mul CReal.half (CReal.add a (CReal.neg u))) :=
          neg_congr (min_zero_halfsum a)
    _ ≈ CReal.mul CReal.half (CReal.neg (CReal.add a (CReal.neg u))) :=
          Setoid.symm (mul_neg_right_equiv CReal.half (CReal.add a (CReal.neg u)))
    _ ≈ CReal.mul CReal.half (CReal.add (CReal.neg a) u) :=
          mul_congr (Setoid.refl CReal.half) (neg_add_neg_right_equiv a u)

#print axioms neg_min_zero_halfsum

theorem max_add_negmin_eq_abs (a : CReal) :
    CReal.add (CReal.max a CReal.zero) (CReal.neg (CReal.min a CReal.zero)) ≈
      CReal.abs a := by
  let u := CReal.abs a
  have h0 :
      CReal.add (CReal.max a CReal.zero) (CReal.neg (CReal.min a CReal.zero)) ≈
        CReal.add (CReal.mul CReal.half (CReal.add a u))
          (CReal.mul CReal.half (CReal.add (CReal.neg a) u)) :=
    add_congr (max_zero_halfsum a) (neg_min_zero_halfsum a)
  have h1 :
      CReal.add (CReal.mul CReal.half (CReal.add a u))
          (CReal.mul CReal.half (CReal.add (CReal.neg a) u)) ≈
        CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half u))
          (CReal.add (CReal.mul CReal.half (CReal.neg a)) (CReal.mul CReal.half u)) :=
    add_congr (CReal.left_distrib CReal.half a u)
      (CReal.left_distrib CReal.half (CReal.neg a) u)
  have h2 :
      CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half u))
          (CReal.add (CReal.mul CReal.half (CReal.neg a)) (CReal.mul CReal.half u)) ≈
        CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half (CReal.neg a)))
          (CReal.add (CReal.mul CReal.half u) (CReal.mul CReal.half u)) :=
    add_pair_swap (CReal.mul CReal.half a) (CReal.mul CReal.half u)
      (CReal.mul CReal.half (CReal.neg a)) (CReal.mul CReal.half u)
  have h3 :
      CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half (CReal.neg a)))
          (CReal.add (CReal.mul CReal.half u) (CReal.mul CReal.half u)) ≈
        CReal.add CReal.zero u :=
    add_congr (half_neg_cancel_equiv a) (half_add_self_equiv u)
  exact Setoid.trans h0 (Setoid.trans h1 (Setoid.trans h2 (Setoid.trans h3 (CReal.zero_add u))))

#print axioms BishopSec1P.max_add_negmin_eq_abs

theorem max_add_min_eq_self (a : CReal) :
    CReal.add (CReal.max a CReal.zero) (CReal.min a CReal.zero) ≈ a := by
  let u := CReal.abs a
  have h0 :
      CReal.add (CReal.max a CReal.zero) (CReal.min a CReal.zero) ≈
        CReal.add (CReal.mul CReal.half (CReal.add a u))
          (CReal.mul CReal.half (CReal.add a (CReal.neg u))) :=
    add_congr (max_zero_halfsum a) (min_zero_halfsum a)
  have h1 :
      CReal.add (CReal.mul CReal.half (CReal.add a u))
          (CReal.mul CReal.half (CReal.add a (CReal.neg u))) ≈
        CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half u))
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half (CReal.neg u))) :=
    add_congr (CReal.left_distrib CReal.half a u)
      (CReal.left_distrib CReal.half a (CReal.neg u))
  have h2 :
      CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half u))
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half (CReal.neg u))) ≈
        CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half a))
          (CReal.add (CReal.mul CReal.half u) (CReal.mul CReal.half (CReal.neg u))) :=
    add_pair_swap (CReal.mul CReal.half a) (CReal.mul CReal.half u)
      (CReal.mul CReal.half a) (CReal.mul CReal.half (CReal.neg u))
  have h3 :
      CReal.add
          (CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half a))
          (CReal.add (CReal.mul CReal.half u) (CReal.mul CReal.half (CReal.neg u))) ≈
        CReal.add a CReal.zero :=
    add_congr (half_add_self_equiv a) (half_neg_cancel_equiv u)
  exact Setoid.trans h0 (Setoid.trans h1 (Setoid.trans h2 (Setoid.trans h3 (CReal.add_zero a))))

#print axioms BishopSec1P.max_add_min_eq_self

-- >>>v7:I.1
-- <<<v7:I.2
structure BFunC (X : Type*) where
  toFun : X → CReal
  dom : Set X

#print axioms BishopSec1P.BFunC

namespace BFunC

def BEquiv {X : Type*} (f g : BFunC X) : Prop :=
  f.dom = g.dom ∧ ∀ x ∈ f.dom, f.toFun x ≈ g.toFun x

#print axioms BishopSec1P.BFunC.BEquiv

def absf {X : Type*} (f : BFunC X) : BFunC X :=
  ⟨fun x => CReal.abs (f.toFun x), f.dom⟩

#print axioms BishopSec1P.BFunC.absf

def smul {X : Type*} (a : CReal) (f : BFunC X) : BFunC X :=
  ⟨fun x => CReal.mul a (f.toFun x), f.dom⟩

#print axioms BishopSec1P.BFunC.smul

def add {X : Type*} (f g : BFunC X) : BFunC X :=
  ⟨fun x => CReal.add (f.toFun x) (g.toFun x), f.dom ∩ g.dom⟩

#print axioms BishopSec1P.BFunC.add

def maxC {X : Type*} (f : BFunC X) (a : CReal) : BFunC X :=
  ⟨fun x => CReal.max (f.toFun x) a, f.dom⟩

#print axioms BishopSec1P.BFunC.maxC

def posPart {X : Type*} (f : BFunC X) : BFunC X :=
  maxC f CReal.zero

#print axioms BishopSec1P.BFunC.posPart

def negPart {X : Type*} (f : BFunC X) : BFunC X :=
  ⟨fun x => CReal.neg (CReal.min (f.toFun x) CReal.zero), f.dom⟩

#print axioms BishopSec1P.BFunC.negPart

def seqSum {X : Type*} (u : Nat → BFunC X) : Nat → BFunC X
  | 0 => u 0
  | Nat.succ n => add (seqSum u n) (u (Nat.succ n))

#print axioms BishopSec1P.BFunC.seqSum

/-- min with a constant (mirror `maxC`); domain unchanged.  `min{f, a}`. -/
def minC {X : Type*} (f : BFunC X) (a : CReal) : BFunC X :=
  ⟨fun x => CReal.min (f.toFun x) a, f.dom⟩

#print axioms BishopSec1P.BFunC.minC

/-- Technical lemma used in the public import closure. -/
def cutNat {X : Type*} (n : Nat) (f : BFunC X) : BFunC X :=
  minC f (constSeq (Nat.cast n))

#print axioms BishopSec1P.BFunC.cutNat

/-- Technical lemma used in the public import closure. -/
def cutSmall {X : Type*} (n : Nat) (f : BFunC X) : BFunC X :=
  minC (absf f) (constSeq (eps n))

#print axioms BishopSec1P.BFunC.cutSmall

/-- pointwise min of two functions `min{f, g}`; domain `f.dom ∩ g.dom`. -/
def min2 {X : Type*} (f g : BFunC X) : BFunC X :=
  ⟨fun x => CReal.min (f.toFun x) (g.toFun x), f.dom ∩ g.dom⟩

#print axioms BishopSec1P.BFunC.min2

/-- Technical lemma used in the public import closure. -/
def PointwiseNonneg {X : Type*} (f : BFunC X) : Prop :=
  ∀ x : X, x ∈ f.dom → RegularSeqLe zeroSeq (f.toFun x)

#print axioms BishopSec1P.BFunC.PointwiseNonneg

/-- Technical lemma used in the public import closure. -/
structure PointwiseLE {X : Type*} (f g : BFunC X) : Prop where
  dom_eq : f.dom = g.dom
  le_val : ∀ x : X, x ∈ f.dom → RegularSeqLe (f.toFun x) (g.toFun x)

#print axioms BishopSec1P.BFunC.PointwiseLE

end BFunC

-- >>>v7:I.2
-- <<<v7:I.3
/-- Technical lemma used in the public import closure. -/
structure RepSeriesTendsto (u : Nat → CReal) (l : CReal) : Type where
  mod : Nat → Nat
  close : ∀ k n : Nat, mod k ≤ n → RepCloseAtGauge (k + 1) (u n) l

#print axioms BishopSec1P.RepSeriesTendsto

/-- Technical lemma used in the public import closure. -/
structure RepSeriesSum (a : Nat → CReal) : Type where
  sum : CReal
  tends : RepSeriesTendsto (regularSeqFinSum a) sum

#print axioms BishopSec1P.RepSeriesSum

structure PointwiseSeriesBelowC {X : Type*}
    (fs : Nat → BFunC X) (f : BFunC X) where
  x : X
  hx_f : x ∈ f.dom
  hx_fs : ∀ n : Nat, x ∈ (fs n).dom
  point_sum : RepSeriesSum (fun n => (fs n).toFun x)
  below : CReal.ltE point_sum.sum (f.toFun x)

#print axioms BishopSec1P.PointwiseSeriesBelowC

structure IntSpaceC (X : Type*) where
  L : Set (BFunC X)
  I : BFunC X → CReal
  L_resp : ∀ {f g : BFunC X}, f ∈ L → BFunC.BEquiv f g → g ∈ L
  I_resp : ∀ {f g : BFunC X}, f ∈ L → BFunC.BEquiv f g → I f ≈ I g
  add_mem : ∀ {f g : BFunC X}, f ∈ L → g ∈ L → BFunC.add f g ∈ L
  smul_mem : ∀ (a : CReal) {f : BFunC X}, f ∈ L → BFunC.smul a f ∈ L
  abs_mem : ∀ {f : BFunC X}, f ∈ L → BFunC.absf f ∈ L
  /-- Technical lemma used in the public import closure. -/
  cutConst_mem : ∀ (a : CReal) {f : BFunC X}, f ∈ L → BFunC.minC f a ∈ L
  I_add : ∀ {f g : BFunC X}, f ∈ L → g ∈ L →
    I (BFunC.add f g) ≈ CReal.add (I f) (I g)
  I_smul : ∀ (a : CReal) {f : BFunC X}, f ∈ L →
    I (BFunC.smul a f) ≈ CReal.mul a (I f)
  /-- Technical lemma used in the public import closure. -/
  cutNat_tendsto : ∀ {f : BFunC X}, f ∈ L →
    RepSeriesTendsto (fun n => I (BFunC.cutNat n f)) (I f)
  /-- Technical lemma used in the public import closure. -/
  cutSmall_tendsto : ∀ {f : BFunC X}, f ∈ L →
    RepSeriesTendsto (fun n => I (BFunC.cutSmall n f)) CReal.zero
  /-- Technical lemma used in the public import closure. -/
  I_nonneg : ∀ {f : BFunC X}, f ∈ L → BFunC.PointwiseNonneg f → RegularSeqLe zeroSeq (I f)
  continuity :
    ∀ {f : BFunC X} {fs : Nat → BFunC X},
      f ∈ L → (∀ n, fs n ∈ L) → (∀ n, BFunC.PointwiseNonneg (fs n)) →
      (hI : RepSeriesSum (fun n => I (fs n))) → CReal.ltE hI.sum (I f) →
      PointwiseSeriesBelowC fs f

#print axioms BishopSec1P.IntSpaceC

namespace IntSpaceC

variable {X : Type*} (S : IntSpaceC X)

theorem I_neg {f : BFunC X} (hf : f ∈ S.L) :
    S.I (BFunC.smul (CReal.neg CReal.one) f) ≈ CReal.neg (S.I f) := by
  exact Setoid.trans (S.I_smul (CReal.neg CReal.one) hf) (neg_one_mul_equiv (S.I f))

#print axioms BishopSec1P.IntSpaceC.I_neg

/-- Technical lemma used in the public import closure. -/
theorem I_absf_neg_eqC {f : BFunC X} (hf : f ∈ S.L) :
    S.I (BFunC.absf (BFunC.smul (CReal.neg CReal.one) f)) ≈ S.I (BFunC.absf f) := by
  refine S.I_resp (S.abs_mem (S.smul_mem (CReal.neg CReal.one) hf)) ⟨rfl, ?_⟩
  intro x _hx
  show CReal.abs (CReal.mul (CReal.neg CReal.one) (f.toFun x)) ≈ CReal.abs (f.toFun x)
  have h1 : CReal.abs (CReal.mul (CReal.neg CReal.one) (f.toFun x)) ≈
      CReal.abs (CReal.neg (f.toFun x)) :=
    abs_congr (neg_one_mul_equiv (f.toFun x))
  have h2 : CReal.abs (CReal.neg (f.toFun x)) ≈ CReal.abs (f.toFun x) := by
    change absSeq (negSeq (f.toFun x)) ≈ absSeq (f.toFun x)
    exact absSeq_negSeq_eventually (f.toFun x)
  exact Setoid.trans h1 h2

#print axioms BishopSec1P.IntSpaceC.I_absf_neg_eqC

theorem I_abs_smul_zeroC {f : BFunC X} (hf : f ∈ S.L) :
    S.I (BFunC.absf (BFunC.smul CReal.zero f)) ≈ CReal.zero := by
  have hsmul_mem : BFunC.smul CReal.zero f ∈ S.L :=
    S.smul_mem CReal.zero hf
  have hbe :
      BFunC.BEquiv (BFunC.absf (BFunC.smul CReal.zero f))
        (BFunC.smul CReal.zero f) := by
    refine ⟨rfl, ?_⟩
    intro x _hx
    have hzero : CReal.mul CReal.zero (f.toFun x) ≈ CReal.zero :=
      zero_mul_equivC (f.toFun x)
    exact Setoid.trans (abs_congr hzero)
      (Setoid.trans CReal.abs_zero (Setoid.symm hzero))
  have hresp :
      S.I (BFunC.absf (BFunC.smul CReal.zero f)) ≈
        S.I (BFunC.smul CReal.zero f) :=
    S.I_resp (S.abs_mem hsmul_mem) hbe
  have hsmul :
      S.I (BFunC.smul CReal.zero f) ≈ CReal.mul CReal.zero (S.I f) :=
    S.I_smul CReal.zero hf
  exact Setoid.trans hresp (Setoid.trans hsmul (zero_mul_equivC (S.I f)))

#print axioms BishopSec1P.IntSpaceC.I_abs_smul_zeroC

theorem I_abs_smulC (a : CReal) {f : BFunC X} (hf : f ∈ S.L) :
    S.I (BFunC.absf (BFunC.smul a f)) ≈
      CReal.mul (CReal.abs a) (S.I (BFunC.absf f)) := by
  have hbe :
      BFunC.BEquiv (BFunC.absf (BFunC.smul a f))
        (BFunC.smul (CReal.abs a) (BFunC.absf f)) := by
    refine ⟨rfl, ?_⟩
    intro x _hx
    show CReal.abs (CReal.mul a (f.toFun x)) ≈
      CReal.mul (CReal.abs a) (CReal.abs (f.toFun x))
    exact CReal.abs_mul a (f.toFun x)
  have hresp :
      S.I (BFunC.absf (BFunC.smul a f)) ≈
        S.I (BFunC.smul (CReal.abs a) (BFunC.absf f)) :=
    S.I_resp (S.abs_mem (S.smul_mem a hf)) hbe
  have hsmul :
      S.I (BFunC.smul (CReal.abs a) (BFunC.absf f)) ≈
        CReal.mul (CReal.abs a) (S.I (BFunC.absf f)) :=
    S.I_smul (CReal.abs a) (S.abs_mem hf)
  exact Setoid.trans hresp hsmul

#print axioms BishopSec1P.IntSpaceC.I_abs_smulC

theorem I_sub {f g : BFunC X} (hf : f ∈ S.L) (hg : g ∈ S.L) :
    S.I (BFunC.add f (BFunC.smul (CReal.neg CReal.one) g)) ≈
      CReal.sub (S.I f) (S.I g) := by
  have hsmul : S.I (BFunC.smul (CReal.neg CReal.one) g) ≈
      CReal.mul (CReal.neg CReal.one) (S.I g) :=
    S.I_smul (CReal.neg CReal.one) hg
  calc
    S.I (BFunC.add f (BFunC.smul (CReal.neg CReal.one) g))
        ≈ CReal.add (S.I f) (S.I (BFunC.smul (CReal.neg CReal.one) g)) :=
          S.I_add hf (S.smul_mem (CReal.neg CReal.one) hg)
    _ ≈ CReal.add (S.I f) (CReal.mul (CReal.neg CReal.one) (S.I g)) :=
          add_congr (Setoid.refl (S.I f)) hsmul
    _ ≈ CReal.sub (S.I f) (S.I g) :=
          add_neg_one_mul_right_sub_equiv (S.I f) (S.I g)

#print axioms BishopSec1P.IntSpaceC.I_sub

theorem seqSum_mem {u : Nat → BFunC X} (hu : ∀ n, u n ∈ S.L) :
    ∀ n, BFunC.seqSum u n ∈ S.L := by
  intro n
  induction n with
  | zero => exact hu 0
  | succ n ih => exact S.add_mem ih (hu (n + 1))

#print axioms BishopSec1P.IntSpaceC.seqSum_mem

theorem posPart_mem {f : BFunC X} (hf : f ∈ S.L) :
    BFunC.posPart f ∈ S.L := by
  have hmem : BFunC.smul CReal.half (BFunC.add f (BFunC.absf f)) ∈ S.L :=
    S.smul_mem CReal.half (S.add_mem hf (S.abs_mem hf))
  refine S.L_resp hmem ⟨?_, ?_⟩
  · exact Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  · intro x _
    exact Setoid.symm (max_zero_halfsum (f.toFun x))

#print axioms BishopSec1P.IntSpaceC.posPart_mem

theorem negPart_mem {f : BFunC X} (hf : f ∈ S.L) :
    BFunC.negPart f ∈ S.L := by
  have hmem :
      BFunC.smul CReal.half
          (BFunC.add (BFunC.smul (CReal.neg CReal.one) f) (BFunC.absf f)) ∈ S.L :=
    S.smul_mem CReal.half
      (S.add_mem (S.smul_mem (CReal.neg CReal.one) hf) (S.abs_mem hf))
  refine S.L_resp hmem ⟨?_, ?_⟩
  · exact Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  · intro x _
    have harg :
        CReal.add (CReal.mul (CReal.neg CReal.one) (f.toFun x))
            (CReal.abs (f.toFun x)) ≈
          CReal.add (CReal.neg (f.toFun x)) (CReal.abs (f.toFun x)) :=
      add_congr (neg_one_mul_equiv (f.toFun x)) (Setoid.refl (CReal.abs (f.toFun x)))
    calc
      CReal.mul CReal.half
          (CReal.add (CReal.mul (CReal.neg CReal.one) (f.toFun x))
            (CReal.abs (f.toFun x)))
          ≈ CReal.mul CReal.half
              (CReal.add (CReal.neg (f.toFun x)) (CReal.abs (f.toFun x))) :=
            mul_congr (Setoid.refl CReal.half) harg
      _ ≈ CReal.neg (CReal.min (f.toFun x) CReal.zero) :=
            Setoid.symm (neg_min_zero_halfsum (f.toFun x))

#print axioms BishopSec1P.IntSpaceC.negPart_mem

/-- Technical lemma used in the public import closure. -/
theorem cutNat_mem {f : BFunC X} (n : Nat) (hf : f ∈ S.L) :
    BFunC.cutNat n f ∈ S.L :=
  S.cutConst_mem (constSeq (Nat.cast n)) hf

#print axioms BishopSec1P.IntSpaceC.cutNat_mem

/-- Technical lemma used in the public import closure. -/
theorem cutSmall_mem {f : BFunC X} (n : Nat) (hf : f ∈ S.L) :
    BFunC.cutSmall n f ∈ S.L :=
  S.cutConst_mem (constSeq (eps n)) (S.abs_mem hf)

#print axioms BishopSec1P.IntSpaceC.cutSmall_mem

theorem I_absf_eq {f : BFunC X} (hf : f ∈ S.L) :
    S.I (BFunC.absf f) ≈
      CReal.add (S.I (BFunC.posPart f)) (S.I (BFunC.negPart f)) := by
  have hp := S.posPart_mem hf
  have hn := S.negPart_mem hf
  have hbe :
      BFunC.BEquiv (BFunC.absf f) (BFunC.add (BFunC.posPart f) (BFunC.negPart f)) := by
    refine ⟨?_, ?_⟩
    · exact Set.ext fun x => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
    · intro x _
      exact Setoid.symm (max_add_negmin_eq_abs (f.toFun x))
  exact Setoid.trans (S.I_resp (S.abs_mem hf) hbe) (S.I_add hp hn)

#print axioms BishopSec1P.IntSpaceC.I_absf_eq

theorem I_self_eq {f : BFunC X} (hf : f ∈ S.L) :
    S.I f ≈ CReal.sub (S.I (BFunC.posPart f)) (S.I (BFunC.negPart f)) := by
  have hp := S.posPart_mem hf
  have hn := S.negPart_mem hf
  have hnegmem := S.smul_mem (CReal.neg CReal.one) hn
  have hbe :
      BFunC.BEquiv f
        (BFunC.add (BFunC.posPart f)
          (BFunC.smul (CReal.neg CReal.one) (BFunC.negPart f))) := by
    refine ⟨?_, ?_⟩
    · exact Set.ext fun x => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
    · intro x _
      have hterm :
          CReal.mul (CReal.neg CReal.one)
              (CReal.neg (CReal.min (f.toFun x) CReal.zero)) ≈
            CReal.min (f.toFun x) CReal.zero :=
        Setoid.trans (neg_one_mul_equiv (CReal.neg (CReal.min (f.toFun x) CReal.zero)))
          (neg_neg_equiv (CReal.min (f.toFun x) CReal.zero))
      have htarget :
          CReal.add (CReal.max (f.toFun x) CReal.zero)
              (CReal.mul (CReal.neg CReal.one)
                (CReal.neg (CReal.min (f.toFun x) CReal.zero))) ≈
            CReal.add (CReal.max (f.toFun x) CReal.zero)
              (CReal.min (f.toFun x) CReal.zero) :=
        add_congr (Setoid.refl (CReal.max (f.toFun x) CReal.zero)) hterm
      exact Setoid.symm (Setoid.trans htarget (max_add_min_eq_self (f.toFun x)))
  have hsmul :
      S.I (BFunC.smul (CReal.neg CReal.one) (BFunC.negPart f)) ≈
        CReal.mul (CReal.neg CReal.one) (S.I (BFunC.negPart f)) :=
    S.I_smul (CReal.neg CReal.one) hn
  calc
    S.I f
        ≈ S.I (BFunC.add (BFunC.posPart f)
            (BFunC.smul (CReal.neg CReal.one) (BFunC.negPart f))) :=
          S.I_resp hf hbe
    _ ≈ CReal.add (S.I (BFunC.posPart f))
          (S.I (BFunC.smul (CReal.neg CReal.one) (BFunC.negPart f))) :=
          S.I_add hp hnegmem
    _ ≈ CReal.add (S.I (BFunC.posPart f))
          (CReal.mul (CReal.neg CReal.one) (S.I (BFunC.negPart f))) :=
          add_congr (Setoid.refl (S.I (BFunC.posPart f))) hsmul
    _ ≈ CReal.sub (S.I (BFunC.posPart f)) (S.I (BFunC.negPart f)) :=
          add_neg_one_mul_right_sub_equiv (S.I (BFunC.posPart f)) (S.I (BFunC.negPart f))

#print axioms BishopSec1P.IntSpaceC.I_self_eq

end IntSpaceC

-- >>>v7:I.3
-- <<<v7:I.5
abbrev SeriesSumC (a : Nat → CReal) : Type :=
  BishopRegularSeqSeriesSum a

#print axioms BishopSec1P.SeriesSumC

structure IntegrableRepC {X : Type*} (S : IntSpaceC X) : Type _ where
  fn : Nat → BFunC X
  fn_mem : ∀ n, fn n ∈ S.L
  abs_integral_sum : SeriesSumC (fun n => S.I (BFunC.absf (fn n)))
  integral_sum : SeriesSumC (fun n => S.I (fn n))

#print axioms BishopSec1P.IntegrableRepC

def IntegrableRepC.I1 {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC S) : CReal :=
  (r.integral_sum).sum

#print axioms BishopSec1P.IntegrableRepC.I1

/-- Data endpoint of representative-level completeness over the presented real.
Supplies the carried `limit` and the convergence modulus `lmod` as *data*
(structure fields), not a `Prop` existence.  This matches the prose "supplies the
carried limit and the convergence rate without choice"; the `∃` form below is now
a one-line corollary.  The witnesses come directly from the already-closed
diagonal construction `cRealRepSequenceCompleteLayer`, so no choice is used. -/
structure CRealRepLimitData (w : Nat → CReal) : Type where
  limit : CReal
  lmod : Nat → Nat
  close : ∀ k n : Nat, lmod k ≤ n → RepCloseAtGauge (k + 1) (w n) limit

def CReal.complete_repCarrying_data
    (w : Nat → CReal) (hc : CRealRepSequenceCauchyData w) :
    CRealRepLimitData w :=
  { limit := cRealRepSequenceCompleteLayer.limit w hc
    lmod  := cRealRepSequenceCompleteLayer.lmod w hc
    close := cRealRepSequenceCompleteLayer.close_to_limit w hc }

#print axioms BishopSec1P.CReal.complete_repCarrying_data

/-- Technical lemma used in the public import closure. -/
def integrableRepC_integral_complete_data {X : Type*} (S : IntSpaceC X)
    (w : Nat → IntegrableRepC S)
    (hc : CRealRepSequenceCauchyData (fun n => (w n).I1)) :
    CRealRepLimitData (fun n => (w n).I1) :=
  CReal.complete_repCarrying_data (fun n => (w n).I1) hc

#print axioms BishopSec1P.integrableRepC_integral_complete_data

/-- `∃` form of the completion endpoint, now a one-line corollary of the data
endpoint `integrableRepC_integral_complete_data`. -/
theorem integrableRepC_integral_complete {X : Type*} (S : IntSpaceC X)
    (w : Nat → IntegrableRepC S)
    (hc : CRealRepSequenceCauchyData (fun n => (w n).I1)) :
    ∃ limit : CReal, ∃ lmod : Nat → Nat,
      ∀ k n : Nat, lmod k ≤ n →
        RepCloseAtGauge (k + 1) ((w n).I1) limit :=
  let d := integrableRepC_integral_complete_data S w hc
  ⟨d.limit, d.lmod, d.close⟩

#print axioms BishopSec1P.integrableRepC_integral_complete

/-- Technical lemma used in the public import closure. -/
def repSeriesSum_of_partialCauchy {a : Nat → CReal}
    (hc : CRealRepSequenceCauchyData (regularSeqFinSum a)) : RepSeriesSum a :=
  let d := CReal.complete_repCarrying_data (regularSeqFinSum a) hc
  { sum := d.limit
    tends := { mod := d.lmod, close := d.close } }

#print axioms BishopSec1P.repSeriesSum_of_partialCauchy

theorem regularSeqLe_zero_of_nonneg {x : CReal}
    (hx : RegularSeqNonneg x) : RegularSeqLe zeroSeq x :=
  regularSeqNonneg_of_eventual (subSeq_zero_right_eventually x) hx

theorem regularSeqNonneg_of_zero_le {x : CReal}
    (hx : RegularSeqLe zeroSeq x) : RegularSeqNonneg x :=
  regularSeqNonneg_of_eventual
    (relEventually_symm (subSeq x zeroSeq) x
      (subSeq_zero_right_eventually x))
    hx

namespace IntSpaceC

variable {X : Type*} (S : IntSpaceC X)

theorem I_mono {f g : BFunC X}
    (hf : f ∈ S.L) (hg : g ∈ S.L) (hfg : BFunC.PointwiseLE f g) :
    RegularSeqLe (S.I f) (S.I g) := by
  let neg_f : BFunC X := BFunC.smul (CReal.neg CReal.one) f
  let diff : BFunC X := BFunC.add g neg_f
  have hneg_mem : neg_f ∈ S.L := by
    simpa [neg_f] using S.smul_mem (CReal.neg CReal.one) hf
  have hdiff_mem : diff ∈ S.L := by
    simpa [diff] using S.add_mem hg hneg_mem
  have hdiff_nn : BFunC.PointwiseNonneg diff := by
    intro x hx
    have hxf : x ∈ f.dom := by
      have hx' : x ∈ g.dom ∩ f.dom := by
        simpa [diff, neg_f, BFunC.add, BFunC.smul] using hx
      exact hx'.2
    have hdiff_val :
        relEventually
          (diff.toFun x)
          (subSeq (g.toFun x) (f.toFun x)) := by
      change relEventually
        (addSeq (g.toFun x)
          (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq) (f.toFun x)))
        (subSeq (g.toFun x) (f.toFun x))
      exact addSeq_negOneMul_right_eventually_subSeq
        cRatScalarMulArch (g.toFun x) (f.toFun x)
    have hdiff_zero_to_sub :
        relEventually
          (subSeq (diff.toFun x) zeroSeq)
          (subSeq (g.toFun x) (f.toFun x)) :=
      relEventually_trans
        (subSeq (diff.toFun x) zeroSeq)
        (diff.toFun x)
        (subSeq (g.toFun x) (f.toFun x))
        (subSeq_zero_right_eventually (diff.toFun x))
        hdiff_val
    change RegularSeqNonneg (subSeq (diff.toFun x) zeroSeq)
    exact regularSeqNonneg_of_eventual hdiff_zero_to_sub (hfg.le_val x hxf)
  have hI_diff_nonneg : RegularSeqLe zeroSeq (S.I diff) :=
    S.I_nonneg hdiff_mem hdiff_nn
  have hI_to_sub :
      relEventually
        (S.I diff)
        (subSeq (S.I g) (S.I f)) := by
    simpa [diff, neg_f] using S.I_sub hg hf
  have hzero_sub : RegularSeqLe zeroSeq (subSeq (S.I g) (S.I f)) :=
    regularSeqLe_of_right_eventual hI_to_sub hI_diff_nonneg
  change RegularSeqNonneg (subSeq (S.I g) (S.I f))
  exact regularSeqNonneg_of_zero_le hzero_sub

#print axioms BishopSec1P.IntSpaceC.I_mono

theorem I_mono' {f g : BFunC X}
    (hf : f ∈ S.L) (hg : g ∈ S.L)
    (hle : ∀ x, x ∈ f.dom → x ∈ g.dom →
      RegularSeqLe (f.toFun x) (g.toFun x)) :
    RegularSeqLe (S.I f) (S.I g) := by
  let neg_f : BFunC X := BFunC.smul (CReal.neg CReal.one) f
  let diff : BFunC X := BFunC.add g neg_f
  have hneg_mem : neg_f ∈ S.L := by
    simpa [neg_f] using S.smul_mem (CReal.neg CReal.one) hf
  have hdiff_mem : diff ∈ S.L := by
    simpa [diff] using S.add_mem hg hneg_mem
  have hdiff_nn : BFunC.PointwiseNonneg diff := by
    intro x hx
    have hxgf : x ∈ g.dom ∩ f.dom := by
      simpa [diff, neg_f, BFunC.add, BFunC.smul] using hx
    have hxg : x ∈ g.dom := hxgf.1
    have hxf : x ∈ f.dom := hxgf.2
    have hdiff_val :
        relEventually
          (diff.toFun x)
          (subSeq (g.toFun x) (f.toFun x)) := by
      change relEventually
        (addSeq (g.toFun x)
          (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq) (f.toFun x)))
        (subSeq (g.toFun x) (f.toFun x))
      exact addSeq_negOneMul_right_eventually_subSeq
        cRatScalarMulArch (g.toFun x) (f.toFun x)
    have hdiff_zero_to_sub :
        relEventually
          (subSeq (diff.toFun x) zeroSeq)
          (subSeq (g.toFun x) (f.toFun x)) :=
      relEventually_trans
        (subSeq (diff.toFun x) zeroSeq)
        (diff.toFun x)
        (subSeq (g.toFun x) (f.toFun x))
        (subSeq_zero_right_eventually (diff.toFun x))
        hdiff_val
    change RegularSeqNonneg (subSeq (diff.toFun x) zeroSeq)
    exact regularSeqNonneg_of_eventual hdiff_zero_to_sub (hle x hxf hxg)
  have hI_diff_nonneg : RegularSeqLe zeroSeq (S.I diff) :=
    S.I_nonneg hdiff_mem hdiff_nn
  have hI_to_sub :
      relEventually
        (S.I diff)
        (subSeq (S.I g) (S.I f)) := by
    simpa [diff, neg_f] using S.I_sub hg hf
  have hzero_sub : RegularSeqLe zeroSeq (subSeq (S.I g) (S.I f)) :=
    regularSeqLe_of_right_eventual hI_to_sub hI_diff_nonneg
  change RegularSeqNonneg (subSeq (S.I g) (S.I f))
  exact regularSeqNonneg_of_zero_le hzero_sub

#print axioms BishopSec1P.IntSpaceC.I_mono'

/-- The integral of an absolute-value function is nonnegative. -/
theorem I_absf_nonneg {g : BFunC X} (hg : g ∈ S.L) :
    RegularSeqNonneg (S.I (BFunC.absf g)) := by
  have hpn : BFunC.PointwiseNonneg (BFunC.absf g) := by
    intro x _hx
    simpa [BFunC.absf] using absSeq_nonnegative_regularSeqLe (g.toFun x)
  exact regularSeqNonneg_of_zero_le (S.I_nonneg (S.abs_mem hg) hpn)

#print axioms BishopSec1P.IntSpaceC.I_absf_nonneg

/-- Absolute value of an integral is bounded by the integral of the absolute value. -/
theorem I_abs_ge {f : BFunC X} (hf : f ∈ S.L) :
    RegularSeqLe (CReal.abs (S.I f)) (S.I (BFunC.absf f)) := by
  have habs : BFunC.absf f ∈ S.L := S.abs_mem hf
  have hle1 : BFunC.PointwiseLE f (BFunC.absf f) :=
    { dom_eq := rfl
      le_val := by
        intro x _hx
        simpa [BFunC.absf, CReal.abs] using
          base_le_abs_base_regularSeqLe (f.toFun x) }
  have hle2 :
      BFunC.PointwiseLE
        (BFunC.smul (CReal.neg CReal.one) f) (BFunC.absf f) :=
    { dom_eq := rfl
      le_val := by
        intro x _hx
        have hneg :
            RegularSeqLe (CReal.neg (f.toFun x)) (CReal.abs (f.toFun x)) :=
          by
            change RegularSeqLe (negSeq (f.toFun x)) (absSeq (f.toFun x))
            exact regularSeqLe_of_right_eventual
              (absSeq_negSeq_eventually (f.toFun x))
              (base_le_abs_base_regularSeqLe (negSeq (f.toFun x)))
        have hmul :
            (BFunC.smul (CReal.neg CReal.one) f).toFun x ≈
              CReal.neg (f.toFun x) := by
          simpa [BFunC.smul] using neg_one_mul_equiv (f.toFun x)
        exact regularSeqLe_of_left_eventual hmul hneg }
  have hI1 : RegularSeqLe (S.I f) (S.I (BFunC.absf f)) :=
    S.I_mono hf habs hle1
  have hI2 :
      RegularSeqLe
        (S.I (BFunC.smul (CReal.neg CReal.one) f))
        (S.I (BFunC.absf f)) :=
    S.I_mono (S.smul_mem (CReal.neg CReal.one) hf) habs hle2
  have hI2' : RegularSeqLe (CReal.neg (S.I f)) (S.I (BFunC.absf f)) :=
    regularSeqLe_of_left_eventual (Setoid.symm (S.I_neg hf)) hI2
  exact regularSeq_abs_le_of_two_sided (S.I f) (S.I (BFunC.absf f)) hI1 hI2'

#print axioms BishopSec1P.IntSpaceC.I_abs_ge

end IntSpaceC

theorem regularSeqNonneg_zero : RegularSeqNonneg zeroSeq :=
  regularSeqNonneg_of_zero_le (regularSeqLe_refl zeroSeq)

theorem regularSeqNonneg_add {x y : CReal}
    (hx : RegularSeqNonneg x) (hy : RegularSeqNonneg y) :
    RegularSeqNonneg (addSeq x y) := by
  have h0x : RegularSeqLe zeroSeq x := regularSeqLe_zero_of_nonneg hx
  have h0y : RegularSeqLe zeroSeq y := regularSeqLe_zero_of_nonneg hy
  have h0zy : RegularSeqLe zeroSeq (addSeq zeroSeq y) :=
    regularSeqLe_of_right_eventual
      (relEventually_symm (addSeq zeroSeq y) y
        (addSeq_zero_left_eventually y))
      h0y
  have hzyxy : RegularSeqLe (addSeq zeroSeq y) (addSeq x y) :=
    addSeq_monotone_left_regularSeqLe zeroSeq x y h0x
  exact regularSeqNonneg_of_zero_le (regularSeqLe_trans h0zy hzyxy)

theorem regularSeqLe_add {x x' y y' : CReal}
    (hxx : RegularSeqLe x x') (hyy : RegularSeqLe y y') :
    RegularSeqLe (addSeq x y) (addSeq x' y') := by
  have hleft : RegularSeqLe (addSeq x y) (addSeq x' y) :=
    addSeq_monotone_left_regularSeqLe x x' y hxx
  have hright0 : RegularSeqLe (addSeq y x') (addSeq y' x') :=
    addSeq_monotone_left_regularSeqLe y y' x' hyy
  have hright1 : RegularSeqLe (addSeq x' y) (addSeq y' x') :=
    regularSeqLe_of_left_eventual (addSeq_comm_eventually x' y) hright0
  have hright : RegularSeqLe (addSeq x' y) (addSeq x' y') :=
    regularSeqLe_of_right_eventual (addSeq_comm_eventually y' x') hright1
  exact regularSeqLe_trans hleft hright

theorem regularSeqLe_neg_nonpos_of_nonneg {x : CReal}
    (hx : RegularSeqNonneg x) : RegularSeqLe (negSeq x) zeroSeq := by
  have hzx : relEventually (subSeq zeroSeq (negSeq x)) x :=
    relEventually_trans
      (subSeq zeroSeq (negSeq x))
      (negSeq (negSeq x))
      x
      (subSeq_zero_left_eventually (negSeq x))
      (negSeq_negSeq_eventually x)
  exact regularSeqNonneg_of_eventual hzx hx

theorem absSeq_subSeq_comm_eventually (x y : CReal) :
    relEventually (absSeq (subSeq x y)) (absSeq (subSeq y x)) := by
  have h0 : relEventually (subSeq x y) (negSeq (subSeq y x)) :=
    subSeq_comm_neg_eventually x y
  have h1 : relEventually (absSeq (subSeq x y))
      (absSeq (negSeq (subSeq y x))) :=
    absSeq_respects_eventually (subSeq x y) (negSeq (subSeq y x)) h0
  have h2 : relEventually (absSeq (negSeq (subSeq y x)))
      (absSeq (subSeq y x)) :=
    absSeq_negSeq_eventually (subSeq y x)
  exact relEventually_trans _ _ _ h1 h2

theorem regularSeqFinSum_gap_succ_eventually
    (u : Nat → CReal) (m d : Nat) :
    relEventually
      (subSeq (regularSeqFinSum u (m + (d + 1))) (regularSeqFinSum u m))
      (addSeq (subSeq (regularSeqFinSum u (m + d)) (regularSeqFinSum u m))
        (u (m + d + 1))) := by
  simpa [regularSeqFinSum, Nat.add_assoc] using
    subSeq_add_left_shift_eventually
      (regularSeqFinSum u (m + d)) (u (m + d + 1)) (regularSeqFinSum u m)

theorem partialSum_gap {a b : Nat → CReal}
    (ha : ∀ n, RegularSeqNonneg (a n))
    (hab : ∀ n, RegularSeqLe (a n) (b n)) :
    ∀ m d : Nat, RegularSeqNonneg
        (subSeq (regularSeqFinSum a (m + d)) (regularSeqFinSum a m)) ∧
      RegularSeqLe
        (subSeq (regularSeqFinSum a (m + d)) (regularSeqFinSum a m))
        (subSeq (regularSeqFinSum b (m + d)) (regularSeqFinSum b m)) := by
  intro m d
  induction d with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa using (regularSeqLe_refl (regularSeqFinSum a m) :
          RegularSeqLe (regularSeqFinSum a m) (regularSeqFinSum a m))
      · have hleft : relEventually
            (subSeq (regularSeqFinSum a (m + 0)) (regularSeqFinSum a m))
            zeroSeq := by
          simpa using subSeq_self_eventually_law (regularSeqFinSum a m)
        have hright : relEventually
            (subSeq (regularSeqFinSum b (m + 0)) (regularSeqFinSum b m))
            zeroSeq := by
          simpa using subSeq_self_eventually_law (regularSeqFinSum b m)
        have hzright : RegularSeqLe zeroSeq
            (subSeq (regularSeqFinSum b (m + 0)) (regularSeqFinSum b m)) :=
          regularSeqLe_of_right_eventual
            (relEventually_symm _ _ hright)
            (regularSeqLe_refl zeroSeq)
        exact regularSeqLe_of_left_eventual hleft hzright
  | succ d ih =>
      let ga := subSeq (regularSeqFinSum a (m + d)) (regularSeqFinSum a m)
      let gb := subSeq (regularSeqFinSum b (m + d)) (regularSeqFinSum b m)
      have haev := regularSeqFinSum_gap_succ_eventually a m d
      have hbev := regularSeqFinSum_gap_succ_eventually b m d
      refine ⟨?_, ?_⟩
      · have hbody : RegularSeqNonneg (addSeq ga (a (m + d + 1))) :=
          regularSeqNonneg_add ih.1 (ha (m + d + 1))
        exact regularSeqNonneg_of_eventual (by simpa [ga] using haev) hbody
      · have hbody : RegularSeqLe (addSeq ga (a (m + d + 1)))
            (addSeq gb (b (m + d + 1))) :=
          regularSeqLe_add ih.2 (hab (m + d + 1))
        have hleft : RegularSeqLe
            (subSeq (regularSeqFinSum a (m + (d + 1))) (regularSeqFinSum a m))
            (addSeq gb (b (m + d + 1))) :=
          regularSeqLe_of_left_eventual (by simpa [ga] using haev) hbody
        exact regularSeqLe_of_right_eventual
          (relEventually_symm _ _ (by simpa [gb] using hbev)) hleft

theorem partialSum_absdiff_aux {a b : Nat → CReal}
    (ha : ∀ n, RegularSeqNonneg (a n))
    (hab : ∀ n, RegularSeqLe (a n) (b n)) (m d : Nat) :
    RegularSeqLe
      (absSeq (subSeq (regularSeqFinSum a m) (regularSeqFinSum a (m + d))))
      (absSeq (subSeq (regularSeqFinSum b m) (regularSeqFinSum b (m + d)))) := by
  let ga := subSeq (regularSeqFinSum a (m + d)) (regularSeqFinSum a m)
  let gb := subSeq (regularSeqFinSum b (m + d)) (regularSeqFinSum b m)
  obtain ⟨hga_nonneg, hga_gb⟩ := partialSum_gap ha hab m d
  have hb_nonneg : ∀ n, RegularSeqNonneg (b n) := fun n =>
    regularSeqNonneg_of_zero_le
      (regularSeqLe_trans (regularSeqLe_zero_of_nonneg (ha n)) (hab n))
  let revA := subSeq (regularSeqFinSum a m) (regularSeqFinSum a (m + d))
  let revB := subSeq (regularSeqFinSum b m) (regularSeqFinSum b (m + d))
  have hgb_abs_gb : RegularSeqLe gb (absSeq gb) := base_le_abs_base_regularSeqLe gb
  have habs_gb_revB : relEventually (absSeq gb) (absSeq revB) := by
    simpa [gb, revB] using
      absSeq_subSeq_comm_eventually (regularSeqFinSum b (m + d)) (regularSeqFinSum b m)
  have hgb_abs_revB : RegularSeqLe gb (absSeq revB) :=
    regularSeqLe_of_right_eventual habs_gb_revB hgb_abs_gb
  have hga_abs_revB : RegularSeqLe ga (absSeq revB) :=
    regularSeqLe_trans hga_gb hgb_abs_revB
  have hrevA_nonpos : RegularSeqLe revA zeroSeq := by
    have hneg_ga : RegularSeqLe (negSeq ga) zeroSeq :=
      regularSeqLe_neg_nonpos_of_nonneg hga_nonneg
    exact regularSeqLe_of_left_eventual
      (by simpa [ga, revA] using
        subSeq_comm_neg_eventually (regularSeqFinSum a m) (regularSeqFinSum a (m + d)))
      hneg_ga
  have hrevA_absB : RegularSeqLe revA (absSeq revB) :=
    regularSeqLe_trans hrevA_nonpos (absSeq_nonnegative_regularSeqLe revB)
  have hneg_revA_absB : RegularSeqLe (negSeq revA) (absSeq revB) := by
    exact regularSeqLe_of_left_eventual
      (relEventually_symm _ _ (by simpa [ga, revA] using
        subSeq_comm_neg_eventually (regularSeqFinSum a (m + d)) (regularSeqFinSum a m)))
      hga_abs_revB
  simpa [revA, revB] using
    regularSeq_abs_le_of_two_sided revA (absSeq revB) hrevA_absB hneg_revA_absB

theorem partialSum_absdiff_le {a b : Nat → CReal}
    (ha : ∀ n, RegularSeqNonneg (a n))
    (hab : ∀ n, RegularSeqLe (a n) (b n)) (m n : Nat) :
    RegularSeqLe
      (absSeq (subSeq (regularSeqFinSum a m) (regularSeqFinSum a n)))
      (absSeq (subSeq (regularSeqFinSum b m) (regularSeqFinSum b n))) := by
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
    subst n
    exact partialSum_absdiff_aux ha hab m d
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
    subst m
    have haux := partialSum_absdiff_aux ha hab n d
    have hleft : RegularSeqLe
        (absSeq (subSeq (regularSeqFinSum a (n + d)) (regularSeqFinSum a n)))
        (absSeq (subSeq (regularSeqFinSum b n) (regularSeqFinSum b (n + d)))) :=
      regularSeqLe_of_left_eventual
        (absSeq_subSeq_comm_eventually (regularSeqFinSum a (n + d)) (regularSeqFinSum a n))
        haux
    exact regularSeqLe_of_right_eventual
      (absSeq_subSeq_comm_eventually (regularSeqFinSum b n) (regularSeqFinSum b (n + d)))
      hleft

theorem repCloseAtGauge_of_absdiff_le
    {x y u v : CReal} (k : Nat)
    (hle : RegularSeqLe (absSeq (subSeq x y)) (absSeq (subSeq u v)))
    (hclose : RepCloseAtGauge (k + 1) u v) :
    RepCloseAtGauge k x y := by
  rcases hclose with ⟨N, hN⟩
  have hb_lt : regularSeqLtData (absSeq (subSeq u v)) (constSeq (eps k)) := by
    refine ⟨k + 2, N, ?_⟩
    intro n hn
    have hle_point : BishopCReal.Le
        (BishopC.COF_core.abs (u.val (n + 2) - v.val (n + 2))) (eps (k + 1)) :=
      hN (n + 2) (Nat.le_trans hn (Nat.le_add_right n 2))
    have hgap := scalar_eps_gap_of_le_succ
      (a := BishopC.COF_core.abs (u.val (n + 2) - v.val (n + 2))) k hle_point
    simpa [subSeq, subVal, constSeq, constVal, absSeq, absVal, addIndex]
      using hgap
  have ha_lt : regularSeqLtData (absSeq (subSeq x y)) (constSeq (eps k)) :=
    regularSeqStrictUpperTransfer.from_le_lt hle hb_lt
  exact repCloseAtGauge_of_absGap x y k ha_lt.toProp

def repIsCauchy_of_tendsto {v : Nat → CReal} {l : CReal}
    (h : RepSeriesTendsto v l) : CRealRepSequenceCauchyData v where
  cmod := fun k => h.mod (k + 1)
  close_eventually := by
    intro k m n hm hn
    have hml : RepCloseAtGauge ((k + 1) + 1) (v m) l :=
      h.close (k + 1) m hm
    have hnl : RepCloseAtGauge ((k + 1) + 1) (v n) l :=
      h.close (k + 1) n hn
    have htri : RepCloseAtGauge (k + 1) (v m) (v n) :=
      repCloseAtGauge_triangle_succ (k + 1) hml (repCloseAtGauge_symm hnl)
    exact repCloseAtGauge_weaken (Nat.le_succ k) htri

def repSeriesSum_comparison {a b : Nat → CReal}
    (ha : ∀ n, RegularSeqNonneg (a n))
    (hab : ∀ n, RegularSeqLe (a n) (b n))
    (hb : RepSeriesSum b) : RepSeriesSum a :=
  let hbcau := repIsCauchy_of_tendsto hb.tends
  repSeriesSum_of_partialCauchy
    { cmod := fun k => hbcau.cmod (k + 1)
      close_eventually := fun k m n hm hn =>
        repCloseAtGauge_of_absdiff_le k
          (partialSum_absdiff_le ha hab m n)
          (hbcau.close_eventually (k + 1) m n hm hn) }

#print axioms BishopSec1P.regularSeqLe_zero_of_nonneg
#print axioms BishopSec1P.regularSeqNonneg_of_zero_le
#print axioms BishopSec1P.regularSeqNonneg_zero
#print axioms BishopSec1P.regularSeqNonneg_add
#print axioms BishopSec1P.regularSeqLe_add
#print axioms BishopSec1P.regularSeqLe_neg_nonpos_of_nonneg
#print axioms BishopSec1P.absSeq_subSeq_comm_eventually
#print axioms BishopSec1P.regularSeqFinSum_gap_succ_eventually
#print axioms BishopSec1P.partialSum_gap
#print axioms BishopSec1P.partialSum_absdiff_aux
#print axioms BishopSec1P.partialSum_absdiff_le
#print axioms BishopSec1P.repCloseAtGauge_of_absdiff_le
#print axioms BishopSec1P.repIsCauchy_of_tendsto
#print axioms BishopSec1P.repSeriesSum_comparison

/-- Triangle inequality in the `RegularSeqLe` surface:
`|x + y| <= |x| + |y|`. -/
theorem regularSeqLe_abs_add (x y : CReal) :
    RegularSeqLe (absSeq (addSeq x y)) (addSeq (absSeq x) (absSeq y)) := by
  apply regularSeqLe_of_not_ltQuot
  change ¬ ltQuot
    (mkQuot (addSeq (absSeq x) (absSeq y)))
    (mkQuot (absSeq (addSeq x y)))
  rw [mkQuot_addSeq_eq_addQuot]
  change ¬ ltQuot
    (addQuot (absQuot (mkQuot x)) (absQuot (mkQuot y)))
    (absQuot (mkQuot (addSeq x y)))
  rw [mkQuot_addSeq_eq_addQuot]
  exact abs_add_leQuot (mkQuot x) (mkQuot y)

#print axioms BishopSec1P.regularSeqLe_abs_add

/-- Subtracting the left summand from an additive upper bound:
`x <= y + z` implies `x - y <= z`. -/
theorem regularSeqLe_sub_of_le_add {x y z : CReal}
    (hxy : RegularSeqLe x (addSeq y z)) :
    RegularSeqLe (subSeq x y) z := by
  have hmono :
      RegularSeqLe
        (subSeq x y)
        (subSeq (addSeq y z) y) :=
    subSeq_monotone_left_regularSeqLe x (addSeq y z) y hxy
  exact
    regularSeqLe_of_right_eventual
      (subSeq_add_left_cancel_eventually y z)
      hmono

#print axioms BishopSec1P.regularSeqLe_sub_of_le_add

/-- Presented reverse triangle inequality for absolute values:
`||a| - |b|| <= |a - b|`. -/
theorem regularSeqLe_abs_abs_sub_abs (a b : CReal) :
    RegularSeqLe
      (absSeq (subSeq (absSeq a) (absSeq b)))
      (absSeq (subSeq a b)) := by
  let d : CReal := absSeq (subSeq a b)
  have habs_a_le :
      RegularSeqLe (absSeq a) (addSeq d (absSeq b)) := by
    have hcancel :
        relEventually (addSeq (subSeq a b) b) a :=
      addSeq_sub_right_cancel_eventually a b
    have habs_cancel :
        relEventually
          (absSeq (addSeq (subSeq a b) b))
          (absSeq a) :=
      absSeq_respects_eventually
        (addSeq (subSeq a b) b) a hcancel
    exact regularSeqLe_of_left_eventual
      (relEventually_symm _ _ habs_cancel)
      (by simpa [d] using regularSeqLe_abs_add (subSeq a b) b)
  have habs_a_le_comm :
      RegularSeqLe (absSeq a) (addSeq (absSeq b) d) :=
    regularSeqLe_of_right_eventual
      (addSeq_comm_eventually d (absSeq b)) habs_a_le
  have hupper :
      RegularSeqLe (subSeq (absSeq a) (absSeq b)) d :=
    regularSeqLe_sub_of_le_add habs_a_le_comm
  have hneg :
      RegularSeqLe (negSeq (subSeq (absSeq a) (absSeq b))) d := by
    let d' : CReal := absSeq (subSeq b a)
    have habs_b_le :
        RegularSeqLe (absSeq b) (addSeq d' (absSeq a)) := by
      have hcancel :
          relEventually (addSeq (subSeq b a) a) b :=
        addSeq_sub_right_cancel_eventually b a
      have habs_cancel :
          relEventually
            (absSeq (addSeq (subSeq b a) a))
            (absSeq b) :=
        absSeq_respects_eventually
          (addSeq (subSeq b a) a) b hcancel
      exact regularSeqLe_of_left_eventual
        (relEventually_symm _ _ habs_cancel)
        (by simpa [d'] using regularSeqLe_abs_add (subSeq b a) a)
    have habs_b_le_comm :
        RegularSeqLe (absSeq b) (addSeq (absSeq a) d') :=
      regularSeqLe_of_right_eventual
        (addSeq_comm_eventually d' (absSeq a)) habs_b_le
    have hlower :
        RegularSeqLe (subSeq (absSeq b) (absSeq a)) d' :=
      regularSeqLe_sub_of_le_add habs_b_le_comm
    have hleft :
        relEventually
          (negSeq (subSeq (absSeq a) (absSeq b)))
          (subSeq (absSeq b) (absSeq a)) :=
      relEventually_symm _ _
        (subSeq_comm_neg_eventually (absSeq b) (absSeq a))
    have hright : relEventually d' d := by
      simpa [d, d'] using absSeq_subSeq_comm_eventually b a
    exact regularSeqLe_of_right_eventual hright
      (regularSeqLe_of_left_eventual hleft hlower)
  simpa [d] using
    regularSeq_abs_le_of_two_sided
      (subSeq (absSeq a) (absSeq b)) d hupper hneg

#print axioms BishopSec1P.regularSeqLe_abs_abs_sub_abs

theorem CReal.abs_min_sub_min_le (a b c : CReal) :
    RegularSeqLe
      (CReal.abs (CReal.sub (CReal.min a c) (CReal.min b c)))
      (CReal.abs (CReal.sub a b)) := by
  let A := cRatScalarMulArch
  have left_mono :
      ∀ x y z : RegularSeq, RegularSeqLe x y →
        RegularSeqLe (minSeqWith A x z) (minSeqWith A y z) := by
    intro x y z hxy
    exact
      minSeqWith_monotone_left_regularSeqLe_of_strict_backward
        A
        (fun x y z hmin =>
          minSeqWith_strict_backward_of_same_sample_expansion
            A
            (fun x y z hmin =>
              minSeqWith_same_sample_expansion_of_two_sample_alignment
                A
                (fun x y z =>
                  twoSampleAlignment_of_commonMaxTransport
                    x y z (commonMaxMinHalfsumTransport_closed x y z))
                x y z hmin)
            x y z hmin)
        x y z hxy
  have right_mono :
      ∀ x y z : RegularSeq, RegularSeqLe y z →
        RegularSeqLe (minSeqWith A x y) (minSeqWith A x z) := by
    intro x y z hyz
    exact
      minSeqWith_monotone_right_regularSeqLe_from_left
        A left_mono x y z hyz
  have translate :
      ∀ x d z : RegularSeq,
        relEventually
          (minSeqWith A (addSeq x d) z)
          (addSeq (minSeqWith A x (subSeq z d)) d) := by
    intro x d z
    exact
      minSeqWith_translate_right_eventually_from_body
        A x d z
        (minSeqBody_translate_right_eventually_from_sum
          x d z (minSeqSum_translate_right_eventually x d z))
  have shift_bound :
      ∀ x d z : RegularSeq, RegularSeqLe zeroSeq d →
        RegularSeqLe
          (minSeqWith A (addSeq x d) z)
          (addSeq (minSeqWith A x z) d) := by
    intro x d z hd
    have htrans :
        RegularSeqLe
          (minSeqWith A (addSeq x d) z)
          (addSeq (minSeqWith A x (subSeq z d)) d) :=
      regularSeqLe_of_relEventually (translate x d z)
    have hzd : RegularSeqLe (subSeq z d) z :=
      regularSeqLe_sub_right_self_of_nonneg z d hd
    have hmin :
        RegularSeqLe
          (minSeqWith A x (subSeq z d))
          (minSeqWith A x z) :=
      right_mono x (subSeq z d) z hzd
    have hadd :
        RegularSeqLe
          (addSeq (minSeqWith A x (subSeq z d)) d)
          (addSeq (minSeqWith A x z) d) :=
      addSeq_monotone_left_regularSeqLe
        (minSeqWith A x (subSeq z d)) (minSeqWith A x z) d hmin
    exact regularSeqLe_trans htrans hadd
  have sub_le_of_add :
      ∀ x y z : RegularSeq,
        RegularSeqLe x (addSeq y z) →
          RegularSeqLe (subSeq x y) z := by
    intro x y z hxy
    have hmono :
        RegularSeqLe
          (subSeq x y)
          (subSeq (addSeq y z) y) :=
      subSeq_monotone_left_regularSeqLe x (addSeq y z) y hxy
    exact
      regularSeqLe_of_right_eventual
        (subSeq_add_left_cancel_eventually y z)
        hmono
  let delta : RegularSeq := absSeq (subSeq a b)
  have hself :
      RegularSeqLe a (addSeq b delta) := by
    simpa [delta] using self_le_base_plus_abs_tail_regularSeqLe a b
  have hmin_upper :
      RegularSeqLe
        (minSeqWith A a c)
        (minSeqWith A (addSeq b delta) c) :=
    left_mono a (addSeq b delta) c hself
  have hshift_upper :
      RegularSeqLe
        (minSeqWith A (addSeq b delta) c)
        (addSeq (minSeqWith A b c) delta) :=
    shift_bound b delta c
      (by simpa [delta] using absSeq_nonnegative_regularSeqLe (subSeq a b))
  have hupper_add :
      RegularSeqLe
        (minSeqWith A a c)
        (addSeq (minSeqWith A b c) delta) :=
    regularSeqLe_trans hmin_upper hshift_upper
  have hupper :
      RegularSeqLe
        (subSeq (minSeqWith A a c) (minSeqWith A b c))
        delta :=
    sub_le_of_add (minSeqWith A a c) (minSeqWith A b c) delta hupper_add
  let delta' : RegularSeq := absSeq (subSeq b a)
  have hself' :
      RegularSeqLe b (addSeq a delta') := by
    simpa [delta'] using self_le_base_plus_abs_tail_regularSeqLe b a
  have hmin_lower :
      RegularSeqLe
        (minSeqWith A b c)
        (minSeqWith A (addSeq a delta') c) :=
    left_mono b (addSeq a delta') c hself'
  have hshift_lower :
      RegularSeqLe
        (minSeqWith A (addSeq a delta') c)
        (addSeq (minSeqWith A a c) delta') :=
    shift_bound a delta' c
      (by simpa [delta'] using absSeq_nonnegative_regularSeqLe (subSeq b a))
  have hlower_add :
      RegularSeqLe
        (minSeqWith A b c)
        (addSeq (minSeqWith A a c) delta') :=
    regularSeqLe_trans hmin_lower hshift_lower
  have hlower_sub :
      RegularSeqLe
        (subSeq (minSeqWith A b c) (minSeqWith A a c))
        delta' :=
    sub_le_of_add (minSeqWith A b c) (minSeqWith A a c) delta' hlower_add
  have hneg :
      RegularSeqLe
        (negSeq (subSeq (minSeqWith A a c) (minSeqWith A b c)))
        delta := by
    have hleft :
        relEventually
          (negSeq (subSeq (minSeqWith A a c) (minSeqWith A b c)))
          (subSeq (minSeqWith A b c) (minSeqWith A a c)) :=
      relEventually_symm
        (subSeq (minSeqWith A b c) (minSeqWith A a c))
        (negSeq (subSeq (minSeqWith A a c) (minSeqWith A b c)))
        (subSeq_comm_neg_eventually (minSeqWith A b c) (minSeqWith A a c))
    have hright : relEventually delta' delta := by
      simpa [delta, delta'] using absSeq_subSeq_comm_eventually b a
    exact regularSeqLe_of_right_eventual hright
      (regularSeqLe_of_left_eventual hleft hlower_sub)
  have habs :
      RegularSeqLe
        (absSeq (subSeq (minSeqWith A a c) (minSeqWith A b c)))
        delta :=
    regularSeq_abs_le_of_two_sided
      (subSeq (minSeqWith A a c) (minSeqWith A b c))
      delta hupper hneg
  simpa [A, delta, CReal.abs, CReal.sub, CReal.min] using habs

#print axioms BishopSec1P.CReal.abs_min_sub_min_le

theorem abs_min_sub_min_leC (a b c : CReal) :
    RegularSeqLe
      (CReal.abs (CReal.sub (CReal.min a c) (CReal.min b c)))
      (CReal.abs (CReal.sub a b)) :=
  CReal.abs_min_sub_min_le a b c

#print axioms BishopSec1P.abs_min_sub_min_leC

/-- The presented minimum is below its left argument. -/
theorem CReal.min_le_leftC (a b : CReal) :
    RegularSeqLe (CReal.min a b) a := by
  let d : CReal := subSeq a b
  let body : CReal := subSeq (absSeq d) (negSeq d)
  have hhalf_nonneg : ¬ CReal.ltE CReal.half CReal.zero := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero
      (CReal.ltE_trans CReal.half_pos_E hlt)
  have hbody_nonneg : RegularSeqNonneg body := by
    change RegularSeqLe (negSeq d) (absSeq d)
    apply regularSeqLe_of_not_ltQuot
    change ¬ CReal.ltE (absSeq d) (negSeq d)
    exact CReal.neg_le_abs_E d
  have hbody_not_lt : ¬ CReal.ltE body CReal.zero := by
    change RegularSeqNonneg body
    exact hbody_nonneg
  have hprod_nonneg : RegularSeqNonneg (CReal.mul CReal.half body) := by
    change ¬ CReal.ltE (CReal.mul CReal.half body) CReal.zero
    exact CReal.mul_nonneg_E hhalf_nonneg hbody_not_lt
  have hto_prod :
      relEventually (subSeq a (CReal.min a b))
        (CReal.mul CReal.half body) := by
    have hq :
        mkQuot (subSeq a (CReal.min a b)) =
          mkQuot (CReal.mul CReal.half body) := by
      change subQuot (mkQuot a)
          (mkQuot (minSeqWith cRatScalarMulArch a b)) =
        mulQuotConcreteWith cRatScalarMulArch halfQuot
          (subQuot (absQuot (subQuot (mkQuot a) (mkQuot b)))
            (negQuot (subQuot (mkQuot a) (mkQuot b))))
      rw [mkQuot_minSeqWith_eq_minQuotCOFWith cRatScalarMulArch a b]
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let D : CRealQuot := A - B
      let U : CRealQuot := absQuot D
      change A - (halfQuot * ((A + B) + -U)) = halfQuot * (U - -D)
      have hhalf : (halfQuot : CRealQuot) + halfQuot = 1 := halfQuot_add_half
      calc
        A - halfQuot * ((A + B) + -U)
            = (halfQuot + halfQuot) * A -
                halfQuot * ((A + B) + -U) := by
              rw [hhalf]
              ring
        _ = halfQuot * (U - -D) := by
              dsimp [D]
              ring
    exact Quotient.exact hq
  change RegularSeqNonneg (subSeq a (CReal.min a b))
  exact regularSeqNonneg_of_eventual hto_prod hprod_nonneg

#print axioms BishopSec1P.CReal.min_le_leftC

theorem CReal.min_zero_const {a : CReal}
    (ha : ¬ CReal.ltE a CReal.zero) :
    CReal.min a CReal.zero ≈ CReal.zero := by
  have habs : CReal.abs a ≈ a := CReal.abs_of_nonneg_E ha
  calc
    CReal.min a CReal.zero
        ≈ CReal.mul CReal.half
            (CReal.add a (CReal.neg (CReal.abs a))) :=
          min_zero_halfsum a
    _ ≈ CReal.mul CReal.half
            (CReal.add a (CReal.neg a)) :=
          mul_congr (Setoid.refl CReal.half)
            (add_congr (Setoid.refl a) (neg_congr habs))
    _ ≈ CReal.mul CReal.half CReal.zero :=
          mul_congr (Setoid.refl CReal.half) (add_right_neg_equiv a)
    _ ≈ CReal.zero := by
          change relEventually
            (mulSeqConcreteWith cRatScalarMulArch halfSeq zeroSeq)
            zeroSeq
          exact mulSeqConcrete_zero_right_eventually cRatScalarMulArch halfSeq

#print axioms BishopSec1P.CReal.min_zero_const

theorem CReal.abs_min_const_le {a : CReal}
    (ha : ¬ CReal.ltE a CReal.zero) (x : CReal) :
    RegularSeqLe (CReal.abs (CReal.min x a)) (CReal.abs x) := by
  have hmin_a0 : CReal.min a CReal.zero ≈ CReal.zero :=
    CReal.min_zero_const ha
  have hmin_0a : CReal.min CReal.zero a ≈ CReal.zero := by
    change relEventually (minSeqWith cRatScalarMulArch zeroSeq a) zeroSeq
    exact
      relEventually_trans
        (minSeqWith cRatScalarMulArch zeroSeq a)
        (minSeqWith cRatScalarMulArch a zeroSeq)
        zeroSeq
        (minSeqWith_comm_eventually cRatScalarMulArch zeroSeq a)
        hmin_a0
  have hbase := CReal.abs_min_sub_min_le x CReal.zero a
  have hleft_sub :
      relEventually
        (subSeq (CReal.min x a) (CReal.min CReal.zero a))
        (CReal.min x a) := by
    have h0 :
        relEventually
          (subSeq (CReal.min x a) (CReal.min CReal.zero a))
          (subSeq (CReal.min x a) CReal.zero) :=
      subSeq_respects_eventually
        (CReal.min x a) (CReal.min x a)
        (CReal.min CReal.zero a) CReal.zero
        (relEventually_refl (CReal.min x a)) hmin_0a
    exact
      relEventually_trans
        (subSeq (CReal.min x a) (CReal.min CReal.zero a))
        (subSeq (CReal.min x a) CReal.zero)
        (CReal.min x a)
        h0
        (subSeq_zero_right_eventually (CReal.min x a))
  have hleft :
      relEventually
        (CReal.abs (CReal.min x a))
        (CReal.abs
          (CReal.sub (CReal.min x a) (CReal.min CReal.zero a))) := by
    change relEventually
      (absSeq (CReal.min x a))
      (absSeq (subSeq (CReal.min x a) (CReal.min CReal.zero a)))
    exact
      relEventually_symm
        (absSeq (subSeq (CReal.min x a) (CReal.min CReal.zero a)))
        (absSeq (CReal.min x a))
        (absSeq_respects_eventually
          (subSeq (CReal.min x a) (CReal.min CReal.zero a))
          (CReal.min x a)
          hleft_sub)
  have hright :
      relEventually
        (CReal.abs (CReal.sub x CReal.zero))
        (CReal.abs x) := by
    change relEventually (absSeq (subSeq x zeroSeq)) (absSeq x)
    exact absSeq_respects_eventually
      (subSeq x zeroSeq) x (subSeq_zero_right_eventually x)
  exact regularSeqLe_of_right_eventual hright
    (regularSeqLe_of_left_eventual hleft hbase)

#print axioms BishopSec1P.CReal.abs_min_const_le

theorem CReal.abs_min_le_abs_of_nonneg_leftC (a b : CReal)
    (ha : ¬ CReal.ltE a CReal.zero) :
    RegularSeqLe (CReal.abs (CReal.min a b)) (CReal.abs b) := by
  have hmin :
      CReal.min a b ≈ CReal.min b a := by
    change relEventually
      (minSeqWith cRatScalarMulArch a b)
      (minSeqWith cRatScalarMulArch b a)
    exact minSeqWith_comm_eventually cRatScalarMulArch a b
  have habs :
      CReal.abs (CReal.min a b) ≈ CReal.abs (CReal.min b a) := by
    change relEventually
      (absSeq (CReal.min a b))
      (absSeq (CReal.min b a))
    exact absSeq_respects_eventually (CReal.min a b) (CReal.min b a) hmin
  exact regularSeqLe_of_left_eventual habs
    (CReal.abs_min_const_le ha b)

#print axioms BishopSec1P.CReal.abs_min_le_abs_of_nonneg_leftC

/-- Finite signed gap estimate:
`|Σ_{n < k <= n+d} u_k| <= Σ_{n < k <= n+d} |u_k|`. -/
theorem regularSeqFinSum_abs_gap_le (u : Nat → CReal) (n d : Nat) :
    RegularSeqLe
      (absSeq (subSeq (regularSeqFinSum u (n + d)) (regularSeqFinSum u n)))
      (subSeq (regularSeqFinSum (fun k => absSeq (u k)) (n + d))
        (regularSeqFinSum (fun k => absSeq (u k)) n)) := by
  induction d with
  | zero =>
      have hleft0 :
          relEventually
            (absSeq (subSeq (regularSeqFinSum u (n + 0)) (regularSeqFinSum u n)))
            zeroSeq := by
        have hsub :
            relEventually
              (subSeq (regularSeqFinSum u (n + 0)) (regularSeqFinSum u n))
              zeroSeq := by
          simpa using subSeq_self_eventually_law (regularSeqFinSum u n)
        have habs :
            relEventually
              (absSeq (subSeq (regularSeqFinSum u (n + 0)) (regularSeqFinSum u n)))
              (absSeq zeroSeq) :=
          absSeq_respects_eventually
            (subSeq (regularSeqFinSum u (n + 0)) (regularSeqFinSum u n))
            zeroSeq hsub
        exact relEventually_trans _ _ _ habs CReal.abs_zero
      have hright0 :
          relEventually
            (subSeq
              (regularSeqFinSum (fun k => absSeq (u k)) (n + 0))
              (regularSeqFinSum (fun k => absSeq (u k)) n))
            zeroSeq := by
        simpa using
          subSeq_self_eventually_law
            (regularSeqFinSum (fun k => absSeq (u k)) n)
      exact regularSeqLe_of_left_eventual hleft0
        (regularSeqLe_of_right_eventual (relEventually_symm _ _ hright0)
          (regularSeqLe_refl zeroSeq))
  | succ d ih =>
      let gu := subSeq (regularSeqFinSum u (n + d)) (regularSeqFinSum u n)
      let ga := subSeq
        (regularSeqFinSum (fun k => absSeq (u k)) (n + d))
        (regularSeqFinSum (fun k => absSeq (u k)) n)
      have hu_ev := regularSeqFinSum_gap_succ_eventually u n d
      have ha_ev :=
        regularSeqFinSum_gap_succ_eventually (fun k => absSeq (u k)) n d
      have hleft_ev :
          relEventually
            (absSeq
              (subSeq (regularSeqFinSum u (n + (d + 1)))
                (regularSeqFinSum u n)))
            (absSeq (addSeq gu (u (n + d + 1)))) :=
        absSeq_respects_eventually
          (subSeq (regularSeqFinSum u (n + (d + 1))) (regularSeqFinSum u n))
          (addSeq gu (u (n + d + 1)))
          (by simpa [gu] using hu_ev)
      have htri :
          RegularSeqLe
            (absSeq (addSeq gu (u (n + d + 1))))
            (addSeq (absSeq gu) (absSeq (u (n + d + 1)))) :=
        regularSeqLe_abs_add gu (u (n + d + 1))
      have hstep :
          RegularSeqLe
            (addSeq (absSeq gu) (absSeq (u (n + d + 1))))
            (addSeq ga (absSeq (u (n + d + 1)))) :=
        regularSeqLe_add ih (regularSeqLe_refl (absSeq (u (n + d + 1))))
      have hbody :
          RegularSeqLe
            (absSeq (addSeq gu (u (n + d + 1))))
            (addSeq ga (absSeq (u (n + d + 1)))) :=
        regularSeqLe_trans htri hstep
      exact regularSeqLe_of_left_eventual hleft_ev
        (regularSeqLe_of_right_eventual
          (relEventually_symm _ _ (by simpa [ga] using ha_ev)) hbody)

#print axioms BishopSec1P.regularSeqFinSum_abs_gap_le

/-- Arbitrary finite signed-sum difference is bounded by the corresponding
absolute-term finite-sum difference. -/
theorem regularSeqFinSum_absdiff_le_abs (u : Nat → CReal) (m n : Nat) :
    RegularSeqLe
      (absSeq (subSeq (regularSeqFinSum u m) (regularSeqFinSum u n)))
      (absSeq
        (subSeq (regularSeqFinSum (fun k => absSeq (u k)) m)
          (regularSeqFinSum (fun k => absSeq (u k)) n))) := by
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
    subst n
    have haux := regularSeqFinSum_abs_gap_le u m d
    have hleft :
        relEventually
          (absSeq (subSeq (regularSeqFinSum u m) (regularSeqFinSum u (m + d))))
          (absSeq (subSeq (regularSeqFinSum u (m + d)) (regularSeqFinSum u m))) :=
      absSeq_subSeq_comm_eventually (regularSeqFinSum u m) (regularSeqFinSum u (m + d))
    let ga := subSeq
      (regularSeqFinSum (fun k => absSeq (u k)) (m + d))
      (regularSeqFinSum (fun k => absSeq (u k)) m)
    have hga_abs_rev :
        RegularSeqLe ga
          (absSeq
            (subSeq (regularSeqFinSum (fun k => absSeq (u k)) m)
              (regularSeqFinSum (fun k => absSeq (u k)) (m + d)))) := by
      have hga_abs : RegularSeqLe ga (absSeq ga) :=
        base_le_abs_base_regularSeqLe ga
      have habs :
          relEventually (absSeq ga)
            (absSeq
              (subSeq (regularSeqFinSum (fun k => absSeq (u k)) m)
                (regularSeqFinSum (fun k => absSeq (u k)) (m + d)))) := by
        simpa [ga] using
          absSeq_subSeq_comm_eventually
            (regularSeqFinSum (fun k => absSeq (u k)) (m + d))
            (regularSeqFinSum (fun k => absSeq (u k)) m)
      exact regularSeqLe_of_right_eventual habs hga_abs
    exact regularSeqLe_of_left_eventual hleft
      (regularSeqLe_trans haux (by simpa [ga] using hga_abs_rev))
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
    subst m
    have haux := regularSeqFinSum_abs_gap_le u n d
    let ga := subSeq
      (regularSeqFinSum (fun k => absSeq (u k)) (n + d))
      (regularSeqFinSum (fun k => absSeq (u k)) n)
    have hga_abs :
        RegularSeqLe ga
          (absSeq
            (subSeq (regularSeqFinSum (fun k => absSeq (u k)) (n + d))
              (regularSeqFinSum (fun k => absSeq (u k)) n))) := by
      exact base_le_abs_base_regularSeqLe ga
    exact regularSeqLe_trans haux (by simpa [ga] using hga_abs)

#print axioms BishopSec1P.regularSeqFinSum_absdiff_le_abs

/-- Signed comparison test: if `|a_n| <= b_n` termwise and the majorant series
`Σ b_n` converges, then `Σ a_n` converges. -/
def repSeriesSum_of_absMajorant {a b : Nat → CReal}
    (hb : RepSeriesSum b)
    (hnn : ∀ n, RegularSeqNonneg (b n))
    (hle : ∀ n, RegularSeqLe (absSeq (a n)) (b n)) :
    RepSeriesSum a :=
  let hbcau := repIsCauchy_of_tendsto hb.tends
  repSeriesSum_of_partialCauchy
    { cmod := fun k => hbcau.cmod (k + 1)
      close_eventually := fun k m n hm hn =>
        repCloseAtGauge_of_absdiff_le k
          (by
            have habs :
                RegularSeqLe
                  (absSeq (subSeq (regularSeqFinSum a m) (regularSeqFinSum a n)))
                  (absSeq
                    (subSeq (regularSeqFinSum (fun k => absSeq (a k)) m)
                      (regularSeqFinSum (fun k => absSeq (a k)) n))) :=
              regularSeqFinSum_absdiff_le_abs a m n
            have hmaj :
                RegularSeqLe
                  (absSeq
                    (subSeq (regularSeqFinSum (fun k => absSeq (a k)) m)
                      (regularSeqFinSum (fun k => absSeq (a k)) n)))
                  (absSeq (subSeq (regularSeqFinSum b m) (regularSeqFinSum b n))) :=
              partialSum_absdiff_le
                (fun n => regularSeqNonneg_of_zero_le
                  (absSeq_nonnegative_regularSeqLe (a n)))
                hle m n
            have hrefl :
                RegularSeqLe
                  (absSeq (subSeq (regularSeqFinSum b m) (regularSeqFinSum b n)))
                  (absSeq (subSeq (regularSeqFinSum b m) (regularSeqFinSum b n))) :=
              partialSum_absdiff_le hnn (fun n => regularSeqLe_refl (b n)) m n
            exact regularSeqLe_trans (regularSeqLe_trans habs hmaj) hrefl)
          (hbcau.close_eventually (k + 1) m n hm hn) }

#print axioms BishopSec1P.repSeriesSum_of_absMajorant

theorem IntegrableRepC.I1_is_carried {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC S) :
    (r.integral_sum).sum = r.I1 :=
  rfl

#print axioms BishopSec1P.IntegrableRepC.I1_is_carried

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def bc1_seqMerge {α : Type*} (a b : Nat → α) : Nat → α :=
  fun n => if n % 2 = 0 then a (n / 2) else b (n / 2)

theorem bc1_seqMerge_even {α : Type*} (a b : Nat → α) (k : Nat) :
    bc1_seqMerge a b (2 * k) = a k := by
  unfold bc1_seqMerge; rw [if_pos (by omega : (2 * k) % 2 = 0)]; congr 1; omega

theorem bc1_seqMerge_odd {α : Type*} (a b : Nat → α) (k : Nat) :
    bc1_seqMerge a b (2 * k + 1) = b k := by
  unfold bc1_seqMerge; rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]; congr 1; omega

/-- Technical lemma used in the public import closure. -/
theorem bc1_addSeq_swap_middle (w x y z : CReal) :
    relEventually
      (addSeq (addSeq (addSeq w x) y) z)
      (addSeq (addSeq w y) (addSeq x z)) := by
  have hL1 : relEventually
      (addSeq (addSeq (addSeq w x) y) z)
      (addSeq (addSeq w x) (addSeq y z)) :=
    addSeq_assoc_eventually (addSeq w x) y z
  have hL2 : relEventually
      (addSeq (addSeq w x) (addSeq y z))
      (addSeq w (addSeq x (addSeq y z))) :=
    addSeq_assoc_eventually w x (addSeq y z)
  have hL : relEventually
      (addSeq (addSeq (addSeq w x) y) z)
      (addSeq w (addSeq x (addSeq y z))) :=
    relEventually_trans _ _ _ hL1 hL2
  have hinner : relEventually (addSeq y (addSeq x z)) (addSeq x (addSeq y z)) := by
    have h1 : relEventually (addSeq y (addSeq x z)) (addSeq (addSeq y x) z) :=
      relEventually_symm _ _ (addSeq_assoc_eventually y x z)
    have h2 : relEventually (addSeq (addSeq y x) z) (addSeq (addSeq x y) z) :=
      addSeq_respects_eventually (addSeq y x) (addSeq x y) z z
        (addSeq_comm_eventually y x) (relEventually_refl z)
    have h3 : relEventually (addSeq (addSeq x y) z) (addSeq x (addSeq y z)) :=
      addSeq_assoc_eventually x y z
    exact relEventually_trans _ _ _ (relEventually_trans _ _ _ h1 h2) h3
  have hR1 : relEventually
      (addSeq (addSeq w y) (addSeq x z))
      (addSeq w (addSeq y (addSeq x z))) :=
    addSeq_assoc_eventually w y (addSeq x z)
  have hR2 : relEventually
      (addSeq w (addSeq y (addSeq x z)))
      (addSeq w (addSeq x (addSeq y z))) :=
    addSeq_respects_eventually w w (addSeq y (addSeq x z)) (addSeq x (addSeq y z))
      (relEventually_refl w) hinner
  have hR : relEventually
      (addSeq (addSeq w y) (addSeq x z))
      (addSeq w (addSeq x (addSeq y z))) :=
    relEventually_trans _ _ _ hR1 hR2
  exact relEventually_trans _ _ _ hL (relEventually_symm _ _ hR)

/-- Technical lemma used in the public import closure. -/
theorem bc1_finSum_interleave_odd (a b : Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum (bc1_seqMerge a b) (2 * N + 1))
      (addSeq (regularSeqFinSum a N) (regularSeqFinSum b N)) := by
  induction N with
  | zero =>
    have hc0 : bc1_seqMerge a b 0 = a 0 := by
      have := bc1_seqMerge_even a b 0; simpa using this
    have hc1 : bc1_seqMerge a b 1 = b 0 := by
      have := bc1_seqMerge_odd a b 0; simpa using this
    show relEventually
      (addSeq (regularSeqFinSum (bc1_seqMerge a b) 0) (bc1_seqMerge a b 1))
      (addSeq (regularSeqFinSum a 0) (regularSeqFinSum b 0))
    simp only [regularSeqFinSum, hc0, hc1]
    exact relEventually_refl _
  | succ n ih =>
    have hcE : bc1_seqMerge a b (2 * n + 2) = a (n + 1) := by
      have := bc1_seqMerge_even a b (n + 1); simpa [Nat.mul_succ] using this
    have hcO : bc1_seqMerge a b (2 * n + 3) = b (n + 1) := by
      have := bc1_seqMerge_odd a b (n + 1)
      simpa [Nat.mul_succ] using this
    have hstep : regularSeqFinSum (bc1_seqMerge a b) (2 * (n + 1) + 1)
        = addSeq
            (addSeq (regularSeqFinSum (bc1_seqMerge a b) (2 * n + 1))
              (bc1_seqMerge a b (2 * n + 2)))
            (bc1_seqMerge a b (2 * n + 3)) := by
      have e1 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by omega
      have e2 : 2 * n + 2 = (2 * n + 1) + 1 := by omega
      rw [e1]
      show addSeq (regularSeqFinSum (bc1_seqMerge a b) (2 * n + 2))
            (bc1_seqMerge a b (2 * n + 2 + 1)) = _
      rw [e2]
      rfl
    rw [hstep, hcE, hcO]
    have hbase : relEventually
        (addSeq (addSeq (regularSeqFinSum (bc1_seqMerge a b) (2 * n + 1)) (a (n + 1)))
          (b (n + 1)))
        (addSeq (addSeq (addSeq (regularSeqFinSum a n) (regularSeqFinSum b n)) (a (n + 1)))
          (b (n + 1))) :=
      addSeq_respects_eventually _ _ (b (n + 1)) (b (n + 1))
        (addSeq_respects_eventually _ _ (a (n + 1)) (a (n + 1)) ih (relEventually_refl _))
        (relEventually_refl _)
    have hswap : relEventually
        (addSeq (addSeq (addSeq (regularSeqFinSum a n) (regularSeqFinSum b n)) (a (n + 1)))
          (b (n + 1)))
        (addSeq (addSeq (regularSeqFinSum a n) (a (n + 1)))
          (addSeq (regularSeqFinSum b n) (b (n + 1)))) :=
      bc1_addSeq_swap_middle (regularSeqFinSum a n) (regularSeqFinSum b n)
        (a (n + 1)) (b (n + 1))
    show relEventually _
      (addSeq (regularSeqFinSum a (n + 1)) (regularSeqFinSum b (n + 1)))
    exact relEventually_trans _ _ _ hbase hswap

#print axioms BishopSec1P.bc1_seqMerge_even
#print axioms BishopSec1P.bc1_seqMerge_odd
#print axioms BishopSec1P.bc1_addSeq_swap_middle
#print axioms BishopSec1P.bc1_finSum_interleave_odd

/-- Technical lemma used in the public import closure. -/
theorem bc1_addSeq_swap3 (A B c : CReal) :
    relEventually (addSeq (addSeq A B) c) (addSeq (addSeq A c) B) :=
  relEventually_trans _ _ _
    (addSeq_assoc_eventually A B c)
    (relEventually_trans _ _ _
      (addSeq_respects_eventually A A (addSeq B c) (addSeq c B)
        (relEventually_refl A) (addSeq_comm_eventually B c))
      (relEventually_symm _ _ (addSeq_assoc_eventually A c B)))

#print axioms BishopSec1P.bc1_addSeq_swap3

/-- Technical lemma used in the public import closure. -/
theorem bc1_finSum_interleave_even (a b : Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum (bc1_seqMerge a b) (2 * N + 2))
      (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N)) := by
  have hmerge : bc1_seqMerge a b (2 * N + 2) = a (N + 1) := by
    have := bc1_seqMerge_even a b (N + 1); simpa [Nat.mul_succ] using this
  have h3 : addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N)
      = addSeq (addSeq (regularSeqFinSum a N) (a (N + 1))) (regularSeqFinSum b N) := rfl
  show relEventually
    (addSeq (regularSeqFinSum (bc1_seqMerge a b) (2 * N + 1)) (bc1_seqMerge a b (2 * N + 2)))
    (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N))
  rw [hmerge, h3]
  exact relEventually_trans _ _ _
    (addSeq_respects_eventually _ _ _ _ (bc1_finSum_interleave_odd a b N) (relEventually_refl _))
    (bc1_addSeq_swap3 (regularSeqFinSum a N) (regularSeqFinSum b N) (a (N + 1)))

#print axioms BishopSec1P.bc1_finSum_interleave_even

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem bc1_repClose_of_relEventually {x y : CReal} (h : relEventually x y) (k : Nat) :
    RepCloseAtGauge k x y := h k

/-- Technical lemma used in the public import closure. -/
theorem bc1_repCloseAtGauge_add (k : Nat) {x x' y y' : CReal}
    (hx : RepCloseAtGauge (k + 1) x x')
    (hy : RepCloseAtGauge (k + 1) y y') :
    RepCloseAtGauge k (addSeq x y) (addSeq x' y') := by
  rcases hx with ⟨Nx, hNx⟩
  rcases hy with ⟨Ny, hNy⟩
  refine ⟨Nx + Ny, ?_⟩
  intro n hn
  have hex := hNx (n + 1) (by omega)
  have hey := hNy (n + 1) (by omega)
  have hax : (addSeq x y).val n = x.val (n + 1) + y.val (n + 1) := rfl
  have hax' : (addSeq x' y').val n = x'.val (n + 1) + y'.val (n + 1) := rfl
  have htri := scalar_abs_add_le
    (x.val (n + 1) - x'.val (n + 1)) (y.val (n + 1) - y'.val (n + 1))
  rw [show (x.val (n + 1) - x'.val (n + 1)) + (y.val (n + 1) - y'.val (n + 1))
      = (addSeq x y).val n - (addSeq x' y').val n
      from by rw [hax, hax']; ring] at htri
  have hsum := BishopC.le_add hex hey
  rw [eps_succ_add_self k] at hsum
  exact BishopC.le_trans htri hsum

/-- Technical lemma used in the public import closure. -/
theorem bc1_addSeq_swap_inner (w x y z : CReal) :
    relEventually
      (addSeq (addSeq w x) (addSeq y z))
      (addSeq (addSeq w y) (addSeq x z)) := by
  have hL : relEventually
      (addSeq (addSeq w x) (addSeq y z))
      (addSeq w (addSeq x (addSeq y z))) :=
    addSeq_assoc_eventually w x (addSeq y z)
  have hinner : relEventually (addSeq x (addSeq y z)) (addSeq y (addSeq x z)) := by
    have h1 : relEventually (addSeq x (addSeq y z)) (addSeq (addSeq x y) z) :=
      relEventually_symm _ _ (addSeq_assoc_eventually x y z)
    have h2 : relEventually (addSeq (addSeq x y) z) (addSeq (addSeq y x) z) :=
      addSeq_respects_eventually (addSeq x y) (addSeq y x) z z
        (addSeq_comm_eventually x y) (relEventually_refl z)
    have h3 : relEventually (addSeq (addSeq y x) z) (addSeq y (addSeq x z)) :=
      addSeq_assoc_eventually y x z
    exact relEventually_trans _ _ _ (relEventually_trans _ _ _ h1 h2) h3
  have hmid : relEventually
      (addSeq w (addSeq x (addSeq y z)))
      (addSeq w (addSeq y (addSeq x z))) :=
    addSeq_respects_eventually w w _ _ (relEventually_refl w) hinner
  have hR : relEventually
      (addSeq (addSeq w y) (addSeq x z))
      (addSeq w (addSeq y (addSeq x z))) :=
    addSeq_assoc_eventually w y (addSeq x z)
  exact relEventually_trans _ _ _ (relEventually_trans _ _ _ hL hmid)
    (relEventually_symm _ _ hR)

/-- Technical lemma used in the public import closure. -/
theorem bc1_finSum_termwise (a b : Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum (fun n => addSeq (a n) (b n)) N)
      (addSeq (regularSeqFinSum a N) (regularSeqFinSum b N)) := by
  induction N with
  | zero => exact relEventually_refl _
  | succ n ih =>
    have hLHS : regularSeqFinSum (fun m => addSeq (a m) (b m)) (n + 1)
        = addSeq (regularSeqFinSum (fun m => addSeq (a m) (b m)) n)
            (addSeq (a (n + 1)) (b (n + 1))) := rfl
    have hRHS : addSeq (regularSeqFinSum a (n + 1)) (regularSeqFinSum b (n + 1))
        = addSeq (addSeq (regularSeqFinSum a n) (a (n + 1)))
            (addSeq (regularSeqFinSum b n) (b (n + 1))) := rfl
    rw [hLHS, hRHS]
    have hcong : relEventually
        (addSeq (regularSeqFinSum (fun m => addSeq (a m) (b m)) n)
          (addSeq (a (n + 1)) (b (n + 1))))
        (addSeq (addSeq (regularSeqFinSum a n) (regularSeqFinSum b n))
          (addSeq (a (n + 1)) (b (n + 1)))) :=
      addSeq_respects_eventually _ _ _ _ ih (relEventually_refl _)
    exact relEventually_trans _ _ _ hcong
      (bc1_addSeq_swap_inner (regularSeqFinSum a n) (regularSeqFinSum b n)
        (a (n + 1)) (b (n + 1)))

/-- Technical lemma used in the public import closure. -/
def bc1_repSeriesTendsto_add {u v : Nat → CReal} {su sv : CReal}
    (hu : RepSeriesTendsto u su) (hv : RepSeriesTendsto v sv) :
    RepSeriesTendsto (fun n => addSeq (u n) (v n)) (addSeq su sv) where
  mod := fun k => Nat.max (hu.mod (k + 1)) (hv.mod (k + 1))
  close := by
    intro k n hn
    have hnu : hu.mod (k + 1) ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hnv : hv.mod (k + 1) ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hcu : RepCloseAtGauge (k + 2) (u n) su := hu.close (k + 1) n hnu
    have hcv : RepCloseAtGauge (k + 2) (v n) sv := hv.close (k + 1) n hnv
    exact bc1_repCloseAtGauge_add (k + 1) hcu hcv

/-- Technical lemma used in the public import closure. -/
def bc1_repSeriesTendsto_congr {u v : Nat → CReal} {l : CReal}
    (hu : RepSeriesTendsto u l) (heq : ∀ n, relEventually (v n) (u n)) :
    RepSeriesTendsto v l where
  mod := fun k => hu.mod (k + 1)
  close := by
    intro k n hn
    have hcu : RepCloseAtGauge (k + 2) (u n) l := hu.close (k + 1) n hn
    have hvu : RepCloseAtGauge (k + 2) (v n) (u n) :=
      bc1_repClose_of_relEventually (heq n) (k + 2)
    exact repCloseAtGauge_triangle_succ (k + 1) hvu hcu

/-- Technical lemma used in the public import closure. -/
def bc1_addSeq_series {a b : Nat → CReal}
    (ha : RepSeriesSum a) (hb : RepSeriesSum b) :
    RepSeriesSum (fun n => addSeq (a n) (b n)) where
  sum := addSeq ha.sum hb.sum
  tends :=
    bc1_repSeriesTendsto_congr
      (bc1_repSeriesTendsto_add ha.tends hb.tends)
      (fun N => bc1_finSum_termwise a b N)

#print axioms BishopSec1P.bc1_repClose_of_relEventually
#print axioms BishopSec1P.bc1_repCloseAtGauge_add
#print axioms BishopSec1P.bc1_addSeq_swap_inner
#print axioms BishopSec1P.bc1_finSum_termwise
#print axioms BishopSec1P.bc1_repSeriesTendsto_add
#print axioms BishopSec1P.bc1_repSeriesTendsto_congr
#print axioms BishopSec1P.bc1_addSeq_series

/-- Technical lemma used in the public import closure. -/
def bc1_repSeriesTendsto_interleave {a b : Nat → CReal} {su sv : CReal}
    (hu : RepSeriesTendsto (regularSeqFinSum a) su)
    (hv : RepSeriesTendsto (regularSeqFinSum b) sv) :
    RepSeriesTendsto (regularSeqFinSum (bc1_seqMerge a b)) (addSeq su sv) where
  mod := fun k => 2 * (Nat.max (hu.mod (k + 2)) (hv.mod (k + 2))) + 2
  close := by
    intro k n hn
    have hmaxa : hu.mod (k + 2) ≤ Nat.max (hu.mod (k + 2)) (hv.mod (k + 2)) :=
      Nat.le_max_left _ _
    have hmaxb : hv.mod (k + 2) ≤ Nat.max (hu.mod (k + 2)) (hv.mod (k + 2)) :=
      Nat.le_max_right _ _
    have hbase : 2 * (Nat.max (hu.mod (k + 2)) (hv.mod (k + 2))) + 2 ≤ n := hn
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · obtain ⟨M, hM⟩ : ∃ M, n = 2 * M := ⟨n / 2, by omega⟩
      obtain ⟨M', hM'⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      have hn2 : n = 2 * M' + 2 := by omega
      rw [hn2]
      have hca : RepCloseAtGauge (k + 3) (regularSeqFinSum a (M' + 1)) su :=
        hu.close (k + 2) (M' + 1) (by omega)
      have hcb : RepCloseAtGauge (k + 3) (regularSeqFinSum b M') sv :=
        hv.close (k + 2) M' (by omega)
      exact repCloseAtGauge_triangle_succ (k + 1)
        (bc1_repClose_of_relEventually (bc1_finSum_interleave_even a b M') (k + 2))
        (bc1_repCloseAtGauge_add (k + 2) hca hcb)
    · obtain ⟨M, hM⟩ : ∃ M, n = 2 * M + 1 := ⟨n / 2, by omega⟩
      rw [hM]
      have hca : RepCloseAtGauge (k + 3) (regularSeqFinSum a M) su :=
        hu.close (k + 2) M (by omega)
      have hcb : RepCloseAtGauge (k + 3) (regularSeqFinSum b M) sv :=
        hv.close (k + 2) M (by omega)
      exact repCloseAtGauge_triangle_succ (k + 1)
        (bc1_repClose_of_relEventually (bc1_finSum_interleave_odd a b M) (k + 2))
        (bc1_repCloseAtGauge_add (k + 2) hca hcb)

#print axioms BishopSec1P.bc1_repSeriesTendsto_interleave

/-- Technical lemma used in the public import closure. -/
def bc1_seriesSum_interleave {a b : Nat → CReal}
    (ha : RepSeriesSum a) (hb : RepSeriesSum b) :
    RepSeriesSum (bc1_seqMerge a b) where
  sum := addSeq ha.sum hb.sum
  tends := bc1_repSeriesTendsto_interleave ha.tends hb.tends

#print axioms BishopSec1P.bc1_seriesSum_interleave

/-- Technical lemma used in the public import closure. -/
def bc1_seqMerge3 {α : Type*} (a b c : Nat → α) : Nat → α :=
  fun n => if n % 3 = 0 then a (n / 3) else if n % 3 = 1 then b (n / 3) else c (n / 3)

#print axioms BishopSec1P.bc1_seqMerge3

theorem bc1_seqMerge3_zero {α : Type*} (a b c : Nat → α) (k : Nat) :
    bc1_seqMerge3 a b c (3 * k) = a k := by
  unfold bc1_seqMerge3
  rw [if_pos (by omega : (3 * k) % 3 = 0)]
  congr 1
  omega

#print axioms BishopSec1P.bc1_seqMerge3_zero

theorem bc1_seqMerge3_one {α : Type*} (a b c : Nat → α) (k : Nat) :
    bc1_seqMerge3 a b c (3 * k + 1) = b k := by
  unfold bc1_seqMerge3
  rw [if_neg (by omega : ¬ (3 * k + 1) % 3 = 0),
    if_pos (by omega : (3 * k + 1) % 3 = 1)]
  congr 1
  omega

#print axioms BishopSec1P.bc1_seqMerge3_one

theorem bc1_seqMerge3_two {α : Type*} (a b c : Nat → α) (k : Nat) :
    bc1_seqMerge3 a b c (3 * k + 2) = c k := by
  unfold bc1_seqMerge3
  rw [if_neg (by omega : ¬ (3 * k + 2) % 3 = 0),
    if_neg (by omega : ¬ (3 * k + 2) % 3 = 1)]
  congr 1
  omega

#print axioms BishopSec1P.bc1_seqMerge3_two

/-- Technical lemma used in the public import closure. -/
theorem bc1_seqMerge3_map {α β : Type*} (φ : α → β) (a b c : Nat → α) (n : Nat) :
    φ (bc1_seqMerge3 a b c n)
      = bc1_seqMerge3 (fun k => φ (a k)) (fun k => φ (b k)) (fun k => φ (c k)) n := by
  show φ (if n % 3 = 0 then a (n / 3) else if n % 3 = 1 then b (n / 3) else c (n / 3))
    = if n % 3 = 0 then φ (a (n / 3))
      else if n % 3 = 1 then φ (b (n / 3)) else φ (c (n / 3))
  rw [apply_ite φ, apply_ite φ]

#print axioms BishopSec1P.bc1_seqMerge3_map

/-- Technical lemma used in the public import closure. -/
theorem bc1_addSeq_rotate_inner (x y z : CReal) :
    relEventually (addSeq x (addSeq y z)) (addSeq y (addSeq x z)) := by
  have h1 : relEventually (addSeq x (addSeq y z)) (addSeq (addSeq x y) z) :=
    relEventually_symm _ _ (addSeq_assoc_eventually x y z)
  have h2 : relEventually (addSeq (addSeq x y) z) (addSeq (addSeq y x) z) :=
    addSeq_respects_eventually (addSeq x y) (addSeq y x) z z
      (addSeq_comm_eventually x y) (relEventually_refl z)
  have h3 : relEventually (addSeq (addSeq y x) z) (addSeq y (addSeq x z)) :=
    addSeq_assoc_eventually y x z
  exact relEventually_trans _ _ _ (relEventually_trans _ _ _ h1 h2) h3

#print axioms BishopSec1P.bc1_addSeq_rotate_inner

/-- Technical lemma used in the public import closure. -/
theorem bc1_addSeq_append3 (A B C a b c : CReal) :
    relEventually
      (addSeq (addSeq (addSeq (addSeq (addSeq A B) C) a) b) c)
      (addSeq (addSeq (addSeq A a) (addSeq B b)) (addSeq C c)) := by
  let P := addSeq (addSeq A B) C
  have hgroup1 : relEventually
      (addSeq (addSeq (addSeq P a) b) c)
      (addSeq (addSeq P (addSeq a b)) c) :=
    addSeq_respects_eventually _ _ c c
      (addSeq_assoc_eventually P a b) (relEventually_refl c)
  have hgroup2 : relEventually
      (addSeq (addSeq P (addSeq a b)) c)
      (addSeq P (addSeq (addSeq a b) c)) :=
    addSeq_assoc_eventually P (addSeq a b) c
  have hgroup3 : relEventually
      (addSeq P (addSeq (addSeq a b) c))
      (addSeq P (addSeq a (addSeq b c))) :=
    addSeq_respects_eventually P P _ _
      (relEventually_refl P) (addSeq_assoc_eventually a b c)
  have hgroup : relEventually
      (addSeq (addSeq (addSeq P a) b) c)
      (addSeq P (addSeq a (addSeq b c))) :=
    relEventually_trans _ _ _ (relEventually_trans _ _ _ hgroup1 hgroup2) hgroup3
  have hswap1 : relEventually
      (addSeq P (addSeq a (addSeq b c)))
      (addSeq (addSeq (addSeq A B) a) (addSeq C (addSeq b c))) := by
    simpa [P] using bc1_addSeq_swap_inner (addSeq A B) C a (addSeq b c)
  have hswap2 : relEventually
      (addSeq (addSeq (addSeq A B) a) (addSeq C (addSeq b c)))
      (addSeq (addSeq (addSeq A a) B) (addSeq C (addSeq b c))) :=
    addSeq_respects_eventually _ _ _ _
      (bc1_addSeq_swap3 A B a) (relEventually_refl _)
  have hswap3 : relEventually
      (addSeq (addSeq (addSeq A a) B) (addSeq C (addSeq b c)))
      (addSeq (addSeq (addSeq A a) B) (addSeq b (addSeq C c))) :=
    addSeq_respects_eventually _ _ _ _
      (relEventually_refl _) (bc1_addSeq_rotate_inner C b c)
  have hswap4 : relEventually
      (addSeq (addSeq (addSeq A a) B) (addSeq b (addSeq C c)))
      (addSeq (addSeq A a) (addSeq B (addSeq b (addSeq C c)))) :=
    addSeq_assoc_eventually (addSeq A a) B (addSeq b (addSeq C c))
  have hswap5 : relEventually
      (addSeq (addSeq A a) (addSeq B (addSeq b (addSeq C c))))
      (addSeq (addSeq A a) (addSeq (addSeq B b) (addSeq C c))) :=
    addSeq_respects_eventually _ _ _ _
      (relEventually_refl _)
      (relEventually_symm _ _ (addSeq_assoc_eventually B b (addSeq C c)))
  have hswap6 : relEventually
      (addSeq (addSeq A a) (addSeq (addSeq B b) (addSeq C c)))
      (addSeq (addSeq (addSeq A a) (addSeq B b)) (addSeq C c)) :=
    relEventually_symm _ _
      (addSeq_assoc_eventually (addSeq A a) (addSeq B b) (addSeq C c))
  exact relEventually_trans _ _ _
    (relEventually_trans _ _ _
      (relEventually_trans _ _ _ hgroup hswap1)
      (relEventually_trans _ _ _ hswap2 hswap3))
    (relEventually_trans _ _ _
      (relEventually_trans _ _ _ hswap4 hswap5) hswap6)

#print axioms BishopSec1P.bc1_addSeq_append3

/-- Technical lemma used in the public import closure. -/
theorem bc1_addSeq_append_left_of_three (A B C a : CReal) :
    relEventually
      (addSeq (addSeq (addSeq A B) C) a)
      (addSeq (addSeq (addSeq A a) B) C) := by
  have h1 : relEventually
      (addSeq (addSeq (addSeq A B) C) a)
      (addSeq (addSeq (addSeq A B) a) C) :=
    bc1_addSeq_swap3 (addSeq A B) C a
  have h2 : relEventually
      (addSeq (addSeq (addSeq A B) a) C)
      (addSeq (addSeq (addSeq A a) B) C) :=
    addSeq_respects_eventually _ _ C C
      (bc1_addSeq_swap3 A B a) (relEventually_refl C)
  exact relEventually_trans _ _ _ h1 h2

#print axioms BishopSec1P.bc1_addSeq_append_left_of_three

/-- Technical lemma used in the public import closure. -/
theorem bc1_addSeq_append_middle_of_three (A B C b : CReal) :
    relEventually
      (addSeq (addSeq (addSeq A B) C) b)
      (addSeq (addSeq A (addSeq B b)) C) := by
  have h1 : relEventually
      (addSeq (addSeq (addSeq A B) C) b)
      (addSeq (addSeq (addSeq A B) b) C) :=
    bc1_addSeq_swap3 (addSeq A B) C b
  have h2 : relEventually
      (addSeq (addSeq (addSeq A B) b) C)
      (addSeq (addSeq A (addSeq B b)) C) :=
    addSeq_respects_eventually _ _ C C
      (addSeq_assoc_eventually A B b) (relEventually_refl C)
  exact relEventually_trans _ _ _ h1 h2

#print axioms BishopSec1P.bc1_addSeq_append_middle_of_three

/-- Technical lemma used in the public import closure. -/
theorem bc1_finSum_merge3_a (a b c : Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * N + 2))
      (addSeq (addSeq (regularSeqFinSum a N) (regularSeqFinSum b N))
        (regularSeqFinSum c N)) := by
  induction N with
  | zero =>
    have h0 : bc1_seqMerge3 a b c 0 = a 0 := by
      have := bc1_seqMerge3_zero a b c 0
      simpa using this
    have h1 : bc1_seqMerge3 a b c 1 = b 0 := by
      have := bc1_seqMerge3_one a b c 0
      simpa using this
    have h2 : bc1_seqMerge3 a b c 2 = c 0 := by
      have := bc1_seqMerge3_two a b c 0
      simpa using this
    show relEventually
      (addSeq (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) 0)
        (bc1_seqMerge3 a b c 1)) (bc1_seqMerge3 a b c 2))
      (addSeq (addSeq (regularSeqFinSum a 0) (regularSeqFinSum b 0))
        (regularSeqFinSum c 0))
    simp only [regularSeqFinSum, h0, h1, h2]
    exact relEventually_refl _
  | succ n ih =>
    have h0 : bc1_seqMerge3 a b c (3 * n + 3) = a (n + 1) := by
      have := bc1_seqMerge3_zero a b c (n + 1)
      simpa [Nat.mul_succ] using this
    have h1 : bc1_seqMerge3 a b c (3 * n + 4) = b (n + 1) := by
      have := bc1_seqMerge3_one a b c (n + 1)
      simpa [Nat.mul_succ] using this
    have h2 : bc1_seqMerge3 a b c (3 * n + 5) = c (n + 1) := by
      have := bc1_seqMerge3_two a b c (n + 1)
      simpa [Nat.mul_succ] using this
    have hstep : regularSeqFinSum (bc1_seqMerge3 a b c) (3 * (n + 1) + 2)
        = addSeq
            (addSeq
              (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * n + 2))
                (bc1_seqMerge3 a b c (3 * n + 3)))
              (bc1_seqMerge3 a b c (3 * n + 4)))
            (bc1_seqMerge3 a b c (3 * n + 5)) := by
      have e1 : 3 * (n + 1) + 2 = (3 * n + 4) + 1 := by omega
      have e2 : 3 * n + 4 = (3 * n + 3) + 1 := by omega
      have e3 : 3 * n + 3 = (3 * n + 2) + 1 := by omega
      rw [e1]
      show addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * n + 4))
          (bc1_seqMerge3 a b c (3 * n + 4 + 1)) = _
      rw [e2]
      show addSeq
          (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * n + 3))
            (bc1_seqMerge3 a b c (3 * n + 3 + 1)))
          (bc1_seqMerge3 a b c (3 * n + 4 + 1)) = _
      rw [e3]
      rfl
    rw [hstep, h0, h1, h2]
    have hbase : relEventually
        (addSeq
          (addSeq
            (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * n + 2)) (a (n + 1)))
            (b (n + 1)))
          (c (n + 1)))
        (addSeq
          (addSeq
            (addSeq (addSeq (addSeq (regularSeqFinSum a n) (regularSeqFinSum b n))
              (regularSeqFinSum c n)) (a (n + 1)))
            (b (n + 1)))
          (c (n + 1))) :=
      addSeq_respects_eventually _ _ (c (n + 1)) (c (n + 1))
        (addSeq_respects_eventually _ _ (b (n + 1)) (b (n + 1))
          (addSeq_respects_eventually _ _ (a (n + 1)) (a (n + 1))
            ih (relEventually_refl _))
          (relEventually_refl _))
        (relEventually_refl _)
    have hswap : relEventually
        (addSeq
          (addSeq
            (addSeq (addSeq (addSeq (regularSeqFinSum a n) (regularSeqFinSum b n))
              (regularSeqFinSum c n)) (a (n + 1)))
            (b (n + 1)))
          (c (n + 1)))
        (addSeq
          (addSeq
            (addSeq (regularSeqFinSum a n) (a (n + 1)))
            (addSeq (regularSeqFinSum b n) (b (n + 1))))
          (addSeq (regularSeqFinSum c n) (c (n + 1)))) :=
      bc1_addSeq_append3 (regularSeqFinSum a n) (regularSeqFinSum b n)
        (regularSeqFinSum c n) (a (n + 1)) (b (n + 1)) (c (n + 1))
    show relEventually _
      (addSeq (addSeq (regularSeqFinSum a (n + 1)) (regularSeqFinSum b (n + 1)))
        (regularSeqFinSum c (n + 1)))
    exact relEventually_trans _ _ _ hbase hswap

#print axioms BishopSec1P.bc1_finSum_merge3_a

/-- Technical lemma used in the public import closure. -/
theorem bc1_finSum_merge3_b (a b c : Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * N + 3))
      (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N))
        (regularSeqFinSum c N)) := by
  have h0 : bc1_seqMerge3 a b c (3 * N + 3) = a (N + 1) := by
    have := bc1_seqMerge3_zero a b c (N + 1)
    simpa [Nat.mul_succ] using this
  show relEventually
    (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * N + 2))
      (bc1_seqMerge3 a b c (3 * N + 3)))
    (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N))
      (regularSeqFinSum c N))
  rw [h0]
  have hbase : relEventually
      (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * N + 2)) (a (N + 1)))
      (addSeq
        (addSeq (addSeq (regularSeqFinSum a N) (regularSeqFinSum b N))
          (regularSeqFinSum c N))
        (a (N + 1))) :=
    addSeq_respects_eventually _ _ _ _
      (bc1_finSum_merge3_a a b c N) (relEventually_refl _)
  have hswap : relEventually
      (addSeq
        (addSeq (addSeq (regularSeqFinSum a N) (regularSeqFinSum b N))
          (regularSeqFinSum c N))
        (a (N + 1)))
      (addSeq
        (addSeq (addSeq (regularSeqFinSum a N) (a (N + 1)))
          (regularSeqFinSum b N))
        (regularSeqFinSum c N)) :=
    bc1_addSeq_append_left_of_three (regularSeqFinSum a N) (regularSeqFinSum b N)
      (regularSeqFinSum c N) (a (N + 1))
  show relEventually _
    (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N))
      (regularSeqFinSum c N))
  exact relEventually_trans _ _ _ hbase hswap

#print axioms BishopSec1P.bc1_finSum_merge3_b

/-- Technical lemma used in the public import closure. -/
theorem bc1_finSum_merge3_c (a b c : Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * N + 4))
      (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b (N + 1)))
        (regularSeqFinSum c N)) := by
  have h1 : bc1_seqMerge3 a b c (3 * N + 4) = b (N + 1) := by
    have := bc1_seqMerge3_one a b c (N + 1)
    simpa [Nat.mul_succ] using this
  show relEventually
    (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * N + 3))
      (bc1_seqMerge3 a b c (3 * N + 4)))
    (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b (N + 1)))
      (regularSeqFinSum c N))
  rw [h1]
  have hbase : relEventually
      (addSeq (regularSeqFinSum (bc1_seqMerge3 a b c) (3 * N + 3)) (b (N + 1)))
      (addSeq
        (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N))
          (regularSeqFinSum c N))
        (b (N + 1))) :=
    addSeq_respects_eventually _ _ _ _
      (bc1_finSum_merge3_b a b c N) (relEventually_refl _)
  have hswap : relEventually
      (addSeq
        (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b N))
          (regularSeqFinSum c N))
        (b (N + 1)))
      (addSeq
        (addSeq (regularSeqFinSum a (N + 1))
          (addSeq (regularSeqFinSum b N) (b (N + 1))))
        (regularSeqFinSum c N)) :=
    bc1_addSeq_append_middle_of_three (regularSeqFinSum a (N + 1))
      (regularSeqFinSum b N) (regularSeqFinSum c N) (b (N + 1))
  show relEventually _
    (addSeq (addSeq (regularSeqFinSum a (N + 1)) (regularSeqFinSum b (N + 1)))
      (regularSeqFinSum c N))
  exact relEventually_trans _ _ _ hbase hswap

#print axioms BishopSec1P.bc1_finSum_merge3_c

/-- Technical lemma used in the public import closure. -/
theorem bc1_repCloseAtGauge_add3 (k : Nat) {x x' y y' z z' : CReal}
    (hx : RepCloseAtGauge (k + 2) x x')
    (hy : RepCloseAtGauge (k + 2) y y')
    (hz : RepCloseAtGauge (k + 2) z z') :
    RepCloseAtGauge k (addSeq (addSeq x y) z) (addSeq (addSeq x' y') z') := by
  have hxy : RepCloseAtGauge (k + 1) (addSeq x y) (addSeq x' y') :=
    bc1_repCloseAtGauge_add (k + 1) hx hy
  have hz' : RepCloseAtGauge (k + 1) z z' :=
    repCloseAtGauge_weaken (by omega : k + 1 ≤ k + 2) hz
  exact bc1_repCloseAtGauge_add k hxy hz'

#print axioms BishopSec1P.bc1_repCloseAtGauge_add3

/-- Technical lemma used in the public import closure. -/
def bc1_repSeriesTendsto_merge3 {a b c : Nat → CReal} {su sv sw : CReal}
    (hu : RepSeriesTendsto (regularSeqFinSum a) su)
    (hv : RepSeriesTendsto (regularSeqFinSum b) sv)
    (hw : RepSeriesTendsto (regularSeqFinSum c) sw) :
    RepSeriesTendsto (regularSeqFinSum (bc1_seqMerge3 a b c))
      (addSeq (addSeq su sv) sw) where
  mod := fun k => 3 * (hu.mod (k + 3) + hv.mod (k + 3) + hw.mod (k + 3)) + 4
  close := by
    intro k n hn
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · obtain ⟨N, hN⟩ : ∃ N, n = 3 * N + 3 := ⟨n / 3 - 1, by omega⟩
      rw [hN]
      have hca : RepCloseAtGauge (k + 4) (regularSeqFinSum a (N + 1)) su :=
        hu.close (k + 3) (N + 1) (by omega)
      have hcb : RepCloseAtGauge (k + 4) (regularSeqFinSum b N) sv :=
        hv.close (k + 3) N (by omega)
      have hcc : RepCloseAtGauge (k + 4) (regularSeqFinSum c N) sw :=
        hw.close (k + 3) N (by omega)
      exact repCloseAtGauge_triangle_succ (k + 1)
        (bc1_repClose_of_relEventually (bc1_finSum_merge3_b a b c N) (k + 2))
        (bc1_repCloseAtGauge_add3 (k + 2) hca hcb hcc)
    · obtain ⟨N, hN⟩ : ∃ N, n = 3 * N + 4 := ⟨n / 3 - 1, by omega⟩
      rw [hN]
      have hca : RepCloseAtGauge (k + 4) (regularSeqFinSum a (N + 1)) su :=
        hu.close (k + 3) (N + 1) (by omega)
      have hcb : RepCloseAtGauge (k + 4) (regularSeqFinSum b (N + 1)) sv :=
        hv.close (k + 3) (N + 1) (by omega)
      have hcc : RepCloseAtGauge (k + 4) (regularSeqFinSum c N) sw :=
        hw.close (k + 3) N (by omega)
      exact repCloseAtGauge_triangle_succ (k + 1)
        (bc1_repClose_of_relEventually (bc1_finSum_merge3_c a b c N) (k + 2))
        (bc1_repCloseAtGauge_add3 (k + 2) hca hcb hcc)
    · obtain ⟨N, hN⟩ : ∃ N, n = 3 * N + 2 := ⟨n / 3, by omega⟩
      rw [hN]
      have hca : RepCloseAtGauge (k + 4) (regularSeqFinSum a N) su :=
        hu.close (k + 3) N (by omega)
      have hcb : RepCloseAtGauge (k + 4) (regularSeqFinSum b N) sv :=
        hv.close (k + 3) N (by omega)
      have hcc : RepCloseAtGauge (k + 4) (regularSeqFinSum c N) sw :=
        hw.close (k + 3) N (by omega)
      exact repCloseAtGauge_triangle_succ (k + 1)
        (bc1_repClose_of_relEventually (bc1_finSum_merge3_a a b c N) (k + 2))
        (bc1_repCloseAtGauge_add3 (k + 2) hca hcb hcc)

#print axioms BishopSec1P.bc1_repSeriesTendsto_merge3

/-- Technical lemma used in the public import closure. -/
def bc1_seriesSum_merge3 {a b c : Nat → CReal}
    (ha : RepSeriesSum a) (hb : RepSeriesSum b) (hc : RepSeriesSum c) :
    RepSeriesSum (bc1_seqMerge3 a b c) where
  sum := addSeq (addSeq ha.sum hb.sum) hc.sum
  tends := bc1_repSeriesTendsto_merge3 ha.tends hb.tends hc.tends

#print axioms BishopSec1P.bc1_seriesSum_merge3

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem bc1_seqMerge_map {α β : Type*} (φ : α → β) (a b : Nat → α) (n : Nat) :
    φ (bc1_seqMerge a b n)
      = bc1_seqMerge (fun k => φ (a k)) (fun k => φ (b k)) n := by
  unfold bc1_seqMerge
  split_ifs <;> rfl

#print axioms BishopSec1P.bc1_seqMerge_map

/-- Technical lemma used in the public import closure. -/
structure IntegrableRepC3 {X : Type*} (S : IntSpaceC X) : Type _ where
  fn : Nat → BFunC X
  fn_mem : ∀ n, fn n ∈ S.L
  abs_integral_sum : RepSeriesSum (fun n => S.I (BFunC.absf (fn n)))
  integral_sum : RepSeriesSum (fun n => S.I (fn n))

#print axioms BishopSec1P.IntegrableRepC3

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.integral {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : CReal :=
  (r.integral_sum).sum

#print axioms BishopSec1P.IntegrableRepC3.integral

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.add {X : Type*} {S : IntSpaceC X}
    (r r' : IntegrableRepC3 S) : IntegrableRepC3 S where
  fn := bc1_seqMerge r.fn r'.fn
  fn_mem := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      rw [hk, bc1_seqMerge_even]; exact r.fn_mem k
    · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      rw [hk, bc1_seqMerge_odd]; exact r'.fn_mem k
  abs_integral_sum := by
    have heq : (fun n => S.I (BFunC.absf (bc1_seqMerge r.fn r'.fn n)))
        = bc1_seqMerge (fun k => S.I (BFunC.absf (r.fn k)))
            (fun k => S.I (BFunC.absf (r'.fn k))) := by
      funext n
      rw [bc1_seqMerge_map BFunC.absf r.fn r'.fn n,
          bc1_seqMerge_map S.I (fun k => BFunC.absf (r.fn k))
            (fun k => BFunC.absf (r'.fn k)) n]
    rw [heq]
    exact bc1_seriesSum_interleave r.abs_integral_sum r'.abs_integral_sum
  integral_sum :=
    -- Technical note.
    -- Technical note.
    { sum := addSeq r.integral r'.integral
      tends := by
        have heq : (fun n => S.I (bc1_seqMerge r.fn r'.fn n))
            = bc1_seqMerge (fun k => S.I (r.fn k)) (fun k => S.I (r'.fn k)) := by
          funext n
          rw [bc1_seqMerge_map S.I r.fn r'.fn n]
        rw [heq]
        exact (bc1_seriesSum_interleave r.integral_sum r'.integral_sum).tends }

#print axioms BishopSec1P.IntegrableRepC3.add

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRepC3.integral_add {X : Type*} {S : IntSpaceC X}
    (r r' : IntegrableRepC3 S) :
    (r.add r').integral = addSeq r.integral r'.integral :=
  rfl

#print axioms BishopSec1P.IntegrableRepC3.integral_add

-- >>>v7:I.5
-- <<<v7:I.6
structure DataPFunRC (X : Type*) : Type _ where
  domData : X → Type*
  toFun : ∀ x : X, domData x → CReal

#print axioms BishopSec1P.DataPFunRC

def DataPFunRC.domain {X : Type*} (p : DataPFunRC X) : Set X :=
  { x | Nonempty (p.domData x) }

#print axioms BishopSec1P.DataPFunRC.domain

def DataPFunRC.fiber {X : Type*} (p : DataPFunRC X) (x : X) : Type* :=
  p.domData x

#print axioms BishopSec1P.DataPFunRC.fiber

theorem DataPFunRC.mem_domain_of_param {X : Type*} (p : DataPFunRC X) {x : X}
    (e : p.domData x) : x ∈ p.domain :=
  ⟨e⟩

#print axioms BishopSec1P.DataPFunRC.mem_domain_of_param

def DataPFunRC.valueAt {X : Type*} (p : DataPFunRC X) (x : X)
    (e : p.domData x) : CReal :=
  p.toFun x e

#print axioms BishopSec1P.DataPFunRC.valueAt

def DataPFunRC.Consistent {X : Type*} (p : DataPFunRC X) : Prop :=
  ∀ (x : X) (e e' : p.domData x), p.toFun x e ≈ p.toFun x e'

#print axioms BishopSec1P.DataPFunRC.Consistent

def DataPFunRC.zero (X : Type*) : DataPFunRC X where
  domData := fun _ => PUnit
  toFun := fun _ _ => CReal.zero

#print axioms BishopSec1P.DataPFunRC.zero

theorem DataPFunRC.zero_consistent (X : Type*) :
    (DataPFunRC.zero X).Consistent := by
  intro x e e'
  exact Setoid.refl _

#print axioms BishopSec1P.DataPFunRC.zero_consistent

theorem DataPFunRC.zero_domain (X : Type*) :
    (DataPFunRC.zero X).domain = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨PUnit.unit⟩

#print axioms BishopSec1P.DataPFunRC.zero_domain

def DataPFunRC.add {X : Type*} (p q : DataPFunRC X) : DataPFunRC X where
  domData := fun x => p.domData x × q.domData x
  toFun := fun x e => CReal.add (p.toFun x e.1) (q.toFun x e.2)

#print axioms BishopSec1P.DataPFunRC.add

theorem DataPFunRC.add_consistent {X : Type*} {p q : DataPFunRC X}
    (hp : p.Consistent) (hq : q.Consistent) :
    (p.add q).Consistent := by
  intro x e e'
  exact CReal.add_respects_equiv (p.toFun x e.1) (p.toFun x e'.1)
    (q.toFun x e.2) (q.toFun x e'.2) (hp x e.1 e'.1) (hq x e.2 e'.2)

#print axioms BishopSec1P.DataPFunRC.add_consistent

structure IntegrableRepC.PointwiseDomainData {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC S) (x : X) : Type _ where
  mem : ∀ n : Nat, x ∈ (r.fn n).dom
  absWitness : SeriesSumC (fun n => absSeq ((r.fn n).toFun x))

#print axioms BishopSec1P.IntegrableRepC.PointwiseDomainData

theorem IntegrableRepC.pointwiseDomainData_mem {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC S) {x : X}
    (hx : r.PointwiseDomainData x) : ∀ n : Nat, x ∈ (r.fn n).dom :=
  hx.mem

#print axioms BishopSec1P.IntegrableRepC.pointwiseDomainData_mem

-- >>>v7:I.6
-- <<<v7:I.7
namespace BishopRegularSeqIntegrableRep

def absDom {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (r : BishopCReal.BishopRegularSeqIntegrableRep S) (x : X) : Type :=
  BishopRegularSeqSeriesSum (fun n => absSeq ((r.fn n).toFun x))

#print axioms BishopSec1P.BishopRegularSeqIntegrableRep.absDom

def toDataPFunRC {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (r : BishopCReal.BishopRegularSeqIntegrableRep S) : DataPFunRC X where
  domData := fun x => absDom r x
  toFun := fun x habs => (r.value_law.value_from_abs x habs).val.sum

#print axioms BishopSec1P.BishopRegularSeqIntegrableRep.toDataPFunRC

theorem toDataPFunRC_faithful {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (r : BishopCReal.BishopRegularSeqIntegrableRep S) (x : X)
    (habs : absDom r x) :
    relEventually (r.pfun.toFun x) ((toDataPFunRC r).toFun x habs) := by
  exact (r.value_law.value_from_abs x habs).property

#print axioms BishopSec1P.BishopRegularSeqIntegrableRep.toDataPFunRC_faithful

theorem mem_toDataPFunRC_domain {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (r : BishopCReal.BishopRegularSeqIntegrableRep S) {x : X}
    (habs : absDom r x) :
    x ∈ (toDataPFunRC r).domain :=
  ⟨habs⟩

#print axioms BishopSec1P.BishopRegularSeqIntegrableRep.mem_toDataPFunRC_domain

end BishopRegularSeqIntegrableRep

-- >>>v7:I.7
-- <<<v7:I.8
structure CleanCharDataC {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type _ where
  rep : BishopCReal.BishopRegularSeqIntegrableRep S
  A : BishopC.BSet X
  value_one :
    ∀ x : X, x ∈ A.S1 →
      ∀ (habs : BishopRegularSeqIntegrableRep.absDom rep x),
        relEventually CReal.one
          ((BishopRegularSeqIntegrableRep.toDataPFunRC rep).toFun x habs)
  value_zero :
    ∀ x : X, x ∈ A.S2 →
      ∀ (habs : BishopRegularSeqIntegrableRep.absDom rep x),
        relEventually CReal.zero
          ((BishopRegularSeqIntegrableRep.toDataPFunRC rep).toFun x habs)
  abs_integral_eq :
    relEventually rep.integral rep.abs_integral_sum.sum

#print axioms BishopSec1P.CleanCharDataC

def CleanCharDataC.value {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (C : CleanCharDataC S) : DataPFunRC X :=
  BishopRegularSeqIntegrableRep.toDataPFunRC C.rep

#print axioms BishopSec1P.CleanCharDataC.value

theorem CleanCharDataC.value_one_on_s1 {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X} (C : CleanCharDataC S)
    {x : X} (hx : x ∈ C.A.S1)
    (habs : BishopRegularSeqIntegrableRep.absDom C.rep x) :
    relEventually CReal.one ((C.value).toFun x habs) :=
  C.value_one x hx habs

#print axioms BishopSec1P.CleanCharDataC.value_one_on_s1

theorem CleanCharDataC.value_zero_on_s2 {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X} (C : CleanCharDataC S)
    {x : X} (hx : x ∈ C.A.S2)
    (habs : BishopRegularSeqIntegrableRep.absDom C.rep x) :
    relEventually CReal.zero ((C.value).toFun x habs) :=
  C.value_zero x hx habs

#print axioms BishopSec1P.CleanCharDataC.value_zero_on_s2

theorem CleanCharDataC.value_faithful {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X} (C : CleanCharDataC S) (x : X)
    (habs : BishopRegularSeqIntegrableRep.absDom C.rep x) :
    relEventually (C.rep.pfun.toFun x) ((C.value).toFun x habs) :=
  BishopRegularSeqIntegrableRep.toDataPFunRC_faithful C.rep x habs

#print axioms BishopSec1P.CleanCharDataC.value_faithful

/-- Section 6 measure primitive for a clean characteristic set:
`mu(A) = integral chi_A`, over the presented Bishop real. -/
def CleanCharDataC.measure {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopCReal.BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (C : CleanCharDataC S) : CReal :=
  C.rep.integral

#print axioms BishopSec1P.CleanCharDataC.measure

/-- The clean-characteristic measure is definitionally the represented
integral. -/
theorem CleanCharDataC.measure_eq_integral {Arch : ScalarMulArchimedeanData}
    {X : Type} {S : BishopCReal.BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (C : CleanCharDataC S) :
    C.measure = C.rep.integral := rfl

#print axioms BishopSec1P.CleanCharDataC.measure_eq_integral

open BishopC BishopCRat

-- >>>v7:I.8
-- <<<v7:I.9
theorem regularSeq_nonneg_of_eventually_zero
    (x : RegularSeq) (hx : relEventually x zeroSeq) :
    ¬ regularSeqLtProp x zeroSeq := by
  intro hlt
  have hsub : relEventually (subSeq zeroSeq x) (subSeq zeroSeq zeroSeq) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq x zeroSeq
      (relEventually_refl zeroSeq) hx
  have hzeroSub : relEventually (subSeq zeroSeq zeroSeq) zeroSeq :=
    subSeq_self_eventually_law zeroSeq
  have hzero : relEventually (subSeq zeroSeq x) zeroSeq :=
    relEventually_trans
      (subSeq zeroSeq x) (subSeq zeroSeq zeroSeq) zeroSeq
      hsub hzeroSub
  exact not_posEventually_zero
    (posEventually_respects (subSeq zeroSeq x) zeroSeq hzero hlt)

#print axioms BishopSec1P.regularSeq_nonneg_of_eventually_zero

theorem regularSeqFinSum_const_eventually_zero
    (z : RegularSeq) (hz : relEventually z zeroSeq) :
    ∀ n : Nat, relEventually (regularSeqFinSum (fun _ : Nat => z) n) zeroSeq := by
  intro n
  induction n with
  | zero =>
      simpa [regularSeqFinSum] using hz
  | succ n ih =>
      have hadd :
          relEventually
            (addSeq (regularSeqFinSum (fun _ : Nat => z) n) z)
            (addSeq zeroSeq zeroSeq) :=
        addSeq_respects_eventually
          (regularSeqFinSum (fun _ : Nat => z) n) zeroSeq
          z zeroSeq ih hz
      have hzero : relEventually (addSeq zeroSeq zeroSeq) zeroSeq :=
        addSeq_zero_left_eventually zeroSeq
      simpa [regularSeqFinSum] using
        relEventually_trans
          (addSeq (regularSeqFinSum (fun _ : Nat => z) n) z)
          (addSeq zeroSeq zeroSeq) zeroSeq
          hadd hzero

#print axioms BishopSec1P.regularSeqFinSum_const_eventually_zero

def regularSeqSeriesSum_const_eventually_zero
    (z : RegularSeq) (hz : relEventually z zeroSeq) :
    BishopRegularSeqSeriesSum (fun _ : Nat => z) where
  sum := zeroSeq
  tends :=
    { modulus := fun _ => 0
      close := by
        intro _ n _
        exact regularSeqFinSum_const_eventually_zero z hz n }

#print axioms BishopSec1P.regularSeqSeriesSum_const_eventually_zero

theorem regularSeqSeriesSum_zero_eventually
    (s : BishopRegularSeqSeriesSum (fun _ : Nat => zeroSeq)) :
    relEventually s.sum zeroSeq := by
  have hclose :
      relEventually
        (regularSeqFinSum (fun _ : Nat => zeroSeq) (s.tends.modulus 0))
        s.sum :=
    s.tends.close 0 (s.tends.modulus 0) (Nat.le_refl _)
  have hfin :
      relEventually
        (regularSeqFinSum (fun _ : Nat => zeroSeq) (s.tends.modulus 0))
        zeroSeq :=
    regularSeqFinSum_const_eventually_zero zeroSeq
      (relEventually_refl zeroSeq) (s.tends.modulus 0)
  exact
    relEventually_trans
      s.sum
      (regularSeqFinSum (fun _ : Nat => zeroSeq) (s.tends.modulus 0))
      zeroSeq
      (relEventually_symm
        (regularSeqFinSum (fun _ : Nat => zeroSeq) (s.tends.modulus 0))
        s.sum hclose)
      hfin

#print axioms BishopSec1P.regularSeqSeriesSum_zero_eventually

theorem concrete_pos_witness {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {g : BishopRegularSeqPFun X} (hg : g ∈ S.core.L)
    (hpos : regularSeqLtData zeroSeq (S.core.I g)) :
    ∃ x : X, x ∈ g.dom ∧ regularSeqLtProp zeroSeq (g.toFun x) := by
  let zfun : BishopRegularSeqPFun X :=
    { toFun := fun _ => zeroSeq
      dom := g.dom }
  have hsmul0_mem : BishopRegularSeqPFun.smul Arch zeroSeq g ∈ S.core.L :=
    S.core.smul_mem zeroSeq hg
  have hsmul0_equiv :
      BishopRegularSeqPFun.equiv
        (BishopRegularSeqPFun.smul Arch zeroSeq g) zfun := by
    constructor
    · rfl
    · intro x _
      change relEventually (mulSeqConcreteWith Arch zeroSeq (g.toFun x)) zeroSeq
      exact mulSeqConcrete_zero_left_eventually Arch (g.toFun x)
  have hzmem : zfun ∈ S.core.L :=
    S.core.L_resp hsmul0_mem hsmul0_equiv
  have hznn : ∀ n : Nat, BishopRegularSeqPFun.PointwiseNonneg zfun := by
    intro _
    exact
      { not_lt := by
          intro _ _
          change ¬ regularSeqLtProp zeroSeq zeroSeq
          exact regularSeqLtProp_irrefl zeroSeq }
  have hIz_resp :
      relEventually
        (S.core.I (BishopRegularSeqPFun.smul Arch zeroSeq g))
        (S.core.I zfun) :=
    S.core.I_resp hsmul0_mem hsmul0_equiv
  have hIz_smul :
      relEventually
        (S.core.I (BishopRegularSeqPFun.smul Arch zeroSeq g))
        (mulSeqConcreteWith Arch zeroSeq (S.core.I g)) :=
    S.core.I_smul zeroSeq hg
  have hIz_zero :
      relEventually (mulSeqConcreteWith Arch zeroSeq (S.core.I g)) zeroSeq :=
    mulSeqConcrete_zero_left_eventually Arch (S.core.I g)
  have hIz : relEventually (S.core.I zfun) zeroSeq :=
    relEventually_trans
      (S.core.I zfun)
      (S.core.I (BishopRegularSeqPFun.smul Arch zeroSeq g))
      zeroSeq
      (relEventually_symm
        (S.core.I (BishopRegularSeqPFun.smul Arch zeroSeq g))
        (S.core.I zfun) hIz_resp)
      (relEventually_trans
        (S.core.I (BishopRegularSeqPFun.smul Arch zeroSeq g))
        (mulSeqConcreteWith Arch zeroSeq (S.core.I g))
        zeroSeq hIz_smul hIz_zero)
  let hI : BishopRegularSeqSeriesSum (fun _ : Nat => S.core.I zfun) :=
    regularSeqSeriesSum_const_eventually_zero (S.core.I zfun) hIz
  have hlt : regularSeqLtData hI.sum (S.core.I g) := by
    simpa [hI, regularSeqSeriesSum_const_eventually_zero] using hpos
  have hpsb : BishopRegularSeqPointwiseSeriesBelow (fun _ : Nat => zfun) g :=
    S.continuity (f := g) (fs := fun _ : Nat => zfun)
      hg (fun _ => hzmem) hznn hI hlt
  have hpoint_zero : relEventually hpsb.point_sum.sum zeroSeq := by
    simpa [zfun] using (regularSeqSeriesSum_zero_eventually hpsb.point_sum)
  have hpoint_nonneg : ¬ regularSeqLtProp hpsb.point_sum.sum zeroSeq :=
    regularSeq_nonneg_of_eventually_zero hpsb.point_sum.sum hpoint_zero
  have hbelow : regularSeqLtProp hpsb.point_sum.sum (g.toFun hpsb.x) :=
    regularSeqLtData_to_prop hpsb.below
  rcases regularSeqLtProp_cotrans hpsb.point_sum.sum (g.toFun hpsb.x) zeroSeq hbelow with
    hsum_lt_zero | hzero_lt_g
  · exact False.elim (hpoint_nonneg hsum_lt_zero)
  · exact ⟨hpsb.x, hpsb.hx_f, hzero_lt_g⟩

#print axioms BishopSec1P.concrete_pos_witness

theorem concrete_I_nonneg {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {g : BishopRegularSeqPFun X} (hg : g ∈ S.core.L)
    (hgnn : BishopRegularSeqPFun.PointwiseNonneg g) :
    ¬ regularSeqLtProp (S.core.I g) zeroSeq := by
  intro hneg
  rcases hneg with ⟨k, N, hN⟩
  let neg_g : BishopRegularSeqPFun X := BishopRegularSeqPFun.neg Arch g
  have hneg_mem : neg_g ∈ S.core.L := by
    simpa [neg_g] using (def11_neg_mem S hg)
  have hI_smul :
      relEventually
        (S.core.I (BishopRegularSeqPFun.smul Arch (negSeq oneSeq) g))
        (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I g)) :=
    S.core.I_smul (negSeq oneSeq) hg
  have hI_negmul :
      relEventually
        (S.core.I neg_g)
        (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I g)) := by
    simpa [neg_g, BishopRegularSeqPFun.neg] using hI_smul
  have hI_neg : relEventually (S.core.I neg_g) (negSeq (S.core.I g)) :=
    relEventually_trans
      (S.core.I neg_g)
      (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I g))
      (negSeq (S.core.I g))
      hI_negmul
      (mulSeq_neg_one_left_eventually_neg Arch (S.core.I g))
  have hsub1 :
      relEventually
        (subSeq (S.core.I neg_g) zeroSeq)
        (subSeq (negSeq (S.core.I g)) zeroSeq) :=
    subSeq_respects_eventually
      (S.core.I neg_g) (negSeq (S.core.I g))
      zeroSeq zeroSeq hI_neg (relEventually_refl zeroSeq)
  have hsub2 :
      relEventually
        (subSeq (negSeq (S.core.I g)) zeroSeq)
        (negSeq (S.core.I g)) :=
    subSeq_zero_right_eventually (negSeq (S.core.I g))
  have hsub3 :
      relEventually (negSeq (S.core.I g)) (subSeq zeroSeq (S.core.I g)) :=
    relEventually_symm
      (subSeq zeroSeq (S.core.I g))
      (negSeq (S.core.I g))
      (subSeq_zero_left_eventually (S.core.I g))
  have hsub_rel :
      relEventually
        (subSeq (S.core.I neg_g) zeroSeq)
        (subSeq zeroSeq (S.core.I g)) :=
    relEventually_trans
      (subSeq (S.core.I neg_g) zeroSeq)
      (subSeq (negSeq (S.core.I g)) zeroSeq)
      (subSeq zeroSeq (S.core.I g))
      hsub1
      (relEventually_trans
        (subSeq (negSeq (S.core.I g)) zeroSeq)
        (negSeq (S.core.I g))
        (subSeq zeroSeq (S.core.I g))
        hsub2 hsub3)
  rcases relEventually_point_lower
      (subSeq zeroSeq (S.core.I g))
      (subSeq (S.core.I neg_g) zeroSeq)
      (relEventually_symm
        (subSeq (S.core.I neg_g) zeroSeq)
        (subSeq zeroSeq (S.core.I g)) hsub_rel)
      (k + 1) with ⟨Nrel, hNrel⟩
  let hIneg : regularSeqLtData zeroSeq (S.core.I neg_g) :=
    { k := k + 1
      N := N + Nrel
      tail_pos := by
        intro n hn
        have hnN : N ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
        have hnRel : Nrel ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
        have htail := hN n hnN
        have hshift :
            COF.lt (eps (k + 1))
              ((subSeq zeroSeq (S.core.I g)).val n - eps (k + 1)) := by
          have t := COF.lt_add_left (-(eps (k + 1))) htail
          rwa [← eps_succ_add_self k,
            show -(eps (k + 1)) + (eps (k + 1) + eps (k + 1)) =
                eps (k + 1) from by ring,
            show -(eps (k + 1)) + (subSeq zeroSeq (S.core.I g)).val n =
                (subSeq zeroSeq (S.core.I g)).val n - eps (k + 1) from by ring] at t
        exact BishopC.lt_of_lt_of_le hshift (hNrel n hnRel) }
  obtain ⟨x, hxdom, hxpos⟩ := concrete_pos_witness S hneg_mem hIneg
  have hxdom_g : x ∈ g.dom := by
    simpa [neg_g, BishopRegularSeqPFun.neg, BishopRegularSeqPFun.smul] using hxdom
  have hxlt_g : regularSeqLtProp (g.toFun x) zeroSeq := by
    have hval : relEventually (neg_g.toFun x) (negSeq (g.toFun x)) := by
      change relEventually
        (mulSeqConcreteWith Arch (negSeq oneSeq) (g.toFun x))
        (negSeq (g.toFun x))
      exact mulSeq_neg_one_left_eventually_neg Arch (g.toFun x)
    have hsuba :
        relEventually
          (subSeq (neg_g.toFun x) zeroSeq)
          (subSeq (negSeq (g.toFun x)) zeroSeq) :=
      subSeq_respects_eventually
        (neg_g.toFun x) (negSeq (g.toFun x))
        zeroSeq zeroSeq hval (relEventually_refl zeroSeq)
    have hsubb :
        relEventually
          (subSeq (negSeq (g.toFun x)) zeroSeq)
          (negSeq (g.toFun x)) :=
      subSeq_zero_right_eventually (negSeq (g.toFun x))
    have hsubc :
        relEventually (negSeq (g.toFun x)) (subSeq zeroSeq (g.toFun x)) :=
      relEventually_symm
        (subSeq zeroSeq (g.toFun x))
        (negSeq (g.toFun x))
        (subSeq_zero_left_eventually (g.toFun x))
    have htarget :
        relEventually
          (subSeq (neg_g.toFun x) zeroSeq)
          (subSeq zeroSeq (g.toFun x)) :=
      relEventually_trans
        (subSeq (neg_g.toFun x) zeroSeq)
        (subSeq (negSeq (g.toFun x)) zeroSeq)
        (subSeq zeroSeq (g.toFun x))
        hsuba
        (relEventually_trans
          (subSeq (negSeq (g.toFun x)) zeroSeq)
          (negSeq (g.toFun x))
          (subSeq zeroSeq (g.toFun x))
          hsubb hsubc)
    exact posEventually_respects
      (subSeq (neg_g.toFun x) zeroSeq)
      (subSeq zeroSeq (g.toFun x)) htarget hxpos
  exact hgnn.not_lt x hxdom_g hxlt_g

#print axioms BishopSec1P.concrete_I_nonneg

/-! ### Concrete `BishopRegularSeqSeriesSum` arithmetic -/

-- >>>v7:I.9
-- <<<v7:I.4
namespace BishopRegularSeqSeriesSum

theorem sum_unique {u : Nat → RegularSeq}
    (a b : BishopRegularSeqSeriesSum u) : relEventually a.sum b.sum := by
  let n : Nat := a.tends.modulus 0 + b.tends.modulus 0
  have haN : a.tends.modulus 0 <= n := by
    dsimp [n]
    exact Nat.le_add_right _ _
  have hbN : b.tends.modulus 0 <= n := by
    dsimp [n]
    exact Nat.le_add_left _ _
  have ha : relEventually (regularSeqFinSum u n) a.sum :=
    a.tends.close 0 n haN
  have hb : relEventually (regularSeqFinSum u n) b.sum :=
    b.tends.close 0 n hbN
  exact
    relEventually_trans
      a.sum
      (regularSeqFinSum u n)
      b.sum
      (relEventually_symm (regularSeqFinSum u n) a.sum ha)
      hb

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.sum_unique

/-- Technical lemma used in the public import closure. -/
theorem regularSeqFinSum_negSeq (u : Nat → RegularSeq) (n : Nat) :
    relEventually
      (regularSeqFinSum (fun n => negSeq (u n)) n)
      (negSeq (regularSeqFinSum u n)) := by
  induction n with
  | zero =>
      simpa [regularSeqFinSum] using
        relEventually_refl (negSeq (u 0))
  | succ n ih =>
      have hcong :
          relEventually
            (addSeq
              (regularSeqFinSum (fun n => negSeq (u n)) n)
              (negSeq (u (Nat.succ n))))
            (addSeq
              (negSeq (regularSeqFinSum u n))
              (negSeq (u (Nat.succ n)))) :=
        addSeq_respects_eventually
          (regularSeqFinSum (fun n => negSeq (u n)) n)
          (negSeq (regularSeqFinSum u n))
          (negSeq (u (Nat.succ n)))
          (negSeq (u (Nat.succ n)))
          ih
          (relEventually_refl (negSeq (u (Nat.succ n))))
      have hstep :
          relEventually
            (addSeq
              (negSeq (regularSeqFinSum u n))
              (negSeq (u (Nat.succ n))))
            (negSeq
              (addSeq (regularSeqFinSum u n) (u (Nat.succ n)))) := by
        apply rel_to_relEventually
        change relVal
          (addVal
            (negVal (regularSeqFinSum u n).val)
            (negVal (u (Nat.succ n)).val))
          (negVal
            (addVal (regularSeqFinSum u n).val
              (u (Nat.succ n)).val))
        intro m
        unfold addVal addIndex negVal
        ring_nf
        change BishopC.Le (BishopCRat.CRat.absF 0) (tol m)
        rw [scalarCOFOSeed.abs_zero]
        exact tol_nonneg m
      simpa [regularSeqFinSum] using
        relEventually_trans
          (addSeq
            (regularSeqFinSum (fun n => negSeq (u n)) n)
            (negSeq (u (Nat.succ n))))
          (addSeq
            (negSeq (regularSeqFinSum u n))
            (negSeq (u (Nat.succ n))))
          (negSeq
            (addSeq (regularSeqFinSum u n) (u (Nat.succ n))))
          hcong
          hstep

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.regularSeqFinSum_negSeq

/-- Technical lemma used in the public import closure. -/
theorem regularSeqFinSum_mulSeq (a : CReal) (u : Nat → CReal) (n : Nat) :
    relEventually
      (regularSeqFinSum (fun k => CReal.mul a (u k)) n)
      (CReal.mul a (regularSeqFinSum u n)) := by
  induction n with
  | zero =>
      simpa [regularSeqFinSum] using
        relEventually_refl (CReal.mul a (u 0))
  | succ n ih =>
      have hcong :
          relEventually
            (addSeq (regularSeqFinSum (fun k => CReal.mul a (u k)) n)
              (CReal.mul a (u (Nat.succ n))))
            (addSeq (CReal.mul a (regularSeqFinSum u n))
              (CReal.mul a (u (Nat.succ n)))) :=
        addSeq_respects_eventually
          (regularSeqFinSum (fun k => CReal.mul a (u k)) n)
          (CReal.mul a (regularSeqFinSum u n))
          (CReal.mul a (u (Nat.succ n)))
          (CReal.mul a (u (Nat.succ n)))
          ih
          (relEventually_refl (CReal.mul a (u (Nat.succ n))))
      have hstep :
          relEventually
            (addSeq (CReal.mul a (regularSeqFinSum u n))
              (CReal.mul a (u (Nat.succ n))))
            (CReal.mul a (addSeq (regularSeqFinSum u n) (u (Nat.succ n)))) :=
        relEventually_symm
          (CReal.mul a (addSeq (regularSeqFinSum u n) (u (Nat.succ n))))
          (addSeq (CReal.mul a (regularSeqFinSum u n))
            (CReal.mul a (u (Nat.succ n))))
          (mulSeqConcrete_left_distrib_eventually cRatScalarMulArch a
            (regularSeqFinSum u n) (u (Nat.succ n)))
      simpa [regularSeqFinSum] using
        relEventually_trans
          (addSeq (regularSeqFinSum (fun k => CReal.mul a (u k)) n)
            (CReal.mul a (u (Nat.succ n))))
          (addSeq (CReal.mul a (regularSeqFinSum u n))
            (CReal.mul a (u (Nat.succ n))))
          (CReal.mul a (addSeq (regularSeqFinSum u n) (u (Nat.succ n))))
          hcong hstep

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.regularSeqFinSum_mulSeq

/-- Technical lemma used in the public import closure. -/
theorem repCloseAtGauge_negSeq {x y : CReal} (k : Nat)
    (h : RepCloseAtGauge (k + 1) x y) :
    RepCloseAtGauge k (negSeq x) (negSeq y) := by
  refine repCloseAtGauge_of_absdiff_le
    (x := negSeq x) (y := negSeq y) (u := x) (v := y) k ?_ h
  apply regularSeqLe_of_relEventually
  have hstepA :
      relEventually (subSeq (negSeq x) (negSeq y)) (negSeq (subSeq x y)) := by
    apply rel_to_relEventually
    change relVal
      (subVal (negVal x.val) (negVal y.val))
      (negVal (subVal x.val y.val))
    intro m
    unfold subVal negVal
    ring_nf
    change BishopC.Le (BishopCRat.CRat.absF 0) (tol m)
    rw [scalarCOFOSeed.abs_zero]
    exact tol_nonneg m
  have hstepB :
      relEventually
        (absSeq (subSeq (negSeq x) (negSeq y)))
        (absSeq (negSeq (subSeq x y))) :=
    absSeq_respects_eventually _ _ hstepA
  have hstepC :
      relEventually (absSeq (negSeq (subSeq x y))) (absSeq (subSeq x y)) :=
    absSeq_negSeq_eventually (subSeq x y)
  exact
    relEventually_trans
      (absSeq (subSeq (negSeq x) (negSeq y)))
      (absSeq (negSeq (subSeq x y)))
      (absSeq (subSeq x y))
      hstepB hstepC

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.repCloseAtGauge_negSeq

/-- Technical lemma used in the public import closure. -/
def repSeriesSum_neg {u : Nat → CReal} (a : RepSeriesSum u) :
    RepSeriesSum (fun n => negSeq (u n)) where
  sum := negSeq a.sum
  tends :=
    { mod := fun k => a.tends.mod (k + 2)
      close := by
        intro k n hn
        have hclose3 : RepCloseAtGauge (k + 3) (regularSeqFinSum u n) a.sum :=
          a.tends.close (k + 2) n hn
        have hneg : RepCloseAtGauge (k + 2)
            (negSeq (regularSeqFinSum u n)) (negSeq a.sum) :=
          repCloseAtGauge_negSeq (k + 2) hclose3
        refine repCloseAtGauge_of_absdiff_le
          (x := regularSeqFinSum (fun n => negSeq (u n)) n) (y := negSeq a.sum)
          (u := negSeq (regularSeqFinSum u n)) (v := negSeq a.sum) (k + 1) ?_ hneg
        apply regularSeqLe_of_relEventually
        apply absSeq_respects_eventually
        exact subSeq_respects_eventually _ _ _ _
          (regularSeqFinSum_negSeq u n) (relEventually_refl (negSeq a.sum)) }

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.repSeriesSum_neg

def neg {u : Nat → RegularSeq}
    (a : BishopRegularSeqSeriesSum u) :
    BishopRegularSeqSeriesSum (fun n => negSeq (u n)) where
  sum := negSeq a.sum
  tends :=
    { modulus := a.tends.modulus
      close := by
        intro k n hn
        have hfin_all : ∀ n : Nat,
            relEventually
              (regularSeqFinSum (fun n => negSeq (u n)) n)
              (negSeq (regularSeqFinSum u n)) := by
          intro n
          induction n with
          | zero =>
              simpa [regularSeqFinSum] using
                relEventually_refl (negSeq (u 0))
          | succ n ih =>
              have hcong :
                  relEventually
                    (addSeq
                      (regularSeqFinSum (fun n => negSeq (u n)) n)
                      (negSeq (u (Nat.succ n))))
                    (addSeq
                      (negSeq (regularSeqFinSum u n))
                      (negSeq (u (Nat.succ n)))) :=
                addSeq_respects_eventually
                  (regularSeqFinSum (fun n => negSeq (u n)) n)
                  (negSeq (regularSeqFinSum u n))
                  (negSeq (u (Nat.succ n)))
                  (negSeq (u (Nat.succ n)))
                  ih
                  (relEventually_refl (negSeq (u (Nat.succ n))))
              have hstep :
                  relEventually
                    (addSeq
                      (negSeq (regularSeqFinSum u n))
                      (negSeq (u (Nat.succ n))))
                    (negSeq
                      (addSeq (regularSeqFinSum u n) (u (Nat.succ n)))) := by
                apply rel_to_relEventually
                change relVal
                  (addVal
                    (negVal (regularSeqFinSum u n).val)
                    (negVal (u (Nat.succ n)).val))
                  (negVal
                    (addVal (regularSeqFinSum u n).val
                      (u (Nat.succ n)).val))
                intro m
                unfold addVal addIndex negVal
                ring_nf
                change BishopC.Le (BishopCRat.CRat.absF 0) (tol m)
                rw [scalarCOFOSeed.abs_zero]
                exact tol_nonneg m
              simpa [regularSeqFinSum] using
                relEventually_trans
                  (addSeq
                    (regularSeqFinSum (fun n => negSeq (u n)) n)
                    (negSeq (u (Nat.succ n))))
                  (addSeq
                    (negSeq (regularSeqFinSum u n))
                    (negSeq (u (Nat.succ n))))
                  (negSeq
                    (addSeq (regularSeqFinSum u n) (u (Nat.succ n))))
                  hcong
                  hstep
        have hfin :
            relEventually
              (regularSeqFinSum (fun n => negSeq (u n)) n)
              (negSeq (regularSeqFinSum u n)) :=
          hfin_all n
        have hlim :
            relEventually
              (negSeq (regularSeqFinSum u n))
              (negSeq a.sum) :=
          negSeq_respects_eventually
            (regularSeqFinSum u n) a.sum
            (a.tends.close k n hn)
        exact
          relEventually_trans
            (regularSeqFinSum (fun n => negSeq (u n)) n)
            (negSeq (regularSeqFinSum u n))
            (negSeq a.sum)
            hfin
            hlim }

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.neg

theorem neg_sum {u : Nat → RegularSeq}
    (a : BishopRegularSeqSeriesSum u) :
    relEventually (BishopRegularSeqSeriesSum.neg a).sum (negSeq a.sum) :=
  relEventually_refl (negSeq a.sum)

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.neg_sum

def add {u v : Nat → RegularSeq}
    (a : BishopRegularSeqSeriesSum u) (b : BishopRegularSeqSeriesSum v) :
    BishopRegularSeqSeriesSum (fun n => addSeq (u n) (v n)) where
  sum := addSeq a.sum b.sum
  tends :=
    { modulus := fun k => a.tends.modulus k + b.tends.modulus k
      close := by
        intro k n hn
        have haN : a.tends.modulus k <= n :=
          Nat.le_trans (Nat.le_add_right _ _) hn
        have hbN : b.tends.modulus k <= n :=
          Nat.le_trans (Nat.le_add_left _ _) hn
        have hfin_all : ∀ n : Nat,
            relEventually
              (regularSeqFinSum (fun n => addSeq (u n) (v n)) n)
              (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n)) := by
          intro n
          induction n with
          | zero =>
              simpa [regularSeqFinSum] using
                relEventually_refl (addSeq (u 0) (v 0))
          | succ n ih =>
              have hcong :
                  relEventually
                    (addSeq
                      (regularSeqFinSum (fun n => addSeq (u n) (v n)) n)
                      (addSeq (u (Nat.succ n)) (v (Nat.succ n))))
                    (addSeq
                      (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n))
                      (addSeq (u (Nat.succ n)) (v (Nat.succ n)))) :=
                addSeq_respects_eventually
                  (regularSeqFinSum (fun n => addSeq (u n) (v n)) n)
                  (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n))
                  (addSeq (u (Nat.succ n)) (v (Nat.succ n)))
                  (addSeq (u (Nat.succ n)) (v (Nat.succ n)))
                  ih
                  (relEventually_refl
                    (addSeq (u (Nat.succ n)) (v (Nat.succ n))))
              have hswap :
                  relEventually
                    (addSeq
                      (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n))
                      (addSeq (u (Nat.succ n)) (v (Nat.succ n))))
                    (addSeq
                      (addSeq (regularSeqFinSum u n) (u (Nat.succ n)))
                      (addSeq (regularSeqFinSum v n) (v (Nat.succ n)))) := by
                apply rel_to_relEventually
                change relVal
                  (addVal
                    (addVal (regularSeqFinSum u n).val
                      (regularSeqFinSum v n).val)
                    (addVal (u (Nat.succ n)).val
                      (v (Nat.succ n)).val))
                  (addVal
                    (addVal (regularSeqFinSum u n).val
                      (u (Nat.succ n)).val)
                    (addVal (regularSeqFinSum v n).val
                      (v (Nat.succ n)).val))
                intro m
                unfold addVal addIndex
                ring_nf
                change BishopC.Le (BishopCRat.CRat.absF 0) (tol m)
                rw [scalarCOFOSeed.abs_zero]
                exact tol_nonneg m
              simpa [regularSeqFinSum] using
                relEventually_trans
                  (addSeq
                    (regularSeqFinSum (fun n => addSeq (u n) (v n)) n)
                    (addSeq (u (Nat.succ n)) (v (Nat.succ n))))
                  (addSeq
                    (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n))
                    (addSeq (u (Nat.succ n)) (v (Nat.succ n))))
                  (addSeq
                    (addSeq (regularSeqFinSum u n) (u (Nat.succ n)))
                    (addSeq (regularSeqFinSum v n) (v (Nat.succ n))))
                  hcong
                  hswap
        have hfin :
            relEventually
              (regularSeqFinSum (fun n => addSeq (u n) (v n)) n)
              (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n)) :=
          hfin_all n
        have hlim :
            relEventually
              (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n))
              (addSeq a.sum b.sum) :=
          addSeq_respects_eventually
            (regularSeqFinSum u n) a.sum
            (regularSeqFinSum v n) b.sum
            (a.tends.close k n haN)
            (b.tends.close k n hbN)
        exact
          relEventually_trans
            (regularSeqFinSum (fun n => addSeq (u n) (v n)) n)
            (addSeq (regularSeqFinSum u n) (regularSeqFinSum v n))
            (addSeq a.sum b.sum)
            hfin
            hlim }

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.add

theorem add_sum {u v : Nat → RegularSeq}
    (a : BishopRegularSeqSeriesSum u) (b : BishopRegularSeqSeriesSum v) :
    relEventually (BishopRegularSeqSeriesSum.add a b).sum
      (addSeq a.sum b.sum) :=
  relEventually_refl (addSeq a.sum b.sum)

#print axioms BishopSec1P.BishopRegularSeqSeriesSum.add_sum

end BishopRegularSeqSeriesSum

/-- Multiplication by a fixed left scalar transports one-gauge representative
closeness.  The input gauge is shifted by the scalar Archimedean bound. -/
theorem repCloseAtGauge_mul_left (c x y : CReal) (k : Nat)
    (hxy : RepCloseAtGauge (CReal.mulArchBound c + (k + 2)) x y) :
    RepCloseAtGauge k (CReal.mul c x) (CReal.mul c y) := by
  rcases hxy with ⟨Nxy, hNxy⟩
  set K : Nat := mulBoundWith cRatScalarMulArch c x with hKdef
  set L : Nat := mulBoundWith cRatScalarMulArch c y with hLdef
  set C : Nat := Nat.max K L with hCdef
  have hKleC : K ≤ C := by
    rw [hCdef]
    exact Nat.le_max_left K L
  have hLleC : L ≤ C := by
    rw [hCdef]
    exact Nat.le_max_right K L
  have hcK : standardBoundWith cRatScalarMulArch c ≤ K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_left cRatScalarMulArch c x
  have hxK : standardBoundWith cRatScalarMulArch x ≤ K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_right cRatScalarMulArch c x
  have hcL : standardBoundWith cRatScalarMulArch c ≤ L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_left cRatScalarMulArch c y
  have hyL : standardBoundWith cRatScalarMulArch y ≤ L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_right cRatScalarMulArch c y
  have hcC : standardBoundWith cRatScalarMulArch c ≤ C := Nat.le_trans hcK hKleC
  have hxC : standardBoundWith cRatScalarMulArch x ≤ C := Nat.le_trans hxK hKleC
  have hyC : standardBoundWith cRatScalarMulArch y ≤ C := Nat.le_trans hyL hLleC
  refine ⟨Nxy + (k + 3), ?_⟩
  intro n hn
  have hnN : Nxy ≤ n := by omega
  have htoln : k + 2 + 1 ≤ n := by omega
  set cidx : Nat := mulIndexFromBound C n with hcidxdef
  have hn_cidx : n ≤ cidx := by
    rw [hcidxdef]
    exact le_mulIndexFromBound C n
  have hN_cidx : Nxy ≤ cidx := Nat.le_trans hnN hn_cidx
  have hcx_close :
      BishopC.Le (COF.abs (c.val cidx - c.val cidx))
        (eps (standardBoundWith cRatScalarMulArch y + (k + 2))) := by
    rw [show c.val cidx - c.val cidx = (0 : Scalar) from by ring]
    change BishopC.Le (BishopCRat.CRat.absF 0)
      (eps (standardBoundWith cRatScalarMulArch y + (k + 2)))
    rw [scalarCOFOSeed.abs_zero]
    exact eps_nonneg (standardBoundWith cRatScalarMulArch y + (k + 2))
  have hxy_close :
      BishopC.Le (COF.abs (x.val cidx - y.val cidx))
        (eps (standardBoundWith cRatScalarMulArch c + (k + 2))) := by
    simpa [CReal.mulArchBound] using hNxy cidx hN_cidx
  have hleft0 : BishopC.Le (COF.abs (mulValWithBound K c.val x.val n -
      mulValWithBound C c.val x.val n)) (tol n) :=
    mulValWithBound_change_le_tol cRatScalarMulArch c x (K := K) (L := C) (n := n)
      hcK hcC hxK hxC
  have hleft : BishopC.Le (COF.abs (mulValWithBound K c.val x.val n -
      mulValWithBound C c.val x.val n)) (eps (k + 2)) :=
    BishopC.le_trans hleft0 (tol_le_eps_of_succ_le (k := k + 2) (n := n) htoln)
  have hmid : BishopC.Le (COF.abs (mulValWithBound C c.val x.val n -
      mulValWithBound C c.val y.val n)) (eps (k + 1)) :=
    mulValWithBound_common_respects_point cRatScalarMulArch c c x y C k n
      (by simpa [cidx, hcidxdef] using hcx_close)
      (by simpa [cidx, hcidxdef] using hxy_close)
  have hright0 : BishopC.Le (COF.abs (mulValWithBound C c.val y.val n -
      mulValWithBound L c.val y.val n)) (tol n) :=
    mulValWithBound_change_le_tol cRatScalarMulArch c y (K := C) (L := L) (n := n)
      hcC hcL hyC hyL
  have hright : BishopC.Le (COF.abs (mulValWithBound C c.val y.val n -
      mulValWithBound L c.val y.val n)) (eps (k + 2)) :=
    BishopC.le_trans hright0 (tol_le_eps_of_succ_le (k := k + 2) (n := n) htoln)
  change BishopC.Le (COF.abs (boundedMulValWith cRatScalarMulArch c x n -
      boundedMulValWith cRatScalarMulArch c y n)) (eps k)
  unfold boundedMulValWith
  rw [← hKdef, ← hLdef]
  have htri := scalar_abs_sub_le_three
    (mulValWithBound K c.val x.val n)
    (mulValWithBound C c.val x.val n)
    (mulValWithBound C c.val y.val n)
    (mulValWithBound L c.val y.val n)
  have htail := BishopC.le_add hmid hright
  have hsum := BishopC.le_add hleft htail
  have hbudget : BishopC.Le (eps (k + 2) + (eps (k + 1) + eps (k + 2))) (eps k) := by
    rw [show eps (k + 2) + (eps (k + 1) + eps (k + 2)) =
        (eps (k + 2) + eps (k + 2)) + eps (k + 1) from by ring]
    rw [show k + 2 = k + 1 + 1 from by omega]
    rw [eps_succ_add_self (k + 1), eps_succ_add_self k]
    exact BishopC.le_refl (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

#print axioms BishopSec1P.repCloseAtGauge_mul_left

/-- A represented #3 series can be multiplied by a fixed left scalar. -/
def repSeriesSum_smul (c : CReal) {u : Nat → CReal} (hu : RepSeriesSum u) :
    RepSeriesSum (fun n => mulSeqConcreteWith cRatScalarMulArch c (u n)) where
  sum := mulSeqConcreteWith cRatScalarMulArch c hu.sum
  tends :=
    { mod := fun k => hu.tends.mod (CReal.mulArchBound c + (k + 3))
      close := by
        intro k n hn
        have hclose_src : RepCloseAtGauge
            ((CReal.mulArchBound c + (k + 3)) + 1)
            (regularSeqFinSum u n) hu.sum :=
          hu.tends.close (CReal.mulArchBound c + (k + 3)) n hn
        have hclose_src' : RepCloseAtGauge
            (CReal.mulArchBound c + ((k + 2) + 2))
            (regularSeqFinSum u n) hu.sum := by
          simpa [Nat.add_assoc] using hclose_src
        have hmul : RepCloseAtGauge (k + 2)
            (mulSeqConcreteWith cRatScalarMulArch c (regularSeqFinSum u n))
            (mulSeqConcreteWith cRatScalarMulArch c hu.sum) :=
          repCloseAtGauge_mul_left c (regularSeqFinSum u n) hu.sum (k + 2)
            hclose_src'
        refine repCloseAtGauge_of_absdiff_le
          (x := regularSeqFinSum
            (fun n => mulSeqConcreteWith cRatScalarMulArch c (u n)) n)
          (y := mulSeqConcreteWith cRatScalarMulArch c hu.sum)
          (u := mulSeqConcreteWith cRatScalarMulArch c (regularSeqFinSum u n))
          (v := mulSeqConcreteWith cRatScalarMulArch c hu.sum) (k + 1) ?_ hmul
        apply regularSeqLe_of_relEventually
        apply absSeq_respects_eventually
        exact subSeq_respects_eventually _ _ _ _
          (BishopRegularSeqSeriesSum.regularSeqFinSum_mulSeq c u n)
          (relEventually_refl (mulSeqConcreteWith cRatScalarMulArch c hu.sum)) }

#print axioms BishopSec1P.repSeriesSum_smul

/-- Technical lemma used in the public import closure. -/
theorem bc1_regularSeqFinSum_congr_terms (u v : Nat → RegularSeq)
    (hterm : ∀ n, relEventually (u n) (v n)) (N : Nat) :
    relEventually (regularSeqFinSum u N) (regularSeqFinSum v N) := by
  induction N with
  | zero => simpa [regularSeqFinSum] using hterm 0
  | succ n ih =>
      simpa [regularSeqFinSum] using
        addSeq_respects_eventually
          (regularSeqFinSum u n) (regularSeqFinSum v n)
          (u (Nat.succ n)) (v (Nat.succ n)) ih (hterm (Nat.succ n))

#print axioms BishopSec1P.bc1_regularSeqFinSum_congr_terms

def repSeriesSum_congr {a b : Nat → CReal}
    (ha : RepSeriesSum a) (heq : ∀ n, relEventually (b n) (a n)) :
    RepSeriesSum b where
  sum := ha.sum
  tends := bc1_repSeriesTendsto_congr ha.tends
    (fun n => bc1_regularSeqFinSum_congr_terms b a heq n)

#print axioms BishopSec1P.repSeriesSum_congr

def repSeriesSum_single (c : CReal) :
    RepSeriesSum (fun m => if m = 0 then c else CReal.zero) where
  sum := c
  tends :=
    { mod := fun _ => 0
      close := by
        intro k n _hn
        have hfin :
            ∀ n : Nat,
              relEventually
                (regularSeqFinSum (fun m => if m = 0 then c else CReal.zero) n) c := by
          intro n
          induction n with
          | zero =>
              simpa [regularSeqFinSum] using relEventually_refl c
          | succ n ih =>
              have hcong :
                  relEventually
                    (addSeq
                      (regularSeqFinSum
                        (fun m => if m = 0 then c else CReal.zero) n)
                      CReal.zero)
                    (addSeq c CReal.zero) :=
                addSeq_respects_eventually
                  (regularSeqFinSum
                    (fun m => if m = 0 then c else CReal.zero) n)
                  c CReal.zero CReal.zero ih (relEventually_refl CReal.zero)
              have hzero : relEventually (addSeq c CReal.zero) c :=
                CReal.add_zero c
              simpa [regularSeqFinSum] using relEventually_trans
                (addSeq
                  (regularSeqFinSum
                    (fun m => if m = 0 then c else CReal.zero) n)
                  CReal.zero)
                (addSeq c CReal.zero) c hcong hzero
        exact bc1_repClose_of_relEventually (hfin n) (k + 1) }

#print axioms BishopSec1P.repSeriesSum_single

def repSeriesSum_add {a b : Nat → CReal}
    (ha : RepSeriesSum a) (hb : RepSeriesSum b) :
    RepSeriesSum (fun n => addSeq (a n) (b n)) :=
  bc1_addSeq_series ha hb

#print axioms BishopSec1P.repSeriesSum_add

def repSeriesSum_sub {a b : Nat → CReal}
    (ha : RepSeriesSum a) (hb : RepSeriesSum b) :
    RepSeriesSum (fun n => subSeq (a n) (b n)) :=
  repSeriesSum_congr
    (repSeriesSum_add ha (BishopRegularSeqSeriesSum.repSeriesSum_neg hb))
    (fun n => subSeq_eq_add_neg_eventually (a n) (b n))

#print axioms BishopSec1P.repSeriesSum_sub

theorem repSeriesSum_unique {a : Nat → CReal}
    (ha hb : RepSeriesSum a) : relEventually ha.sum hb.sum := by
  intro k
  let N : Nat := Nat.max (ha.tends.mod (k + 1)) (hb.tends.mod (k + 1))
  have hNa : ha.tends.mod (k + 1) ≤ N := by
    dsimp [N]
    exact Nat.le_max_left _ _
  have hNb : hb.tends.mod (k + 1) ≤ N := by
    dsimp [N]
    exact Nat.le_max_right _ _
  have ha_close : RepCloseAtGauge ((k + 1) + 1)
      (regularSeqFinSum a N) ha.sum :=
    ha.tends.close (k + 1) N hNa
  have hb_close : RepCloseAtGauge ((k + 1) + 1)
      (regularSeqFinSum a N) hb.sum :=
    hb.tends.close (k + 1) N hNb
  have htri : RepCloseAtGauge (k + 1) ha.sum hb.sum :=
    repCloseAtGauge_triangle_succ (k + 1)
      (repCloseAtGauge_symm ha_close) hb_close
  exact repCloseAtGauge_weaken (Nat.le_succ k) htri

#print axioms BishopSec1P.repSeriesSum_unique

theorem repSeriesSum_sum_eq {a b : Nat → CReal}
    (ha : RepSeriesSum a) (h : ∀ n, relEventually (a n) (b n))
    (hb : RepSeriesSum b) : relEventually ha.sum hb.sum := by
  let hb' : RepSeriesSum b :=
    repSeriesSum_congr ha (fun n => relEventually_symm _ _ (h n))
  change relEventually hb'.sum hb.sum
  exact repSeriesSum_unique hb' hb

#print axioms BishopSec1P.repSeriesSum_sum_eq

theorem regularSeqLe_subSeq_right {a b : CReal} (c : CReal)
    (hab : RegularSeqLe a b) : RegularSeqLe (subSeq c b) (subSeq c a) := by
  change RegularSeqNonneg (subSeq (subSeq c a) (subSeq c b))
  have hev :
      relEventually
        (subSeq (subSeq c a) (subSeq c b))
        (subSeq b a) := by
    have hinner :
        relEventually
          (subSeq (subSeq c a) (subSeq b a))
          (subSeq c b) :=
      subSeq_same_right_diff_eventually b c a
    have hmain :
        relEventually
          (subSeq (subSeq c a) (subSeq c b))
          (subSeq (subSeq c a)
            (subSeq (subSeq c a) (subSeq b a))) :=
      subSeq_respects_eventually
        (subSeq c a) (subSeq c a)
        (subSeq c b) (subSeq (subSeq c a) (subSeq b a))
        (relEventually_refl (subSeq c a))
        (relEventually_symm
          (subSeq (subSeq c a) (subSeq b a))
          (subSeq c b) hinner)
    exact relEventually_trans
      (subSeq (subSeq c a) (subSeq c b))
      (subSeq (subSeq c a)
        (subSeq (subSeq c a) (subSeq b a)))
      (subSeq b a)
      hmain
      (subSeq_right_sub_cancel_eventually (subSeq c a) (subSeq b a))
  exact regularSeqNonneg_of_eventual hev hab

#print axioms BishopSec1P.regularSeqLe_subSeq_right

theorem regularSeqLtProp_of_le_of_lt {x y z : CReal}
    (hxy : RegularSeqLe x y) (hyz : regularSeqLtProp y z) :
    regularSeqLtProp x z := by
  rcases regularSeqLtProp_cotrans y z x hyz with hyx | hxz
  · exact False.elim (regularSeqLe_not_lt_reverse_prop hxy hyx)
  · exact hxz

#print axioms BishopSec1P.regularSeqLtProp_of_le_of_lt

theorem regularSeqLtProp_of_lt_of_le {x y z : CReal}
    (hxy : regularSeqLtProp x y) (hyz : RegularSeqLe y z) :
    regularSeqLtProp x z := by
  rcases regularSeqLtProp_cotrans x y z hxy with hxz | hzy
  · exact hxz
  · exact False.elim (regularSeqLe_not_lt_reverse_prop hyz hzy)

#print axioms BishopSec1P.regularSeqLtProp_of_lt_of_le

theorem regularSeqLtProp_zero_lt_sub {x y : CReal}
    (hxy : regularSeqLtProp x y) :
    CReal.ltE CReal.zero (subSeq y x) := by
  change PosEventually (subSeq (subSeq y x) zeroSeq)
  exact posEventually_respects
    (subSeq y x)
    (subSeq (subSeq y x) zeroSeq)
    (relEventually_symm
      (subSeq (subSeq y x) zeroSeq)
      (subSeq y x)
      (subSeq_zero_right_eventually (subSeq y x)))
    hxy

#print axioms BishopSec1P.regularSeqLtProp_zero_lt_sub

theorem regularSeqLtProp_sub_of_repClose_succ {x y : CReal} (k : Nat)
    (hclose : RepCloseAtGauge (k + 1) x y) :
    regularSeqLtProp (subSeq y x) (constSeq (eps k)) := by
  let d : CReal := subSeq x y
  have habs_lt :
      regularSeqLtProp (absSeq d) (constSeq (eps k)) := by
    have hq := ltQuot_abs_sub_const_of_repClose_succ x y k hclose
    change regularSeqLtProp (absSeq (subSeq x y)) (constSeq (eps k)) at hq
    simpa [d] using hq
  have hneg_abs : RegularSeqLe (negSeq d) (absSeq d) := by
    have hbase : RegularSeqLe (negSeq d) (absSeq (negSeq d)) :=
      base_le_abs_base_regularSeqLe (negSeq d)
    exact regularSeqLe_of_right_eventual
      (absSeq_negSeq_eventually d) hbase
  have hle : RegularSeqLe (subSeq y x) (absSeq d) :=
    regularSeqLe_of_left_eventual
      (by simpa [d] using subSeq_comm_neg_eventually y x)
      hneg_abs
  exact regularSeqLtProp_of_le_of_lt hle habs_lt

#print axioms BishopSec1P.regularSeqLtProp_sub_of_repClose_succ

theorem regularSeqFinSum_mono_of_nonneg {a : Nat → CReal}
    (ha : ∀ n, RegularSeqNonneg (a n)) {N M : Nat} (hNM : N ≤ M) :
    RegularSeqLe (regularSeqFinSum a N) (regularSeqFinSum a M) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hNM
  subst M
  simpa using
    (partialSum_gap ha (fun n => regularSeqLe_refl (a n)) N d).1

#print axioms BishopSec1P.regularSeqFinSum_mono_of_nonneg

theorem repLe_of_tendsto_le {a : Nat → CReal} (ha : RepSeriesSum a) (c : CReal)
    (hub : ∀ N, RegularSeqLe (regularSeqFinSum a N) c) :
    RegularSeqLe ha.sum c := by
  intro hcounter
  have hpos_order : regularSeqLtProp c ha.sum :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hpos_sub : CReal.ltE CReal.zero (subSeq ha.sum c) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  obtain ⟨k, hk⟩ := CReal.archimedean_E (subSeq ha.sum c) hpos_sub
  let N : Nat := ha.tends.mod k
  have hclose : RepCloseAtGauge (k + 1) (regularSeqFinSum a N) ha.sum :=
    ha.tends.close k N (Nat.le_refl _)
  have hsum_partial_lt :
      regularSeqLtProp
        (subSeq ha.sum (regularSeqFinSum a N)) (constSeq (eps k)) :=
    regularSeqLtProp_sub_of_repClose_succ k hclose
  have hle_gap :
      RegularSeqLe
        (subSeq ha.sum c)
        (subSeq ha.sum (regularSeqFinSum a N)) :=
    regularSeqLe_subSeq_right ha.sum (hub N)
  have heps_lt_gap :
      regularSeqLtProp
        (constSeq (eps k))
        (subSeq ha.sum (regularSeqFinSum a N)) :=
    regularSeqLtProp_of_lt_of_le (by simpa [CReal.epsSeq] using hk) hle_gap
  exact regularSeqLtProp_irrefl (constSeq (eps k))
    (regularSeqLtProp_trans
      (constSeq (eps k))
      (subSeq ha.sum (regularSeqFinSum a N))
      (constSeq (eps k))
      heps_lt_gap hsum_partial_lt)

#print axioms BishopSec1P.repLe_of_tendsto_le

theorem repPartialSum_le_sum {a : Nat → CReal} (ha : ∀ n, RegularSeqNonneg (a n))
    (hb : RepSeriesSum a) (N : Nat) :
    RegularSeqLe (regularSeqFinSum a N) hb.sum := by
  intro hcounter
  have hpos_order : regularSeqLtProp hb.sum (regularSeqFinSum a N) :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hpos_sub : CReal.ltE CReal.zero (subSeq (regularSeqFinSum a N) hb.sum) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  obtain ⟨k, hk⟩ :=
    CReal.archimedean_E (subSeq (regularSeqFinSum a N) hb.sum) hpos_sub
  let M : Nat := Nat.max N (hb.tends.mod k)
  have hNM : N ≤ M := by
    dsimp [M]
    exact Nat.le_max_left _ _
  have hmodM : hb.tends.mod k ≤ M := by
    dsimp [M]
    exact Nat.le_max_right _ _
  have hmono :
      RegularSeqLe (regularSeqFinSum a N) (regularSeqFinSum a M) :=
    regularSeqFinSum_mono_of_nonneg ha hNM
  have hgap_mono :
      RegularSeqLe
        (subSeq (regularSeqFinSum a N) hb.sum)
        (subSeq (regularSeqFinSum a M) hb.sum) :=
    subSeq_monotone_left_regularSeqLe
      (regularSeqFinSum a N) (regularSeqFinSum a M) hb.sum hmono
  have hclose : RepCloseAtGauge (k + 1) hb.sum (regularSeqFinSum a M) :=
    repCloseAtGauge_symm (hb.tends.close k M hmodM)
  have hpartial_sum_lt :
      regularSeqLtProp
        (subSeq (regularSeqFinSum a M) hb.sum) (constSeq (eps k)) :=
    regularSeqLtProp_sub_of_repClose_succ k hclose
  have heps_lt_gap :
      regularSeqLtProp
        (constSeq (eps k))
        (subSeq (regularSeqFinSum a M) hb.sum) :=
    regularSeqLtProp_of_lt_of_le (by simpa [CReal.epsSeq] using hk) hgap_mono
  exact regularSeqLtProp_irrefl (constSeq (eps k))
    (regularSeqLtProp_trans
      (constSeq (eps k))
      (subSeq (regularSeqFinSum a M) hb.sum)
      (constSeq (eps k))
      heps_lt_gap hpartial_sum_lt)

#print axioms BishopSec1P.repPartialSum_le_sum

/-- Order-limit (upper): if the sequence `w` has a rep-carrying limit `d` and is
eventually `≤ c`, then the limit is `≤ c`.  Choice-free; mirrors
`repLe_of_tendsto_le`. -/
theorem repLimitData_le_of_eventually_le {w : Nat → CReal}
    (d : CRealRepLimitData w) (c : CReal) (N₀ : Nat)
    (hub : ∀ n, N₀ ≤ n → RegularSeqLe (w n) c) :
    RegularSeqLe d.limit c := by
  intro hcounter
  have hpos_order : regularSeqLtProp c d.limit :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hpos_sub : CReal.ltE CReal.zero (subSeq d.limit c) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  obtain ⟨k, hk⟩ := CReal.archimedean_E (subSeq d.limit c) hpos_sub
  let N : Nat := Nat.max N₀ (d.lmod k)
  have hN0 : N₀ ≤ N := Nat.le_max_left _ _
  have hmod : d.lmod k ≤ N := Nat.le_max_right _ _
  have hclose : RepCloseAtGauge (k + 1) (w N) d.limit := d.close k N hmod
  have hsum_partial_lt :
      regularSeqLtProp (subSeq d.limit (w N)) (constSeq (eps k)) :=
    regularSeqLtProp_sub_of_repClose_succ k hclose
  have hle_gap :
      RegularSeqLe (subSeq d.limit c) (subSeq d.limit (w N)) :=
    regularSeqLe_subSeq_right d.limit (hub N hN0)
  have heps_lt_gap :
      regularSeqLtProp (constSeq (eps k)) (subSeq d.limit (w N)) :=
    regularSeqLtProp_of_lt_of_le (by simpa [CReal.epsSeq] using hk) hle_gap
  exact regularSeqLtProp_irrefl (constSeq (eps k))
    (regularSeqLtProp_trans (constSeq (eps k))
      (subSeq d.limit (w N)) (constSeq (eps k))
      heps_lt_gap hsum_partial_lt)

#print axioms BishopSec1P.repLimitData_le_of_eventually_le

/-- Order-limit (lower): if the sequence `w` has a rep-carrying limit `d` and is
eventually `≥ c`, then the limit is `≥ c`.  Choice-free; mirrors
`repPartialSum_le_sum`. -/
theorem repLimitData_ge_of_eventually_ge {w : Nat → CReal}
    (d : CRealRepLimitData w) (c : CReal) (N₀ : Nat)
    (hlb : ∀ n, N₀ ≤ n → RegularSeqLe c (w n)) :
    RegularSeqLe c d.limit := by
  intro hcounter
  have hpos_order : regularSeqLtProp d.limit c :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hpos_sub : CReal.ltE CReal.zero (subSeq c d.limit) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  obtain ⟨k, hk⟩ := CReal.archimedean_E (subSeq c d.limit) hpos_sub
  let M : Nat := Nat.max N₀ (d.lmod k)
  have hN0 : N₀ ≤ M := Nat.le_max_left _ _
  have hmodM : d.lmod k ≤ M := Nat.le_max_right _ _
  have hgap :
      RegularSeqLe (subSeq c d.limit) (subSeq (w M) d.limit) :=
    subSeq_monotone_left_regularSeqLe c (w M) d.limit (hlb M hN0)
  have hclose : RepCloseAtGauge (k + 1) d.limit (w M) :=
    repCloseAtGauge_symm (d.close k M hmodM)
  have hpartial_lt :
      regularSeqLtProp (subSeq (w M) d.limit) (constSeq (eps k)) :=
    regularSeqLtProp_sub_of_repClose_succ k hclose
  have heps_lt_gap :
      regularSeqLtProp (constSeq (eps k)) (subSeq (w M) d.limit) :=
    regularSeqLtProp_of_lt_of_le (by simpa [CReal.epsSeq] using hk) hgap
  exact regularSeqLtProp_irrefl (constSeq (eps k))
    (regularSeqLtProp_trans (constSeq (eps k))
      (subSeq (w M) d.limit) (constSeq (eps k))
      heps_lt_gap hpartial_lt)

#print axioms BishopSec1P.repLimitData_ge_of_eventually_ge

namespace BFunC

theorem seqSum_toFun {X : Type*} (u : Nat → BFunC X) (x : X) :
    ∀ n, (BFunC.seqSum u n).toFun x =
      regularSeqFinSum (fun n => (u n).toFun x) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show addSeq ((BFunC.seqSum u n).toFun x) ((u (n + 1)).toFun x) =
        addSeq (regularSeqFinSum (fun n => (u n).toFun x) n)
          ((u (n + 1)).toFun x)
      rw [ih]

#print axioms BishopSec1P.BFunC.seqSum_toFun

theorem posPart_pwnn {X : Type*} (f : BFunC X) :
    BFunC.PointwiseNonneg (BFunC.posPart f) := by
  intro x _hx
  exact regularSeqLe_zero_of_nonneg
    (by
      simpa [BFunC.posPart, BFunC.maxC] using
        CReal.max_zero_nonneg_E (f.toFun x))

#print axioms BishopSec1P.BFunC.posPart_pwnn

theorem negPart_pwnn {X : Type*} (f : BFunC X) :
    BFunC.PointwiseNonneg (BFunC.negPart f) := by
  intro x _hx
  exact regularSeqLe_zero_of_nonneg
    (by
      simpa [BFunC.negPart] using
        CReal.neg_min_zero_nonneg_E (f.toFun x))

#print axioms BishopSec1P.BFunC.negPart_pwnn

theorem posPart_le_abs {X : Type*} (f : BFunC X) :
    BFunC.PointwiseLE (BFunC.posPart f) (BFunC.absf f) where
  dom_eq := rfl
  le_val := by
    intro x _hx
    exact regularSeqLe_of_not_ltQuot
      (CReal.max (f.toFun x) CReal.zero)
      (CReal.abs (f.toFun x))
      (by
        change ¬ regularSeqLtProp
          (CReal.abs (f.toFun x))
          (CReal.max (f.toFun x) CReal.zero)
        exact CReal.max_le_abs_E (f.toFun x))

#print axioms BishopSec1P.BFunC.posPart_le_abs

theorem negPart_le_abs {X : Type*} (f : BFunC X) :
    BFunC.PointwiseLE (BFunC.negPart f) (BFunC.absf f) where
  dom_eq := rfl
  le_val := by
    intro x _hx
    exact regularSeqLe_of_not_ltQuot
      (CReal.neg (CReal.min (f.toFun x) CReal.zero))
      (CReal.abs (f.toFun x))
      (by
        change ¬ regularSeqLtProp
          (CReal.abs (f.toFun x))
          (CReal.neg (CReal.min (f.toFun x) CReal.zero))
        exact CReal.neg_min_le_abs_E (f.toFun x))

#print axioms BishopSec1P.BFunC.negPart_le_abs

end BFunC

namespace IntSpaceC

variable {X : Type*} (S : IntSpaceC X)

theorem I_seqSum {u : Nat → BFunC X} (hu : ∀ n, u n ∈ S.L) :
    ∀ n, S.I (BFunC.seqSum u n) ≈
      regularSeqFinSum (fun k => S.I (u k)) n := by
  intro n
  induction n with
  | zero => exact relEventually_refl (S.I (u 0))
  | succ n ih =>
      have hI :=
        S.I_add (S.seqSum_mem hu n) (hu (n + 1))
      have hcong :
          relEventually
            (addSeq (S.I (BFunC.seqSum u n)) (S.I (u (n + 1))))
            (addSeq (regularSeqFinSum (fun k => S.I (u k)) n)
              (S.I (u (n + 1)))) :=
        addSeq_respects_eventually
          (S.I (BFunC.seqSum u n))
          (regularSeqFinSum (fun k => S.I (u k)) n)
          (S.I (u (n + 1))) (S.I (u (n + 1)))
          ih (relEventually_refl (S.I (u (n + 1))))
      simpa [regularSeqFinSum] using relEventually_trans
        (S.I (BFunC.seqSum u (n + 1)))
        (addSeq (S.I (BFunC.seqSum u n)) (S.I (u (n + 1))))
        (addSeq (regularSeqFinSum (fun k => S.I (u k)) n)
          (S.I (u (n + 1))))
        hI hcong

#print axioms BishopSec1P.IntSpaceC.I_seqSum

def I_posPart_seriesConvC {f : Nat → BFunC X}
    (hmem : ∀ n, f n ∈ S.L)
    (habs : RepSeriesSum (fun n => S.I (BFunC.absf (f n)))) :
    RepSeriesSum (fun n => S.I (BFunC.posPart (f n))) :=
  repSeriesSum_comparison
    (fun n => regularSeqNonneg_of_zero_le
      (S.I_nonneg (S.posPart_mem (hmem n)) (BFunC.posPart_pwnn (f n))))
    (fun n => S.I_mono (S.posPart_mem (hmem n)) (S.abs_mem (hmem n))
      (BFunC.posPart_le_abs (f n)))
    habs

#print axioms BishopSec1P.IntSpaceC.I_posPart_seriesConvC

def I_negPart_seriesConvC {f : Nat → BFunC X}
    (hmem : ∀ n, f n ∈ S.L)
    (habs : RepSeriesSum (fun n => S.I (BFunC.absf (f n)))) :
    RepSeriesSum (fun n => S.I (BFunC.negPart (f n))) :=
  repSeriesSum_comparison
    (fun n => regularSeqNonneg_of_zero_le
      (S.I_nonneg (S.negPart_mem (hmem n)) (BFunC.negPart_pwnn (f n))))
    (fun n => S.I_mono (S.negPart_mem (hmem n)) (S.abs_mem (hmem n))
      (BFunC.negPart_le_abs (f n)))
    habs

#print axioms BishopSec1P.IntSpaceC.I_negPart_seriesConvC

end IntSpaceC

theorem regularSeqLe_cancel_add_right {a b c : CReal}
    (h : RegularSeqLe (addSeq a c) (addSeq b c)) :
    RegularSeqLe a b := by
  change RegularSeqNonneg (subSeq b a)
  have hev :
      relEventually
        (subSeq b a)
        (subSeq (addSeq b c) (addSeq a c)) := by
    have hb_comm :
        relEventually
          (subSeq (addSeq b c) c)
          (subSeq (addSeq c b) c) :=
      subSeq_respects_eventually
        (addSeq b c) (addSeq c b) c c
        (addSeq_comm_eventually b c)
        (relEventually_refl c)
    have hb_cancel :
        relEventually (subSeq (addSeq c b) c) b :=
      subSeq_add_left_cancel_eventually c b
    have hb_sub :
        relEventually (subSeq (addSeq b c) c) b :=
      relEventually_trans
        (subSeq (addSeq b c) c)
        (subSeq (addSeq c b) c)
        b hb_comm hb_cancel
    have ha_comm :
        relEventually
          (subSeq (addSeq a c) c)
          (subSeq (addSeq c a) c) :=
      subSeq_respects_eventually
        (addSeq a c) (addSeq c a) c c
        (addSeq_comm_eventually a c)
        (relEventually_refl c)
    have ha_cancel :
        relEventually (subSeq (addSeq c a) c) a :=
      subSeq_add_left_cancel_eventually c a
    have ha_sub :
        relEventually (subSeq (addSeq a c) c) a :=
      relEventually_trans
        (subSeq (addSeq a c) c)
        (subSeq (addSeq c a) c)
        a ha_comm ha_cancel
    have hsame :
        relEventually
          (subSeq (subSeq (addSeq b c) c) (subSeq (addSeq a c) c))
          (subSeq (addSeq b c) (addSeq a c)) :=
      subSeq_same_right_diff_eventually (addSeq a c) (addSeq b c) c
    have hcancel_sub :
        relEventually
          (subSeq (subSeq (addSeq b c) c) (subSeq (addSeq a c) c))
          (subSeq b a) :=
      subSeq_respects_eventually
        (subSeq (addSeq b c) c) b
        (subSeq (addSeq a c) c) a
        hb_sub ha_sub
    exact relEventually_trans
      (subSeq b a)
      (subSeq (subSeq (addSeq b c) c) (subSeq (addSeq a c) c))
      (subSeq (addSeq b c) (addSeq a c))
      (relEventually_symm
        (subSeq (subSeq (addSeq b c) c) (subSeq (addSeq a c) c))
        (subSeq b a) hcancel_sub)
      hsame
  exact regularSeqNonneg_of_eventual hev h

#print axioms BishopSec1P.regularSeqLe_cancel_add_right

theorem max_sub_negmin_eq_self (a : CReal) :
    relEventually
      (subSeq (CReal.max a CReal.zero)
        (CReal.neg (CReal.min a CReal.zero)))
      a := by
  have hsub :
      relEventually
        (subSeq (CReal.max a CReal.zero)
          (CReal.neg (CReal.min a CReal.zero)))
        (addSeq (CReal.max a CReal.zero)
          (negSeq (CReal.neg (CReal.min a CReal.zero)))) :=
    subSeq_eq_add_neg_eventually
      (CReal.max a CReal.zero) (CReal.neg (CReal.min a CReal.zero))
  have hneg :
      relEventually
        (negSeq (CReal.neg (CReal.min a CReal.zero)))
        (CReal.min a CReal.zero) :=
    negSeq_negSeq_eventually (CReal.min a CReal.zero)
  have hadd :
      relEventually
        (addSeq (CReal.max a CReal.zero)
          (negSeq (CReal.neg (CReal.min a CReal.zero))))
        (addSeq (CReal.max a CReal.zero) (CReal.min a CReal.zero)) :=
    addSeq_respects_eventually
      (CReal.max a CReal.zero) (CReal.max a CReal.zero)
      (negSeq (CReal.neg (CReal.min a CReal.zero)))
      (CReal.min a CReal.zero)
      (relEventually_refl (CReal.max a CReal.zero))
      hneg
  exact relEventually_trans _ _ _ (relEventually_trans _ _ _ hsub hadd)
    (max_add_min_eq_self a)

#print axioms BishopSec1P.max_sub_negmin_eq_self

theorem IntSpaceC.lemma_1_7C {X : Type*} (S : IntSpaceC X)
    {f : Nat → BFunC X}
    (hmem : ∀ n, f n ∈ S.L)
    (habs : RepSeriesSum (fun n => S.I (BFunC.absf (f n))))
    (hpos : ∀ x : X, (∀ n, x ∈ (f n).dom) →
              RepSeriesSum (fun n => CReal.abs ((f n).toFun x)) →
              ∀ (hfx : RepSeriesSum (fun n => (f n).toFun x)),
                RegularSeqNonneg hfx.sum)
    (hsum : RepSeriesSum (fun n => S.I (f n))) :
    RegularSeqNonneg hsum.sum := by
  let cP := IntSpaceC.I_posPart_seriesConvC S hmem habs
  let cM := IntSpaceC.I_negPart_seriesConvC S hmem habs
  have habs_split :
      relEventually habs.sum (addSeq cP.sum cM.sum) :=
    repSeriesSum_sum_eq habs
      (fun n => S.I_absf_eq (hmem n))
      (repSeriesSum_add cP cM)
  have per_N : ∀ N : Nat,
      RegularSeqLe
        (addSeq
          (regularSeqFinSum
            (fun n => S.I (BFunC.negPart (f n))) N)
          (regularSeqFinSum
            (fun n => S.I (BFunC.negPart (f n))) N))
        habs.sum := by
    intro N
    let negTerms : Nat → BFunC X := fun n => BFunC.negPart (f n)
    let G : BFunC X :=
      BFunC.add (BFunC.seqSum negTerms N) (BFunC.seqSum negTerms N)
    let pm : CReal := regularSeqFinSum (fun n => S.I (negTerms n)) N
    have hgmem : ∀ n, negTerms n ∈ S.L := by
      intro n
      exact S.negPart_mem (hmem n)
    have hseq_mem : BFunC.seqSum negTerms N ∈ S.L :=
      S.seqSum_mem hgmem N
    have hGmem : G ∈ S.L := by
      exact S.add_mem hseq_mem hseq_mem
    have hIseq : relEventually (S.I (BFunC.seqSum negTerms N)) pm :=
      S.I_seqSum hgmem N
    have hIG : relEventually (S.I G) (addSeq pm pm) :=
      relEventually_trans _ _ _
        (by simpa [G] using S.I_add hseq_mem hseq_mem)
        (addSeq_respects_eventually
          (S.I (BFunC.seqSum negTerms N)) pm
          (S.I (BFunC.seqSum negTerms N)) pm
          hIseq hIseq)
    have hmain : RegularSeqLe (S.I G) habs.sum := by
      intro hcounter
      have hlt : CReal.ltE habs.sum (S.I G) :=
        regularSeqLtProp_reverse_of_le_counterexample hcounter
      have hpsb :=
        S.continuity (f := G) (fs := fun n => BFunC.absf (f n))
          hGmem
          (fun n => S.abs_mem (hmem n))
          (fun n x hx => by
            simpa [BFunC.absf] using
              absSeq_nonnegative_regularSeqLe ((f n).toFun x))
          habs hlt
      rcases hpsb with ⟨x, _hxG, hxfs, point_sum, below⟩
      have hx_orig : ∀ n, x ∈ (f n).dom := by
        intro n
        simpa [BFunC.absf] using hxfs n
      have point_abs :
          RepSeriesSum (fun n => CReal.abs ((f n).toFun x)) := by
        simpa [BFunC.absf] using point_sum
      have cPx :
          RepSeriesSum
            (fun n => CReal.max ((f n).toFun x) CReal.zero) := by
        refine repSeriesSum_comparison ?_ ?_ point_abs
        · intro n
          change ¬ CReal.ltE
            (CReal.max ((f n).toFun x) CReal.zero) CReal.zero
          exact CReal.max_zero_nonneg_E ((f n).toFun x)
        · intro n
          exact regularSeqLe_of_not_ltQuot
            (CReal.max ((f n).toFun x) CReal.zero)
            (CReal.abs ((f n).toFun x))
            (by
              change ¬ regularSeqLtProp
                (CReal.abs ((f n).toFun x))
                (CReal.max ((f n).toFun x) CReal.zero)
              exact CReal.max_le_abs_E ((f n).toFun x))
      have cMx :
          RepSeriesSum
            (fun n => CReal.neg (CReal.min ((f n).toFun x) CReal.zero)) := by
        refine repSeriesSum_comparison ?_ ?_ point_abs
        · intro n
          change ¬ CReal.ltE
            (CReal.neg (CReal.min ((f n).toFun x) CReal.zero))
            CReal.zero
          exact CReal.neg_min_zero_nonneg_E ((f n).toFun x)
        · intro n
          exact regularSeqLe_of_not_ltQuot
            (CReal.neg (CReal.min ((f n).toFun x) CReal.zero))
            (CReal.abs ((f n).toFun x))
            (by
              change ¬ regularSeqLtProp
                (CReal.abs ((f n).toFun x))
                (CReal.neg (CReal.min ((f n).toFun x) CReal.zero))
              exact CReal.neg_min_le_abs_E ((f n).toFun x))
      have hterm_self : ∀ n,
          relEventually ((f n).toFun x)
            (subSeq
              (CReal.max ((f n).toFun x) CReal.zero)
              (CReal.neg (CReal.min ((f n).toFun x) CReal.zero))) := by
        intro n
        exact relEventually_symm _ _
          (max_sub_negmin_eq_self ((f n).toFun x))
      let cSubx := repSeriesSum_sub cPx cMx
      have hfx : RepSeriesSum (fun n => (f n).toFun x) :=
        repSeriesSum_congr cSubx hterm_self
      have hfx_split_raw : relEventually hfx.sum cSubx.sum :=
        repSeriesSum_sum_eq hfx hterm_self cSubx
      have hcSubx_sum :
          relEventually cSubx.sum (subSeq cPx.sum cMx.sum) := by
        change relEventually
          (addSeq cPx.sum (negSeq cMx.sum))
          (subSeq cPx.sum cMx.sum)
        exact relEventually_symm _ _
          (subSeq_eq_add_neg_eventually cPx.sum cMx.sum)
      have hfx_split :
          relEventually hfx.sum (subSeq cPx.sum cMx.sum) :=
        relEventually_trans _ _ _ hfx_split_raw hcSubx_sum
      have hnn : RegularSeqNonneg hfx.sum :=
        hpos x hx_orig point_abs hfx
      have hMP : RegularSeqLe cMx.sum cPx.sum := by
        change RegularSeqNonneg (subSeq cPx.sum cMx.sum)
        exact regularSeqNonneg_of_eventual
          (relEventually_symm hfx.sum (subSeq cPx.sum cMx.sum) hfx_split)
          hnn
      have hps_split :
          relEventually point_sum.sum (addSeq cPx.sum cMx.sum) :=
        repSeriesSum_sum_eq point_sum
          (fun n => by
            change relEventually
              (CReal.abs ((f n).toFun x))
              (addSeq
                (CReal.max ((f n).toFun x) CReal.zero)
                (CReal.neg (CReal.min ((f n).toFun x) CReal.zero)))
            exact relEventually_symm _ _
              (max_add_negmin_eq_abs ((f n).toFun x)))
          (repSeriesSum_add cPx cMx)
      let pN : CReal :=
        regularSeqFinSum
          (fun n => CReal.neg (CReal.min ((f n).toFun x) CReal.zero)) N
      have hpN_le : RegularSeqLe pN cMx.sum := by
        dsimp [pN]
        refine repPartialSum_le_sum ?_ cMx N
        intro n
        change ¬ CReal.ltE
          (CReal.neg (CReal.min ((f n).toFun x) CReal.zero))
          CReal.zero
        exact CReal.neg_min_zero_nonneg_E ((f n).toFun x)
      have hpN_le_cP : RegularSeqLe pN cPx.sum :=
        regularSeqLe_trans hpN_le hMP
      have hle_model :
          RegularSeqLe (addSeq pN pN) (addSeq cPx.sum cMx.sum) :=
        regularSeqLe_add hpN_le_cP hpN_le
      have hle_point_sum :
          RegularSeqLe (addSeq pN pN) point_sum.sum :=
        regularSeqLe_of_right_eventual
          (relEventually_symm point_sum.sum (addSeq cPx.sum cMx.sum)
            hps_split)
          hle_model
      have hGx :
          relEventually (G.toFun x) (addSeq pN pN) := by
        have hseqx :
            (BFunC.seqSum negTerms N).toFun x =
              regularSeqFinSum (fun n => (negTerms n).toFun x) N :=
          BFunC.seqSum_toFun negTerms x N
        change relEventually
          (addSeq ((BFunC.seqSum negTerms N).toFun x)
            ((BFunC.seqSum negTerms N).toFun x))
          (addSeq
            (regularSeqFinSum
              (fun n =>
                CReal.neg (CReal.min ((f n).toFun x) CReal.zero)) N)
            (regularSeqFinSum
              (fun n =>
                CReal.neg (CReal.min ((f n).toFun x) CReal.zero)) N))
        rw [hseqx]
        exact relEventually_refl _
      have hle : RegularSeqLe (G.toFun x) point_sum.sum :=
        regularSeqLe_of_left_eventual (by simpa [pN] using hGx)
          hle_point_sum
      exact regularSeqLe_not_lt_reverse_prop hle below
    simpa [pm, negTerms] using
      regularSeqLe_of_left_eventual
        (relEventually_symm (S.I G) (addSeq pm pm) hIG)
        hmain
  have h2cm : RegularSeqLe (addSeq cM.sum cM.sum) habs.sum := by
    refine repLe_of_tendsto_le (repSeriesSum_add cM cM) habs.sum ?_
    intro N
    have hfin :
        relEventually
          (regularSeqFinSum
            (fun n =>
              addSeq (S.I (BFunC.negPart (f n)))
                (S.I (BFunC.negPart (f n)))) N)
          (addSeq
            (regularSeqFinSum
              (fun n => S.I (BFunC.negPart (f n))) N)
            (regularSeqFinSum
              (fun n => S.I (BFunC.negPart (f n))) N)) :=
      bc1_finSum_termwise
        (fun n => S.I (BFunC.negPart (f n)))
        (fun n => S.I (BFunC.negPart (f n))) N
    exact regularSeqLe_of_left_eventual hfin (per_N N)
  have h2cm_to_split :
      RegularSeqLe (addSeq cM.sum cM.sum) (addSeq cP.sum cM.sum) :=
    regularSeqLe_of_right_eventual habs_split h2cm
  have hkey : RegularSeqLe cM.sum cP.sum :=
    regularSeqLe_cancel_add_right h2cm_to_split
  let cSub := repSeriesSum_sub cP cM
  have hsum_split_raw : relEventually hsum.sum cSub.sum :=
    repSeriesSum_sum_eq hsum
      (fun n => S.I_self_eq (hmem n))
      cSub
  have hcSub_sum : relEventually cSub.sum (subSeq cP.sum cM.sum) := by
    change relEventually
      (addSeq cP.sum (negSeq cM.sum))
      (subSeq cP.sum cM.sum)
    exact relEventually_symm _ _
      (subSeq_eq_add_neg_eventually cP.sum cM.sum)
  have hsum_split : relEventually hsum.sum (subSeq cP.sum cM.sum) :=
    relEventually_trans _ _ _ hsum_split_raw hcSub_sum
  change RegularSeqNonneg hsum.sum
  exact regularSeqNonneg_of_eventual hsum_split hkey

#print axioms BishopSec1P.IntSpaceC.lemma_1_7C

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.neg {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : IntegrableRepC3 S where
  fn := fun n => BFunC.smul (CReal.neg CReal.one) (r.fn n)
  fn_mem := fun n => S.smul_mem (CReal.neg CReal.one) (r.fn_mem n)
  abs_integral_sum :=
    -- Technical note.
    { sum := r.abs_integral_sum.sum
      tends := bc1_repSeriesTendsto_congr r.abs_integral_sum.tends
        (fun n => bc1_regularSeqFinSum_congr_terms
          (fun k => S.I (BFunC.absf (BFunC.smul (CReal.neg CReal.one) (r.fn k))))
          (fun k => S.I (BFunC.absf (r.fn k)))
          (fun k => S.I_absf_neg_eqC (r.fn_mem k)) n) }
  integral_sum :=
    -- Technical note.
    { sum := (BishopRegularSeqSeriesSum.repSeriesSum_neg r.integral_sum).sum
      tends := bc1_repSeriesTendsto_congr
        (BishopRegularSeqSeriesSum.repSeriesSum_neg r.integral_sum).tends
        (fun n => bc1_regularSeqFinSum_congr_terms
          (fun k => S.I (BFunC.smul (CReal.neg CReal.one) (r.fn k)))
          (fun k => negSeq (S.I (r.fn k)))
          (fun k => S.I_neg (r.fn_mem k)) n) }

#print axioms BishopSec1P.IntegrableRepC3.neg

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRepC3.integral_neg {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    r.neg.integral = negSeq r.integral :=
  rfl

#print axioms BishopSec1P.IntegrableRepC3.integral_neg

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.sub {X : Type*} {S : IntSpaceC X}
    (r r' : IntegrableRepC3 S) : IntegrableRepC3 S :=
  r.add r'.neg

#print axioms BishopSec1P.IntegrableRepC3.sub

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRepC3.integral_sub {X : Type*} {S : IntSpaceC X}
    (r r' : IntegrableRepC3 S) :
    (r.sub r').integral = addSeq r.integral (negSeq r'.integral) :=
  rfl

#print axioms BishopSec1P.IntegrableRepC3.integral_sub

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.smul {X : Type*} {S : IntSpaceC X}
    (a : CReal) (r : IntegrableRepC3 S) : IntegrableRepC3 S where
  fn := fun n => BFunC.smul a (r.fn n)
  fn_mem := fun n => S.smul_mem a (r.fn_mem n)
  abs_integral_sum :=
    repSeriesSum_congr
      (repSeriesSum_smul (CReal.abs a) r.abs_integral_sum)
      (fun n => S.I_abs_smulC a (r.fn_mem n))
  integral_sum :=
    repSeriesSum_congr
      (repSeriesSum_smul a r.integral_sum)
      (fun n => S.I_smul a (r.fn_mem n))

#print axioms BishopSec1P.IntegrableRepC3.smul

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRepC3.integral_smul {X : Type*} {S : IntSpaceC X}
    (a : CReal) (r : IntegrableRepC3 S) :
    (IntegrableRepC3.smul a r).integral = CReal.mul a r.integral :=
  rfl

#print axioms BishopSec1P.IntegrableRepC3.integral_smul

/-- Presented dyadic half-powers as constant regular sequences. -/
def halfPow (n : Nat) : CReal :=
  CReal.epsSeq n

#print axioms BishopSec1P.halfPow

/-- The presented dyadic half-powers are nonnegative, hence absolute-value
normalization is eventual equality. -/
theorem halfPow_abs (n : Nat) :
    CReal.abs (halfPow n) ≈ halfPow n := by
  apply rel_to_relEventually
  intro k
  change BishopC.Le
    (BishopCRat.CRat.absF
      (BishopCRat.CRat.absF (eps n) - eps n))
    (tol k)
  rw [scalarCOFOSeed.abs_of_nonneg (eps_nonneg n)]
  rw [show eps n - eps n = (0 : Scalar) from by ring]
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg k

#print axioms BishopSec1P.halfPow_abs

/-- The concrete multiplication bound absorbs a dyadic scale selected from
`CReal.mulArchBound`: `2^-(j+M) * x <= 2^-j`. -/
theorem halfPow_mul_archBound_le (x : CReal) (j : Nat) :
    RegularSeqLe
      (CReal.mul (halfPow (j + CReal.mulArchBound x)) x)
      (halfPow j) := by
  apply regularSeqLe_of_indexed_pointwise_le
  intro n
  set m : Nat := CReal.mulArchBound x with hm
  set K : Nat :=
    mulBoundWith cRatScalarMulArch (constSeq (eps (j + m))) x
    with hK
  set q : Nat := mulIndexFromBound K (n + 1) with hq
  change BishopC.Le (eps (j + m) * x.val q) (eps j)
  have hx_le_abs : BishopC.Le (x.val q) (COF.abs (x.val q)) :=
    scalarCOFOSeed.le_abs_self (x.val q)
  have hto_abs : BishopC.Le (eps (j + m) * x.val q)
      (eps (j + m) * COF.abs (x.val q)) :=
    scalar_mul_le_mul_left hx_le_abs (eps_nonneg (j + m))
  have hsample : BishopC.Le (COF.abs (x.val q) * eps m) 1 := by
    subst q
    subst m
    exact abs_sample_mul_standard_eps_le_one cRatScalarMulArch x K (n + 1)
  have hsample' : BishopC.Le (eps m * COF.abs (x.val q)) 1 := by
    rwa [mul_comm] at hsample
  have hscaled : BishopC.Le (eps j * (eps m * COF.abs (x.val q))) (eps j * 1) :=
    scalar_mul_le_mul_left hsample' (eps_nonneg j)
  have hscaled' : BishopC.Le ((eps j * eps m) * COF.abs (x.val q)) (eps j) := by
    rwa [show eps j * (eps m * COF.abs (x.val q)) =
          (eps j * eps m) * COF.abs (x.val q) from by ring,
        show eps j * 1 = eps j from by ring] at hscaled
  have hbudget : BishopC.Le (eps (j + m) * COF.abs (x.val q)) (eps j) := by
    rwa [eps_add_mul_local j m]
  exact BishopC.le_trans hto_abs hbudget

#print axioms BishopSec1P.halfPow_mul_archBound_le

/-- Absolute integral sums after scalar multiplication are fixed to the
scalar-multiplied absolute sum by the `IntegrableRepC3.smul` constructor. -/
theorem IntegrableRepC3.smul_absSum {X : Type*} {S : IntSpaceC X}
    (a : CReal) (r : IntegrableRepC3 S) :
    (IntegrableRepC3.smul a r).abs_integral_sum.sum ≈
      CReal.mul (CReal.abs a) r.abs_integral_sum.sum :=
  relEventually_refl _

#print axioms BishopSec1P.IntegrableRepC3.smul_absSum

/-- The Archimedean scale factor for the absolute integral sum. -/
def IntegrableRepC3.scaleFactor {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : Nat :=
  CReal.mulArchBound r.abs_integral_sum.sum

#print axioms BishopSec1P.IntegrableRepC3.scaleFactor

/-- Scaling a representation by `halfPow (j + scaleFactor)` makes its
absolute integral sum bounded by `halfPow j`. -/
theorem IntegrableRepC3.scaleFactor_spec {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (j : Nat) :
    RegularSeqLe
      ((IntegrableRepC3.smul (halfPow (j + r.scaleFactor)) r).abs_integral_sum.sum)
      (halfPow j) := by
  have hleft :
      relEventually
        ((IntegrableRepC3.smul (halfPow (j + r.scaleFactor)) r).abs_integral_sum.sum)
        (CReal.mul (halfPow (j + r.scaleFactor))
          r.abs_integral_sum.sum) := by
    have habs := halfPow_abs (j + r.scaleFactor)
    change relEventually
      (CReal.mul (CReal.abs (halfPow (j + r.scaleFactor)))
        r.abs_integral_sum.sum)
      (CReal.mul (halfPow (j + r.scaleFactor))
        r.abs_integral_sum.sum)
    exact mulSeqConcrete_respects_eventually cRatScalarMulArch
      (CReal.abs (halfPow (j + r.scaleFactor)))
      (halfPow (j + r.scaleFactor))
      r.abs_integral_sum.sum r.abs_integral_sum.sum
      habs (relEventually_refl r.abs_integral_sum.sum)
  exact regularSeqLe_of_left_eventual hleft
    (by
      simpa [IntegrableRepC3.scaleFactor] using
        halfPow_mul_archBound_le r.abs_integral_sum.sum j)

#print axioms BishopSec1P.IntegrableRepC3.scaleFactor_spec

/-- The zeroth dyadic half-power is one. -/
theorem halfPow_zero :
    halfPow 0 ≈ CReal.one := by
  apply rel_to_relEventually
  intro k
  change BishopC.Le
    (BishopCRat.CRat.absF (eps 0 - (1 : Scalar)))
    (tol k)
  rw [show eps 0 = (1 : Scalar) from rfl]
  rw [show (1 : Scalar) - 1 = 0 from by ring]
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg k

#print axioms BishopSec1P.halfPow_zero

/-- Successive dyadic half-powers double back to the previous one. -/
theorem halfPow_succ_add_self (n : Nat) :
    CReal.add (halfPow (n + 1)) (halfPow (n + 1)) ≈ halfPow n := by
  apply rel_to_relEventually
  intro k
  change BishopC.Le
    (BishopCRat.CRat.absF
      ((eps (n + 1) + eps (n + 1)) - eps n))
    (tol k)
  rw [eps_succ_add_self n]
  rw [show eps n - eps n = (0 : Scalar) from by ring]
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg k

#print axioms BishopSec1P.halfPow_succ_add_self

/-- Pointwise scalar form of the finite geometric sum:
`sum_{i<=N} 2^-i = 2 - 2^-N`. -/
theorem regularSeqFinSum_halfPow_val (N n : Nat) :
    (regularSeqFinSum (fun i => halfPow i) N).val n = (2 : Scalar) - eps N := by
  induction N generalizing n with
  | zero =>
      change eps 0 = (2 : Scalar) - eps 0
      unfold eps
      change (1 : Scalar) = (2 : Scalar) - 1
      ring
  | succ N ih =>
      rw [regularSeqFinSum]
      change
        (regularSeqFinSum (fun i => halfPow i) N).val (n + 1) + eps (N + 1) =
          (2 : Scalar) - eps (N + 1)
      rw [ih (n + 1)]
      rw [← eps_succ_add_self N]
      ring

#print axioms BishopSec1P.regularSeqFinSum_halfPow_val

/-- At the dyadic gauge `k`, a sufficiently long finite half-power sum is
representatively close to the presented real `2`. -/
theorem repCloseAtGauge_halfPow_partial {k n : Nat} (hkn : k ≤ n) :
    RepCloseAtGauge k
      (regularSeqFinSum (fun i => halfPow i) n)
      (addSeq CReal.one CReal.one) := by
  refine ⟨0, ?_⟩
  intro m _hm
  have hval := regularSeqFinSum_halfPow_val n m
  change BishopC.Le
    (COF.abs
      ((regularSeqFinSum (fun i => halfPow i) n).val m -
        (addSeq CReal.one CReal.one).val m))
    (eps k)
  rw [hval]
  change BishopC.Le (COF.abs (((2 : Scalar) - eps n) - ((1 : Scalar) + 1))) (eps k)
  rw [show ((2 : Scalar) - eps n) - ((1 : Scalar) + 1) = -eps n by ring]
  change BishopC.Le (BishopCRat.CRat.absF (-(eps n))) (eps k)
  rw [scalarCOFOSeed.abs_neg (eps n)]
  rw [scalarCOFOSeed.abs_of_nonneg (eps_nonneg n)]
  exact eps_le_of_le hkn

#print axioms BishopSec1P.repCloseAtGauge_halfPow_partial

/-- Presented geometric series `sum_n halfPow n = 2`. -/
def repSeriesSum_halfPow : RepSeriesSum halfPow where
  sum := addSeq CReal.one CReal.one
  tends :=
    { mod := fun k => k + 1
      close := by
        intro k n hn
        exact repCloseAtGauge_halfPow_partial (k := k + 1) (n := n) hn }

#print axioms BishopSec1P.repSeriesSum_halfPow

/-- Nonnegative termwise domination by `halfPow` gives represented summability. -/
def repSeriesSum_of_le_halfPow {u : Nat → CReal}
    (hnn : ∀ n, RegularSeqNonneg (u n))
    (hle : ∀ n, RegularSeqLe (u n) (halfPow n)) : RepSeriesSum u :=
  repSeriesSum_comparison hnn hle repSeriesSum_halfPow

#print axioms BishopSec1P.repSeriesSum_of_le_halfPow

/-- If a presented real is nonnegative, its absolute value is below itself. -/
theorem regularSeqLe_abs_of_nonneg {x : CReal}
    (hx : RegularSeqLe zeroSeq x) : RegularSeqLe (absSeq x) x := by
  have hnn : RegularSeqNonneg x := regularSeqNonneg_of_zero_le hx
  have hneg0 : RegularSeqLe (negSeq x) zeroSeq :=
    regularSeqLe_neg_nonpos_of_nonneg hnn
  have hnegx : RegularSeqLe (negSeq x) x :=
    regularSeqLe_trans hneg0 hx
  exact regularSeq_abs_le_of_two_sided x x (regularSeqLe_refl x) hnegx

#print axioms BishopSec1P.regularSeqLe_abs_of_nonneg

/-- For a monotone sequence bounded by `T`, any two tail values after `M`
are within the remaining gap `T - v M`. -/
theorem regularSeqLe_abs_sub_of_mono_bounded_gap {v : Nat → CReal} {T : CReal}
    (hmono : ∀ {p q : Nat}, p ≤ q → RegularSeqLe (v p) (v q))
    (hbd : ∀ q : Nat, RegularSeqLe (v q) T)
    {M m n : Nat} (hm : M ≤ m) (hn : M ≤ n) :
    RegularSeqLe (absSeq (subSeq (v m) (v n))) (subSeq T (v M)) := by
  rcases Nat.le_total m n with hmn | hnm
  · have hmn_le : RegularSeqLe (v m) (v n) := hmono hmn
    have hdiff_nonneg : RegularSeqLe zeroSeq (subSeq (v n) (v m)) :=
      regularSeqLe_zero_of_nonneg hmn_le
    have habs_rev :
        RegularSeqLe (absSeq (subSeq (v n) (v m))) (subSeq (v n) (v m)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have habs :
        RegularSeqLe (absSeq (subSeq (v m) (v n))) (subSeq (v n) (v m)) :=
      regularSeqLe_of_left_eventual (absSeq_subSeq_comm_eventually (v m) (v n))
        habs_rev
    have hleft :
        RegularSeqLe (subSeq (v n) (v m)) (subSeq T (v m)) :=
      subSeq_monotone_left_regularSeqLe (v n) T (v m) (hbd n)
    have hright :
        RegularSeqLe (subSeq T (v m)) (subSeq T (v M)) :=
      regularSeqLe_subSeq_right T (hmono hm)
    exact regularSeqLe_trans habs (regularSeqLe_trans hleft hright)
  · have hnm_le : RegularSeqLe (v n) (v m) := hmono hnm
    have hdiff_nonneg : RegularSeqLe zeroSeq (subSeq (v m) (v n)) :=
      regularSeqLe_zero_of_nonneg hnm_le
    have habs :
        RegularSeqLe (absSeq (subSeq (v m) (v n))) (subSeq (v m) (v n)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have hleft :
        RegularSeqLe (subSeq (v m) (v n)) (subSeq T (v n)) :=
      subSeq_monotone_left_regularSeqLe (v m) T (v n) (hbd m)
    have hright :
        RegularSeqLe (subSeq T (v n)) (subSeq T (v M)) :=
      regularSeqLe_subSeq_right T (hmono hn)
    exact regularSeqLe_trans habs (regularSeqLe_trans hleft hright)

#print axioms BishopSec1P.regularSeqLe_abs_sub_of_mono_bounded_gap

/-- Monotone bounded sequences are Cauchy once every dyadic gauge has an
explicit tail gap. -/
def repIsCauchy_of_mono_bounded_gap {v : Nat → CReal} {T : CReal}
    (hmono : ∀ {p q : Nat}, p ≤ q → RegularSeqLe (v p) (v q))
    (hbd : ∀ q : Nat, RegularSeqLe (v q) T)
    (hgap : ∀ k : Nat, {M : Nat // regularSeqLtProp (subSeq T (v M)) (halfPow k)}) :
    CRealRepSequenceCauchyData v where
  cmod := fun k => (hgap k).val
  close_eventually := by
    intro k m n hm hn
    have hle :
        RegularSeqLe (absSeq (subSeq (v m) (v n)))
          (subSeq T (v ((hgap k).val))) :=
      regularSeqLe_abs_sub_of_mono_bounded_gap hmono hbd hm hn
    have hlt_gap : regularSeqLtProp (subSeq T (v ((hgap k).val))) (halfPow k) :=
      (hgap k).property
    have hlt_abs : regularSeqLtProp (absSeq (subSeq (v m) (v n))) (halfPow k) :=
      regularSeqLtProp_of_le_of_lt hle hlt_gap
    simpa [halfPow, CReal.epsSeq] using
      repCloseAtGauge_of_absGap (v m) (v n) k hlt_abs

#print axioms BishopSec1P.repIsCauchy_of_mono_bounded_gap

/-- A finite partial sum of nonnegative presented reals is nonnegative. -/
theorem regularSeqFinSum_nonneg_of_terms {u : Nat → CReal}
    (hu : ∀ n, RegularSeqNonneg (u n)) (N : Nat) :
    RegularSeqNonneg (regularSeqFinSum u N) := by
  induction N with
  | zero => exact hu 0
  | succ n ih => exact regularSeqNonneg_add ih (hu (n + 1))

#print axioms BishopSec1P.regularSeqFinSum_nonneg_of_terms

/-- A represented sum of nonnegative terms is nonnegative. -/
theorem repSeriesSum_nonneg {u : Nat → CReal}
    (hu : ∀ n, RegularSeqNonneg (u n)) (h : RepSeriesSum u) :
    RegularSeqNonneg h.sum := by
  have hneg_sum_le_zero : RegularSeqLe (negSeq h.sum) zeroSeq := by
    refine repLe_of_tendsto_le
      (BishopRegularSeqSeriesSum.repSeriesSum_neg h) zeroSeq ?_
    intro N
    have hpart_nn : RegularSeqNonneg (regularSeqFinSum u N) :=
      regularSeqFinSum_nonneg_of_terms hu N
    have hneg_part_le_zero : RegularSeqLe (negSeq (regularSeqFinSum u N)) zeroSeq :=
      regularSeqLe_neg_nonpos_of_nonneg hpart_nn
    exact regularSeqLe_of_left_eventual
      (BishopRegularSeqSeriesSum.regularSeqFinSum_negSeq u N)
      hneg_part_le_zero
  have hev : relEventually (subSeq zeroSeq (negSeq h.sum)) h.sum :=
    relEventually_trans
      (subSeq zeroSeq (negSeq h.sum))
      (negSeq (negSeq h.sum))
      h.sum
      (subSeq_zero_left_eventually (negSeq h.sum))
      (negSeq_negSeq_eventually h.sum)
  exact regularSeqNonneg_of_eventual (relEventually_symm _ _ hev) hneg_sum_le_zero

#print axioms BishopSec1P.repSeriesSum_nonneg

/-- Termwise non-strict order is preserved by finite presented sums. -/
theorem regularSeqFinSum_le_of_termwise_le {u v : Nat → CReal}
    (h : ∀ n, RegularSeqLe (u n) (v n)) :
    ∀ N : Nat, RegularSeqLe (regularSeqFinSum u N) (regularSeqFinSum v N)
  | 0 => h 0
  | N + 1 => by
      change RegularSeqLe
        (addSeq (regularSeqFinSum u N) (u (N + 1)))
        (addSeq (regularSeqFinSum v N) (v (N + 1)))
      exact regularSeqLe_add (regularSeqFinSum_le_of_termwise_le h N) (h (N + 1))

#print axioms BishopSec1P.regularSeqFinSum_le_of_termwise_le

/-- Square grid sum `sum_{i<=N} sum_{j<=N} a i j` in the presented layer. -/
def gridSumC (a : Nat → Nat → CReal) (N : Nat) : CReal :=
  regularSeqFinSum (fun i => regularSeqFinSum (a i) N) N

#print axioms BishopSec1P.gridSumC

/-- The presented square grid is bounded by the total row-sum series. -/
theorem gridSum_le_TC {a : Nat → Nat → CReal}
    (ha : ∀ i j, RegularSeqNonneg (a i j))
    (hrow : ∀ i, RepSeriesSum (a i))
    (hrowsum : RepSeriesSum (fun i => (hrow i).sum)) (N : Nat) :
    RegularSeqLe (gridSumC a N) hrowsum.sum := by
  have hrs_nn : ∀ i, RegularSeqNonneg ((hrow i).sum) :=
    fun i => repSeriesSum_nonneg (fun j => ha i j) (hrow i)
  have step1 :
      RegularSeqLe (gridSumC a N)
        (regularSeqFinSum (fun i => (hrow i).sum) N) :=
    regularSeqFinSum_le_of_termwise_le
      (fun i => repPartialSum_le_sum (fun j => ha i j) (hrow i) N) N
  exact regularSeqLe_trans step1 (repPartialSum_le_sum hrs_nn hrowsum N)

#print axioms BishopSec1P.gridSum_le_TC

/-- Bounded termwise equality gives exact equality of presented finite sums. -/
theorem regularSeqFinSum_congr_upto {u v : Nat → CReal} :
    ∀ N : Nat, (∀ j, j ≤ N → u j = v j) →
      regularSeqFinSum u N = regularSeqFinSum v N
  | 0, h => h 0 (Nat.le_refl 0)
  | N + 1, h => by
      rw [regularSeqFinSum, regularSeqFinSum,
        regularSeqFinSum_congr_upto N (fun j hj => h j (Nat.le_succ_of_le hj)),
        h (N + 1) (Nat.le_refl _)]

#print axioms BishopSec1P.regularSeqFinSum_congr_upto

/-- Splitting a finite presented sum at `p`; algebraic reassociation is
eventual equality in the representative layer. -/
theorem regularSeqFinSum_split_eventually (u : Nat → CReal) (p : Nat) :
    ∀ d : Nat,
      relEventually
        (regularSeqFinSum u (p + (d + 1)))
        (addSeq (regularSeqFinSum u p)
          (regularSeqFinSum (fun j => u (p + 1 + j)) d))
  | 0 => by
      simpa [regularSeqFinSum, Nat.add_assoc] using
        (relEventually_refl
          (addSeq (regularSeqFinSum u p) (u (p + 1))))
  | d + 1 => by
      let shift : Nat → CReal := fun j => u (p + 1 + j)
      have ih := regularSeqFinSum_split_eventually u p d
      have hcong :
          relEventually
            (addSeq (regularSeqFinSum u (p + (d + 1)))
              (u (p + (d + 1) + 1)))
            (addSeq
              (addSeq (regularSeqFinSum u p) (regularSeqFinSum shift d))
              (u (p + (d + 1) + 1))) :=
        addSeq_respects_eventually _ _ _ _ ih (relEventually_refl _)
      have htarget :
          relEventually
            (addSeq
              (addSeq (regularSeqFinSum u p) (regularSeqFinSum shift d))
              (u (p + (d + 1) + 1)))
            (addSeq (regularSeqFinSum u p)
              (addSeq (regularSeqFinSum shift d) (shift (d + 1)))) := by
        have hidx : u (p + (d + 1) + 1) = shift (d + 1) := by
          dsimp [shift]
          congr 1
          omega
        rw [hidx]
        exact addSeq_assoc_eventually
          (regularSeqFinSum u p) (regularSeqFinSum shift d) (shift (d + 1))
      simpa [regularSeqFinSum, shift, Nat.add_assoc] using
        relEventually_trans _ _ _ hcong htarget

#print axioms BishopSec1P.regularSeqFinSum_split_eventually

/-- The square grid increment is the new bottom row plus right column. -/
theorem gridSum_succC (a : Nat → Nat → CReal) (N : Nat) :
    relEventually
      (gridSumC a (N + 1))
      (addSeq (gridSumC a N)
        (addSeq
          (regularSeqFinSum (a (N + 1)) (N + 1))
          (regularSeqFinSum (fun i => a i (N + 1)) N))) := by
  let rowN : Nat → CReal := fun i => regularSeqFinSum (a i) N
  let col : Nat → CReal := fun i => a i (N + 1)
  let rowBlock : CReal := regularSeqFinSum (a (N + 1)) (N + 1)
  have hrow :
      relEventually
        (regularSeqFinSum (fun i => regularSeqFinSum (a i) (N + 1)) N)
        (addSeq (regularSeqFinSum rowN N) (regularSeqFinSum col N)) := by
    have hcongr :
      relEventually
          (regularSeqFinSum (fun i => regularSeqFinSum (a i) (N + 1)) N)
          (regularSeqFinSum (fun i => addSeq (rowN i) (col i)) N) :=
      bc1_regularSeqFinSum_congr_terms _ _
        (fun _ => relEventually_refl _) N
    exact relEventually_trans _ _ _ hcongr (bc1_finSum_termwise rowN col N)
  have houter :
      relEventually
        (addSeq
          (regularSeqFinSum (fun i => regularSeqFinSum (a i) (N + 1)) N)
          rowBlock)
        (addSeq
          (addSeq (regularSeqFinSum rowN N) (regularSeqFinSum col N))
          rowBlock) :=
    addSeq_respects_eventually _ _ _ _ hrow (relEventually_refl rowBlock)
  have hreassoc :
      relEventually
        (addSeq
          (addSeq (regularSeqFinSum rowN N) (regularSeqFinSum col N))
          rowBlock)
        (addSeq (regularSeqFinSum rowN N)
          (addSeq rowBlock (regularSeqFinSum col N))) := by
    have hassoc :=
      addSeq_assoc_eventually
        (regularSeqFinSum rowN N) (regularSeqFinSum col N) rowBlock
    have hcomm :
        relEventually
          (addSeq (regularSeqFinSum col N) rowBlock)
          (addSeq rowBlock (regularSeqFinSum col N)) :=
      addSeq_comm_eventually (regularSeqFinSum col N) rowBlock
    exact relEventually_trans _ _ _ hassoc
      (addSeq_respects_eventually _ _ _ _
        (relEventually_refl (regularSeqFinSum rowN N)) hcomm)
  simpa [gridSumC, rowN, col, rowBlock, regularSeqFinSum] using
    relEventually_trans _ _ _ houter hreassoc

#print axioms BishopSec1P.gridSum_succC

/-- A square-shell block enumerates exactly the new bottom row and right column,
up to representative algebra equality. -/
theorem block_eqC (a : Nat → Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum
        (fun j =>
          a (BishopC.cellAt ((N + 1) * (N + 1) + j)).1
            (BishopC.cellAt ((N + 1) * (N + 1) + j)).2)
        (2 * N + 2))
      (addSeq
        (regularSeqFinSum (a (N + 1)) (N + 1))
        (regularSeqFinSum (fun i => a i (N + 1)) N)) := by
  let block : Nat → CReal := fun j =>
    a (BishopC.cellAt ((N + 1) * (N + 1) + j)).1
      (BishopC.cellAt ((N + 1) * (N + 1) + j)).2
  have hA :
      regularSeqFinSum block (N + 1) =
        regularSeqFinSum (a (N + 1)) (N + 1) :=
    regularSeqFinSum_congr_upto (N + 1) (fun j hj => by
      dsimp [block]
      rw [BishopC.cellAt_block (N + 1) j (by omega), if_pos hj])
  have hB :
      regularSeqFinSum (fun j => block ((N + 1) + 1 + j)) N =
        regularSeqFinSum (fun i => a i (N + 1)) N :=
    regularSeqFinSum_congr_upto N (fun j hj => by
      dsimp [block]
      have hnot : ¬ (N + 1 + 1 + j ≤ N + 1) := by omega
      simp [BishopC.cellAt_block (N + 1) ((N + 1) + 1 + j) (by omega),
        hnot, show (N + 1) + 1 + j - (N + 1) - 1 = j by omega])
  have hsplit := regularSeqFinSum_split_eventually block (N + 1) N
  have hsplit' :
      relEventually
        (regularSeqFinSum block (2 * N + 2))
        (addSeq (regularSeqFinSum block (N + 1))
          (regularSeqFinSum (fun j => block ((N + 1) + 1 + j)) N)) := by
    simpa [show 2 * N + 2 = (N + 1) + (N + 1) by omega,
      Nat.add_assoc] using hsplit
  have hright :
      relEventually
        (addSeq (regularSeqFinSum block (N + 1))
          (regularSeqFinSum (fun j => block ((N + 1) + 1 + j)) N))
        (addSeq
          (regularSeqFinSum (a (N + 1)) (N + 1))
          (regularSeqFinSum (fun i => a i (N + 1)) N)) := by
    rw [hA, hB]
    exact relEventually_refl _
  simpa [block] using relEventually_trans _ _ _ hsplit' hright

#print axioms BishopSec1P.block_eqC

/-- Shell-bound flatten finite sums agree with square grid sums up to
representative equality.  The shell reindex itself is exact at Nat level; only
presented addition reassociation forces `relEventually`. -/
theorem regularSeqFinSum_cellAt_eq_gridSumC (a : Nat → Nat → CReal) :
    ∀ N : Nat,
      relEventually
        (regularSeqFinSum
          (fun m => a (BishopC.cellAt m).1 (BishopC.cellAt m).2)
          (N * N + 2 * N))
        (gridSumC a N)
  | 0 => by
      have hcell : BishopC.cellAt 0 = (0, 0) := by
        simpa using BishopC.cellAt_block 0 0 (by omega)
      change relEventually
        (a (BishopC.cellAt 0).1 (BishopC.cellAt 0).2)
        (a 0 0)
      rw [hcell]
      exact relEventually_refl _
  | N + 1 => by
      let flat : Nat → CReal := fun m => a (BishopC.cellAt m).1 (BishopC.cellAt m).2
      let previous : Nat := N * N + 2 * N
      let blockTarget : CReal :=
        addSeq
          (regularSeqFinSum (a (N + 1)) (N + 1))
          (regularSeqFinSum (fun i => a i (N + 1)) N)
      have hsplit :
          relEventually
            (regularSeqFinSum flat (previous + ((2 * N + 2) + 1)))
            (addSeq (regularSeqFinSum flat previous)
              (regularSeqFinSum (fun j => flat (previous + 1 + j)) (2 * N + 2))) :=
        regularSeqFinSum_split_eventually flat previous (2 * N + 2)
      have hblock :
          relEventually
            (regularSeqFinSum (fun j => flat (previous + 1 + j)) (2 * N + 2))
            blockTarget := by
        have hcongr :
            relEventually
              (regularSeqFinSum (fun j => flat (previous + 1 + j)) (2 * N + 2))
              (regularSeqFinSum
                (fun j =>
                  a (BishopC.cellAt ((N + 1) * (N + 1) + j)).1
                    (BishopC.cellAt ((N + 1) * (N + 1) + j)).2)
                (2 * N + 2)) :=
          bc1_regularSeqFinSum_congr_terms _ _
            (fun j => by
              dsimp [flat, previous]
              rw [show N * N + 2 * N + 1 + j = (N + 1) * (N + 1) + j by ring]
              exact relEventually_refl _) (2 * N + 2)
        exact relEventually_trans _ _ _ hcongr (block_eqC a N)
      have hparts :
          relEventually
            (addSeq (regularSeqFinSum flat previous)
              (regularSeqFinSum (fun j => flat (previous + 1 + j)) (2 * N + 2)))
            (addSeq (gridSumC a N) blockTarget) :=
        addSeq_respects_eventually _ _ _ _
          (regularSeqFinSum_cellAt_eq_gridSumC a N) hblock
      have hgrid :
          relEventually (gridSumC a (N + 1)) (addSeq (gridSumC a N) blockTarget) := by
        simpa [blockTarget] using gridSum_succC a N
      have hmain :
          relEventually
            (regularSeqFinSum flat (previous + ((2 * N + 2) + 1)))
            (gridSumC a (N + 1)) :=
        relEventually_trans _ _ _
          hsplit
          (relEventually_trans _ _ _ hparts (relEventually_symm _ _ hgrid))
      simpa [flat, previous,
        show (N + 1) * (N + 1) + 2 * (N + 1) =
          (N * N + 2 * N) + ((2 * N + 2) + 1) by ring] using hmain

#print axioms BishopSec1P.regularSeqFinSum_cellAt_eq_gridSumC

/-- Strict representative order is stable under eventual equality on the left
side. -/
theorem regularSeqLtProp_of_left_eventual {x x' y : CReal}
    (hxx : relEventually x x') (h : regularSeqLtProp x' y) :
    regularSeqLtProp x y :=
  posEventually_respects _ _
    (subSeq_respects_eventually y y x' x
      (relEventually_refl y) (relEventually_symm x x' hxx))
    h

#print axioms BishopSec1P.regularSeqLtProp_of_left_eventual

/-- Strict representative order is stable under eventual equality on the right
side. -/
theorem regularSeqLtProp_of_right_eventual {x y y' : CReal}
    (hyy : relEventually y y') (h : regularSeqLtProp x y) :
    regularSeqLtProp x y' :=
  posEventually_respects _ _
    (subSeq_respects_eventually y y' x x hyy (relEventually_refl x))
    h

#print axioms BishopSec1P.regularSeqLtProp_of_right_eventual

/-- Strict representative order is preserved by adding strict inequalities. -/
theorem regularSeqLtProp_add {a b c d : CReal}
    (hab : regularSeqLtProp a b) (hcd : regularSeqLtProp c d) :
    regularSeqLtProp (addSeq a c) (addSeq b d) := by
  have hleft0 : regularSeqLtProp (addSeq c a) (addSeq c b) :=
    regularSeqLtProp_add_left c a b hab
  have hleft1 : regularSeqLtProp (addSeq a c) (addSeq c b) :=
    regularSeqLtProp_of_left_eventual (addSeq_comm_eventually a c) hleft0
  have hleft : regularSeqLtProp (addSeq a c) (addSeq b c) :=
    regularSeqLtProp_of_right_eventual (addSeq_comm_eventually c b) hleft1
  have hright : regularSeqLtProp (addSeq b c) (addSeq b d) :=
    regularSeqLtProp_add_left b c d hcd
  exact regularSeqLtProp_trans _ _ _ hleft hright

#print axioms BishopSec1P.regularSeqLtProp_add

/-- Zero is strictly below every presented dyadic half-power. -/
theorem regularSeqLtProp_zero_halfPow (k : Nat) :
    regularSeqLtProp zeroSeq (halfPow k) := by
  refine ⟨k + 1, 0, ?_⟩
  intro n _hn
  change COF.lt (eps (k + 1)) (eps k - 0)
  rw [show eps k - 0 = eps k by ring]
  exact eps_succ_lt_eps k

#print axioms BishopSec1P.regularSeqLtProp_zero_halfPow

/-- The next dyadic half-power is strictly below the previous one. -/
theorem regularSeqLtProp_halfPow_succ (k : Nat) :
    regularSeqLtProp (halfPow (k + 1)) (halfPow k) := by
  let hp : CReal := halfPow (k + 1)
  have hpos : regularSeqLtProp zeroSeq hp :=
    regularSeqLtProp_zero_halfPow (k + 1)
  have hadd : regularSeqLtProp (addSeq hp zeroSeq) (addSeq hp hp) :=
    regularSeqLtProp_add_left hp zeroSeq hp hpos
  have hleft : regularSeqLtProp hp (addSeq hp hp) :=
    regularSeqLtProp_of_left_eventual
      (relEventually_symm _ _ (addSeq_zero_right_eventually hp)) hadd
  exact regularSeqLtProp_of_right_eventual (halfPow_succ_add_self k) hleft

#print axioms BishopSec1P.regularSeqLtProp_halfPow_succ

/-- Termwise strict order over a bounded index range is preserved by finite
presented sums. -/
theorem regularSeqFinSum_lt_of_termwise_lt {u v : Nat → CReal} :
    ∀ N : Nat, (∀ i, i ≤ N → regularSeqLtProp (u i) (v i)) →
      regularSeqLtProp (regularSeqFinSum u N) (regularSeqFinSum v N)
  | 0, h => h 0 (Nat.le_refl 0)
  | N + 1, h => by
      change regularSeqLtProp
        (addSeq (regularSeqFinSum u N) (u (N + 1)))
        (addSeq (regularSeqFinSum v N) (v (N + 1)))
      exact regularSeqLtProp_add
        (regularSeqFinSum_lt_of_termwise_lt N
          (fun i hi => h i (Nat.le_succ_of_le hi)))
        (h (N + 1) (Nat.le_refl _))

#print axioms BishopSec1P.regularSeqFinSum_lt_of_termwise_lt

/-- Finite presented sums commute with pointwise subtraction up to
representative equality. -/
theorem regularSeqFinSum_sub_eventually (u v : Nat → CReal) (N : Nat) :
    relEventually
      (regularSeqFinSum (fun i => subSeq (u i) (v i)) N)
      (subSeq (regularSeqFinSum u N) (regularSeqFinSum v N)) := by
  have hsub_add :
      relEventually
        (regularSeqFinSum (fun i => subSeq (u i) (v i)) N)
        (regularSeqFinSum (fun i => addSeq (u i) (negSeq (v i))) N) :=
    bc1_regularSeqFinSum_congr_terms _ _
      (fun i => subSeq_eq_add_neg_eventually (u i) (v i)) N
  have hadd :
      relEventually
        (regularSeqFinSum (fun i => addSeq (u i) (negSeq (v i))) N)
        (addSeq (regularSeqFinSum u N)
          (regularSeqFinSum (fun i => negSeq (v i)) N)) :=
    bc1_finSum_termwise u (fun i => negSeq (v i)) N
  have hneg :
      relEventually
        (regularSeqFinSum (fun i => negSeq (v i)) N)
        (negSeq (regularSeqFinSum v N)) :=
    BishopRegularSeqSeriesSum.regularSeqFinSum_negSeq v N
  have hright_add :
      relEventually
        (addSeq (regularSeqFinSum u N)
          (regularSeqFinSum (fun i => negSeq (v i)) N))
        (addSeq (regularSeqFinSum u N) (negSeq (regularSeqFinSum v N))) :=
    addSeq_respects_eventually _ _ _ _
      (relEventually_refl (regularSeqFinSum u N)) hneg
  have hto_sub :
      relEventually
        (addSeq (regularSeqFinSum u N) (negSeq (regularSeqFinSum v N)))
        (subSeq (regularSeqFinSum u N) (regularSeqFinSum v N)) :=
    relEventually_symm _ _ (subSeq_eq_add_neg_eventually _ _)
  exact relEventually_trans _ _ _ hsub_add
    (relEventually_trans _ _ _ hadd
      (relEventually_trans _ _ _ hright_add hto_sub))

#print axioms BishopSec1P.regularSeqFinSum_sub_eventually

/-- The two adjacent subtraction gaps telescope under addition. -/
theorem subSeq_add_sub_cancel_eventually (x y z : CReal) :
    relEventually
      (addSeq (subSeq x y) (subSeq y z))
      (subSeq x z) := by
  have h1 :
      relEventually
        (addSeq (subSeq x y) (subSeq y z))
        (addSeq (subSeq x y) (addSeq y (negSeq z))) :=
    addSeq_respects_eventually _ _ _ _
      (relEventually_refl (subSeq x y))
      (subSeq_eq_add_neg_eventually y z)
  have h2 :
      relEventually
        (addSeq (subSeq x y) (addSeq y (negSeq z)))
        (addSeq (addSeq (subSeq x y) y) (negSeq z)) :=
    relEventually_symm _ _ (addSeq_assoc_eventually (subSeq x y) y (negSeq z))
  have hcancel :
      relEventually (addSeq (subSeq x y) y) x :=
    addSeq_sub_right_cancel_eventually x y
  have h3 :
      relEventually
        (addSeq (addSeq (subSeq x y) y) (negSeq z))
        (addSeq x (negSeq z)) :=
    addSeq_respects_eventually _ _ _ _
      hcancel (relEventually_refl (negSeq z))
  have h4 :
      relEventually (addSeq x (negSeq z)) (subSeq x z) :=
    relEventually_symm _ _ (subSeq_eq_add_neg_eventually x z)
  exact relEventually_trans _ _ _ h1
    (relEventually_trans _ _ _ h2
      (relEventually_trans _ _ _ h3 h4))

#print axioms BishopSec1P.subSeq_add_sub_cancel_eventually

/-- Pointwise scalar form of a shifted finite geometric tail:
`sum_{i<=M} 2^-(c+1+i) = 2^-c - 2^-(c+1+M)`. -/
theorem regularSeqFinSum_halfPow_tail_val (c M n : Nat) :
    (regularSeqFinSum (fun i => halfPow (c + 1 + i)) M).val n =
      eps c - eps (c + 1 + M) := by
  induction M generalizing n with
  | zero =>
      change eps (c + 1 + 0) = eps c - eps (c + 1 + 0)
      rw [Nat.add_zero]
      rw [← eps_succ_add_self c]
      ring
  | succ M ih =>
      rw [regularSeqFinSum]
      change
        (regularSeqFinSum (fun i => halfPow (c + 1 + i)) M).val (n + 1) +
            eps (c + 1 + (M + 1)) =
          eps c - eps (c + 1 + (M + 1))
      rw [ih (n + 1)]
      have hidx : c + 1 + (M + 1) = c + 1 + M + 1 := by omega
      rw [hidx]
      rw [← eps_succ_add_self (c + 1 + M)]
      ring

#print axioms BishopSec1P.regularSeqFinSum_halfPow_tail_val

/-- A finite shifted dyadic tail is strictly below its preceding half-power. -/
theorem regularSeqFinSum_halfPow_tail_lt (c M : Nat) :
    regularSeqLtProp
      (regularSeqFinSum (fun i => halfPow (c + 1 + i)) M)
      (halfPow c) := by
  refine ⟨c + 1 + M + 1, 0, ?_⟩
  intro n _hn
  have hval := regularSeqFinSum_halfPow_tail_val c M (n + 1)
  change COF.lt (eps (c + 1 + M + 1))
    (eps c - (regularSeqFinSum (fun i => halfPow (c + 1 + i)) M).val (n + 1))
  rw [hval]
  rw [show eps c - (eps c - eps (c + 1 + M)) = eps (c + 1 + M) by ring]
  exact eps_succ_lt_eps (c + 1 + M)

#print axioms BishopSec1P.regularSeqFinSum_halfPow_tail_lt

/-- A represented row tail is strictly below the requested dyadic gauge once
the row modulus has fired. -/
theorem rowTail_ltC {w : Nat → CReal} (h : RepSeriesSum w) (L N : Nat)
    (hN : h.tends.mod L ≤ N) :
    regularSeqLtProp (subSeq h.sum (regularSeqFinSum w N)) (halfPow L) := by
  have hclose : RepCloseAtGauge (L + 1) (regularSeqFinSum w N) h.sum :=
    h.tends.close L N hN
  simpa [halfPow, CReal.epsSeq] using
    regularSeqLtProp_sub_of_repClose_succ L hclose

#print axioms BishopSec1P.rowTail_ltC

/-- Finite maximum of a natural-number modulus family over `0..M`. -/
def maxUptoC (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | M + 1 => Nat.max (maxUptoC g M) (g (M + 1))

#print axioms BishopSec1P.maxUptoC

/-- Every entry below the bound is below the finite maximum. -/
theorem le_maxUptoC (g : Nat → Nat) :
    ∀ {M i : Nat}, i ≤ M → g i ≤ maxUptoC g M := by
  intro M
  induction M with
  | zero =>
      intro i hi
      rw [Nat.le_zero.mp hi]
      exact Nat.le_refl _
  | succ M ih =>
      intro i hi
      rcases Nat.lt_or_ge M i with hlt | hge
      · have heq : i = M + 1 := Nat.le_antisymm hi (Nat.succ_le_of_lt hlt)
        subst heq
        exact Nat.le_max_right _ _
      · exact Nat.le_trans (ih hge) (Nat.le_max_left _ _)

#print axioms BishopSec1P.le_maxUptoC

/-- Analytic grid-gap estimate: if `N` covers the row-sum modulus, the outer
row-sum modulus, and finitely many row tail moduli, then `T - gridSum N` is
strictly below the requested dyadic gauge. -/
theorem gridSum_gap_atC {a : Nat → Nat → CReal}
    (ha : ∀ i j, RegularSeqNonneg (a i j))
    (hrow : ∀ i, RepSeriesSum (a i))
    (hrowsum : RepSeriesSum (fun i => (hrow i).sum)) (k I0 N : Nat)
    (hI0 : hrowsum.tends.mod (k + 3) ≤ I0)
    (hNI0 : I0 ≤ N)
    (hNA : hrowsum.tends.mod (k + 2) ≤ N)
    (hNrow : ∀ i, i ≤ I0 → (hrow i).tends.mod (k + 4 + i) ≤ N) :
    regularSeqLtProp (subSeq hrowsum.sum (gridSumC a N)) (halfPow k) := by
  let rowSum : Nat → CReal := fun i => (hrow i).sum
  let rowPartial : Nat → CReal := fun i => regularSeqFinSum (a i) N
  let rt : Nat → CReal := fun i => subSeq (rowSum i) (rowPartial i)
  have hrt_eq :
      relEventually
        (regularSeqFinSum rt N)
        (subSeq (regularSeqFinSum rowSum N) (gridSumC a N)) := by
    simpa [rt, rowSum, rowPartial, gridSumC] using
      regularSeqFinSum_sub_eventually rowSum rowPartial N
  have hdecomp :
      relEventually
        (addSeq
          (subSeq hrowsum.sum (regularSeqFinSum rowSum N))
          (regularSeqFinSum rt N))
        (subSeq hrowsum.sum (gridSumC a N)) := by
    have hsecond :
        relEventually
          (addSeq
            (subSeq hrowsum.sum (regularSeqFinSum rowSum N))
            (regularSeqFinSum rt N))
          (addSeq
            (subSeq hrowsum.sum (regularSeqFinSum rowSum N))
            (subSeq (regularSeqFinSum rowSum N) (gridSumC a N))) :=
      addSeq_respects_eventually _ _ _ _
        (relEventually_refl (subSeq hrowsum.sum (regularSeqFinSum rowSum N)))
        hrt_eq
    exact relEventually_trans _ _ _ hsecond
      (subSeq_add_sub_cancel_eventually
        hrowsum.sum (regularSeqFinSum rowSum N) (gridSumC a N))
  have hP1 :
      regularSeqLtProp
        (subSeq hrowsum.sum (regularSeqFinSum rowSum N))
        (halfPow (k + 2)) := by
    simpa [rowSum] using rowTail_ltC hrowsum (k + 2) N hNA
  have hP2a_to_geom :
      regularSeqLtProp
        (regularSeqFinSum rt I0)
        (regularSeqFinSum (fun i => halfPow (k + 4 + i)) I0) := by
    refine regularSeqFinSum_lt_of_termwise_lt I0 ?_
    intro i hi
    simpa [rt, rowSum, rowPartial] using
      rowTail_ltC (hrow i) (k + 4 + i) N (hNrow i hi)
  have hgeom :
      regularSeqLtProp
        (regularSeqFinSum (fun i => halfPow (k + 4 + i)) I0)
        (halfPow (k + 3)) := by
    simpa [Nat.add_assoc] using
      regularSeqFinSum_halfPow_tail_lt (k + 3) I0
  have hP2a :
      regularSeqLtProp (regularSeqFinSum rt I0) (halfPow (k + 3)) :=
    regularSeqLtProp_trans _ _ _ hP2a_to_geom hgeom
  have hrt_nonneg : ∀ i, RegularSeqNonneg (rt i) := by
    intro i
    simpa [rt, rowSum, rowPartial] using
      (repPartialSum_le_sum (fun j => ha i j) (hrow i) N :
        RegularSeqLe (rowPartial i) (rowSum i))
  have hrt_le_rowsum : ∀ i, RegularSeqLe (rt i) (rowSum i) := by
    intro i
    have hpartial_nonneg : RegularSeqLe zeroSeq (rowPartial i) := by
      simpa [rowPartial] using
        regularSeqLe_zero_of_nonneg
          (regularSeqFinSum_nonneg_of_terms (fun j => ha i j) N)
    simpa [rt] using
      regularSeqLe_sub_right_self_of_nonneg
        (rowSum i) (rowPartial i) hpartial_nonneg
  have hP2b_le_gap :
      RegularSeqLe
        (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0))
        (subSeq (regularSeqFinSum rowSum N) (regularSeqFinSum rowSum I0)) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hNI0
    have hgap := (partialSum_gap hrt_nonneg hrt_le_rowsum I0 d).2
    rw [← hd] at hgap
    exact hgap
  have hrowSum_nonneg : ∀ i, RegularSeqNonneg (rowSum i) := by
    intro i
    dsimp [rowSum]
    exact repSeriesSum_nonneg (fun j => ha i j) (hrow i)
  have hrow_partial_le_total :
      RegularSeqLe (regularSeqFinSum rowSum N) hrowsum.sum :=
    repPartialSum_le_sum hrowSum_nonneg hrowsum N
  have hP2b_le_tail :
      RegularSeqLe
        (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0))
        (subSeq hrowsum.sum (regularSeqFinSum rowSum I0)) :=
    regularSeqLe_trans hP2b_le_gap
      (subSeq_monotone_left_regularSeqLe
        (regularSeqFinSum rowSum N) hrowsum.sum
        (regularSeqFinSum rowSum I0) hrow_partial_le_total)
  have hrows_tail :
      regularSeqLtProp
        (subSeq hrowsum.sum (regularSeqFinSum rowSum I0))
        (halfPow (k + 3)) := by
    simpa [rowSum] using rowTail_ltC hrowsum (k + 3) I0 hI0
  have hP2b :
      regularSeqLtProp
        (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0))
        (halfPow (k + 3)) :=
    regularSeqLtProp_of_le_of_lt hP2b_le_tail hrows_tail
  have hP2_left_event :
      relEventually
        (addSeq (regularSeqFinSum rt I0)
          (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0)))
        (regularSeqFinSum rt N) := by
    have hcomm :
        relEventually
          (addSeq (regularSeqFinSum rt I0)
            (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0)))
          (addSeq
            (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0))
            (regularSeqFinSum rt I0)) :=
      addSeq_comm_eventually
        (regularSeqFinSum rt I0)
        (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0))
    exact relEventually_trans _ _ _ hcomm
      (addSeq_sub_right_cancel_eventually
        (regularSeqFinSum rt N) (regularSeqFinSum rt I0))
  have hP2_raw :
      regularSeqLtProp
        (addSeq (regularSeqFinSum rt I0)
          (subSeq (regularSeqFinSum rt N) (regularSeqFinSum rt I0)))
        (addSeq (halfPow (k + 3)) (halfPow (k + 3))) :=
    regularSeqLtProp_add hP2a hP2b
  have hP2_left :
      regularSeqLtProp
        (regularSeqFinSum rt N)
        (addSeq (halfPow (k + 3)) (halfPow (k + 3))) :=
    regularSeqLtProp_of_left_eventual
      (relEventually_symm _ _ hP2_left_event) hP2_raw
  have hP2 :
      regularSeqLtProp (regularSeqFinSum rt N) (halfPow (k + 2)) :=
    regularSeqLtProp_of_right_eventual (halfPow_succ_add_self (k + 2)) hP2_left
  have hfinal_raw :
      regularSeqLtProp
        (addSeq
          (subSeq hrowsum.sum (regularSeqFinSum rowSum N))
          (regularSeqFinSum rt N))
        (addSeq (halfPow (k + 2)) (halfPow (k + 2))) :=
    regularSeqLtProp_add hP1 hP2
  have hfinal_left :
      regularSeqLtProp
        (subSeq hrowsum.sum (gridSumC a N))
        (addSeq (halfPow (k + 2)) (halfPow (k + 2))) :=
    regularSeqLtProp_of_left_eventual
      (relEventually_symm _ _ hdecomp) hfinal_raw
  have hfinal_k1 :
      regularSeqLtProp
        (subSeq hrowsum.sum (gridSumC a N))
        (halfPow (k + 1)) :=
    regularSeqLtProp_of_right_eventual (halfPow_succ_add_self (k + 1)) hfinal_left
  exact regularSeqLtProp_trans _ _ _ hfinal_k1 (regularSeqLtProp_halfPow_succ k)

#print axioms BishopSec1P.gridSum_gap_atC

/-- Data form of the grid gap: for every dyadic gauge, produce a concrete grid
size where `T - gridSum` is below that gauge. -/
def gridSum_gapC {a : Nat → Nat → CReal}
    (ha : ∀ i j, RegularSeqNonneg (a i j))
    (hrow : ∀ i, RepSeriesSum (a i))
    (hrowsum : RepSeriesSum (fun i => (hrow i).sum)) (k : Nat) :
    {N : Nat // regularSeqLtProp (subSeq hrowsum.sum (gridSumC a N)) (halfPow k)} :=
  let I0 := hrowsum.tends.mod (k + 3)
  let B := maxUptoC (fun i => (hrow i).tends.mod (k + 4 + i)) I0
  ⟨I0 + B + hrowsum.tends.mod (k + 2),
    gridSum_gap_atC ha hrow hrowsum k I0
      (I0 + B + hrowsum.tends.mod (k + 2))
      (Nat.le_refl _)
      (by omega)
      (by omega)
      (fun i hi =>
        Nat.le_trans
          (le_maxUptoC (fun i => (hrow i).tends.mod (k + 4 + i)) hi)
          (by omega))⟩

#print axioms BishopSec1P.gridSum_gapC

/-- Presented Fubini core: a nonnegative double series whose rows sum and whose
row sums themselves sum has a represented sum after square-shell flattening. -/
def cellAt_repSeriesSum {a : Nat → Nat → CReal}
    (ha : ∀ i j, RegularSeqNonneg (a i j))
    (hrow : ∀ i, RepSeriesSum (a i))
    (hrowsum : RepSeriesSum (fun i => (hrow i).sum)) :
    RepSeriesSum (fun k => a (BishopC.cellAt k).1 (BishopC.cellAt k).2) :=
  let flat : Nat → CReal :=
    fun k => a (BishopC.cellAt k).1 (BishopC.cellAt k).2
  let hb_nn : ∀ k, RegularSeqNonneg (flat k) :=
    fun k => ha (BishopC.cellAt k).1 (BishopC.cellAt k).2
  repSeriesSum_of_partialCauchy
    (repIsCauchy_of_mono_bounded_gap
      (v := regularSeqFinSum flat) (T := hrowsum.sum)
      (fun {_ _} hpq => regularSeqFinSum_mono_of_nonneg hb_nn hpq)
      (fun q =>
        have hmono_shell :
            RegularSeqLe (regularSeqFinSum flat q)
              (regularSeqFinSum flat (q * q + 2 * q)) :=
          regularSeqFinSum_mono_of_nonneg hb_nn
            (BishopC.self_le_sq_add q (2 * q))
        have hshell_grid :
            RegularSeqLe
              (regularSeqFinSum flat (q * q + 2 * q))
              (gridSumC a q) :=
          regularSeqLe_of_relEventually
            (by
              simpa [flat] using regularSeqFinSum_cellAt_eq_gridSumC a q)
        regularSeqLe_trans hmono_shell
          (regularSeqLe_trans hshell_grid (gridSum_le_TC ha hrow hrowsum q)))
      (fun k =>
        let g := gridSum_gapC ha hrow hrowsum k
        ⟨g.val * g.val + 2 * g.val, by
          have hrel :
              relEventually
                (regularSeqFinSum flat (g.val * g.val + 2 * g.val))
                (gridSumC a g.val) := by
            simpa [flat] using regularSeqFinSum_cellAt_eq_gridSumC a g.val
          have hgap_rel :
              relEventually
                (subSeq hrowsum.sum
                  (regularSeqFinSum flat (g.val * g.val + 2 * g.val)))
                (subSeq hrowsum.sum (gridSumC a g.val)) :=
            subSeq_respects_eventually _ _ _ _
              (relEventually_refl hrowsum.sum) hrel
          exact regularSeqLtProp_of_left_eventual hgap_rel g.property⟩))

#print axioms BishopSec1P.cellAt_repSeriesSum

/-- Presented dyadic powers of two, as the inverse scale to `halfPow`. -/
def twoPow : Nat → CReal
  | 0 => CReal.one
  | n + 1 => CReal.add (twoPow n) (twoPow n)

#print axioms BishopSec1P.twoPow

/-- The dyadic power `twoPow K` cancels the scale `halfPow K`. -/
theorem twoPow_mul_halfPow (n : Nat) :
    CReal.mul (twoPow n) (halfPow n) ≈ CReal.one := by
  induction n with
  | zero =>
      calc
        CReal.mul (twoPow 0) (halfPow 0)
            ≈ CReal.mul CReal.one CReal.one :=
              mul_congr (Setoid.refl CReal.one) halfPow_zero
        _ ≈ CReal.one := CReal.one_mul CReal.one
  | succ n ih =>
      calc
        CReal.mul (twoPow (n + 1)) (halfPow (n + 1))
            ≈ CReal.add
                (CReal.mul (twoPow n) (halfPow (n + 1)))
                (CReal.mul (twoPow n) (halfPow (n + 1))) := by
              simpa [twoPow] using
                CReal.right_distrib (twoPow n) (twoPow n) (halfPow (n + 1))
        _ ≈ CReal.mul (twoPow n)
              (CReal.add (halfPow (n + 1)) (halfPow (n + 1))) :=
              Setoid.symm
                (CReal.left_distrib (twoPow n) (halfPow (n + 1))
                  (halfPow (n + 1)))
        _ ≈ CReal.mul (twoPow n) (halfPow n) :=
              mul_congr (Setoid.refl (twoPow n)) (halfPow_succ_add_self n)
        _ ≈ CReal.one := ih

#print axioms BishopSec1P.twoPow_mul_halfPow

/-- Definition 1.6 domain for the presented #3 representation: every component
is defined at `x`, and the pointwise absolute value series is represented by
`RepSeriesSum`. -/
def IntegrableRepC3.domain {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : Set X :=
  { x | (∀ n, x ∈ (r.fn n).dom) ∧
      Nonempty (RepSeriesSum (fun n => CReal.abs ((r.fn n).toFun x))) }

#print axioms BishopSec1P.IntegrableRepC3.domain

/-- Multiplication by `halfPow K` does not enlarge the Definition 1.6 domain:
`twoPow K` recovers the original absolute point series. -/
theorem IntegrableRepC3.smul_halfPow_domain_subset {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (K : Nat) :
    (IntegrableRepC3.smul (halfPow K) r).domain ⊆ r.domain := by
  intro x hx
  rcases hx with ⟨hdom, hconv⟩
  refine ⟨?_, ?_⟩
  · intro n
    simpa [IntegrableRepC3.smul, BFunC.smul] using hdom n
  · rcases hconv with ⟨ss⟩
    refine ⟨repSeriesSum_congr (repSeriesSum_smul (twoPow K) ss) ?_⟩
    intro n
    let u : CReal := (r.fn n).toFun x
    have hscaled :
        CReal.mul (twoPow K) (CReal.abs (CReal.mul (halfPow K) u)) ≈
          CReal.abs u := by
      calc
        CReal.mul (twoPow K) (CReal.abs (CReal.mul (halfPow K) u))
            ≈ CReal.mul (twoPow K)
                (CReal.mul (CReal.abs (halfPow K)) (CReal.abs u)) :=
              mul_congr (Setoid.refl (twoPow K)) (CReal.abs_mul (halfPow K) u)
        _ ≈ CReal.mul (twoPow K)
              (CReal.mul (halfPow K) (CReal.abs u)) :=
              mul_congr (Setoid.refl (twoPow K))
                (mul_congr (halfPow_abs K) (Setoid.refl (CReal.abs u)))
        _ ≈ CReal.mul (CReal.mul (twoPow K) (halfPow K)) (CReal.abs u) :=
              Setoid.symm (CReal.mul_assoc (twoPow K) (halfPow K) (CReal.abs u))
        _ ≈ CReal.mul CReal.one (CReal.abs u) :=
              mul_congr (twoPow_mul_halfPow K) (Setoid.refl (CReal.abs u))
        _ ≈ CReal.abs u := CReal.one_mul (CReal.abs u)
    simpa [IntegrableRepC3.smul, BFunC.smul, u] using Setoid.symm hscaled

#print axioms BishopSec1P.IntegrableRepC3.smul_halfPow_domain_subset

theorem IntegrableRepC3.domain_subset_smulC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (c : CReal) :
    r.domain ⊆ (IntegrableRepC3.smul c r).domain := by
  intro x hx
  rcases hx with ⟨hdom, hconv⟩
  refine ⟨?_, ?_⟩
  · intro n
    simpa [IntegrableRepC3.smul, BFunC.smul] using hdom n
  · rcases hconv with ⟨ss⟩
    refine ⟨repSeriesSum_congr (repSeriesSum_smul (CReal.abs c) ss) ?_⟩
    intro n
    simpa [IntegrableRepC3.smul, BFunC.smul] using
      CReal.abs_mul c ((r.fn n).toFun x)

#print axioms BishopSec1P.IntegrableRepC3.domain_subset_smulC

def IsFullC {X : Type*} (S : IntSpaceC X) (A : Set X) : Prop :=
  ∃ F : Nat → IntegrableRepC3 S, { x | ∀ n, x ∈ (F n).domain } ⊆ A

#print axioms BishopSec1P.IsFullC

/-- Pointwise nonnegativity for a represented integrable function on the #3
`RepSeriesSum` track. -/
def RepNonnegC {X : Type*} {S : IntSpaceC X} (r : IntegrableRepC3 S) : Prop :=
  ∀ x : X, RepSeriesSum (fun n => CReal.abs ((r.fn n).toFun x)) →
    ∀ (hx : RepSeriesSum (fun n => (r.fn n).toFun x)), RegularSeqNonneg hx.sum

#print axioms BishopSec1P.RepNonnegC

/-- Presented #3 measurable-set package mirroring `IntegrableSet1`: a full
carrier set together with a characteristic-like integrable representative. -/
structure IntegrableSet1C {X : Type*} (S : IntSpaceC X) (A : BishopC.BSet X) where
  full : IsFullC S (A.S1 ∪ A.S2)
  rep : IntegrableRepC3 S
  valid : ∀ x, RepSeriesSum (fun n => CReal.abs ((rep.fn n).toFun x)) →
      (x ∈ A.S1 ∪ A.S2) ∧
      (x ∈ A.S1 → ∀ (h : RepSeriesSum (fun n => (rep.fn n).toFun x)),
        relEventually h.sum CReal.one) ∧
      (x ∈ A.S2 → ∀ (h : RepSeriesSum (fun n => (rep.fn n).toFun x)),
        relEventually h.sum CReal.zero)

#print axioms BishopSec1P.IntegrableSet1C

theorem IntegrableSet1_repNonnegC {X : Type*} {S : IntSpaceC X}
    {A : BishopC.BSet X} (hA : IntegrableSet1C S A) : RepNonnegC hA.rep := by
  intro x habs hx
  rcases (hA.valid x habs).1 with hx1 | hx2
  · have he : relEventually hx.sum CReal.one := (hA.valid x habs).2.1 hx1 hx
    have hone : RegularSeqNonneg CReal.one := by
      exact regularSeqNonneg_of_zero_le (by
        change RegularSeqLe zeroSeq oneSeq
        apply regularSeqLe_of_indexed_pointwise_le
        intro n
        change BishopC.Le (0 : Scalar) (1 : Scalar)
        exact scalar_nonneg_of_pos scalarCOFOSeed.one_pos)
    exact regularSeqNonneg_of_eventual he hone
  · have he : relEventually hx.sum CReal.zero := (hA.valid x habs).2.2 hx2 hx
    exact regularSeqNonneg_of_eventual he regularSeqNonneg_zero

#print axioms BishopSec1P.IntegrableSet1_repNonnegC

theorem IntegrableRepC3.domain_isFull {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    IsFullC S r.domain :=
  ⟨fun _ => r, fun _ hx => hx 0⟩

#print axioms BishopSec1P.IntegrableRepC3.domain_isFull

def IntegrableRepC3.ofL {X : Type*} {S : IntSpaceC X} {g : BFunC X}
    (hg : g ∈ S.L) : IntegrableRepC3 S where
  fn := fun n => if n = 0 then g else BFunC.smul CReal.zero g
  fn_mem := by
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn]
      exact hg
    · rw [if_neg hn]
      exact S.smul_mem CReal.zero hg
  abs_integral_sum := by
    refine repSeriesSum_congr (repSeriesSum_single (S.I (BFunC.absf g))) ?_
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]
      exact relEventually_refl _
    · rw [if_neg hn, if_neg hn]
      exact S.I_abs_smul_zeroC hg
  integral_sum := by
    refine repSeriesSum_congr (repSeriesSum_single (S.I g)) ?_
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]
      exact relEventually_refl _
    · rw [if_neg hn, if_neg hn]
      exact Setoid.trans (S.I_smul CReal.zero hg) (zero_mul_equivC (S.I g))

#print axioms BishopSec1P.IntegrableRepC3.ofL

theorem IntegrableRepC3.ofL_integral {X : Type*} {S : IntSpaceC X} {g : BFunC X}
    (hg : g ∈ S.L) :
    (IntegrableRepC3.ofL hg).integral = S.I g :=
  rfl

#print axioms BishopSec1P.IntegrableRepC3.ofL_integral

def IntegrableRepC3.ofL_value {X : Type*} {S : IntSpaceC X} {g : BFunC X}
    (hg : g ∈ S.L) (x : X) :
    { hs : RepSeriesSum (fun n => ((IntegrableRepC3.ofL hg).fn n).toFun x) //
        relEventually hs.sum (g.toFun x) } := by
  refine ⟨repSeriesSum_congr (repSeriesSum_single (g.toFun x)) ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · simpa [IntegrableRepC3.ofL, hn] using relEventually_refl (g.toFun x)
    · simpa [IntegrableRepC3.ofL, hn, BFunC.smul] using zero_mul_equivC (g.toFun x)
  · exact relEventually_refl (g.toFun x)

#print axioms BishopSec1P.IntegrableRepC3.ofL_value

def add_seriesSum_valueC3 {X : Type*} {S : IntSpaceC X}
    {r r' : IntegrableRepC3 S} {x : X}
    (hr : RepSeriesSum (fun k => (r.fn k).toFun x))
    (hr' : RepSeriesSum (fun k => (r'.fn k).toFun x)) :
    RepSeriesSum (fun n => ((r.add r').fn n).toFun x) := by
  refine repSeriesSum_congr (bc1_seriesSum_interleave hr hr') ?_
  intro n
  have hmap :
      ((r.add r').fn n).toFun x =
        bc1_seqMerge (fun k => (r.fn k).toFun x)
          (fun k => (r'.fn k).toFun x) n := by
    simpa [IntegrableRepC3.add] using
      (bc1_seqMerge_map (fun f : BFunC X => f.toFun x) r.fn r'.fn n)
  rw [hmap]
  exact relEventually_refl _

#print axioms BishopSec1P.add_seriesSum_valueC3

def neg_seriesSum_valueC3 {X : Type*} {S : IntSpaceC X}
    {r : IntegrableRepC3 S} {x : X}
    (hr : RepSeriesSum (fun k => (r.fn k).toFun x)) :
    RepSeriesSum (fun n => ((r.neg).fn n).toFun x) := by
  refine repSeriesSum_congr (BishopRegularSeqSeriesSum.repSeriesSum_neg hr) ?_
  intro n
  simpa [IntegrableRepC3.neg, BFunC.smul] using neg_one_mul_equiv ((r.fn n).toFun x)

#print axioms BishopSec1P.neg_seriesSum_valueC3

def sub_seriesSum_valueC3 {X : Type*} {S : IntSpaceC X}
    {r r' : IntegrableRepC3 S} {x : X}
    (hr : RepSeriesSum (fun k => (r.fn k).toFun x))
    (hr' : RepSeriesSum (fun k => (r'.fn k).toFun x)) :
    RepSeriesSum (fun n => ((r.sub r').fn n).toFun x) := by
  simpa [IntegrableRepC3.sub] using
    (add_seriesSum_valueC3 (r := r) (r' := r'.neg) (x := x)
      hr (neg_seriesSum_valueC3 (r := r') (x := x) hr'))

#print axioms BishopSec1P.sub_seriesSum_valueC3

def smul_seriesSum_valueC3 {X : Type*} {S : IntSpaceC X}
    (a : CReal) {r : IntegrableRepC3 S} {x : X}
    (hr : RepSeriesSum (fun k => (r.fn k).toFun x)) :
    RepSeriesSum (fun n => ((IntegrableRepC3.smul a r).fn n).toFun x) := by
  refine repSeriesSum_congr (repSeriesSum_smul a hr) ?_
  intro n
  change relEventually
    (CReal.mul a ((r.fn n).toFun x))
    (CReal.mul a ((r.fn n).toFun x))
  exact relEventually_refl _

#print axioms BishopSec1P.smul_seriesSum_valueC3

theorem IntegrableRepC3.smul_fn_toFunC {X : Type*} {S : IntSpaceC X}
    (c : CReal) (r : IntegrableRepC3 S) (n : Nat) (x : X) :
    ((IntegrableRepC3.smul c r).fn n).toFun x =
      CReal.mul c ((r.fn n).toFun x) :=
  rfl

#print axioms BishopSec1P.IntegrableRepC3.smul_fn_toFunC

/-- Technical lemma used in the public import closure. -/
def natFoldAdd : Nat → CReal → CReal
  | 0, z => addSeq z (negSeq z)
  | Nat.succ n, z => addSeq z (natFoldAdd n z)

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.natSmul {X : Type*} {S : IntSpaceC X}
    (n : Nat) (r : IntegrableRepC3 S) : IntegrableRepC3 S :=
  match n with
  | 0 => r.sub r
  | Nat.succ m => r.add (r.natSmul m)

#print axioms BishopSec1P.IntegrableRepC3.natSmul

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRepC3.integral_natSmul {X : Type*} {S : IntSpaceC X}
    (n : Nat) (r : IntegrableRepC3 S) :
    (r.natSmul n).integral = natFoldAdd n r.integral := by
  induction n with
  | zero => rfl
  | succ m ih =>
      show addSeq r.integral (r.natSmul m).integral
        = addSeq r.integral (natFoldAdd m r.integral)
      rw [ih]

#print axioms BishopSec1P.IntegrableRepC3.integral_natSmul

/-- Truncation telescope difference sequence:
`m_0 = min(S_0,a)`, `m_{j+1} = min(S_{j+1},a) - min(S_j,a)`. -/
def IntegrableRepC3.cutConstDiffFn {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) : Nat → BFunC X
  | 0 => BFunC.minC (BFunC.seqSum r.fn 0) a
  | (j + 1) =>
      BFunC.add (BFunC.minC (BFunC.seqSum r.fn (j + 1)) a)
        (BFunC.smul (CReal.neg CReal.one)
          (BFunC.minC (BFunC.seqSum r.fn j) a))

#print axioms BishopSec1P.IntegrableRepC3.cutConstDiffFn

/-- Each truncation telescope difference belongs to the integration space. -/
theorem IntegrableRepC3.cutConstDiffFn_mem {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) :
    ∀ j, r.cutConstDiffFn a j ∈ S.L
  | 0 => S.cutConst_mem a (S.seqSum_mem r.fn_mem 0)
  | (j + 1) =>
      S.add_mem
        (S.cutConst_mem a (S.seqSum_mem r.fn_mem (j + 1)))
        (S.smul_mem (CReal.neg CReal.one)
          (S.cutConst_mem a (S.seqSum_mem r.fn_mem j)))

#print axioms BishopSec1P.IntegrableRepC3.cutConstDiffFn_mem

theorem IntegrableRepC3.cutConstDiffFn_abs_le {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (ha : ¬ CReal.ltE a CReal.zero)
    (j : Nat) (x : X) :
    RegularSeqLe
      (CReal.abs ((r.cutConstDiffFn a j).toFun x))
      (CReal.abs ((r.fn j).toFun x)) := by
  induction j with
  | zero =>
      simpa [IntegrableRepC3.cutConstDiffFn, BFunC.seqSum, BFunC.minC]
        using CReal.abs_min_const_le ha ((r.fn 0).toFun x)
  | succ j =>
      let s0 : CReal := (BFunC.seqSum r.fn j).toFun x
      let s1 : CReal := (BFunC.seqSum r.fn (j + 1)).toFun x
      let fj : CReal := (r.fn (j + 1)).toFun x
      have hcut_to_sub :
          relEventually
            ((r.cutConstDiffFn a (j + 1)).toFun x)
            (CReal.sub (CReal.min s1 a) (CReal.min s0 a)) := by
        change relEventually
          (addSeq (CReal.min s1 a)
            (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq)
              (CReal.min s0 a)))
          (subSeq (CReal.min s1 a) (CReal.min s0 a))
        exact addSeq_negOneMul_right_eventually_subSeq
          cRatScalarMulArch (CReal.min s1 a) (CReal.min s0 a)
      have hleft :
          relEventually
            (CReal.abs ((r.cutConstDiffFn a (j + 1)).toFun x))
            (CReal.abs (CReal.sub (CReal.min s1 a) (CReal.min s0 a))) := by
        change relEventually
          (absSeq ((r.cutConstDiffFn a (j + 1)).toFun x))
          (absSeq (subSeq (CReal.min s1 a) (CReal.min s0 a)))
        exact absSeq_respects_eventually
          ((r.cutConstDiffFn a (j + 1)).toFun x)
          (subSeq (CReal.min s1 a) (CReal.min s0 a))
          hcut_to_sub
      have hmin :
          RegularSeqLe
            (CReal.abs (CReal.sub (CReal.min s1 a) (CReal.min s0 a)))
            (CReal.abs (CReal.sub s1 s0)) :=
        CReal.abs_min_sub_min_le s1 s0 a
      have htel :
          relEventually (CReal.sub s1 s0) fj := by
        simpa [s0, s1, fj, BFunC.seqSum, BFunC.add] using
          subSeq_add_left_cancel_eventually
            ((BFunC.seqSum r.fn j).toFun x)
            ((r.fn (j + 1)).toFun x)
      have hright :
          relEventually
            (CReal.abs (CReal.sub s1 s0))
            (CReal.abs fj) := by
        change relEventually (absSeq (subSeq s1 s0)) (absSeq fj)
        exact absSeq_respects_eventually (subSeq s1 s0) fj htel
      exact regularSeqLe_of_right_eventual hright
        (regularSeqLe_of_left_eventual hleft hmin)

#print axioms BishopSec1P.IntegrableRepC3.cutConstDiffFn_abs_le

theorem IntegrableRepC3.I_cutConstDiffFn_le {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (ha : ¬ CReal.ltE a CReal.zero)
    (j : Nat) :
    RegularSeqLe
      (S.I (BFunC.absf (r.cutConstDiffFn a j)))
      (S.I (BFunC.absf (r.fn j))) := by
  refine S.I_mono'
    (S.abs_mem (r.cutConstDiffFn_mem a j))
    (S.abs_mem (r.fn_mem j))
    ?_
  intro x _hcut _hfn
  simpa [BFunC.absf] using r.cutConstDiffFn_abs_le a ha j x

#print axioms BishopSec1P.IntegrableRepC3.I_cutConstDiffFn_le

/-- Integrable representation of `min{Σ fₙ, a}` for `a >= 0`.
The function sequence is the three-way merge of the truncation telescope
differences, the original terms, and their negatives. -/
def IntegrableRepC3.cutConstVal {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (ha : ¬ CReal.ltE a CReal.zero) :
    IntegrableRepC3 S :=
  let negFn : Nat → BFunC X :=
    fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)
  let mergedFn : Nat → BFunC X :=
    bc1_seqMerge3 (r.cutConstDiffFn a) r.fn negFn
  let hmem : ∀ n, mergedFn n ∈ S.L := by
    intro n
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
      subst n
      simpa [mergedFn, bc1_seqMerge3_zero] using r.cutConstDiffFn_mem a k
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
      subst n
      simpa [mergedFn, bc1_seqMerge3_one] using r.fn_mem k
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
      subst n
      simpa [mergedFn, negFn, bc1_seqMerge3_two] using
        S.smul_mem (CReal.neg CReal.one) (r.fn_mem k)
  let habs : RepSeriesSum (fun n => S.I (BFunC.absf (mergedFn n))) := by
    let absCut : Nat → CReal :=
      fun j => S.I (BFunC.absf (r.cutConstDiffFn a j))
    let absBase : Nat → CReal :=
      fun k => S.I (BFunC.absf (r.fn k))
    let absNeg : Nat → CReal :=
      fun k => S.I (BFunC.absf (negFn k))
    have hmap :
        (fun n => S.I (BFunC.absf (mergedFn n))) =
          bc1_seqMerge3 absCut absBase absNeg := by
      funext n
      simpa [mergedFn, negFn, absCut, absBase, absNeg] using
        bc1_seqMerge3_map
          (fun g : BFunC X => S.I (BFunC.absf g))
          (r.cutConstDiffFn a) r.fn negFn n
    rw [hmap]
    refine repSeriesSum_comparison ?_ ?_
      (bc1_seriesSum_merge3
        r.abs_integral_sum r.abs_integral_sum r.abs_integral_sum)
    · intro n
      have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
        subst n
        simpa [absCut, absBase, absNeg, bc1_seqMerge3_zero] using
          S.I_absf_nonneg (r.cutConstDiffFn_mem a k)
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
        subst n
        simpa [absCut, absBase, absNeg, bc1_seqMerge3_one] using
          S.I_absf_nonneg (r.fn_mem k)
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
        subst n
        simpa [absCut, absBase, absNeg, bc1_seqMerge3_two] using
          S.I_absf_nonneg (S.smul_mem (CReal.neg CReal.one) (r.fn_mem k))
    · intro n
      have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
        subst n
        simpa [absCut, absBase, absNeg, bc1_seqMerge3_zero] using
          r.I_cutConstDiffFn_le a ha k
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
        subst n
        simpa [absCut, absBase, absNeg, bc1_seqMerge3_one] using
          regularSeqLe_refl (S.I (BFunC.absf (r.fn k)))
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
        subst n
        have hneg :
            RegularSeqLe
              (S.I (BFunC.absf (BFunC.smul (CReal.neg CReal.one) (r.fn k))))
              (S.I (BFunC.absf (r.fn k))) :=
          regularSeqLe_of_left_eventual
            (S.I_absf_neg_eqC (r.fn_mem k))
            (regularSeqLe_refl (S.I (BFunC.absf (r.fn k))))
        simpa [absCut, absBase, absNeg, negFn, bc1_seqMerge3_two] using hneg
  { fn := mergedFn
    fn_mem := hmem
    abs_integral_sum := habs
    integral_sum :=
      repSeriesSum_of_absMajorant habs
        (fun n => S.I_absf_nonneg (hmem n))
        (fun n => S.I_abs_ge (hmem n)) }

#print axioms BishopSec1P.IntegrableRepC3.cutConstVal

/-- Absolute-value telescope difference sequence:
`d_0 = |S_0|`, `d_{j+1} = |S_{j+1}| - |S_j|`. -/
def IntegrableRepC3.absDiffFn {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : Nat → BFunC X
  | 0 => BFunC.absf (BFunC.seqSum r.fn 0)
  | (j + 1) =>
      BFunC.add (BFunC.absf (BFunC.seqSum r.fn (j + 1)))
        (BFunC.smul (CReal.neg CReal.one)
          (BFunC.absf (BFunC.seqSum r.fn j)))

#print axioms BishopSec1P.IntegrableRepC3.absDiffFn

/-- Each absolute-value telescope difference belongs to the integration space. -/
theorem IntegrableRepC3.absDiffFn_mem {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    ∀ j, r.absDiffFn j ∈ S.L
  | 0 => S.abs_mem (S.seqSum_mem r.fn_mem 0)
  | (j + 1) =>
      S.add_mem
        (S.abs_mem (S.seqSum_mem r.fn_mem (j + 1)))
        (S.smul_mem (CReal.neg CReal.one)
          (S.abs_mem (S.seqSum_mem r.fn_mem j)))

#print axioms BishopSec1P.IntegrableRepC3.absDiffFn_mem

theorem IntegrableRepC3.absDiffFn_abs_le {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (j : Nat) (x : X) :
    RegularSeqLe
      (CReal.abs ((r.absDiffFn j).toFun x))
      (CReal.abs ((r.fn j).toFun x)) := by
  induction j with
  | zero =>
      simpa [IntegrableRepC3.absDiffFn, BFunC.seqSum, BFunC.absf] using
        (regularSeqLe_abs_of_nonneg
          (absSeq_nonnegative_regularSeqLe ((r.fn 0).toFun x)) :
          RegularSeqLe
            (absSeq (absSeq ((r.fn 0).toFun x)))
            (absSeq ((r.fn 0).toFun x)))
  | succ j =>
      let s0 : CReal := (BFunC.seqSum r.fn j).toFun x
      let s1 : CReal := (BFunC.seqSum r.fn (j + 1)).toFun x
      let fj : CReal := (r.fn (j + 1)).toFun x
      have hdiff_to_sub :
          relEventually
            ((r.absDiffFn (j + 1)).toFun x)
            (CReal.sub (CReal.abs s1) (CReal.abs s0)) := by
        change relEventually
          (addSeq (CReal.abs s1)
            (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq)
              (CReal.abs s0)))
          (subSeq (CReal.abs s1) (CReal.abs s0))
        exact addSeq_negOneMul_right_eventually_subSeq
          cRatScalarMulArch (CReal.abs s1) (CReal.abs s0)
      have hleft :
          relEventually
            (CReal.abs ((r.absDiffFn (j + 1)).toFun x))
            (CReal.abs (CReal.sub (CReal.abs s1) (CReal.abs s0))) := by
        change relEventually
          (absSeq ((r.absDiffFn (j + 1)).toFun x))
          (absSeq (subSeq (CReal.abs s1) (CReal.abs s0)))
        exact absSeq_respects_eventually
          ((r.absDiffFn (j + 1)).toFun x)
          (subSeq (CReal.abs s1) (CReal.abs s0))
          hdiff_to_sub
      have habs :
          RegularSeqLe
            (CReal.abs (CReal.sub (CReal.abs s1) (CReal.abs s0)))
            (CReal.abs (CReal.sub s1 s0)) := by
        simpa [CReal.abs, CReal.sub] using
          regularSeqLe_abs_abs_sub_abs s1 s0
      have htel :
          relEventually (CReal.sub s1 s0) fj := by
        simpa [s0, s1, fj, BFunC.seqSum, BFunC.add] using
          subSeq_add_left_cancel_eventually
            ((BFunC.seqSum r.fn j).toFun x)
            ((r.fn (j + 1)).toFun x)
      have hright :
          relEventually
            (CReal.abs (CReal.sub s1 s0))
            (CReal.abs fj) := by
        change relEventually (absSeq (subSeq s1 s0)) (absSeq fj)
        exact absSeq_respects_eventually (subSeq s1 s0) fj htel
      exact regularSeqLe_of_right_eventual hright
        (regularSeqLe_of_left_eventual hleft habs)

#print axioms BishopSec1P.IntegrableRepC3.absDiffFn_abs_le

theorem IntegrableRepC3.I_absDiffFn_le {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (j : Nat) :
    RegularSeqLe
      (S.I (BFunC.absf (r.absDiffFn j)))
      (S.I (BFunC.absf (r.fn j))) := by
  refine S.I_mono'
    (S.abs_mem (r.absDiffFn_mem j))
    (S.abs_mem (r.fn_mem j))
    ?_
  intro x _hdiff _hfn
  simpa [BFunC.absf] using r.absDiffFn_abs_le j x

#print axioms BishopSec1P.IntegrableRepC3.I_absDiffFn_le

/-- Integrable representation of `|Σ fₙ|`.
The function sequence is the three-way merge of the absolute telescope
differences, the original terms, and their negatives. -/
def IntegrableRepC3.absVal {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : IntegrableRepC3 S :=
  let negFn : Nat → BFunC X :=
    fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)
  let mergedFn : Nat → BFunC X :=
    bc1_seqMerge3 r.absDiffFn r.fn negFn
  let hmem : ∀ n, mergedFn n ∈ S.L := by
    intro n
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
      subst n
      simpa [mergedFn, bc1_seqMerge3_zero] using r.absDiffFn_mem k
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
      subst n
      simpa [mergedFn, bc1_seqMerge3_one] using r.fn_mem k
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
      subst n
      simpa [mergedFn, negFn, bc1_seqMerge3_two] using
        S.smul_mem (CReal.neg CReal.one) (r.fn_mem k)
  let habs : RepSeriesSum (fun n => S.I (BFunC.absf (mergedFn n))) := by
    let absDiff : Nat → CReal :=
      fun j => S.I (BFunC.absf (r.absDiffFn j))
    let absBase : Nat → CReal :=
      fun k => S.I (BFunC.absf (r.fn k))
    let absNeg : Nat → CReal :=
      fun k => S.I (BFunC.absf (negFn k))
    have hmap :
        (fun n => S.I (BFunC.absf (mergedFn n))) =
          bc1_seqMerge3 absDiff absBase absNeg := by
      funext n
      simpa [mergedFn, negFn, absDiff, absBase, absNeg] using
        bc1_seqMerge3_map
          (fun g : BFunC X => S.I (BFunC.absf g))
          r.absDiffFn r.fn negFn n
    rw [hmap]
    refine repSeriesSum_comparison ?_ ?_
      (bc1_seriesSum_merge3
        r.abs_integral_sum r.abs_integral_sum r.abs_integral_sum)
    · intro n
      have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
        subst n
        simpa [absDiff, absBase, absNeg, bc1_seqMerge3_zero] using
          S.I_absf_nonneg (r.absDiffFn_mem k)
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
        subst n
        simpa [absDiff, absBase, absNeg, bc1_seqMerge3_one] using
          S.I_absf_nonneg (r.fn_mem k)
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
        subst n
        simpa [absDiff, absBase, absNeg, bc1_seqMerge3_two] using
          S.I_absf_nonneg (S.smul_mem (CReal.neg CReal.one) (r.fn_mem k))
    · intro n
      have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hcases with h0 | h1 | h2
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
        subst n
        simpa [absDiff, absBase, absNeg, bc1_seqMerge3_zero] using
          r.I_absDiffFn_le k
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
        subst n
        simpa [absDiff, absBase, absNeg, bc1_seqMerge3_one] using
          regularSeqLe_refl (S.I (BFunC.absf (r.fn k)))
      · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
        subst n
        have hneg :
            RegularSeqLe
              (S.I (BFunC.absf (BFunC.smul (CReal.neg CReal.one) (r.fn k))))
              (S.I (BFunC.absf (r.fn k))) :=
          regularSeqLe_of_left_eventual
            (S.I_absf_neg_eqC (r.fn_mem k))
            (regularSeqLe_refl (S.I (BFunC.absf (r.fn k))))
        simpa [absDiff, absBase, absNeg, negFn, bc1_seqMerge3_two] using hneg
  { fn := mergedFn
    fn_mem := hmem
    abs_integral_sum := habs
    integral_sum :=
      repSeriesSum_of_absMajorant habs
        (fun n => S.I_absf_nonneg (hmem n))
        (fun n => S.I_abs_ge (hmem n)) }

#print axioms BishopSec1P.IntegrableRepC3.absVal

/-- Integral telescope for the absolute-value difference sequence.  In the
presented layer this is `≈`, because `IntSpaceC.I_sub` is setoid equality. -/
theorem IntegrableRepC3.partialSum_absDiffFn_I {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (N : Nat) :
    relEventually
      (regularSeqFinSum (fun j => S.I (r.absDiffFn j)) N)
      (S.I (BFunC.absf (BFunC.seqSum r.fn N))) := by
  induction N with
  | zero =>
      exact relEventually_refl (S.I (BFunC.absf (BFunC.seqSum r.fn 0)))
  | succ N ih =>
      let i0 : CReal := S.I (BFunC.absf (BFunC.seqSum r.fn N))
      let i1 : CReal := S.I (BFunC.absf (BFunC.seqSum r.fn (N + 1)))
      have hterm :
          relEventually
            (S.I (r.absDiffFn (N + 1)))
            (subSeq i1 i0) := by
        simpa [IntegrableRepC3.absDiffFn, i0, i1] using
          S.I_sub
            (S.abs_mem (S.seqSum_mem r.fn_mem (N + 1)))
            (S.abs_mem (S.seqSum_mem r.fn_mem N))
      have hcong :
          relEventually
            (addSeq
              (regularSeqFinSum (fun j => S.I (r.absDiffFn j)) N)
              (S.I (r.absDiffFn (N + 1))))
            (addSeq i0 (subSeq i1 i0)) :=
        add_congr ih hterm
      have hcancel :
          relEventually (addSeq i0 (subSeq i1 i0)) i1 := by
        calc
          addSeq i0 (subSeq i1 i0)
              ≈ addSeq (subSeq i1 i0) i0 :=
                CReal.add_comm i0 (subSeq i1 i0)
          _ ≈ i1 := addSeq_sub_right_cancel_eventually i1 i0
      simpa [regularSeqFinSum, i1] using
        relEventually_trans _ _ _ hcong hcancel

#print axioms BishopSec1P.IntegrableRepC3.partialSum_absDiffFn_I

/-- Summability of the integral absolute-value difference sequence. -/
def IntegrableRepC3.seriesSum_absDiffFn_I {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RepSeriesSum (fun j => S.I (r.absDiffFn j)) :=
  let hAbsDiff : RepSeriesSum
      (fun j => S.I (BFunC.absf (r.absDiffFn j))) :=
    repSeriesSum_comparison
      (fun j => S.I_absf_nonneg (r.absDiffFn_mem j))
      (fun j => r.I_absDiffFn_le j)
      r.abs_integral_sum
  repSeriesSum_of_absMajorant hAbsDiff
    (fun j => S.I_absf_nonneg (r.absDiffFn_mem j))
    (fun j => S.I_abs_ge (r.absDiffFn_mem j))

#print axioms BishopSec1P.IntegrableRepC3.seriesSum_absDiffFn_I

/-- The integral of `absVal` is the sum of the absolute-value differences;
the two padding series `f` and `-f` cancel up to `≈`. -/
theorem IntegrableRepC3.absVal_integral_eq {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    relEventually r.absVal.integral r.seriesSum_absDiffFn_I.sum := by
  let negFn : Nat → BFunC X :=
    fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)
  let hneg : RepSeriesSum (fun k => S.I (negFn k)) :=
    repSeriesSum_congr
      (BishopRegularSeqSeriesSum.repSeriesSum_neg r.integral_sum)
      (fun k => S.I_neg (r.fn_mem k))
  let hmerged : RepSeriesSum (fun n => S.I (r.absVal.fn n)) :=
    repSeriesSum_congr
      (bc1_seriesSum_merge3
        r.seriesSum_absDiffFn_I r.integral_sum hneg)
      (fun n => by
        change relEventually
          (S.I (bc1_seqMerge3 r.absDiffFn r.fn negFn n))
          (bc1_seqMerge3
            (fun j => S.I (r.absDiffFn j))
            (fun k => S.I (r.fn k))
            (fun k => S.I (negFn k)) n)
        rw [bc1_seqMerge3_map
          (fun g : BFunC X => S.I g) r.absDiffFn r.fn negFn n]
        exact relEventually_refl _)
  have huniq : relEventually r.absVal.integral hmerged.sum :=
    repSeriesSum_unique r.absVal.integral_sum hmerged
  have hcancel :
      relEventually hmerged.sum r.seriesSum_absDiffFn_I.sum := by
    change relEventually
      (addSeq (addSeq r.seriesSum_absDiffFn_I.sum r.integral) hneg.sum)
      r.seriesSum_absDiffFn_I.sum
    calc
      addSeq (addSeq r.seriesSum_absDiffFn_I.sum r.integral) hneg.sum
          ≈ addSeq (addSeq r.seriesSum_absDiffFn_I.sum r.integral)
              (negSeq r.integral) := Setoid.refl _
      _ ≈ addSeq r.seriesSum_absDiffFn_I.sum
              (addSeq r.integral (negSeq r.integral)) :=
            CReal.add_assoc r.seriesSum_absDiffFn_I.sum r.integral
              (negSeq r.integral)
      _ ≈ addSeq r.seriesSum_absDiffFn_I.sum zeroSeq :=
            add_congr (Setoid.refl _) (add_right_neg_equiv r.integral)
      _ ≈ r.seriesSum_absDiffFn_I.sum :=
            CReal.add_zero r.seriesSum_absDiffFn_I.sum
  exact relEventually_trans _ _ _ huniq hcancel

#print axioms BishopSec1P.IntegrableRepC3.absVal_integral_eq

/-- Pointwise telescope for the absolute-value difference sequence.  This is
`≈` in the presented layer because `(-1)·x` is eventfully `-x`. -/
theorem IntegrableRepC3.partialSum_absDiffFn_value {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (x : X) (N : Nat) :
    relEventually
      (regularSeqFinSum (fun j => (r.absDiffFn j).toFun x) N)
      (absSeq ((BFunC.seqSum r.fn N).toFun x)) := by
  induction N with
  | zero =>
      exact relEventually_refl (absSeq ((BFunC.seqSum r.fn 0).toFun x))
  | succ N ih =>
      let s0 : CReal := (BFunC.seqSum r.fn N).toFun x
      let s1 : CReal := (BFunC.seqSum r.fn (N + 1)).toFun x
      have hterm :
          relEventually
            ((r.absDiffFn (N + 1)).toFun x)
            (subSeq (absSeq s1) (absSeq s0)) := by
        change relEventually
          (addSeq (absSeq s1)
            (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq)
              (absSeq s0)))
          (subSeq (absSeq s1) (absSeq s0))
        exact addSeq_negOneMul_right_eventually_subSeq
          cRatScalarMulArch (absSeq s1) (absSeq s0)
      have hcong :
          relEventually
            (addSeq
              (regularSeqFinSum (fun j => (r.absDiffFn j).toFun x) N)
              ((r.absDiffFn (N + 1)).toFun x))
            (addSeq (absSeq s0) (subSeq (absSeq s1) (absSeq s0))) :=
        add_congr ih hterm
      have hcancel :
          relEventually
            (addSeq (absSeq s0) (subSeq (absSeq s1) (absSeq s0)))
            (absSeq s1) := by
        calc
          addSeq (absSeq s0) (subSeq (absSeq s1) (absSeq s0))
              ≈ addSeq (subSeq (absSeq s1) (absSeq s0)) (absSeq s0) :=
                CReal.add_comm (absSeq s0) (subSeq (absSeq s1) (absSeq s0))
          _ ≈ absSeq s1 :=
                addSeq_sub_right_cancel_eventually (absSeq s1) (absSeq s0)
      simpa [regularSeqFinSum, s1] using
        relEventually_trans _ _ _ hcong hcancel

#print axioms BishopSec1P.IntegrableRepC3.partialSum_absDiffFn_value

/-- Absolute value is continuous for represented tendsto data. -/
def IntegrableRepC3.repTendsto_abs {u : Nat → CReal} {l : CReal}
    (h : RepSeriesTendsto u l) :
    RepSeriesTendsto (fun N => absSeq (u N)) (absSeq l) where
  mod := fun k => h.mod (k + 1)
  close := by
    intro k n hn
    exact repCloseAtGauge_of_absdiff_le (k + 1)
      (regularSeqLe_abs_abs_sub_abs (u n) l)
      (h.close (k + 1) n hn)

#print axioms BishopSec1P.IntegrableRepC3.repTendsto_abs

/-- The `d_j(x)` series converges to `|Σ f_j(x)|`. -/
def IntegrableRepC3.absVal_value {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (x : X)
    (hx : RepSeriesSum (fun n => (r.fn n).toFun x)) :
    { hd : RepSeriesSum (fun j => (r.absDiffFn j).toFun x) //
      relEventually hd.sum (absSeq hx.sum) } :=
  ⟨{ sum := absSeq hx.sum
     tends :=
       bc1_repSeriesTendsto_congr
         (IntegrableRepC3.repTendsto_abs hx.tends)
         (fun N => by
           simpa [BFunC.seqSum_toFun] using
             r.partialSum_absDiffFn_value x N) },
   relEventually_refl (absSeq hx.sum)⟩

#print axioms BishopSec1P.IntegrableRepC3.absVal_value

/-- Domain membership for finite `BFunC.seqSum` partial sums. -/
theorem mem_seqSum_domC {X : Type*} {S : IntSpaceC X}
    {r : IntegrableRepC3 S} {x : X}
    (hdom : ∀ k, x ∈ (r.fn k).dom) :
    ∀ m, x ∈ (BFunC.seqSum r.fn m).dom := by
  intro m
  induction m with
  | zero => exact hdom 0
  | succ m ih => exact ⟨ih, hdom (m + 1)⟩

#print axioms BishopSec1P.mem_seqSum_domC

/-- Domain membership for every absolute-value telescope difference. -/
theorem IntegrableRepC3.mem_absDiffFn_dom {X : Type*} {S : IntSpaceC X}
    {r : IntegrableRepC3 S} {x : X}
    (hdom : ∀ k, x ∈ (r.fn k).dom) :
    ∀ j, x ∈ (r.absDiffFn j).dom := by
  intro j
  cases j with
  | zero => exact mem_seqSum_domC (r := r) hdom 0
  | succ j =>
      exact ⟨mem_seqSum_domC (r := r) hdom (j + 1),
        mem_seqSum_domC (r := r) hdom j⟩

#print axioms BishopSec1P.IntegrableRepC3.mem_absDiffFn_dom

/-- Domain membership for every component of `absVal`. -/
theorem IntegrableRepC3.mem_absVal_dom {X : Type*} {S : IntSpaceC X}
    {r : IntegrableRepC3 S} {x : X}
    (hdom : ∀ k, x ∈ (r.fn k).dom) :
    ∀ n, x ∈ (r.absVal.fn n).dom := by
  intro n
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    subst n
    simpa [IntegrableRepC3.absVal, bc1_seqMerge3_zero] using
      r.mem_absDiffFn_dom hdom k
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    subst n
    simpa [IntegrableRepC3.absVal, bc1_seqMerge3_one] using hdom k
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    subst n
    simpa [IntegrableRepC3.absVal, bc1_seqMerge3_two] using hdom k

#print axioms BishopSec1P.IntegrableRepC3.mem_absVal_dom

/-- Absolute point-series convergence for the `absVal` three-way merge. -/
def IntegrableRepC3.absVal_absSeries {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) {x : X}
    (hconv : RepSeriesSum (fun n => absSeq ((r.fn n).toFun x))) :
    RepSeriesSum (fun n => absSeq ((r.absVal.fn n).toFun x)) := by
  have ad :
      RepSeriesSum (fun j => absSeq ((r.absDiffFn j).toFun x)) :=
    repSeriesSum_comparison
      (fun j => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe ((r.absDiffFn j).toFun x)))
      (fun j => r.absDiffFn_abs_le j x)
      hconv
  have anf :
      RepSeriesSum
        (fun k =>
          absSeq ((BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x)) :=
    repSeriesSum_congr hconv
      (fun k => by
        have hneg :
            relEventually
              ((BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x)
              (negSeq ((r.fn k).toFun x)) :=
          neg_one_mul_equiv ((r.fn k).toFun x)
        calc
          absSeq ((BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x)
              ≈ absSeq (negSeq ((r.fn k).toFun x)) :=
                absSeq_respects_eventually _ _ hneg
          _ ≈ absSeq ((r.fn k).toFun x) :=
                absSeq_negSeq_eventually ((r.fn k).toFun x))
  refine repSeriesSum_congr
    (bc1_seriesSum_merge3 ad hconv anf)
    ?_
  intro n
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    subst n
    simpa [IntegrableRepC3.absVal, bc1_seqMerge3_zero] using
      relEventually_refl (absSeq ((r.absDiffFn k).toFun x))
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    subst n
    simpa [IntegrableRepC3.absVal, bc1_seqMerge3_one] using
      relEventually_refl (absSeq ((r.fn k).toFun x))
  · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
    subst n
    simpa [IntegrableRepC3.absVal, bc1_seqMerge3_two] using
      relEventually_refl
        (absSeq ((BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x))

#print axioms BishopSec1P.IntegrableRepC3.absVal_absSeries

/-- Definition 1.13: the `L1` seminorm is the integral of `|f|`. -/
def IntegrableRepC3.normL1 {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : CReal :=
  r.absVal.integral

#print axioms BishopSec1P.IntegrableRepC3.normL1

/-- Signed point-series value of `absVal`: the three-way merge sums to
`|Σ f_n(x)|`, with the `f` and `-f` padding terms cancelling up to `≈`. -/
def IntegrableRepC3.absVal_signed_value {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (x : X)
    (hx : RepSeriesSum (fun n => (r.fn n).toFun x)) :
    { hs : RepSeriesSum (fun n => (r.absVal.fn n).toFun x) //
      relEventually hs.sum (absSeq hx.sum) } := by
  obtain ⟨hd, hdeq⟩ := r.absVal_value x hx
  let hneg :
      RepSeriesSum
        (fun k => (BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x) :=
    repSeriesSum_congr
      (BishopRegularSeqSeriesSum.repSeriesSum_neg hx)
      (fun k => neg_one_mul_equiv ((r.fn k).toFun x))
  let hmerged : RepSeriesSum (fun n => (r.absVal.fn n).toFun x) :=
    repSeriesSum_congr
      (bc1_seriesSum_merge3 hd hx hneg)
      (fun n => by
        change relEventually
          ((bc1_seqMerge3 r.absDiffFn r.fn
            (fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)) n).toFun x)
          (bc1_seqMerge3
            (fun j => (r.absDiffFn j).toFun x)
            (fun k => (r.fn k).toFun x)
            (fun k => (BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x) n)
        rw [bc1_seqMerge3_map
          (fun g : BFunC X => g.toFun x) r.absDiffFn r.fn
          (fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)) n]
        exact relEventually_refl _)
  refine ⟨hmerged, ?_⟩
  change relEventually
    (addSeq (addSeq hd.sum hx.sum) hneg.sum)
    (absSeq hx.sum)
  calc
    addSeq (addSeq hd.sum hx.sum) hneg.sum
        ≈ addSeq (addSeq hd.sum hx.sum) (negSeq hx.sum) :=
          Setoid.refl _
    _ ≈ addSeq hd.sum (addSeq hx.sum (negSeq hx.sum)) :=
          CReal.add_assoc hd.sum hx.sum (negSeq hx.sum)
    _ ≈ addSeq hd.sum zeroSeq :=
          add_congr (Setoid.refl _) (add_right_neg_equiv hx.sum)
    _ ≈ hd.sum := CReal.add_zero hd.sum
    _ ≈ absSeq hx.sum := hdeq

#print axioms BishopSec1P.IntegrableRepC3.absVal_signed_value

def repTendsto_min_constC (a : CReal) {u : Nat → CReal} {l : CReal}
    (h : RepSeriesTendsto u l) :
    RepSeriesTendsto (fun n => CReal.min (u n) a) (CReal.min l a) where
  mod := fun k => h.mod (k + 1)
  close := by
    intro k n hn
    exact repCloseAtGauge_of_absdiff_le (k + 1)
      (abs_min_sub_min_leC (u n) l a)
      (h.close (k + 1) n hn)

#print axioms BishopSec1P.repTendsto_min_constC

theorem IntegrableRepC3.partialSum_cutConstDiffFn_valueC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (x : X) (N : Nat) :
    relEventually
      (regularSeqFinSum (fun j => (r.cutConstDiffFn a j).toFun x) N)
      (CReal.min ((BFunC.seqSum r.fn N).toFun x) a) := by
  induction N with
  | zero =>
      exact relEventually_refl (CReal.min ((BFunC.seqSum r.fn 0).toFun x) a)
  | succ N ih =>
      let s0 : CReal := (BFunC.seqSum r.fn N).toFun x
      let s1 : CReal := (BFunC.seqSum r.fn (N + 1)).toFun x
      have hterm :
          relEventually
            ((r.cutConstDiffFn a (N + 1)).toFun x)
            (subSeq (CReal.min s1 a) (CReal.min s0 a)) := by
        change relEventually
          (addSeq (CReal.min s1 a)
            (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq)
              (CReal.min s0 a)))
          (subSeq (CReal.min s1 a) (CReal.min s0 a))
        exact addSeq_negOneMul_right_eventually_subSeq
          cRatScalarMulArch (CReal.min s1 a) (CReal.min s0 a)
      have hcong :
          relEventually
            (addSeq
              (regularSeqFinSum (fun j => (r.cutConstDiffFn a j).toFun x) N)
              ((r.cutConstDiffFn a (N + 1)).toFun x))
            (addSeq (CReal.min s0 a)
              (subSeq (CReal.min s1 a) (CReal.min s0 a))) :=
        add_congr ih hterm
      have hcancel :
          relEventually
            (addSeq (CReal.min s0 a)
              (subSeq (CReal.min s1 a) (CReal.min s0 a)))
            (CReal.min s1 a) := by
        calc
          addSeq (CReal.min s0 a)
              (subSeq (CReal.min s1 a) (CReal.min s0 a))
              ≈ addSeq (subSeq (CReal.min s1 a) (CReal.min s0 a))
                  (CReal.min s0 a) :=
                CReal.add_comm (CReal.min s0 a)
                  (subSeq (CReal.min s1 a) (CReal.min s0 a))
          _ ≈ CReal.min s1 a :=
                addSeq_sub_right_cancel_eventually
                  (CReal.min s1 a) (CReal.min s0 a)
      simpa [regularSeqFinSum, s1] using
        relEventually_trans _ _ _ hcong hcancel

#print axioms BishopSec1P.IntegrableRepC3.partialSum_cutConstDiffFn_valueC

def IntegrableRepC3.cutConstVal_valueC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (x : X)
    (hx : RepSeriesSum (fun n => (r.fn n).toFun x)) :
    { hd : RepSeriesSum (fun j => (r.cutConstDiffFn a j).toFun x) //
      relEventually hd.sum (CReal.min hx.sum a) } :=
  ⟨{ sum := CReal.min hx.sum a
     tends :=
       bc1_repSeriesTendsto_congr
         (repTendsto_min_constC a hx.tends)
         (fun N => by
           simpa [BFunC.seqSum_toFun] using
             r.partialSum_cutConstDiffFn_valueC a x N) },
   relEventually_refl (CReal.min hx.sum a)⟩

#print axioms BishopSec1P.IntegrableRepC3.cutConstVal_valueC

def IntegrableRepC3.cutConstVal_signed_valueC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (ha : ¬ CReal.ltE a CReal.zero) (x : X)
    (hx : RepSeriesSum (fun n => (r.fn n).toFun x)) :
    { hs : RepSeriesSum (fun n => ((r.cutConstVal a ha).fn n).toFun x) //
      relEventually hs.sum (CReal.min hx.sum a) } := by
  obtain ⟨hd, hdeq⟩ := r.cutConstVal_valueC a x hx
  let hneg :
      RepSeriesSum
        (fun k => (BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x) :=
    repSeriesSum_congr
      (BishopRegularSeqSeriesSum.repSeriesSum_neg hx)
      (fun k => neg_one_mul_equiv ((r.fn k).toFun x))
  let hmerged : RepSeriesSum (fun n => ((r.cutConstVal a ha).fn n).toFun x) :=
    repSeriesSum_congr
      (bc1_seriesSum_merge3 hd hx hneg)
      (fun n => by
        change relEventually
          ((bc1_seqMerge3 (r.cutConstDiffFn a) r.fn
            (fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)) n).toFun x)
          (bc1_seqMerge3
            (fun j => (r.cutConstDiffFn a j).toFun x)
            (fun k => (r.fn k).toFun x)
            (fun k => (BFunC.smul (CReal.neg CReal.one) (r.fn k)).toFun x) n)
        rw [bc1_seqMerge3_map
          (fun g : BFunC X => g.toFun x) (r.cutConstDiffFn a) r.fn
          (fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)) n]
        exact relEventually_refl _)
  refine ⟨hmerged, ?_⟩
  change relEventually
    (addSeq (addSeq hd.sum hx.sum) hneg.sum)
    (CReal.min hx.sum a)
  calc
    addSeq (addSeq hd.sum hx.sum) hneg.sum
        ≈ addSeq (addSeq hd.sum hx.sum) (negSeq hx.sum) :=
          Setoid.refl _
    _ ≈ addSeq hd.sum (addSeq hx.sum (negSeq hx.sum)) :=
          CReal.add_assoc hd.sum hx.sum (negSeq hx.sum)
    _ ≈ addSeq hd.sum zeroSeq :=
          add_congr (Setoid.refl _) (add_right_neg_equiv hx.sum)
    _ ≈ hd.sum := CReal.add_zero hd.sum
    _ ≈ CReal.min hx.sum a := hdeq

#print axioms BishopSec1P.IntegrableRepC3.cutConstVal_signed_valueC

theorem natCast_nonnegC (n : Nat) :
    ¬ CReal.ltE (constSeq (Nat.cast n)) CReal.zero := by
  have hle : RegularSeqLe zeroSeq (constSeq (Nat.cast n)) := by
    apply regularSeqLe_of_indexed_pointwise_le
    intro m
    change BishopC.Le (0 : Scalar) ((Nat.cast n : Scalar))
    induction n with
    | zero =>
        simpa using (BishopC.le_refl (0 : Scalar))
    | succ n ih =>
        have h1 : BishopC.Le (0 : Scalar) (1 : Scalar) :=
          scalar_nonneg_of_pos scalarCOFOSeed.one_pos
        have hsum : BishopC.Le ((0 : Scalar) + 0) ((Nat.cast n : Scalar) + 1) :=
          BishopC.le_add ih h1
        simpa [Nat.cast_succ] using hsum
  intro hlt
  change regularSeqLtProp (constSeq (Nat.cast n)) zeroSeq at hlt
  exact regularSeqLe_not_lt_reverse_prop hle hlt

#print axioms BishopSec1P.natCast_nonnegC

def IntegrableRepC3.cutNatVal {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (n : Nat) : IntegrableRepC3 S :=
  r.cutConstVal (constSeq (Nat.cast n)) (natCast_nonnegC n)

#print axioms BishopSec1P.IntegrableRepC3.cutNatVal

theorem epsConst_nonnegC (k : Nat) :
    ¬ CReal.ltE (constSeq (eps k)) CReal.zero := by
  have hle : RegularSeqLe zeroSeq (constSeq (eps k)) := by
    apply regularSeqLe_of_indexed_pointwise_le
    intro m
    change BishopC.Le (0 : Scalar) (eps k)
    exact eps_nonneg k
  intro hlt
  change regularSeqLtProp (constSeq (eps k)) zeroSeq at hlt
  exact regularSeqLe_not_lt_reverse_prop hle hlt

#print axioms BishopSec1P.epsConst_nonnegC

def IntegrableRepC3.cutSmallVal {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (k : Nat) : IntegrableRepC3 S :=
  r.absVal.cutConstVal (constSeq (eps k)) (epsConst_nonnegC k)

#print axioms BishopSec1P.IntegrableRepC3.cutSmallVal

theorem three_halfPow_add2_lt (k : Nat) :
    regularSeqLtProp
      (addSeq (addSeq (halfPow (k + 2)) (halfPow (k + 2))) (halfPow (k + 2)))
      (halfPow k) := by
  let hp2 : CReal := halfPow (k + 2)
  let hp1 : CReal := halfPow (k + 1)
  have hleft :
      relEventually
        (addSeq (addSeq hp2 hp2) hp2)
        (addSeq hp1 hp2) := by
    exact addSeq_respects_eventually _ _ _ _
      (by simpa [hp2, hp1, Nat.add_assoc] using halfPow_succ_add_self (k + 1))
      (relEventually_refl hp2)
  have hmid :
      regularSeqLtProp (addSeq hp1 hp2) (addSeq hp1 hp1) :=
    regularSeqLtProp_add_left hp1 hp2 hp1
      (by simpa [hp2, hp1, Nat.add_assoc] using
        regularSeqLtProp_halfPow_succ (k + 1))
  have hleft' :
      regularSeqLtProp (addSeq (addSeq hp2 hp2) hp2) (addSeq hp1 hp1) :=
    regularSeqLtProp_of_left_eventual hleft hmid
  have hright :
      relEventually (addSeq hp1 hp1) (halfPow k) := by
    simpa [hp1] using halfPow_succ_add_self k
  exact regularSeqLtProp_of_right_eventual hright hleft'

#print axioms BishopSec1P.three_halfPow_add2_lt

-- >>>v7:I.4
-- <<<v7:I.9
namespace BishopRegularSeqPFun

def posPart {X : Type} (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun X :=
  BishopCReal.BishopRegularSeqPFun.posPart A f

#print axioms BishopSec1P.BishopRegularSeqPFun.posPart

def negPart {X : Type} (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun X :=
  BishopCReal.BishopRegularSeqPFun.negPart A f

#print axioms BishopSec1P.BishopRegularSeqPFun.negPart

def posPart_pwnn {X : Type} (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun.PointwiseNonneg (posPart A f) where
  not_lt := by
    intro x _hx
    simpa [posPart, BishopCReal.BishopRegularSeqPFun.posPart,
      BishopCReal.BishopRegularSeqPFun.maxConst, regularSeqLtProp,
      maxSeqWith, subSeq] using
      not_posEventually_zero_sub_max_with A (f.toFun x)

#print axioms BishopSec1P.BishopRegularSeqPFun.posPart_pwnn

def negPart_pwnn {X : Type} (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun.PointwiseNonneg (negPart A f) where
  not_lt := by
    intro x _hx
    simpa [negPart, BishopCReal.BishopRegularSeqPFun.negPart,
      regularSeqLtProp, minSeqWith, subSeq] using
      not_posEventually_min_positive_with A (f.toFun x)

#print axioms BishopSec1P.BishopRegularSeqPFun.negPart_pwnn

theorem posPart_formula_equiv {X : Type} (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun.equiv
      (BishopCReal.BishopRegularSeqPFun.smul A halfSeq
        (BishopCReal.BishopRegularSeqPFun.add f
          (BishopCReal.BishopRegularSeqPFun.absf f)))
      (posPart A f) := by
  refine ⟨?_, ?_⟩
  · exact Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  · intro x _hx
    dsimp [BishopCReal.BishopRegularSeqPFun.smul,
      BishopCReal.BishopRegularSeqPFun.add,
      BishopCReal.BishopRegularSeqPFun.absf, posPart,
      BishopCReal.BishopRegularSeqPFun.posPart,
      BishopCReal.BishopRegularSeqPFun.maxConst, maxSeqWith]
    apply mulSeqConcrete_respects_eventually
    · exact relEventually_refl halfSeq
    · apply addSeq_respects_eventually
      · exact relEventually_symm (addSeq (f.toFun x) zeroSeq) (f.toFun x)
          (addSeq_zero_right_eventually (f.toFun x))
      · exact absSeq_respects_eventually (f.toFun x) (subSeq (f.toFun x) zeroSeq)
          (relEventually_symm (subSeq (f.toFun x) zeroSeq) (f.toFun x)
            (subSeq_zero_right_eventually (f.toFun x)))

#print axioms BishopSec1P.BishopRegularSeqPFun.posPart_formula_equiv

theorem negPart_formula_equiv {X : Type} (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun.equiv
      (BishopCReal.BishopRegularSeqPFun.smul A halfSeq
        (BishopCReal.BishopRegularSeqPFun.add
          (BishopCReal.BishopRegularSeqPFun.smul A (negSeq oneSeq) f)
          (BishopCReal.BishopRegularSeqPFun.absf f)))
      (negPart A f) := by
  refine ⟨?_, ?_⟩
  · exact Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  · intro x _hx
    dsimp [BishopCReal.BishopRegularSeqPFun.smul,
      BishopCReal.BishopRegularSeqPFun.add,
      BishopCReal.BishopRegularSeqPFun.absf, negPart,
      BishopCReal.BishopRegularSeqPFun.negPart, minSeqWith]
    let y : RegularSeq := f.toFun x
    let body : RegularSeq :=
      subSeq (addSeq y zeroSeq) (absSeq (subSeq y zeroSeq))
    have hnegmul :
        relEventually
          (mulSeqConcreteWith A (negSeq oneSeq) y)
          (negSeq y) :=
      mulSeq_neg_one_left_eventually_neg A y
    have hleft :
        relEventually
          (addSeq (mulSeqConcreteWith A (negSeq oneSeq) y) (absSeq y))
          (addSeq (negSeq y) (absSeq y)) :=
      addSeq_respects_eventually
        (mulSeqConcreteWith A (negSeq oneSeq) y) (negSeq y)
        (absSeq y) (absSeq y)
        hnegmul
        (relEventually_refl (absSeq y))
    have hbody0 : relEventually body (subSeq y (absSeq y)) := by
      dsimp [body]
      exact subSeq_respects_eventually
        (addSeq y zeroSeq) y
        (absSeq (subSeq y zeroSeq)) (absSeq y)
        (addSeq_zero_right_eventually y)
        (absSeq_respects_eventually (subSeq y zeroSeq) y
          (subSeq_zero_right_eventually y))
    have hbody1 :
        relEventually (subSeq y (absSeq y))
          (addSeq y (negSeq (absSeq y))) :=
      subSeq_eq_add_neg_eventually y (absSeq y)
    have hbody_add :
        relEventually body (addSeq y (negSeq (absSeq y))) :=
      relEventually_trans body (subSeq y (absSeq y))
        (addSeq y (negSeq (absSeq y))) hbody0 hbody1
    have hneg_body :
        relEventually (negSeq body)
          (negSeq (addSeq y (negSeq (absSeq y)))) :=
      negSeq_respects_eventually body
        (addSeq y (negSeq (absSeq y))) hbody_add
    have hneg_add :
        relEventually
          (negSeq (addSeq y (negSeq (absSeq y))))
          (addSeq (negSeq y) (absSeq y)) := by
      simpa using neg_add_neg_right_equiv y (absSeq y)
    have htarget_rev :
        relEventually (negSeq body)
          (addSeq (negSeq y) (absSeq y)) :=
      relEventually_trans (negSeq body)
        (negSeq (addSeq y (negSeq (absSeq y))))
        (addSeq (negSeq y) (absSeq y)) hneg_body hneg_add
    have htarget :
        relEventually (addSeq (negSeq y) (absSeq y)) (negSeq body) :=
      relEventually_symm (negSeq body)
        (addSeq (negSeq y) (absSeq y)) htarget_rev
    have hmul_left :
        relEventually
          (mulSeqConcreteWith A halfSeq
            (addSeq (mulSeqConcreteWith A (negSeq oneSeq) y) (absSeq y)))
          (mulSeqConcreteWith A halfSeq
            (addSeq (negSeq y) (absSeq y))) :=
      mulSeqConcrete_respects_eventually A
        halfSeq halfSeq
        (addSeq (mulSeqConcreteWith A (negSeq oneSeq) y) (absSeq y))
        (addSeq (negSeq y) (absSeq y))
        (relEventually_refl halfSeq) hleft
    have hmul_body :
        relEventually
          (mulSeqConcreteWith A halfSeq
            (addSeq (negSeq y) (absSeq y)))
          (mulSeqConcreteWith A halfSeq (negSeq body)) :=
      mulSeqConcrete_respects_eventually A
        halfSeq halfSeq
        (addSeq (negSeq y) (absSeq y)) (negSeq body)
        (relEventually_refl halfSeq) htarget
    have hmul_neg :
        relEventually
          (mulSeqConcreteWith A halfSeq (negSeq body))
          (negSeq (mulSeqConcreteWith A halfSeq body)) :=
      bounded_mul_neg_right_eventually_with A halfSeq body
    exact relEventually_trans
      (mulSeqConcreteWith A halfSeq
        (addSeq (mulSeqConcreteWith A (negSeq oneSeq) y) (absSeq y)))
      (mulSeqConcreteWith A halfSeq (addSeq (negSeq y) (absSeq y)))
      (negSeq (mulSeqConcreteWith A halfSeq body))
      hmul_left
      (relEventually_trans
        (mulSeqConcreteWith A halfSeq (addSeq (negSeq y) (absSeq y)))
        (mulSeqConcreteWith A halfSeq (negSeq body))
        (negSeq (mulSeqConcreteWith A halfSeq body))
        hmul_body hmul_neg)

#print axioms BishopSec1P.BishopRegularSeqPFun.negPart_formula_equiv

theorem posPart_mem {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopCReal.BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    posPart Arch f ∈ S.core.L := by
  have hformula :
      BishopCReal.BishopRegularSeqPFun.smul Arch halfSeq
        (BishopCReal.BishopRegularSeqPFun.add f
          (BishopCReal.BishopRegularSeqPFun.absf f)) ∈ S.core.L :=
    S.core.smul_mem halfSeq
      (S.core.add_mem hf (S.core.abs_mem hf))
  exact S.core.L_resp hformula (posPart_formula_equiv Arch f)

#print axioms BishopSec1P.BishopRegularSeqPFun.posPart_mem

theorem negPart_mem {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopCReal.BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    negPart Arch f ∈ S.core.L := by
  have hformula :
      BishopCReal.BishopRegularSeqPFun.smul Arch halfSeq
        (BishopCReal.BishopRegularSeqPFun.add
          (BishopCReal.BishopRegularSeqPFun.smul Arch (negSeq oneSeq) f)
          (BishopCReal.BishopRegularSeqPFun.absf f)) ∈ S.core.L :=
    S.core.smul_mem halfSeq
      (S.core.add_mem
        (S.core.smul_mem (negSeq oneSeq) hf)
        (S.core.abs_mem hf))
  exact S.core.L_resp hformula (negPart_formula_equiv Arch f)

#print axioms BishopSec1P.BishopRegularSeqPFun.negPart_mem

end BishopRegularSeqPFun

theorem maxSeqWith_zero_not_lt_zero
    (A : ScalarMulArchimedeanData) (y : RegularSeq) :
    ¬ regularSeqLtProp (maxSeqWith A y zeroSeq) zeroSeq := by
  simpa [regularSeqLtProp, maxSeqWith, subSeq] using
    not_posEventually_zero_sub_max_with A y

#print axioms BishopSec1P.maxSeqWith_zero_not_lt_zero

theorem negMinSeqWith_zero_not_lt_zero
    (A : ScalarMulArchimedeanData) (y : RegularSeq) :
    ¬ regularSeqLtProp (negSeq (minSeqWith A y zeroSeq)) zeroSeq := by
  simpa [regularSeqLtProp, minSeqWith, subSeq] using
    not_posEventually_min_positive_with A y

#print axioms BishopSec1P.negMinSeqWith_zero_not_lt_zero

def posPart_pwnn {X : Type}
    (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun.PointwiseNonneg
      (BishopCReal.BishopRegularSeqPFun.posPart A f) :=
  ⟨fun x _hx => maxSeqWith_zero_not_lt_zero A (f.toFun x)⟩

#print axioms BishopSec1P.posPart_pwnn

def negPart_pwnn {X : Type}
    (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun.PointwiseNonneg
      (BishopCReal.BishopRegularSeqPFun.negPart A f) :=
  ⟨fun x _hx => negMinSeqWith_zero_not_lt_zero A (f.toFun x)⟩

#print axioms BishopSec1P.negPart_pwnn

theorem maxSeqWith_zero_equiv_half_add_abs
    (A : ScalarMulArchimedeanData) (y : RegularSeq) :
    relEventually (maxSeqWith A y zeroSeq)
      (mulSeqConcreteWith A halfSeq (addSeq y (absSeq y))) := by
  exact relEventually_symm
    (mulSeqConcreteWith A halfSeq (addSeq y (absSeq y)))
    (maxSeqWith A y zeroSeq)
    (by
      dsimp [maxSeqWith]
      apply mulSeqConcrete_respects_eventually
      · exact relEventually_refl halfSeq
      · apply addSeq_respects_eventually
        · exact relEventually_symm (addSeq y zeroSeq) y
            (addSeq_zero_right_eventually y)
        · exact absSeq_respects_eventually y (subSeq y zeroSeq)
            (relEventually_symm (subSeq y zeroSeq) y
              (subSeq_zero_right_eventually y)))

#print axioms BishopSec1P.maxSeqWith_zero_equiv_half_add_abs

theorem posPart_equiv_half {X : Type}
    (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    BishopCReal.BishopRegularSeqPFun.equiv
      (BishopCReal.BishopRegularSeqPFun.smul A halfSeq
        (BishopCReal.BishopRegularSeqPFun.add f
          (BishopCReal.BishopRegularSeqPFun.absf f)))
      (BishopCReal.BishopRegularSeqPFun.posPart A f) := by
  refine ⟨?_, ?_⟩
  · exact Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  · intro x _hx
    change relEventually
      (mulSeqConcreteWith A halfSeq
        (addSeq (f.toFun x) (absSeq (f.toFun x))))
      (maxSeqWith A (f.toFun x) zeroSeq)
    exact relEventually_symm
      (maxSeqWith A (f.toFun x) zeroSeq)
      (mulSeqConcreteWith A halfSeq
        (addSeq (f.toFun x) (absSeq (f.toFun x))))
      (maxSeqWith_zero_equiv_half_add_abs A (f.toFun x))

#print axioms BishopSec1P.posPart_equiv_half

theorem posPart_mem {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopCReal.BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    BishopCReal.BishopRegularSeqPFun.posPart Arch f ∈ S.core.L := by
  have hformula :
      BishopCReal.BishopRegularSeqPFun.smul Arch halfSeq
        (BishopCReal.BishopRegularSeqPFun.add f
          (BishopCReal.BishopRegularSeqPFun.absf f)) ∈ S.core.L :=
    S.core.smul_mem halfSeq
      (S.core.add_mem hf (S.core.abs_mem hf))
  exact S.core.L_resp hformula (posPart_equiv_half Arch f)

#print axioms BishopSec1P.posPart_mem

theorem negPart_mem {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopCReal.BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    BishopCReal.BishopRegularSeqPFun.negPart Arch f ∈ S.core.L := by
  simpa [BishopRegularSeqPFun.negPart] using
    BishopRegularSeqPFun.negPart_mem S hf

#print axioms BishopSec1P.negPart_mem

namespace BishopRegularSeqPFun

structure PointwiseLE {X : Type}
    (f g : BishopCReal.BishopRegularSeqPFun X) : Prop where
  dom_eq : f.dom = g.dom
  le_val :
    forall x : X, x ∈ f.dom ->
      Not (regularSeqLtProp (g.toFun x) (f.toFun x))

#print axioms BishopSec1P.BishopRegularSeqPFun.PointwiseLE

end BishopRegularSeqPFun

theorem maxSeqWith_zero_le_abs
    (A : ScalarMulArchimedeanData) (y : RegularSeq) :
    ¬ regularSeqLtProp (absSeq y) (maxSeqWith A y zeroSeq) := by
  simpa [regularSeqLtProp, maxSeqWith, subSeq] using
    not_posEventually_max_sub_abs_with A y

#print axioms BishopSec1P.maxSeqWith_zero_le_abs

theorem negMinSeqWith_zero_le_abs
    (A : ScalarMulArchimedeanData) (y : RegularSeq) :
    ¬ regularSeqLtProp (absSeq y) (negSeq (minSeqWith A y zeroSeq)) := by
  simpa [regularSeqLtProp, minSeqWith, subSeq] using
    not_posEventually_neg_min_sub_abs_with A y

#print axioms BishopSec1P.negMinSeqWith_zero_le_abs

namespace BishopRegularSeqPFun

theorem posPart_le_abs {X : Type}
    (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    PointwiseLE
      (BishopCReal.BishopRegularSeqPFun.posPart A f)
      (BishopCReal.BishopRegularSeqPFun.absf f) := by
  refine ⟨rfl, ?_⟩
  intro x _hx
  simpa [BishopCReal.BishopRegularSeqPFun.posPart,
    BishopCReal.BishopRegularSeqPFun.maxConst,
    BishopCReal.BishopRegularSeqPFun.absf] using
    maxSeqWith_zero_le_abs A (f.toFun x)

#print axioms BishopSec1P.BishopRegularSeqPFun.posPart_le_abs

theorem negPart_le_abs {X : Type}
    (A : ScalarMulArchimedeanData)
    (f : BishopCReal.BishopRegularSeqPFun X) :
    PointwiseLE
      (BishopCReal.BishopRegularSeqPFun.negPart A f)
      (BishopCReal.BishopRegularSeqPFun.absf f) := by
  refine ⟨rfl, ?_⟩
  intro x _hx
  simpa [BishopCReal.BishopRegularSeqPFun.negPart,
    BishopCReal.BishopRegularSeqPFun.absf] using
    negMinSeqWith_zero_le_abs A (f.toFun x)

#print axioms BishopSec1P.BishopRegularSeqPFun.negPart_le_abs

end BishopRegularSeqPFun

theorem concrete_I_mono {Arch : ScalarMulArchimedeanData} {X : Type}
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f g : BishopCReal.BishopRegularSeqPFun X}
    (hf : f ∈ S.core.L) (hg : g ∈ S.core.L)
    (hfg : BishopRegularSeqPFun.PointwiseLE f g) :
    RegularSeqLe (S.core.I f) (S.core.I g) := by
  let neg_f : BishopCReal.BishopRegularSeqPFun X :=
    BishopCReal.BishopRegularSeqPFun.smul Arch (negSeq oneSeq) f
  let diff : BishopCReal.BishopRegularSeqPFun X :=
    BishopCReal.BishopRegularSeqPFun.add g neg_f
  have hneg_mem : neg_f ∈ S.core.L := by
    simpa [neg_f] using S.core.smul_mem (negSeq oneSeq) hf
  have hdiff_mem : diff ∈ S.core.L := by
    simpa [diff] using S.core.add_mem hg hneg_mem
  have hdiff_nn : BishopCReal.BishopRegularSeqPFun.PointwiseNonneg diff := by
    refine ⟨?_⟩
    intro x hx hlt
    have hxf : x ∈ f.dom := by
      have hx' : x ∈ g.dom ∩ f.dom := by
        simpa [diff, neg_f, BishopCReal.BishopRegularSeqPFun.add,
          BishopCReal.BishopRegularSeqPFun.smul] using hx
      exact hx'.2
    have hdiff_val :
        relEventually
          (diff.toFun x)
          (subSeq (g.toFun x) (f.toFun x)) := by
      change relEventually
        (addSeq (g.toFun x)
          (mulSeqConcreteWith Arch (negSeq oneSeq) (f.toFun x)))
        (subSeq (g.toFun x) (f.toFun x))
      exact addSeq_negOneMul_right_eventually_subSeq
        Arch (g.toFun x) (f.toFun x)
    have hsub0 :
        relEventually
          (subSeq zeroSeq (diff.toFun x))
          (subSeq zeroSeq (subSeq (g.toFun x) (f.toFun x))) :=
      subSeq_respects_eventually
        zeroSeq zeroSeq
        (diff.toFun x) (subSeq (g.toFun x) (f.toFun x))
        (relEventually_refl zeroSeq)
        hdiff_val
    have hzero_left :
        relEventually
          (subSeq zeroSeq (subSeq (g.toFun x) (f.toFun x)))
          (negSeq (subSeq (g.toFun x) (f.toFun x))) :=
      subSeq_zero_left_eventually (subSeq (g.toFun x) (f.toFun x))
    have hswap :
        relEventually
          (negSeq (subSeq (g.toFun x) (f.toFun x)))
          (subSeq (f.toFun x) (g.toFun x)) :=
      relEventually_symm
        (subSeq (f.toFun x) (g.toFun x))
        (negSeq (subSeq (g.toFun x) (f.toFun x)))
        (subSeq_comm_neg_eventually (f.toFun x) (g.toFun x))
    have htarget :
        relEventually
          (subSeq zeroSeq (diff.toFun x))
          (subSeq (f.toFun x) (g.toFun x)) :=
      relEventually_trans
        (subSeq zeroSeq (diff.toFun x))
        (subSeq zeroSeq (subSeq (g.toFun x) (f.toFun x)))
        (subSeq (f.toFun x) (g.toFun x))
        hsub0
        (relEventually_trans
          (subSeq zeroSeq (subSeq (g.toFun x) (f.toFun x)))
          (negSeq (subSeq (g.toFun x) (f.toFun x)))
          (subSeq (f.toFun x) (g.toFun x))
          hzero_left hswap)
    have hforbidden : regularSeqLtProp (g.toFun x) (f.toFun x) := by
      change PosEventually (subSeq (f.toFun x) (g.toFun x))
      exact posEventually_respects
        (subSeq zeroSeq (diff.toFun x))
        (subSeq (f.toFun x) (g.toFun x))
        htarget
        (by
          change PosEventually (subSeq zeroSeq (diff.toFun x)) at hlt
          exact hlt)
    exact hfg.le_val x hxf hforbidden
  have hI_diff_nonneg :
      ¬ regularSeqLtProp (S.core.I diff) zeroSeq :=
    concrete_I_nonneg S hdiff_mem hdiff_nn
  have hI_add :
      relEventually
        (S.core.I diff)
        (addSeq (S.core.I g) (S.core.I neg_f)) := by
    simpa [diff] using S.core.I_add hg hneg_mem
  have hI_smul :
      relEventually
        (S.core.I neg_f)
        (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I f)) := by
    simpa [neg_f] using S.core.I_smul (negSeq oneSeq) hf
  have hI_add_smul :
      relEventually
        (addSeq (S.core.I g) (S.core.I neg_f))
        (addSeq (S.core.I g)
          (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I f))) :=
    addSeq_respects_eventually
      (S.core.I g) (S.core.I g)
      (S.core.I neg_f)
      (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I f))
      (relEventually_refl (S.core.I g))
      hI_smul
  have hI_to_sub :
      relEventually
        (S.core.I diff)
        (subSeq (S.core.I g) (S.core.I f)) :=
    relEventually_trans
      (S.core.I diff)
      (addSeq (S.core.I g) (S.core.I neg_f))
      (subSeq (S.core.I g) (S.core.I f))
      hI_add
      (relEventually_trans
        (addSeq (S.core.I g) (S.core.I neg_f))
        (addSeq (S.core.I g)
          (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I f)))
        (subSeq (S.core.I g) (S.core.I f))
        hI_add_smul
        (addSeq_negOneMul_right_eventually_subSeq
          Arch (S.core.I g) (S.core.I f)))
  change RegularSeqNonneg (subSeq (S.core.I g) (S.core.I f))
  intro hcounter
  have hcounter_pos :
      PosEventually
        (subSeq zeroSeq (subSeq (S.core.I g) (S.core.I f)) ) := by
    change PosEventually
      (subSeq zeroSeq (subSeq (S.core.I g) (S.core.I f))) at hcounter
    exact hcounter
  have hsub_transport :
      relEventually
        (subSeq zeroSeq (subSeq (S.core.I g) (S.core.I f)))
        (subSeq zeroSeq (S.core.I diff)) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      (subSeq (S.core.I g) (S.core.I f)) (S.core.I diff)
      (relEventually_refl zeroSeq)
      (relEventually_symm
        (S.core.I diff)
        (subSeq (S.core.I g) (S.core.I f))
        hI_to_sub)
  exact hI_diff_nonneg
    (by
      change PosEventually (subSeq zeroSeq (S.core.I diff))
      exact posEventually_respects
        (subSeq zeroSeq (subSeq (S.core.I g) (S.core.I f)))
        (subSeq zeroSeq (S.core.I diff))
        hsub_transport
        hcounter_pos)

#print axioms BishopSec1P.concrete_I_mono

/-! ### Section 6 measure non-negativity `mu(C) >= 0`

The clean-characteristic measure `mu(C) = integral chi_C` is the represented
signed series `Sum_n I(f_n)`, not a single `L`-integral, so `concrete_I_nonneg`
does not apply to it directly.  The non-trivial fact that IS reachable
choice-free is that the `L1` norm `Sum_n I(|f_n|) >= 0`: each term
`I(|f_n|) = I(absf (f_n)) >= 0` by `concrete_I_nonneg` (abs is pointwise
non-negative and `L` is closed under `absf`), and a finite partial sum of
non-negative reals is non-negative, transported to the sum through the
represented `tends` datum.  Deriving `mu(C) = |mu|(C)` (hence `mu(C) >= 0`)
from pointwise non-negativity would require the general Lemma 1.7
well-definedness bridge `BishopRegularSeqLemma17ZeroBridge S`, which is not
built for `Def11`.  It is therefore packaged as the `abs_integral_eq`
certificate carried by `CleanCharDataC`. -/

/-- `absf g` is pointwise non-negative: at every point its value is
`absSeq (g.toFun x) >= 0`.  (`PointwiseNonneg` is a `Type`-valued structure,
so this is a `def`, not a `theorem`.) -/
def absf_pointwiseNonneg {X : Type} (g : BishopRegularSeqPFun X) :
    BishopRegularSeqPFun.PointwiseNonneg (BishopRegularSeqPFun.absf g) :=
  { not_lt := fun x _hx =>
      regularSeqNonneg_of_zero_le (absSeq_nonnegative_regularSeqLe (g.toFun x)) }

#print axioms BishopSec1P.absf_pointwiseNonneg

/-- A finite partial sum of pointwise non-negative reals is non-negative. -/
theorem regularSeqFinSum_nonneg {u : Nat → CReal}
    (hu : ∀ n, RegularSeqNonneg (u n)) (N : Nat) :
    RegularSeqNonneg (regularSeqFinSum u N) := by
  induction N with
  | zero => exact hu 0
  | succ n ih => exact regularSeqNonneg_add ih (hu (n + 1))

#print axioms BishopSec1P.regularSeqFinSum_nonneg

/-! ### Lemma 1.10 assembly over the presented Fubini core -/

/-- Dropping a finite prefix does not affect represented summability. -/
def repSeriesSum_of_tailC {u : Nat → CReal} (p : Nat)
    (htail : RepSeriesSum (fun l => u (p + 1 + l))) : RepSeriesSum u where
  sum := addSeq (regularSeqFinSum u p) htail.sum
  tends :=
    { mod := fun k => p + 1 + htail.tends.mod (k + 2)
      close := by
        intro k n hn
        obtain ⟨d, hd⟩ : ∃ d, n = p + (d + 1) := ⟨n - p - 1, by omega⟩
        subst n
        have hdmod : htail.tends.mod (k + 2) ≤ d := by omega
        have hsplit : RepCloseAtGauge (k + 2)
            (regularSeqFinSum u (p + (d + 1)))
            (addSeq (regularSeqFinSum u p)
              (regularSeqFinSum (fun j => u (p + 1 + j)) d)) :=
          bc1_repClose_of_relEventually
            (regularSeqFinSum_split_eventually u p d) (k + 2)
        have hhead : RepCloseAtGauge (k + 3)
            (regularSeqFinSum u p) (regularSeqFinSum u p) :=
          bc1_repClose_of_relEventually (relEventually_refl _) (k + 3)
        have htail_close : RepCloseAtGauge (k + 3)
            (regularSeqFinSum (fun j => u (p + 1 + j)) d) htail.sum :=
          htail.tends.close (k + 2) d hdmod
        have hadd : RepCloseAtGauge (k + 2)
            (addSeq (regularSeqFinSum u p)
              (regularSeqFinSum (fun j => u (p + 1 + j)) d))
            (addSeq (regularSeqFinSum u p) htail.sum) :=
          bc1_repCloseAtGauge_add (k + 2) hhead htail_close
        exact repCloseAtGauge_triangle_succ (k + 1) hsplit hadd }

#print axioms BishopSec1P.repSeriesSum_of_tailC

theorem regularSeqTerm_le_finSum_of_nonneg {u : Nat → CReal}
    (hu : ∀ n, RegularSeqNonneg (u n)) :
    ∀ N : Nat, RegularSeqLe (u N) (regularSeqFinSum u N)
  | 0 => regularSeqLe_refl (u 0)
  | N + 1 => by
      have hprefix : RegularSeqNonneg (regularSeqFinSum u N) :=
        regularSeqFinSum_nonneg_of_terms hu N
      have h0prefix : RegularSeqLe zeroSeq (regularSeqFinSum u N) :=
        regularSeqLe_zero_of_nonneg hprefix
      have hle :
          RegularSeqLe (addSeq zeroSeq (u (N + 1)))
            (addSeq (regularSeqFinSum u N) (u (N + 1))) :=
        addSeq_monotone_left_regularSeqLe zeroSeq (regularSeqFinSum u N)
          (u (N + 1)) h0prefix
      exact regularSeqLe_of_left_eventual
        (relEventually_symm _ _ (addSeq_zero_left_eventually (u (N + 1)))) hle

#print axioms BishopSec1P.regularSeqTerm_le_finSum_of_nonneg

theorem regularSeqTerm_le_finSum_gap_of_lt {u : Nat → CReal}
    (hu : ∀ n, RegularSeqNonneg (u n)) {m n : Nat} (hmn : m < n) :
    RegularSeqLe (u n)
      (subSeq (regularSeqFinSum u n) (regularSeqFinSum u m)) := by
  obtain ⟨d, hd⟩ : ∃ d, n = m + (d + 1) := ⟨n - m - 1, by omega⟩
  subst n
  let shift : Nat → CReal := fun j => u (m + 1 + j)
  have hterm : RegularSeqLe (shift d) (regularSeqFinSum shift d) :=
    regularSeqTerm_le_finSum_of_nonneg (fun j => hu (m + 1 + j)) d
  have hgap :
      relEventually
        (subSeq (regularSeqFinSum u (m + (d + 1))) (regularSeqFinSum u m))
        (regularSeqFinSum shift d) := by
    have hsplit := regularSeqFinSum_split_eventually u m d
    have hsub :
        relEventually
          (subSeq (regularSeqFinSum u (m + (d + 1))) (regularSeqFinSum u m))
          (subSeq
            (addSeq (regularSeqFinSum u m) (regularSeqFinSum shift d))
            (regularSeqFinSum u m)) :=
      subSeq_respects_eventually _ _ _ _ hsplit
        (relEventually_refl (regularSeqFinSum u m))
    exact relEventually_trans _ _ _ hsub
      (subSeq_add_left_cancel_eventually (regularSeqFinSum u m)
        (regularSeqFinSum shift d))
  have hright : RegularSeqLe (shift d)
      (subSeq (regularSeqFinSum u (m + (d + 1))) (regularSeqFinSum u m)) :=
    regularSeqLe_of_right_eventual (relEventually_symm _ _ hgap) hterm
  simpa [shift, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright

#print axioms BishopSec1P.regularSeqTerm_le_finSum_gap_of_lt

theorem regularSeqFinSum_inj_gap_leC {b : Nat → CReal}
    (hb : ∀ n, RegularSeqNonneg (b n)) {e : Nat → Nat}
    (he : ∀ l, e l < e (l + 1)) :
    ∀ L d : Nat,
      RegularSeqLe
        (subSeq
          (regularSeqFinSum (fun l => b (e l)) (L + d))
          (regularSeqFinSum (fun l => b (e l)) L))
        (subSeq (regularSeqFinSum b (e (L + d))) (regularSeqFinSum b (e L)))
  | L, 0 => by
      have hleft :
          relEventually
            (subSeq
              (regularSeqFinSum (fun l => b (e l)) (L + 0))
              (regularSeqFinSum (fun l => b (e l)) L))
            zeroSeq := by
        simpa using subSeq_self_eventually_law
          (regularSeqFinSum (fun l => b (e l)) L)
      have hright :
          relEventually
            (subSeq (regularSeqFinSum b (e (L + 0))) (regularSeqFinSum b (e L)))
            zeroSeq := by
        simpa using subSeq_self_eventually_law (regularSeqFinSum b (e L))
      have hzright :
          RegularSeqLe zeroSeq
            (subSeq (regularSeqFinSum b (e (L + 0))) (regularSeqFinSum b (e L))) :=
        regularSeqLe_of_right_eventual (relEventually_symm _ _ hright)
          (regularSeqLe_refl zeroSeq)
      exact regularSeqLe_of_left_eventual hleft hzright
  | L, d + 1 => by
      let re : Nat → CReal := fun l => b (e l)
      let leftOld : CReal :=
        subSeq (regularSeqFinSum re (L + d)) (regularSeqFinSum re L)
      let rightOld : CReal :=
        subSeq (regularSeqFinSum b (e (L + d))) (regularSeqFinSum b (e L))
      let gapNext : CReal :=
        subSeq (regularSeqFinSum b (e (L + (d + 1))))
          (regularSeqFinSum b (e (L + d)))
      have hleft_ev :
          relEventually
            (subSeq
              (regularSeqFinSum re (L + (d + 1))) (regularSeqFinSum re L))
            (addSeq leftOld (re (L + d + 1))) := by
        simpa [leftOld, re, Nat.add_assoc] using
          regularSeqFinSum_gap_succ_eventually re L d
      have hterm_gap :
          RegularSeqLe (re (L + d + 1)) gapNext := by
        have hlt : e (L + d) < e (L + d + 1) := he (L + d)
        simpa [re, gapNext, Nat.add_assoc] using
          regularSeqTerm_le_finSum_gap_of_lt hb hlt
      have hadd :
          RegularSeqLe (addSeq leftOld (re (L + d + 1)))
            (addSeq rightOld gapNext) :=
        regularSeqLe_add (regularSeqFinSum_inj_gap_leC hb he L d) hterm_gap
      have hright_ev :
          relEventually (addSeq rightOld gapNext)
            (subSeq (regularSeqFinSum b (e (L + (d + 1))))
              (regularSeqFinSum b (e L))) := by
        have hcomm : relEventually (addSeq rightOld gapNext) (addSeq gapNext rightOld) :=
          addSeq_comm_eventually rightOld gapNext
        have hcancel : relEventually (addSeq gapNext rightOld)
            (subSeq (regularSeqFinSum b (e (L + (d + 1))))
              (regularSeqFinSum b (e L))) := by
          simpa [gapNext, rightOld] using
            subSeq_add_sub_cancel_eventually
              (regularSeqFinSum b (e (L + (d + 1))))
              (regularSeqFinSum b (e (L + d)))
              (regularSeqFinSum b (e L))
        exact relEventually_trans _ _ _ hcomm hcancel
      exact regularSeqLe_of_left_eventual hleft_ev
        (regularSeqLe_of_right_eventual hright_ev hadd)

#print axioms BishopSec1P.regularSeqFinSum_inj_gap_leC

theorem regularSeqFinSum_inj_absdiff_auxC {b : Nat → CReal}
    (hb : ∀ n, RegularSeqNonneg (b n)) {e : Nat → Nat}
    (he : ∀ l, e l < e (l + 1)) (m d : Nat) :
    RegularSeqLe
      (absSeq
        (subSeq
          (regularSeqFinSum (fun l => b (e l)) m)
          (regularSeqFinSum (fun l => b (e l)) (m + d))))
      (absSeq
        (subSeq (regularSeqFinSum b (e m)) (regularSeqFinSum b (e (m + d))))) := by
  let re : Nat → CReal := fun l => b (e l)
  have hre_nn : ∀ l, RegularSeqNonneg (re l) := fun l => hb (e l)
  let ga := subSeq (regularSeqFinSum re (m + d)) (regularSeqFinSum re m)
  let gb := subSeq (regularSeqFinSum b (e (m + d))) (regularSeqFinSum b (e m))
  let revA := subSeq (regularSeqFinSum re m) (regularSeqFinSum re (m + d))
  let revB := subSeq (regularSeqFinSum b (e m)) (regularSeqFinSum b (e (m + d)))
  have hga_nonneg : RegularSeqNonneg ga :=
    (partialSum_gap hre_nn (fun n => regularSeqLe_refl (re n)) m d).1
  have hga_gb : RegularSeqLe ga gb :=
    regularSeqFinSum_inj_gap_leC hb he m d
  have hgb_abs_gb : RegularSeqLe gb (absSeq gb) := base_le_abs_base_regularSeqLe gb
  have habs_gb_revB : relEventually (absSeq gb) (absSeq revB) := by
    simpa [gb, revB] using
      (absSeq_subSeq_comm_eventually
        (regularSeqFinSum b (e (m + d))) (regularSeqFinSum b (e m)))
  have hgb_abs_revB : RegularSeqLe gb (absSeq revB) :=
    regularSeqLe_of_right_eventual habs_gb_revB hgb_abs_gb
  have hga_abs_revB : RegularSeqLe ga (absSeq revB) :=
    regularSeqLe_trans hga_gb hgb_abs_revB
  have hrevA_nonpos : RegularSeqLe revA zeroSeq := by
    have hneg_ga : RegularSeqLe (negSeq ga) zeroSeq :=
      regularSeqLe_neg_nonpos_of_nonneg hga_nonneg
    exact regularSeqLe_of_left_eventual
      (by
        simpa [ga, revA] using
          (subSeq_comm_neg_eventually
            (regularSeqFinSum re m) (regularSeqFinSum re (m + d))))
      hneg_ga
  have hrevA_absB : RegularSeqLe revA (absSeq revB) :=
    regularSeqLe_trans hrevA_nonpos (absSeq_nonnegative_regularSeqLe revB)
  have hneg_revA_absB : RegularSeqLe (negSeq revA) (absSeq revB) := by
    exact regularSeqLe_of_left_eventual
      (relEventually_symm _ _ (by
        simpa [ga, revA] using
          (subSeq_comm_neg_eventually
            (regularSeqFinSum re (m + d)) (regularSeqFinSum re m))))
      hga_abs_revB
  simpa [re, revA, revB] using
    regularSeq_abs_le_of_two_sided revA (absSeq revB) hrevA_absB hneg_revA_absB

#print axioms BishopSec1P.regularSeqFinSum_inj_absdiff_auxC

theorem regularSeqFinSum_inj_absdiff_leC {b : Nat → CReal}
    (hb : ∀ n, RegularSeqNonneg (b n)) {e : Nat → Nat}
    (he : ∀ l, e l < e (l + 1)) (m n : Nat) :
    RegularSeqLe
      (absSeq
        (subSeq
          (regularSeqFinSum (fun l => b (e l)) m)
          (regularSeqFinSum (fun l => b (e l)) n)))
      (absSeq
        (subSeq (regularSeqFinSum b (e m)) (regularSeqFinSum b (e n)))) := by
  let re : Nat → CReal := fun l => b (e l)
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
    subst n
    exact regularSeqFinSum_inj_absdiff_auxC hb he m d
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hnm
    subst m
    have haux := regularSeqFinSum_inj_absdiff_auxC hb he n d
    exact regularSeqLe_of_right_eventual
      (absSeq_subSeq_comm_eventually
        (regularSeqFinSum b (e n)) (regularSeqFinSum b (e (n + d))))
      (regularSeqLe_of_left_eventual
        (absSeq_subSeq_comm_eventually
          (regularSeqFinSum re (n + d)) (regularSeqFinSum re n))
        haux)

#print axioms BishopSec1P.regularSeqFinSum_inj_absdiff_leC

/-- Strictly monotone subsequences of nonnegative partial sums are Cauchy. -/
def repIsCauchy_of_injC {b : Nat → CReal} (hb : ∀ n, RegularSeqNonneg (b n))
    {e : Nat → Nat} (he : ∀ l, e l < e (l + 1)) (hege : ∀ l, l ≤ e l)
    (hbc : CRealRepSequenceCauchyData (regularSeqFinSum b)) :
    CRealRepSequenceCauchyData (regularSeqFinSum (fun l => b (e l))) where
  cmod := fun k => hbc.cmod (k + 1)
  close_eventually := by
    intro k m n hm hn
    refine repCloseAtGauge_of_absdiff_le k
      (regularSeqFinSum_inj_absdiff_leC hb he m n) ?_
    exact hbc.close_eventually (k + 1) (e m) (e n)
      (Nat.le_trans hm (hege m)) (Nat.le_trans hn (hege n))

#print axioms BishopSec1P.repIsCauchy_of_injC

/-- Flattened summability of a nonnegative matrix gives summability of each row. -/
def row_seriesSumC {A : Nat → Nat → CReal} (hA : ∀ i j, RegularSeqNonneg (A i j))
    (hflat : RepSeriesSum (fun k => A (BishopC.cellAt k).1 (BishopC.cellAt k).2))
    (m : Nat) : RepSeriesSum (A m) :=
  let he : ∀ l, BishopC.rowIdx m (m + 1 + l) <
      BishopC.rowIdx m (m + 1 + (l + 1)) :=
    fun l => BishopC.rowIdx_lt_succ m (m + 1 + l)
  let hege : ∀ l, l ≤ BishopC.rowIdx m (m + 1 + l) :=
    fun l => Nat.le_trans (by omega) (BishopC.rowIdx_ge m (m + 1 + l))
  let tailFlat : RepSeriesSum
      (fun l => A (BishopC.cellAt (BishopC.rowIdx m (m + 1 + l))).1
        (BishopC.cellAt (BishopC.rowIdx m (m + 1 + l))).2) :=
    repSeriesSum_of_partialCauchy
      (repIsCauchy_of_injC
        (fun k => hA (BishopC.cellAt k).1 (BishopC.cellAt k).2)
        he hege (repIsCauchy_of_tendsto hflat.tends))
  repSeriesSum_of_tailC m
    (repSeriesSum_congr tailFlat
      (fun l => by
        rw [BishopC.cellAt_rowIdx (show m < m + 1 + l by omega)]
        exact relEventually_refl _))

#print axioms BishopSec1P.row_seriesSumC

/-- Lemma 1.10 core: a summable family of integrable representatives can be flattened. -/
def seriesIntegrableC {X : Type*} {S : IntSpaceC X} (F : Nat → IntegrableRepC3 S)
    (hsum : RepSeriesSum (fun m => (F m).abs_integral_sum.sum)) :
    IntegrableRepC3 S :=
  let fn : Nat → BFunC X :=
    fun k => (F (BishopC.cellAt k).1).fn (BishopC.cellAt k).2
  let hmem : ∀ k, fn k ∈ S.L :=
    fun k => (F (BishopC.cellAt k).1).fn_mem (BishopC.cellAt k).2
  let habs : RepSeriesSum (fun k => S.I (BFunC.absf (fn k))) :=
    cellAt_repSeriesSum
      (a := fun i j => S.I (BFunC.absf ((F i).fn j)))
      (fun i j => S.I_absf_nonneg ((F i).fn_mem j))
      (fun i => (F i).abs_integral_sum) hsum
  { fn := fn
    fn_mem := hmem
    abs_integral_sum := habs
    integral_sum :=
      repSeriesSum_of_absMajorant habs
        (fun k => S.I_absf_nonneg (hmem k))
        (fun k => S.I_abs_ge (hmem k)) }

#print axioms BishopSec1P.seriesIntegrableC

theorem seriesIntegrable_domain_subsetC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S)
    (hsum : RepSeriesSum (fun m => (F m).abs_integral_sum.sum)) :
    (seriesIntegrableC F hsum).domain ⊆ {x | ∀ m, x ∈ (F m).domain} := by
  intro x hx m
  rcases hx with ⟨hdom, hconv⟩
  refine ⟨?_, ?_⟩
  · intro n
    obtain ⟨k, hk⟩ := BishopC.cellAt_surj m n
    have hd : x ∈ ((F (BishopC.cellAt k).1).fn (BishopC.cellAt k).2).dom := by
      simpa [seriesIntegrableC] using hdom k
    rw [hk] at hd
    exact hd
  · rcases hconv with ⟨flatSS⟩
    have hflat' :
        RepSeriesSum
          (fun k => CReal.abs
            (((F (BishopC.cellAt k).1).fn (BishopC.cellAt k).2).toFun x)) := by
      simpa [seriesIntegrableC] using flatSS
    refine ⟨row_seriesSumC
      (A := fun i j => CReal.abs (((F i).fn j).toFun x)) ?_ hflat' m⟩
    intro i j
    exact regularSeqNonneg_of_zero_le
      (by simpa [CReal.abs] using
        absSeq_nonnegative_regularSeqLe (((F i).fn j).toFun x))

#print axioms BishopSec1P.seriesIntegrable_domain_subsetC

theorem lemma_1_10C {X : Type*} {S : IntSpaceC X} (F : Nat → IntegrableRepC3 S) :
    ∃ G : IntegrableRepC3 S, G.domain ⊆ {x | ∀ m, x ∈ (F m).domain} := by
  let H : Nat → IntegrableRepC3 S :=
    fun m => IntegrableRepC3.smul (halfPow (m + (F m).scaleFactor)) (F m)
  have hsum' : RepSeriesSum (fun m => (H m).abs_integral_sum.sum) := by
    refine repSeriesSum_of_le_halfPow ?_ ?_
    · intro m
      exact repSeriesSum_nonneg
        (fun n => S.I_absf_nonneg ((H m).fn_mem n))
        (H m).abs_integral_sum
    · intro m
      simpa [H] using (F m).scaleFactor_spec m
  refine ⟨seriesIntegrableC H hsum', ?_⟩
  intro x hx m
  exact (IntegrableRepC3.smul_halfPow_domain_subset (F m)
    (m + (F m).scaleFactor)) (seriesIntegrable_domain_subsetC H hsum' hx m)

#print axioms BishopSec1P.lemma_1_10C

theorem lemma_1_10_fullC {X : Type*} {S : IntSpaceC X} {A : Set X}
    (hA : IsFullC S A) :
    ∃ G : IntegrableRepC3 S, G.domain ⊆ A := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨G, hG⟩ := lemma_1_10C F
  exact ⟨G, fun _ hx => hF (hG hx)⟩

#print axioms BishopSec1P.lemma_1_10_fullC

/-! ### Stage 8: a.e.-respect gateway toward normL1/DCT -/

/-- Interleave abs convergence gives abs convergence of the even component. -/
def repSeriesSum_even_of_interleave_absC {u v : Nat → CReal}
    (h : RepSeriesSum (fun n => absSeq (bc1_seqMerge u v n))) :
    RepSeriesSum (fun k => absSeq (u k)) :=
  repSeriesSum_congr
    (repSeriesSum_of_partialCauchy
      (repIsCauchy_of_injC
        (fun n => regularSeqNonneg_of_zero_le
          (absSeq_nonnegative_regularSeqLe (bc1_seqMerge u v n)))
        (e := fun k => 2 * k)
        (fun l => by change 2 * l < 2 * (l + 1); omega)
        (fun l => by change l ≤ 2 * l; omega)
        (repIsCauchy_of_tendsto h.tends)))
    (fun k => by
      rw [bc1_seqMerge_even]
      exact relEventually_refl _)

#print axioms BishopSec1P.repSeriesSum_even_of_interleave_absC

/-- Interleave abs convergence gives abs convergence of the odd component. -/
def repSeriesSum_odd_of_interleave_absC {u v : Nat → CReal}
    (h : RepSeriesSum (fun n => absSeq (bc1_seqMerge u v n))) :
    RepSeriesSum (fun k => absSeq (v k)) :=
  repSeriesSum_congr
    (repSeriesSum_of_partialCauchy
      (repIsCauchy_of_injC
        (fun n => regularSeqNonneg_of_zero_le
          (absSeq_nonnegative_regularSeqLe (bc1_seqMerge u v n)))
        (e := fun k => 2 * k + 1)
        (fun l => by change 2 * l + 1 < 2 * (l + 1) + 1; omega)
        (fun l => by change l ≤ 2 * l + 1; omega)
        (repIsCauchy_of_tendsto h.tends)))
    (fun k => by
      rw [bc1_seqMerge_odd]
      exact relEventually_refl _)

#print axioms BishopSec1P.repSeriesSum_odd_of_interleave_absC

/-- Abs convergence of `r.add r'` gives abs convergence of the left summand. -/
def add_absSeriesSum_leftC {X : Type*} {S : IntSpaceC X}
    {r r' : IntegrableRepC3 S} {x : X}
    (habs : RepSeriesSum (fun n => absSeq (((r.add r').fn n).toFun x))) :
    RepSeriesSum (fun k => absSeq ((r.fn k).toFun x)) :=
  repSeriesSum_even_of_interleave_absC
    (repSeriesSum_congr habs
      (fun n => by
        have hmap :
            ((r.add r').fn n).toFun x =
              bc1_seqMerge (fun k => (r.fn k).toFun x)
                (fun k => (r'.fn k).toFun x) n := by
          simpa [IntegrableRepC3.add] using
            (bc1_seqMerge_map (fun f : BFunC X => f.toFun x) r.fn r'.fn n)
        rw [hmap]
        exact relEventually_refl _))

#print axioms BishopSec1P.add_absSeriesSum_leftC

/-- Abs convergence of `r.add r'` gives abs convergence of the right summand. -/
def add_absSeriesSum_rightC {X : Type*} {S : IntSpaceC X}
    {r r' : IntegrableRepC3 S} {x : X}
    (habs : RepSeriesSum (fun n => absSeq (((r.add r').fn n).toFun x))) :
    RepSeriesSum (fun k => absSeq ((r'.fn k).toFun x)) :=
  repSeriesSum_odd_of_interleave_absC
    (repSeriesSum_congr habs
      (fun n => by
        have hmap :
            ((r.add r').fn n).toFun x =
              bc1_seqMerge (fun k => (r.fn k).toFun x)
                (fun k => (r'.fn k).toFun x) n := by
          simpa [IntegrableRepC3.add] using
            (bc1_seqMerge_map (fun f : BFunC X => f.toFun x) r.fn r'.fn n)
        rw [hmap]
        exact relEventually_refl _))

#print axioms BishopSec1P.add_absSeriesSum_rightC

/-- Abs convergence of `r.neg` gives abs convergence of `r`. -/
def neg_absSeriesSumC {X : Type*} {S : IntSpaceC X}
    {r : IntegrableRepC3 S} {x : X}
    (habs : RepSeriesSum (fun n => absSeq (((r.neg).fn n).toFun x))) :
    RepSeriesSum (fun k => absSeq ((r.fn k).toFun x)) :=
  repSeriesSum_congr habs
    (fun n => by
      have hneg :
          ((r.neg).fn n).toFun x ≈ negSeq ((r.fn n).toFun x) := by
        simpa [IntegrableRepC3.neg, BFunC.smul] using
          neg_one_mul_equiv ((r.fn n).toFun x)
      have habs_neg :
          relEventually (absSeq (((r.neg).fn n).toFun x))
            (absSeq (negSeq ((r.fn n).toFun x))) :=
        absSeq_respects_eventually _ _ hneg
      have habs_self :
          relEventually (absSeq (negSeq ((r.fn n).toFun x)))
            (absSeq ((r.fn n).toFun x)) :=
        absSeq_negSeq_eventually ((r.fn n).toFun x)
      exact relEventually_symm _ _
        (relEventually_trans _ _ _ habs_neg habs_self))

#print axioms BishopSec1P.neg_absSeriesSumC

/-- Domain membership for `r.add r'` gives domain membership for the left summand. -/
theorem add_dom_leftC {X : Type*} {S : IntSpaceC X}
    {r r' : IntegrableRepC3 S} {x : X}
    (hd : ∀ n, x ∈ ((r.add r').fn n).dom) (k : Nat) :
    x ∈ (r.fn k).dom := by
  have hk := hd (2 * k)
  rwa [show (r.add r').fn (2 * k) = r.fn k by
    simpa [IntegrableRepC3.add] using bc1_seqMerge_even r.fn r'.fn k] at hk

#print axioms BishopSec1P.add_dom_leftC

/-- Domain membership for `r.add r'` gives domain membership for the right summand. -/
theorem add_dom_rightC {X : Type*} {S : IntSpaceC X}
    {r r' : IntegrableRepC3 S} {x : X}
    (hd : ∀ n, x ∈ ((r.add r').fn n).dom) (k : Nat) :
    x ∈ (r'.fn k).dom := by
  have hk := hd (2 * k + 1)
  rwa [show (r.add r').fn (2 * k + 1) = r'.fn k by
    simpa [IntegrableRepC3.add] using bc1_seqMerge_odd r.fn r'.fn k] at hk

#print axioms BishopSec1P.add_dom_rightC

/-- Absolute convergence gives signed convergence. -/
def seriesSum_of_absC {u : Nat → CReal}
    (h : RepSeriesSum (fun k => absSeq (u k))) : RepSeriesSum u :=
  repSeriesSum_of_absMajorant h
    (fun n => regularSeqNonneg_of_zero_le (absSeq_nonnegative_regularSeqLe (u n)))
    (fun n => regularSeqLe_refl (absSeq (u n)))

#print axioms BishopSec1P.seriesSum_of_absC

/-- Full sets are closed under binary intersection. -/
theorem isFull_interC {X : Type*} {S : IntSpaceC X} {A B : Set X}
    (hA : IsFullC S A) (hB : IsFullC S B) : IsFullC S (A ∩ B) := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨G, hG⟩ := hB
  exact ⟨bc1_seqMerge F G, fun _ hx =>
    ⟨hF (fun k => by
      have h := hx (2 * k)
      rwa [bc1_seqMerge_even] at h),
     hG (fun k => by
      have h := hx (2 * k + 1)
      rwa [bc1_seqMerge_odd] at h)⟩⟩

#print axioms BishopSec1P.isFull_interC

/-- Proposition 1.11, presented-real version: a.e. pointwise monotonicity implies
monotonicity of the integral. -/
theorem prop_1_11C {X : Type*} {S : IntSpaceC X} {A : Set X}
    (hA : IsFullC S A) (r r' : IntegrableRepC3 S)
    (hle : ∀ x ∈ A,
      ∀ (hr : RepSeriesSum (fun n => (r.fn n).toFun x))
        (hr' : RepSeriesSum (fun n => (r'.fn n).toFun x)),
        RegularSeqLe hr.sum hr'.sum) :
    RegularSeqLe r.integral r'.integral := by
  obtain ⟨h, hhA⟩ := lemma_1_10_fullC hA
  let K : IntegrableRepC3 S := (r'.sub r).add (h.sub h)
  have hKnn : RegularSeqNonneg K.integral := by
    change RegularSeqNonneg K.integral_sum.sum
    refine IntSpaceC.lemma_1_7C S K.fn_mem K.abs_integral_sum ?_ K.integral_sum
    intro x hdomK habsK hKx
    have hleftAbs :
        RepSeriesSum (fun k => absSeq (((r'.sub r).fn k).toFun x)) :=
      add_absSeriesSum_leftC (r := r'.sub r) (r' := h.sub h) (x := x) habsK
    have hrightAbs :
        RepSeriesSum (fun k => absSeq (((h.sub h).fn k).toFun x)) :=
      add_absSeriesSum_rightC (r := r'.sub r) (r' := h.sub h) (x := x) habsK
    have hhabs : RepSeriesSum (fun k => absSeq ((h.fn k).toFun x)) :=
      add_absSeriesSum_leftC (r := h) (r' := h.neg) (x := x) hrightAbs
    have hhdom : ∀ n, x ∈ (h.fn n).dom :=
      add_dom_leftC (r := h) (r' := h.neg) (x := x)
        (add_dom_rightC (r := r'.sub r) (r' := h.sub h) (x := x) hdomK)
    have hxA : x ∈ A := hhA ⟨hhdom, ⟨hhabs⟩⟩
    have hr'abs : RepSeriesSum (fun n => absSeq ((r'.fn n).toFun x)) :=
      add_absSeriesSum_leftC (r := r') (r' := r.neg) (x := x) hleftAbs
    have hrnegAbs : RepSeriesSum (fun n => absSeq (((r.neg).fn n).toFun x)) :=
      add_absSeriesSum_rightC (r := r') (r' := r.neg) (x := x) hleftAbs
    have hrabs : RepSeriesSum (fun n => absSeq ((r.fn n).toFun x)) :=
      neg_absSeriesSumC (r := r) (x := x) hrnegAbs
    have hr'v : RepSeriesSum (fun n => (r'.fn n).toFun x) :=
      seriesSum_of_absC hr'abs
    have hrv : RepSeriesSum (fun n => (r.fn n).toFun x) :=
      seriesSum_of_absC hrabs
    have hhv : RepSeriesSum (fun n => (h.fn n).toFun x) :=
      seriesSum_of_absC hhabs
    let hleftv : RepSeriesSum (fun n => ((r'.sub r).fn n).toFun x) :=
      sub_seriesSum_valueC3 (r := r') (r' := r) (x := x) hr'v hrv
    let hrightv : RepSeriesSum (fun n => ((h.sub h).fn n).toFun x) :=
      sub_seriesSum_valueC3 (r := h) (r' := h) (x := x) hhv hhv
    let hmodel : RepSeriesSum (fun n => (K.fn n).toFun x) := by
      dsimp [K]
      exact add_seriesSum_valueC3
        (r := r'.sub r) (r' := h.sub h) (x := x) hleftv hrightv
    have huniq : relEventually hKx.sum hmodel.sum :=
      repSeriesSum_unique hKx hmodel
    have hpoint :
        relEventually hKx.sum (subSeq hr'v.sum hrv.sum) := by
      calc
        hKx.sum ≈ hmodel.sum := huniq
        _ ≈ addSeq (addSeq hr'v.sum (negSeq hrv.sum))
              (addSeq hhv.sum (negSeq hhv.sum)) := by
            change relEventually
              (addSeq (addSeq hr'v.sum (negSeq hrv.sum))
                (addSeq hhv.sum (negSeq hhv.sum)))
              (addSeq (addSeq hr'v.sum (negSeq hrv.sum))
                (addSeq hhv.sum (negSeq hhv.sum)))
            exact relEventually_refl _
        _ ≈ addSeq (addSeq hr'v.sum (negSeq hrv.sum)) zeroSeq :=
            add_congr (Setoid.refl _) (add_right_neg_equiv hhv.sum)
        _ ≈ addSeq hr'v.sum (negSeq hrv.sum) :=
            CReal.add_zero (addSeq hr'v.sum (negSeq hrv.sum))
        _ ≈ subSeq hr'v.sum hrv.sum :=
            add_sub_right_equiv hr'v.sum hrv.sum
    have hle_point : RegularSeqLe hrv.sum hr'v.sum := hle x hxA hrv hr'v
    change RegularSeqNonneg hKx.sum
    exact regularSeqNonneg_of_eventual hpoint hle_point
  have hK_integral :
      relEventually K.integral (subSeq r'.integral r.integral) := by
    dsimp [K]
    rw [IntegrableRepC3.integral_add, IntegrableRepC3.integral_sub,
      IntegrableRepC3.integral_sub]
    calc
      addSeq (addSeq r'.integral (negSeq r.integral))
          (addSeq h.integral (negSeq h.integral))
          ≈ addSeq (addSeq r'.integral (negSeq r.integral)) zeroSeq :=
            add_congr (Setoid.refl _) (add_right_neg_equiv h.integral)
      _ ≈ addSeq r'.integral (negSeq r.integral) :=
            CReal.add_zero (addSeq r'.integral (negSeq r.integral))
      _ ≈ subSeq r'.integral r.integral :=
            add_sub_right_equiv r'.integral r.integral
  change RegularSeqNonneg (subSeq r'.integral r.integral)
  exact regularSeqNonneg_of_eventual
    (relEventually_symm _ _ hK_integral) hKnn

#print axioms BishopSec1P.prop_1_11C

/-- Monotonicity of the `L1` seminorm from pointwise absolute-value
monotonicity on a full set. -/
theorem IntegrableRepC3.normL1_monoC {X : Type*} {S : IntSpaceC X}
    {A : Set X} (hA : IsFullC S A) (u v : IntegrableRepC3 S)
    (hle : ∀ x ∈ A,
      ∀ (hu : RepSeriesSum (fun n => (u.fn n).toFun x))
        (hv : RepSeriesSum (fun n => (v.fn n).toFun x)),
        RegularSeqLe (absSeq hu.sum) (absSeq hv.sum)) :
    RegularSeqLe u.normL1 v.normL1 := by
  show RegularSeqLe u.absVal.integral v.absVal.integral
  refine prop_1_11C
    (isFull_interC (isFull_interC hA u.domain_isFull) v.domain_isFull)
    u.absVal v.absVal ?_
  intro x hx hr hr'
  obtain ⟨⟨hxA, hxu⟩, hxv⟩ := hx
  obtain ⟨_, ⟨huabs⟩⟩ := hxu
  obtain ⟨_, ⟨hvabs⟩⟩ := hxv
  have hu : RepSeriesSum (fun n => (u.fn n).toFun x) :=
    seriesSum_of_absC huabs
  have hv : RepSeriesSum (fun n => (v.fn n).toFun x) :=
    seriesSum_of_absC hvabs
  obtain ⟨hsu, hsueq⟩ := u.absVal_signed_value x hu
  obtain ⟨hsv, hsveq⟩ := v.absVal_signed_value x hv
  have hueq : relEventually hr.sum (absSeq hu.sum) :=
    relEventually_trans _ _ _
      (repSeriesSum_unique hr hsu) hsueq
  have hveq : relEventually hr'.sum (absSeq hv.sum) :=
    relEventually_trans _ _ _
      (repSeriesSum_unique hr' hsv) hsveq
  exact regularSeqLe_of_right_eventual
    (relEventually_symm _ _ hveq)
    (regularSeqLe_of_left_eventual hueq (hle x hxA hu hv))

#print axioms BishopSec1P.IntegrableRepC3.normL1_monoC

/-! ### Stage 10a: normL1 analytic infrastructure -/

theorem Le_of_tendstoHalf_leC {u v : Nat → CReal} {a b : CReal}
    (hu : RepSeriesTendsto u a) (hv : RepSeriesTendsto v b)
    (hle : ∀ n, RegularSeqLe (u n) (v n)) : RegularSeqLe a b := by
  intro hcounter
  have hpos_order : regularSeqLtProp b a :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hpos_sub : CReal.ltE CReal.zero (subSeq a b) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  obtain ⟨k, hk⟩ := CReal.archimedean_E (subSeq a b) hpos_sub
  let N : Nat := Nat.max (hu.mod (k + 1)) (hv.mod (k + 1))
  have hNu : hu.mod (k + 1) ≤ N := by
    dsimp [N]
    exact Nat.le_max_left _ _
  have hNv : hv.mod (k + 1) ≤ N := by
    dsimp [N]
    exact Nat.le_max_right _ _
  have hcu : RepCloseAtGauge ((k + 1) + 1) (u N) a :=
    hu.close (k + 1) N hNu
  have hcv : RepCloseAtGauge ((k + 1) + 1) (v N) b :=
    hv.close (k + 1) N hNv
  have hgap_u :
      regularSeqLtProp (subSeq a (u N)) (halfPow (k + 1)) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ (k + 1) hcu
  have hgap_v :
      regularSeqLtProp (subSeq (v N) b) (halfPow (k + 1)) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ (k + 1)
        (repCloseAtGauge_symm hcv)
  have hmiddle_le_zero :
      RegularSeqLe (subSeq (u N) (v N)) zeroSeq := by
    have hto_self :
        RegularSeqLe (subSeq (u N) (v N)) (subSeq (u N) (u N)) :=
      regularSeqLe_subSeq_right (u N) (hle N)
    exact regularSeqLe_of_right_eventual
      (subSeq_self_eventually_law (u N)) hto_self
  have hsum_full :
      relEventually
        (addSeq (addSeq (subSeq a (u N)) (subSeq (u N) (v N)))
          (subSeq (v N) b))
        (subSeq a b) := by
    have hleft :
        relEventually
          (addSeq (subSeq a (u N)) (subSeq (u N) (v N)))
          (subSeq a (v N)) :=
      subSeq_add_sub_cancel_eventually a (u N) (v N)
    have hcong :
        relEventually
          (addSeq
            (addSeq (subSeq a (u N)) (subSeq (u N) (v N)))
            (subSeq (v N) b))
          (addSeq (subSeq a (v N)) (subSeq (v N) b)) :=
      addSeq_respects_eventually _ _ _ _ hleft (relEventually_refl _)
    exact relEventually_trans _ _ _ hcong
      (subSeq_add_sub_cancel_eventually a (v N) b)
  have hdrop_middle :
      RegularSeqLe
        (addSeq (addSeq (subSeq a (u N)) (subSeq (u N) (v N)))
          (subSeq (v N) b))
        (addSeq (addSeq (subSeq a (u N)) zeroSeq)
          (subSeq (v N) b)) := by
    exact regularSeqLe_add
      (regularSeqLe_add (regularSeqLe_refl _) hmiddle_le_zero)
      (regularSeqLe_refl _)
  have hdrop_middle' :
      RegularSeqLe
        (subSeq a b)
        (addSeq (addSeq (subSeq a (u N)) zeroSeq)
          (subSeq (v N) b)) :=
    regularSeqLe_of_left_eventual
      (relEventually_symm _ _ hsum_full) hdrop_middle
  have hupper_zero :
      relEventually
        (addSeq (addSeq (subSeq a (u N)) zeroSeq)
          (subSeq (v N) b))
        (addSeq (subSeq a (u N)) (subSeq (v N) b)) := by
    exact addSeq_respects_eventually _ _ _ _
      (addSeq_zero_right_eventually (subSeq a (u N)))
      (relEventually_refl _)
  have hgap_le_sum :
      RegularSeqLe (subSeq a b)
        (addSeq (subSeq a (u N)) (subSeq (v N) b)) :=
    regularSeqLe_of_right_eventual hupper_zero hdrop_middle'
  have hsum_lt :
      regularSeqLtProp
        (addSeq (subSeq a (u N)) (subSeq (v N) b))
        (halfPow k) := by
    have hadd :
        regularSeqLtProp
          (addSeq (subSeq a (u N)) (subSeq (v N) b))
          (addSeq (halfPow (k + 1)) (halfPow (k + 1))) :=
      regularSeqLtProp_add hgap_u hgap_v
    exact regularSeqLtProp_of_right_eventual
      (halfPow_succ_add_self k) hadd
  have hgap_lt_half :
      regularSeqLtProp (subSeq a b) (halfPow k) :=
    regularSeqLtProp_of_le_of_lt hgap_le_sum hsum_lt
  have hhalf_lt_gap :
      regularSeqLtProp (halfPow k) (subSeq a b) := by
    simpa [halfPow, CReal.epsSeq] using hk
  exact regularSeqLtProp_irrefl (halfPow k)
    (regularSeqLtProp_trans _ _ _ hhalf_lt_gap hgap_lt_half)

#print axioms BishopSec1P.Le_of_tendstoHalf_leC

def IntegrableRepC3.integral_tendstoC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RepSeriesTendsto (fun N => S.I (BFunC.seqSum r.fn N)) r.integral :=
  bc1_repSeriesTendsto_congr r.integral_sum.tends
    (fun N => S.I_seqSum r.fn_mem N)

#print axioms BishopSec1P.IntegrableRepC3.integral_tendstoC

def repTendsto_absC {u : Nat → CReal} {l : CReal}
    (h : RepSeriesTendsto u l) :
    RepSeriesTendsto (fun n => CReal.abs (u n)) (CReal.abs l) := by
  simpa [CReal.abs] using IntegrableRepC3.repTendsto_abs h

#print axioms BishopSec1P.repTendsto_absC

def repSeriesTendsto_limit_congr {u : Nat → CReal} {l l' : CReal}
    (h : RepSeriesTendsto u l) (heq : relEventually l l') :
    RepSeriesTendsto u l' where
  mod := fun k => h.mod (k + 1)
  close := by
    intro k n hn
    have hul : RepCloseAtGauge (k + 2) (u n) l :=
      h.close (k + 1) n hn
    have hll' : RepCloseAtGauge (k + 2) l l' :=
      bc1_repClose_of_relEventually heq (k + 2)
    exact repCloseAtGauge_triangle_succ (k + 1) hul hll'

#print axioms BishopSec1P.repSeriesTendsto_limit_congr

def IntegrableRepC3.normL1_tendstoC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RepSeriesTendsto
      (fun N => S.I (BFunC.absf (BFunC.seqSum r.fn N))) r.normL1 := by
  let hseq :
      RepSeriesTendsto
        (fun N => S.I (BFunC.absf (BFunC.seqSum r.fn N)))
        r.seriesSum_absDiffFn_I.sum :=
    bc1_repSeriesTendsto_congr r.seriesSum_absDiffFn_I.tends
      (fun N => relEventually_symm _ _ (r.partialSum_absDiffFn_I N))
  exact repSeriesTendsto_limit_congr hseq
    (relEventually_symm _ _
      (by
        simpa [IntegrableRepC3.normL1] using r.absVal_integral_eq))

#print axioms BishopSec1P.IntegrableRepC3.normL1_tendstoC

theorem IntegrableRepC3.abs_integral_le_normL1C {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RegularSeqLe (CReal.abs r.integral) r.normL1 :=
  Le_of_tendstoHalf_leC (repTendsto_absC r.integral_tendstoC)
    r.normL1_tendstoC
    (fun N => S.I_abs_ge (S.seqSum_mem r.fn_mem N))

#print axioms BishopSec1P.IntegrableRepC3.abs_integral_le_normL1C

theorem IntegrableRepC3.normL1_nonnegC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : RegularSeqNonneg r.normL1 := by
  exact regularSeqNonneg_of_zero_le
    (regularSeqLe_trans
      (by
        simpa [CReal.abs] using
          absSeq_nonnegative_regularSeqLe r.integral)
      r.abs_integral_le_normL1C)

#print axioms BishopSec1P.IntegrableRepC3.normL1_nonnegC

theorem seqSum_absf_dom_eqC {X : Type*} {S : IntSpaceC X}
    {r : IntegrableRepC3 S} (N : Nat) :
    (BFunC.seqSum r.fn N).dom =
      (BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N).dom := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show (BFunC.seqSum r.fn N).dom ∩ (r.fn (N + 1)).dom =
        (BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N).dom ∩
          (r.fn (N + 1)).dom
      rw [ih]

#print axioms BishopSec1P.seqSum_absf_dom_eqC

theorem abs_seqSum_leC {X : Type*} {S : IntSpaceC X}
    {r : IntegrableRepC3 S} (x : X) (N : Nat) :
    RegularSeqLe (CReal.abs ((BFunC.seqSum r.fn N).toFun x))
      ((BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N).toFun x) := by
  induction N with
  | zero =>
      exact regularSeqLe_refl _
  | succ N ih =>
      change RegularSeqLe
        (CReal.abs
          (CReal.add ((BFunC.seqSum r.fn N).toFun x)
            ((r.fn (N + 1)).toFun x)))
        (CReal.add
          ((BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N).toFun x)
          (CReal.abs ((r.fn (N + 1)).toFun x)))
      have htri :
          RegularSeqLe
            (CReal.abs
              (CReal.add ((BFunC.seqSum r.fn N).toFun x)
                ((r.fn (N + 1)).toFun x)))
            (CReal.add (CReal.abs ((BFunC.seqSum r.fn N).toFun x))
              (CReal.abs ((r.fn (N + 1)).toFun x))) := by
        simpa [CReal.abs] using
          regularSeqLe_abs_add ((BFunC.seqSum r.fn N).toFun x)
            ((r.fn (N + 1)).toFun x)
      have hmono :
          RegularSeqLe
            (CReal.add (CReal.abs ((BFunC.seqSum r.fn N).toFun x))
              (CReal.abs ((r.fn (N + 1)).toFun x)))
            (CReal.add
              ((BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N).toFun x)
              (CReal.abs ((r.fn (N + 1)).toFun x))) :=
        regularSeqLe_add ih (regularSeqLe_refl _)
      exact regularSeqLe_trans htri hmono

#print axioms BishopSec1P.abs_seqSum_leC

theorem IntegrableRepC3.absSeqSum_pointwiseLEC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (N : Nat) :
    BFunC.PointwiseLE (BFunC.absf (BFunC.seqSum r.fn N))
      (BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N) where
  dom_eq := seqSum_absf_dom_eqC N
  le_val := fun x _ => abs_seqSum_leC x N

#print axioms BishopSec1P.IntegrableRepC3.absSeqSum_pointwiseLEC

def repSeriesTendsto_constC (c : CReal) :
    RepSeriesTendsto (fun _ : Nat => c) c where
  mod := fun _ => 0
  close := by
    intro k _n _hn
    exact bc1_repClose_of_relEventually (relEventually_refl c) (k + 1)

#print axioms BishopSec1P.repSeriesTendsto_constC

theorem IntegrableRepC3.normL1_le_absConvC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RegularSeqLe r.normL1 r.abs_integral_sum.sum := by
  refine Le_of_tendstoHalf_leC r.normL1_tendstoC
    (repSeriesTendsto_constC r.abs_integral_sum.sum) ?_
  intro N
  have hI_mono :
      RegularSeqLe
        (S.I (BFunC.absf (BFunC.seqSum r.fn N)))
        (S.I (BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N)) :=
    S.I_mono
      (S.abs_mem (S.seqSum_mem r.fn_mem N))
      (S.seqSum_mem (fun k => S.abs_mem (r.fn_mem k)) N)
      (r.absSeqSum_pointwiseLEC N)
  have hpart :
      RegularSeqLe
        (regularSeqFinSum (fun k => S.I (BFunC.absf (r.fn k))) N)
        r.abs_integral_sum.sum :=
    repPartialSum_le_sum
      (fun k => S.I_absf_nonneg (r.fn_mem k))
      r.abs_integral_sum N
  have hseq :
      relEventually
        (S.I (BFunC.seqSum (fun k => BFunC.absf (r.fn k)) N))
        (regularSeqFinSum (fun k => S.I (BFunC.absf (r.fn k))) N) :=
    S.I_seqSum (fun k => S.abs_mem (r.fn_mem k)) N
  exact regularSeqLe_trans hI_mono
    (regularSeqLe_of_left_eventual hseq hpart)

#print axioms BishopSec1P.IntegrableRepC3.normL1_le_absConvC

theorem regularSeqFinSum_tail_sub_eventuallyC (u : Nat → CReal) (p d : Nat) :
    relEventually
      (regularSeqFinSum (fun j => u (p + 1 + j)) d)
      (subSeq (regularSeqFinSum u (p + (d + 1))) (regularSeqFinSum u p)) := by
  let shift : Nat → CReal := fun j => u (p + 1 + j)
  have hgap :
      relEventually
        (subSeq (regularSeqFinSum u (p + (d + 1))) (regularSeqFinSum u p))
        (regularSeqFinSum shift d) := by
    have hsplit := regularSeqFinSum_split_eventually u p d
    have hsub :
        relEventually
          (subSeq (regularSeqFinSum u (p + (d + 1))) (regularSeqFinSum u p))
          (subSeq
            (addSeq (regularSeqFinSum u p) (regularSeqFinSum shift d))
            (regularSeqFinSum u p)) :=
      subSeq_respects_eventually _ _ _ _ hsplit
        (relEventually_refl (regularSeqFinSum u p))
    exact relEventually_trans _ _ _ hsub
      (subSeq_add_left_cancel_eventually (regularSeqFinSum u p)
        (regularSeqFinSum shift d))
  exact relEventually_symm _ _ (by simpa [shift] using hgap)

#print axioms BishopSec1P.regularSeqFinSum_tail_sub_eventuallyC

def seriesSum_tailC {u : Nat → CReal} (h : RepSeriesSum u) (p : Nat) :
    RepSeriesSum (fun l => u (p + 1 + l)) where
  sum := subSeq h.sum (regularSeqFinSum u p)
  tends :=
    { mod := fun k => h.tends.mod (k + 3)
      close := by
        intro k M hM
        let head : CReal := regularSeqFinSum u p
        let full : CReal := regularSeqFinSum u (p + (M + 1))
        let tail : CReal := regularSeqFinSum (fun l => u (p + 1 + l)) M
        have hidx : h.tends.mod (k + 3) ≤ p + (M + 1) := by omega
        have hfull : RepCloseAtGauge ((k + 3) + 1) full h.sum := by
          simpa [full] using h.tends.close (k + 3) (p + (M + 1)) hidx
        have hneg_head : RepCloseAtGauge ((k + 3) + 1)
            (negSeq head) (negSeq head) :=
          bc1_repClose_of_relEventually (relEventually_refl _) ((k + 3) + 1)
        have hadd : RepCloseAtGauge (k + 3)
            (addSeq full (negSeq head)) (addSeq h.sum (negSeq head)) :=
          bc1_repCloseAtGauge_add (k + 3) hfull hneg_head
        have htail_sub : RepCloseAtGauge ((k + 3) + 1)
            tail (subSeq full head) :=
          bc1_repClose_of_relEventually
            (by
              simpa [tail, full, head] using
                regularSeqFinSum_tail_sub_eventuallyC u p M)
            ((k + 3) + 1)
        have hsub_add : RepCloseAtGauge ((k + 3) + 1)
            (subSeq full head) (addSeq full (negSeq head)) :=
          bc1_repClose_of_relEventually
            (subSeq_eq_add_neg_eventually full head) ((k + 3) + 1)
        have hpre : RepCloseAtGauge (k + 3)
            tail (addSeq full (negSeq head)) :=
          repCloseAtGauge_triangle_succ (k + 3) htail_sub hsub_add
        have hmid : RepCloseAtGauge (k + 2)
            tail (addSeq h.sum (negSeq head)) :=
          repCloseAtGauge_triangle_succ (k + 2) hpre hadd
        have hright : RepCloseAtGauge ((k + 1) + 1)
            (addSeq h.sum (negSeq head)) (subSeq h.sum head) :=
          bc1_repClose_of_relEventually
            (relEventually_symm _ _ (subSeq_eq_add_neg_eventually h.sum head))
            ((k + 1) + 1)
        exact repCloseAtGauge_triangle_succ (k + 1) hmid hright }

#print axioms BishopSec1P.seriesSum_tailC

def IntegrableRepC3.tailFrom {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (p : Nat) : IntegrableRepC3 S where
  fn := fun k => r.fn (p + 1 + k)
  fn_mem := fun k => r.fn_mem (p + 1 + k)
  abs_integral_sum := seriesSum_tailC r.abs_integral_sum p
  integral_sum := seriesSum_tailC r.integral_sum p

#print axioms BishopSec1P.IntegrableRepC3.tailFrom

theorem repCloseAtGauge_zero_of_nonneg_le_ltC {x y : CReal} {k : Nat}
    (hx : RegularSeqNonneg x)
    (hle : RegularSeqLe x y)
    (hy : regularSeqLtProp y (halfPow k)) :
    RepCloseAtGauge k x CReal.zero := by
  have h0x : RegularSeqLe zeroSeq x := regularSeqLe_zero_of_nonneg hx
  have habs_x : RegularSeqLe (absSeq (subSeq x zeroSeq)) x :=
    regularSeqLe_of_left_eventual
      (absSeq_respects_eventually (subSeq x zeroSeq) x
        (subSeq_zero_right_eventually x))
      (regularSeqLe_abs_of_nonneg h0x)
  have hlt_abs : regularSeqLtProp (absSeq (subSeq x zeroSeq)) (halfPow k) :=
    regularSeqLtProp_of_le_of_lt (regularSeqLe_trans habs_x hle) hy
  simpa [halfPow, CReal.epsSeq] using
    repCloseAtGauge_of_absGap x CReal.zero k hlt_abs

#print axioms BishopSec1P.repCloseAtGauge_zero_of_nonneg_le_ltC

def lemma_1_15C {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RepSeriesTendsto (fun p => (r.tailFrom p).normL1) CReal.zero where
  mod := fun k => r.abs_integral_sum.tends.mod (k + 1)
  close := by
    intro k p hp
    have hclose_abs :
        RepCloseAtGauge ((k + 1) + 1)
          (regularSeqFinSum (fun n => S.I (BFunC.absf (r.fn n))) p)
          r.abs_integral_sum.sum :=
      r.abs_integral_sum.tends.close (k + 1) p hp
    have htail_lt :
        regularSeqLtProp
          (subSeq r.abs_integral_sum.sum
            (regularSeqFinSum (fun n => S.I (BFunC.absf (r.fn n))) p))
          (halfPow (k + 1)) := by
      simpa [halfPow, CReal.epsSeq] using
        regularSeqLtProp_sub_of_repClose_succ (k + 1) hclose_abs
    have hnorm_le :
        RegularSeqLe (r.tailFrom p).normL1
          (subSeq r.abs_integral_sum.sum
            (regularSeqFinSum (fun n => S.I (BFunC.absf (r.fn n))) p)) := by
      simpa [IntegrableRepC3.tailFrom, seriesSum_tailC] using
        (r.tailFrom p).normL1_le_absConvC
    exact repCloseAtGauge_zero_of_nonneg_le_ltC
      (IntegrableRepC3.normL1_nonnegC (r.tailFrom p)) hnorm_le htail_lt

#print axioms BishopSec1P.lemma_1_15C

theorem IntegrableRepC3.tailFrom_normL1_ltC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (k : Nat) :
    regularSeqLtProp
      ((r.tailFrom (r.abs_integral_sum.tends.mod k)).normL1)
      (halfPow k) := by
  let p : Nat := r.abs_integral_sum.tends.mod k
  have hclose_abs :
      RepCloseAtGauge (k + 1)
        (regularSeqFinSum (fun n => S.I (BFunC.absf (r.fn n))) p)
        r.abs_integral_sum.sum :=
    r.abs_integral_sum.tends.close k p (Nat.le_refl _)
  have htail_lt :
      regularSeqLtProp
        (subSeq r.abs_integral_sum.sum
          (regularSeqFinSum (fun n => S.I (BFunC.absf (r.fn n))) p))
        (halfPow k) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ k hclose_abs
  have hnorm_le :
      RegularSeqLe (r.tailFrom p).normL1
        (subSeq r.abs_integral_sum.sum
          (regularSeqFinSum (fun n => S.I (BFunC.absf (r.fn n))) p)) := by
    simpa [p, IntegrableRepC3.tailFrom, seriesSum_tailC] using
      (r.tailFrom p).normL1_le_absConvC
  exact regularSeqLtProp_of_le_of_lt hnorm_le htail_lt

#print axioms BishopSec1P.IntegrableRepC3.tailFrom_normL1_ltC

theorem regularSeqLe_of_ltPropC {x y : CReal}
    (hxy : regularSeqLtProp x y) : RegularSeqLe x y := by
  apply regularSeqLe_of_not_ltQuot
  intro hyx
  have hyx' : regularSeqLtProp y x := by
    change PosEventually (subSeq x y) at hyx
    exact hyx
  exact regularSeqLtProp_irrefl x
    (regularSeqLtProp_trans x y x hxy hyx')

#print axioms BishopSec1P.regularSeqLe_of_ltPropC

def NmC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) : Nat :=
  max ((IntegrableRepC3.normL1_tendstoC (F m)).mod m)
    ((F m).abs_integral_sum.tends.mod m)

#print axioms BishopSec1P.NmC

def tail_mC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) : IntegrableRepC3 S :=
  (F m).tailFrom (NmC F m)

#print axioms BishopSec1P.tail_mC

def psi_mC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) : BFunC X :=
  BFunC.seqSum (F m).fn (NmC F m)

#print axioms BishopSec1P.psi_mC

theorem psi_m_memC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) : psi_mC F m ∈ S.L :=
  S.seqSum_mem (F m).fn_mem (NmC F m)

#print axioms BishopSec1P.psi_m_memC

def G_mC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) : IntegrableRepC3 S :=
  IntegrableRepC3.ofL (psi_m_memC F m)

#print axioms BishopSec1P.G_mC

theorem tail_m_abs_sum_ltC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) :
    regularSeqLtProp (tail_mC F m).abs_integral_sum.sum (halfPow m) := by
  let p : Nat := NmC F m
  have hp : (F m).abs_integral_sum.tends.mod m ≤ p := by
    dsimp [p, NmC]
    exact Nat.le_max_right ((IntegrableRepC3.normL1_tendstoC (F m)).mod m)
      ((F m).abs_integral_sum.tends.mod m)
  have hclose_abs :
      RepCloseAtGauge (m + 1)
        (regularSeqFinSum (fun n => S.I (BFunC.absf ((F m).fn n))) p)
        (F m).abs_integral_sum.sum :=
    (F m).abs_integral_sum.tends.close m p hp
  have htail_lt :
      regularSeqLtProp
        (subSeq (F m).abs_integral_sum.sum
          (regularSeqFinSum (fun n => S.I (BFunC.absf ((F m).fn n))) p))
        (halfPow m) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ m hclose_abs
  simpa [tail_mC, p, IntegrableRepC3.tailFrom, seriesSum_tailC] using htail_lt

#print axioms BishopSec1P.tail_m_abs_sum_ltC

theorem G_m_abs_sum_ltC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) :
    regularSeqLtProp (G_mC F m).abs_integral_sum.sum
      (addSeq (F m).normL1 (halfPow m)) := by
  let p : Nat := NmC F m
  let iabs : CReal := S.I (BFunC.absf (psi_mC F m))
  have hp : (IntegrableRepC3.normL1_tendstoC (F m)).mod m ≤ p := by
    dsimp [p, NmC]
    exact Nat.le_max_left ((IntegrableRepC3.normL1_tendstoC (F m)).mod m)
      ((F m).abs_integral_sum.tends.mod m)
  have hclose :
      RepCloseAtGauge (m + 1) iabs (F m).normL1 := by
    simpa [p, iabs, psi_mC] using
      (IntegrableRepC3.normL1_tendstoC (F m)).close m p hp
  have hdiff_lt :
      regularSeqLtProp (subSeq iabs (F m).normL1) (halfPow m) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ m (repCloseAtGauge_symm hclose)
  have hshift :
      regularSeqLtProp
        (addSeq (F m).normL1 (subSeq iabs (F m).normL1))
        (addSeq (F m).normL1 (halfPow m)) :=
    regularSeqLtProp_add_left (F m).normL1
      (subSeq iabs (F m).normL1) (halfPow m) hdiff_lt
  have hleft :
      relEventually
        iabs
        (addSeq (F m).normL1 (subSeq iabs (F m).normL1)) := by
    exact relEventually_symm _ _
      (relEventually_trans _ _ _
        (CReal.add_comm (F m).normL1 (subSeq iabs (F m).normL1))
        (addSeq_sub_right_cancel_eventually iabs (F m).normL1))
  have hiabs_lt :
      regularSeqLtProp iabs (addSeq (F m).normL1 (halfPow m)) :=
    regularSeqLtProp_of_left_eventual hleft hshift
  simpa [G_mC, IntegrableRepC3.ofL, iabs, psi_mC] using hiabs_lt

#print axioms BishopSec1P.G_m_abs_sum_ltC

def tail_m_abs_seriesSumC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) :
    RepSeriesSum (fun m => (tail_mC F m).abs_integral_sum.sum) :=
  repSeriesSum_comparison
    (fun m => repSeriesSum_nonneg
      (fun n => S.I_absf_nonneg ((tail_mC F m).fn_mem n))
      (tail_mC F m).abs_integral_sum)
    (fun m => regularSeqLe_of_ltPropC (tail_m_abs_sum_ltC F m))
    repSeriesSum_halfPow

#print axioms BishopSec1P.tail_m_abs_seriesSumC

def G_m_abs_seriesSumC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S)
    (hsum : RepSeriesSum (fun m => (F m).normL1)) :
    RepSeriesSum (fun m => (G_mC F m).abs_integral_sum.sum) :=
  repSeriesSum_comparison
    (fun m => repSeriesSum_nonneg
      (fun n => S.I_absf_nonneg ((G_mC F m).fn_mem n))
      (G_mC F m).abs_integral_sum)
    (fun m => regularSeqLe_of_ltPropC (G_m_abs_sum_ltC F m))
    (repSeriesSum_add hsum repSeriesSum_halfPow)

#print axioms BishopSec1P.G_m_abs_seriesSumC

def seriesSumRep_L1C {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S)
    (hsum : RepSeriesSum (fun m => (F m).normL1)) : IntegrableRepC3 S :=
  (seriesIntegrableC (G_mC F) (G_m_abs_seriesSumC F hsum)).add
    (seriesIntegrableC (tail_mC F) (tail_m_abs_seriesSumC F))

#print axioms BishopSec1P.seriesSumRep_L1C

def IntegrableRepC3.tailFrom_valueC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (M : Nat) (x : X)
    (hx : RepSeriesSum (fun n => (r.fn n).toFun x)) :
    { hs : RepSeriesSum (fun k => ((r.tailFrom M).fn k).toFun x) //
        hs.sum ≈ CReal.sub hx.sum ((BFunC.seqSum r.fn M).toFun x) } := by
  refine ⟨seriesSum_tailC hx M, ?_⟩
  change relEventually
    (subSeq hx.sum (regularSeqFinSum (fun n => (r.fn n).toFun x) M))
    (subSeq hx.sum ((BFunC.seqSum r.fn M).toFun x))
  rw [BFunC.seqSum_toFun r.fn x M]
  exact relEventually_refl _

#print axioms BishopSec1P.IntegrableRepC3.tailFrom_valueC

theorem IntegrableRepC3.tailFrom_integralC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (M : Nat) :
    (r.tailFrom M).integral ≈
      CReal.sub r.integral (S.I (BFunC.seqSum r.fn M)) := by
  change relEventually
    (subSeq r.integral
      (regularSeqFinSum (fun k => S.I (r.fn k)) M))
    (subSeq r.integral (S.I (BFunC.seqSum r.fn M)))
  exact subSeq_respects_eventually _ _ _ _
    (relEventually_refl r.integral)
    (relEventually_symm _ _ (S.I_seqSum r.fn_mem M))

#print axioms BishopSec1P.IntegrableRepC3.tailFrom_integralC

theorem IntegrableRepC3.cutNat_tendsto_aux {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (k M n : Nat)
    (hSM : BFunC.seqSum r.fn M ∈ S.L)
    (htailClose : RepCloseAtGauge (k + 4) ((r.tailFrom M).normL1) CReal.zero)
    (hn : (S.cutNat_tendsto hSM).mod (k + 2) ≤ n) :
    RepCloseAtGauge (k + 1) ((r.cutNatVal n).integral) r.integral := by
  let a : CReal := constSeq (Nat.cast n)
  let SM : BFunC X := BFunC.seqSum r.fn M
  let rg : IntegrableRepC3 S := IntegrableRepC3.ofL (S.cutNat_mem n hSM)
  let diff : IntegrableRepC3 S := (r.cutNatVal n).sub rg
  have htail_norm_to_abs :
      RegularSeqLe ((r.tailFrom M).normL1)
        (absSeq (subSeq ((r.tailFrom M).normL1) zeroSeq)) := by
    exact regularSeqLe_of_left_eventual
      (relEventually_symm _ _
        (subSeq_zero_right_eventually ((r.tailFrom M).normL1)))
      (base_le_abs_base_regularSeqLe
        (subSeq ((r.tailFrom M).normL1) zeroSeq))
  have term2 :
      RepCloseAtGauge (k + 3)
        (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M)))
        (S.I (BFunC.seqSum r.fn M)) :=
    (S.cutNat_tendsto hSM).close (k + 2) n hn
  have htail_int :
      (r.tailFrom M).integral ≈
        subSeq r.integral (S.I (BFunC.seqSum r.fn M)) :=
    r.tailFrom_integralC M
  have hsub_to_negtail :
      relEventually
        (subSeq (S.I (BFunC.seqSum r.fn M)) r.integral)
        (negSeq (r.tailFrom M).integral) := by
    calc
      subSeq (S.I (BFunC.seqSum r.fn M)) r.integral
          ≈ negSeq (subSeq r.integral (S.I (BFunC.seqSum r.fn M))) :=
            subSeq_comm_neg_eventually (S.I (BFunC.seqSum r.fn M)) r.integral
      _ ≈ negSeq (r.tailFrom M).integral :=
            relEventually_symm _ _ (neg_congr htail_int)
  have hleft3 :
      relEventually
        (absSeq (subSeq (S.I (BFunC.seqSum r.fn M)) r.integral))
        (absSeq (r.tailFrom M).integral) := by
    calc
      absSeq (subSeq (S.I (BFunC.seqSum r.fn M)) r.integral)
          ≈ absSeq (negSeq (r.tailFrom M).integral) :=
            absSeq_respects_eventually _ _ hsub_to_negtail
      _ ≈ absSeq (r.tailFrom M).integral :=
            CReal.abs_neg (r.tailFrom M).integral
  have hle3 :
      RegularSeqLe
        (absSeq (subSeq (S.I (BFunC.seqSum r.fn M)) r.integral))
        (absSeq (subSeq ((r.tailFrom M).normL1) CReal.zero)) :=
    regularSeqLe_trans
      (regularSeqLe_of_left_eventual hleft3
        ((r.tailFrom M).abs_integral_le_normL1C))
      htail_norm_to_abs
  have term3 :
      RepCloseAtGauge (k + 3)
        (S.I (BFunC.seqSum r.fn M)) r.integral :=
    repCloseAtGauge_of_absdiff_le (k + 3) hle3 htailClose
  have hdiff_integral :
      relEventually
        (subSeq ((r.cutNatVal n).integral)
          (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M))))
        diff.integral := by
    change relEventually
      (subSeq ((r.cutNatVal n).integral)
        (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M))))
      (addSeq ((r.cutNatVal n).integral)
        (negSeq (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M)))))
    exact subSeq_eq_add_neg_eventually
      ((r.cutNatVal n).integral)
      (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M)))
  have hleft1 :
      relEventually
        (absSeq (subSeq ((r.cutNatVal n).integral)
          (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M)))))
        (absSeq diff.integral) :=
    absSeq_respects_eventually _ _ hdiff_integral
  have hmono : RegularSeqLe diff.normL1 ((r.tailFrom M).normL1) := by
    refine IntegrableRepC3.normL1_monoC r.domain_isFull diff (r.tailFrom M) ?_
    intro x hx hxDiff hxTail
    obtain ⟨_, ⟨habs⟩⟩ := hx
    have hxsum : RepSeriesSum (fun q => (r.fn q).toFun x) :=
      seriesSum_of_absC habs
    obtain ⟨hcut0, hcut0eq⟩ :=
      r.cutConstVal_signed_valueC a (natCast_nonnegC n) x hxsum
    let hcut :
        RepSeriesSum (fun q => ((r.cutNatVal n).fn q).toFun x) := by
      simpa [IntegrableRepC3.cutNatVal, a] using hcut0
    have hcut_eq : relEventually hcut.sum (CReal.min hxsum.sum a) := by
      simpa [hcut, IntegrableRepC3.cutNatVal, a] using hcut0eq
    obtain ⟨hfinite, hfinite_eq0⟩ :=
      IntegrableRepC3.ofL_value (S.cutNat_mem n hSM) x
    have hfinite_eq :
        relEventually hfinite.sum
          (CReal.min ((BFunC.seqSum r.fn M).toFun x) a) := by
      simpa [BFunC.cutNat, BFunC.minC, SM, a] using hfinite_eq0
    obtain ⟨htail, htail_eq⟩ := r.tailFrom_valueC M x hxsum
    let hdiff :
        RepSeriesSum (fun q => (diff.fn q).toFun x) := by
      dsimp [diff, rg]
      exact sub_seriesSum_valueC3
        (r := r.cutNatVal n)
        (r' := IntegrableRepC3.ofL (S.cutNat_mem n hSM))
        (x := x) hcut hfinite
    have hdiff_to_sub :
        relEventually hdiff.sum (subSeq hcut.sum hfinite.sum) := by
      change relEventually
        (addSeq hcut.sum (negSeq hfinite.sum))
        (subSeq hcut.sum hfinite.sum)
      exact add_sub_right_equiv hcut.sum hfinite.sum
    have hdiff_to_min :
        relEventually hdiff.sum
          (subSeq (CReal.min hxsum.sum a)
            (CReal.min ((BFunC.seqSum r.fn M).toFun x) a)) := by
      calc
        hdiff.sum ≈ subSeq hcut.sum hfinite.sum := hdiff_to_sub
        _ ≈ subSeq (CReal.min hxsum.sum a)
              (CReal.min ((BFunC.seqSum r.fn M).toFun x) a) :=
            subSeq_respects_eventually _ _ _ _ hcut_eq hfinite_eq
    have hbase :
        RegularSeqLe
          (absSeq hdiff.sum)
          (absSeq htail.sum) := by
      exact regularSeqLe_of_right_eventual
        (absSeq_respects_eventually
          (subSeq hxsum.sum ((BFunC.seqSum r.fn M).toFun x))
          htail.sum
          (relEventually_symm _ _ htail_eq))
        (regularSeqLe_of_left_eventual
          (absSeq_respects_eventually hdiff.sum
            (subSeq (CReal.min hxsum.sum a)
              (CReal.min ((BFunC.seqSum r.fn M).toFun x) a))
            hdiff_to_min)
          (abs_min_sub_min_leC hxsum.sum
            ((BFunC.seqSum r.fn M).toFun x) a))
    have hxDiff_eq : relEventually hxDiff.sum hdiff.sum :=
      repSeriesSum_unique hxDiff hdiff
    have hxTail_eq : relEventually hxTail.sum htail.sum :=
      repSeriesSum_unique hxTail htail
    exact regularSeqLe_of_right_eventual
      (absSeq_respects_eventually htail.sum hxTail.sum
        (relEventually_symm _ _ hxTail_eq))
      (regularSeqLe_of_left_eventual
        (absSeq_respects_eventually hxDiff.sum hdiff.sum hxDiff_eq)
        hbase)
  have hle1 :
      RegularSeqLe
        (absSeq (subSeq ((r.cutNatVal n).integral)
          (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M)))))
        (absSeq (subSeq ((r.tailFrom M).normL1) CReal.zero)) :=
    regularSeqLe_trans
      (regularSeqLe_trans
        (regularSeqLe_of_left_eventual hleft1 diff.abs_integral_le_normL1C)
        hmono)
      htail_norm_to_abs
  have term1 :
      RepCloseAtGauge (k + 3)
        ((r.cutNatVal n).integral)
        (S.I (BFunC.cutNat n (BFunC.seqSum r.fn M))) :=
    repCloseAtGauge_of_absdiff_le (k + 3) hle1 htailClose
  have htri1 :
      RepCloseAtGauge (k + 2)
        ((r.cutNatVal n).integral)
        (S.I (BFunC.seqSum r.fn M)) :=
    repCloseAtGauge_triangle_succ (k + 2) term1 term2
  have term3' :
      RepCloseAtGauge (k + 2)
        (S.I (BFunC.seqSum r.fn M)) r.integral :=
    repCloseAtGauge_weaken (by omega : k + 2 ≤ k + 3) term3
  exact repCloseAtGauge_triangle_succ (k + 1) htri1 term3'

#print axioms BishopSec1P.IntegrableRepC3.cutNat_tendsto_aux

def IntegrableRepC3.cutNat_tendsto_rep {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RepSeriesTendsto (fun n => (r.cutNatVal n).integral) r.integral where
  mod := fun k =>
    (S.cutNat_tendsto
      (S.seqSum_mem r.fn_mem (r.abs_integral_sum.tends.mod (k + 4)))).mod (k + 2)
  close := by
    intro k n hn
    let M : Nat := r.abs_integral_sum.tends.mod (k + 4)
    refine r.cutNat_tendsto_aux k M n
      (S.seqSum_mem r.fn_mem M)
      ((lemma_1_15C r).close (k + 3) M ?_)
      ?_
    · have hk : (k + 3) + 1 = k + 4 := by omega
      change r.abs_integral_sum.tends.mod ((k + 3) + 1) ≤ M
      rw [hk]
    · simpa [M] using hn

#print axioms BishopSec1P.IntegrableRepC3.cutNat_tendsto_rep

theorem IntegrableRepC3.cutSmall_tendsto_aux {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (p M k : Nat)
    (hSM : BFunC.seqSum r.fn M ∈ S.L)
    (htailClose : RepCloseAtGauge (p + 3) ((r.tailFrom M).normL1) CReal.zero)
    (hk : (S.cutSmall_tendsto hSM).mod (p + 1) ≤ k) :
    RepCloseAtGauge (p + 1) ((r.cutSmallVal k).integral) CReal.zero := by
  let a : CReal := constSeq (eps k)
  let SM : BFunC X := BFunC.seqSum r.fn M
  let rg : IntegrableRepC3 S := IntegrableRepC3.ofL (S.cutSmall_mem k hSM)
  let diff : IntegrableRepC3 S := (r.cutSmallVal k).sub rg
  have htail_norm_to_abs :
      RegularSeqLe ((r.tailFrom M).normL1)
        (absSeq (subSeq ((r.tailFrom M).normL1) zeroSeq)) := by
    exact regularSeqLe_of_left_eventual
      (relEventually_symm _ _
        (subSeq_zero_right_eventually ((r.tailFrom M).normL1)))
      (base_le_abs_base_regularSeqLe
        (subSeq ((r.tailFrom M).normL1) zeroSeq))
  have term2 :
      RepCloseAtGauge (p + 2)
        (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M)))
        CReal.zero :=
    (S.cutSmall_tendsto hSM).close (p + 1) k hk
  have hdiff_integral :
      relEventually
        (subSeq ((r.cutSmallVal k).integral)
          (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M))))
        diff.integral := by
    change relEventually
      (subSeq ((r.cutSmallVal k).integral)
        (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M))))
      (addSeq ((r.cutSmallVal k).integral)
        (negSeq (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M)))))
    exact subSeq_eq_add_neg_eventually
      ((r.cutSmallVal k).integral)
      (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M)))
  have hleft1 :
      relEventually
        (absSeq (subSeq ((r.cutSmallVal k).integral)
          (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M)))))
        (absSeq diff.integral) :=
    absSeq_respects_eventually _ _ hdiff_integral
  have hmono : RegularSeqLe diff.normL1 ((r.tailFrom M).normL1) := by
    refine IntegrableRepC3.normL1_monoC r.domain_isFull diff (r.tailFrom M) ?_
    intro x hx hxDiff hxTail
    obtain ⟨_, ⟨habs⟩⟩ := hx
    have hxsum : RepSeriesSum (fun q => (r.fn q).toFun x) :=
      seriesSum_of_absC habs
    obtain ⟨hav, hav_eq⟩ := r.absVal_signed_value x hxsum
    obtain ⟨hcut0, hcut0eq⟩ :=
      r.absVal.cutConstVal_signed_valueC a (epsConst_nonnegC k) x hav
    let hcut :
        RepSeriesSum (fun q => ((r.cutSmallVal k).fn q).toFun x) := by
      simpa [IntegrableRepC3.cutSmallVal, a] using hcut0
    have hcut_eq0 : relEventually hcut.sum (CReal.min hav.sum a) := by
      simpa [hcut, IntegrableRepC3.cutSmallVal, a] using hcut0eq
    have hcut_eq :
        relEventually hcut.sum (CReal.min (absSeq hxsum.sum) a) := by
      have hmin :
          relEventually (CReal.min hav.sum a)
            (CReal.min (absSeq hxsum.sum) a) := by
        change relEventually
          (minSeqWith cRatScalarMulArch hav.sum a)
          (minSeqWith cRatScalarMulArch (absSeq hxsum.sum) a)
        exact minSeqWith_respects_eventually cRatScalarMulArch
          hav.sum (absSeq hxsum.sum) a a hav_eq (relEventually_refl a)
      exact relEventually_trans _ _ _ hcut_eq0 hmin
    obtain ⟨hfinite, hfinite_eq0⟩ :=
      IntegrableRepC3.ofL_value (S.cutSmall_mem k hSM) x
    have hfinite_eq :
        relEventually hfinite.sum
          (CReal.min (absSeq ((BFunC.seqSum r.fn M).toFun x)) a) := by
      simpa [BFunC.cutSmall, BFunC.minC, BFunC.absf, SM, a]
        using hfinite_eq0
    obtain ⟨htail, htail_eq⟩ := r.tailFrom_valueC M x hxsum
    let hdiff :
        RepSeriesSum (fun q => (diff.fn q).toFun x) := by
      dsimp [diff, rg]
      exact sub_seriesSum_valueC3
        (r := r.cutSmallVal k)
        (r' := IntegrableRepC3.ofL (S.cutSmall_mem k hSM))
        (x := x) hcut hfinite
    have hdiff_to_sub :
        relEventually hdiff.sum (subSeq hcut.sum hfinite.sum) := by
      change relEventually
        (addSeq hcut.sum (negSeq hfinite.sum))
        (subSeq hcut.sum hfinite.sum)
      exact add_sub_right_equiv hcut.sum hfinite.sum
    have hdiff_to_min :
        relEventually hdiff.sum
          (subSeq (CReal.min (absSeq hxsum.sum) a)
            (CReal.min
              (absSeq ((BFunC.seqSum r.fn M).toFun x)) a)) := by
      calc
        hdiff.sum ≈ subSeq hcut.sum hfinite.sum := hdiff_to_sub
        _ ≈ subSeq (CReal.min (absSeq hxsum.sum) a)
              (CReal.min
                (absSeq ((BFunC.seqSum r.fn M).toFun x)) a) :=
            subSeq_respects_eventually _ _ _ _ hcut_eq hfinite_eq
    have hbase :
        RegularSeqLe
          (absSeq hdiff.sum)
          (absSeq htail.sum) := by
      exact regularSeqLe_of_right_eventual
        (absSeq_respects_eventually
          (subSeq hxsum.sum ((BFunC.seqSum r.fn M).toFun x))
          htail.sum
          (relEventually_symm _ _ htail_eq))
        (regularSeqLe_of_left_eventual
          (absSeq_respects_eventually hdiff.sum
            (subSeq (CReal.min (absSeq hxsum.sum) a)
              (CReal.min
                (absSeq ((BFunC.seqSum r.fn M).toFun x)) a))
            hdiff_to_min)
          (regularSeqLe_trans
            (abs_min_sub_min_leC (absSeq hxsum.sum)
              (absSeq ((BFunC.seqSum r.fn M).toFun x)) a)
            (regularSeqLe_abs_abs_sub_abs hxsum.sum
              ((BFunC.seqSum r.fn M).toFun x))))
    have hxDiff_eq : relEventually hxDiff.sum hdiff.sum :=
      repSeriesSum_unique hxDiff hdiff
    have hxTail_eq : relEventually hxTail.sum htail.sum :=
      repSeriesSum_unique hxTail htail
    exact regularSeqLe_of_right_eventual
      (absSeq_respects_eventually htail.sum hxTail.sum
        (relEventually_symm _ _ hxTail_eq))
      (regularSeqLe_of_left_eventual
        (absSeq_respects_eventually hxDiff.sum hdiff.sum hxDiff_eq)
        hbase)
  have hle1 :
      RegularSeqLe
        (absSeq (subSeq ((r.cutSmallVal k).integral)
          (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M)))))
        (absSeq (subSeq ((r.tailFrom M).normL1) CReal.zero)) :=
    regularSeqLe_trans
      (regularSeqLe_trans
        (regularSeqLe_of_left_eventual hleft1 diff.abs_integral_le_normL1C)
        hmono)
      htail_norm_to_abs
  have term1 :
      RepCloseAtGauge (p + 2)
        ((r.cutSmallVal k).integral)
        (S.I (BFunC.cutSmall k (BFunC.seqSum r.fn M))) :=
    repCloseAtGauge_of_absdiff_le (p + 2) hle1 htailClose
  exact repCloseAtGauge_triangle_succ (p + 1) term1 term2

#print axioms BishopSec1P.IntegrableRepC3.cutSmall_tendsto_aux

def IntegrableRepC3.cutSmall_tendsto_rep {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) :
    RepSeriesTendsto (fun k => (r.cutSmallVal k).integral) CReal.zero where
  mod := fun p =>
    (S.cutSmall_tendsto
      (S.seqSum_mem r.fn_mem (r.abs_integral_sum.tends.mod (p + 3)))).mod
      (p + 1)
  close := by
    intro p k hk
    let M : Nat := r.abs_integral_sum.tends.mod (p + 3)
    refine r.cutSmall_tendsto_aux p M k
      (S.seqSum_mem r.fn_mem M)
      ((lemma_1_15C r).close (p + 2) M ?_)
      ?_
    · change r.abs_integral_sum.tends.mod ((p + 2) + 1) ≤ M
      have h : (p + 2) + 1 = p + 3 := by omega
      rw [h]
    · simpa [M] using hk

#print axioms BishopSec1P.IntegrableRepC3.cutSmall_tendsto_rep

/-- Antisymmetry of the presented non-strict order, at the setoid equality level. -/
theorem regularSeqLe_antisymm_eventuallyC {x y : CReal}
    (hxy : RegularSeqLe x y) (hyx : RegularSeqLe y x) :
    x ≈ y := by
  apply CReal.eq_of_small_E
  intro k hbad
  have hzero_eps : CReal.ltE CReal.zero (CReal.epsSeq k) := by
    simpa [halfPow] using regularSeqLtProp_zero_halfPow k
  have hposAbs : CReal.ltE CReal.zero
      (CReal.abs (CReal.add x (CReal.neg y))) :=
    CReal.ltE_trans hzero_eps hbad
  have hcancel :
      relEventually (CReal.add y (CReal.add x (CReal.neg y))) x := by
    change relEventually (addSeq y (addSeq x (negSeq y))) x
    calc
      addSeq y (addSeq x (negSeq y))
          ≈ addSeq y (addSeq (negSeq y) x) :=
            add_congr (Setoid.refl y) (CReal.add_comm x (negSeq y))
      _ ≈ addSeq (addSeq y (negSeq y)) x :=
            Setoid.symm (CReal.add_assoc y (negSeq y) x)
      _ ≈ addSeq zeroSeq x :=
            add_congr (add_right_neg_equiv y) (Setoid.refl x)
      _ ≈ x := CReal.zero_add x
  rcases CReal.lt_or_lt_of_abs_pos_E hposAbs with hpos | hneg
  · have hshift : CReal.ltE (CReal.add y CReal.zero)
        (CReal.add y (CReal.add x (CReal.neg y))) :=
      CReal.ltE_add_left y hpos
    have hy_left :
        regularSeqLtProp y (CReal.add y (CReal.add x (CReal.neg y))) :=
      regularSeqLtProp_of_left_eventual
        (relEventually_symm _ _ (CReal.add_zero y)) hshift
    have hyx_lt : regularSeqLtProp y x :=
      regularSeqLtProp_of_right_eventual hcancel hy_left
    exact regularSeqLe_not_lt_reverse_prop hxy hyx_lt
  · have hshift : CReal.ltE
        (CReal.add y (CReal.add x (CReal.neg y)))
        (CReal.add y CReal.zero) :=
      CReal.ltE_add_left y hneg
    have hx_right : regularSeqLtProp x (CReal.add y CReal.zero) :=
      regularSeqLtProp_of_left_eventual
        (relEventually_symm _ _ hcancel) hshift
    have hxy_lt : regularSeqLtProp x y :=
      regularSeqLtProp_of_right_eventual (CReal.add_zero y) hx_right
    exact regularSeqLe_not_lt_reverse_prop hyx hxy_lt

#print axioms BishopSec1P.regularSeqLe_antisymm_eventuallyC

/-- Corollary 1.12, presented-real version: a.e. pointwise equality implies
equality of integrals at the presented-real setoid level. -/
theorem cor_1_12C {X : Type*} {S : IntSpaceC X} {A : Set X}
    (hA : IsFullC S A) (r r' : IntegrableRepC3 S)
    (heq : ∀ x ∈ A,
      ∀ (hr : RepSeriesSum (fun n => (r.fn n).toFun x))
        (hr' : RepSeriesSum (fun n => (r'.fn n).toFun x)),
        hr.sum = hr'.sum) :
    r.integral ≈ r'.integral :=
  regularSeqLe_antisymm_eventuallyC
    (prop_1_11C hA r r'
      (fun x hx hr hr' => by
        rw [heq x hx hr hr']
        exact regularSeqLe_refl _))
    (prop_1_11C hA r' r
      (fun x hx hr hr' => by
        rw [heq x hx hr' hr]
        exact regularSeqLe_refl _))

#print axioms BishopSec1P.cor_1_12C

/-- For a pointwise nonnegative presented representative, the `L1` norm equals
its integral at the presented-real equality level. -/
theorem IntegrableRepC3.normL1_eq_integral_of_nonnegC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (hnn : RepNonnegC r) : r.normL1 ≈ r.integral := by
  change r.absVal.integral ≈ r.integral
  refine regularSeqLe_antisymm_eventuallyC ?_ ?_
  · refine prop_1_11C r.domain_isFull r.absVal r ?_
    intro x hx hr_abs hr
    rcases hx with ⟨_hdom, ⟨habs⟩⟩
    obtain ⟨hs_abs, hs_abs_eq⟩ := r.absVal_signed_value x hr
    have huniq : hr_abs.sum ≈ hs_abs.sum :=
      repSeriesSum_unique hr_abs hs_abs
    have hnonneg : RegularSeqNonneg hr.sum := hnn x habs hr
    have habs_eq : CReal.abs hr.sum ≈ hr.sum :=
      CReal.abs_of_nonneg_E hnonneg
    have hpoint : hr_abs.sum ≈ hr.sum :=
      relEventually_trans _ _ _ huniq
        (relEventually_trans _ _ _ hs_abs_eq habs_eq)
    exact regularSeqLe_of_relEventually hpoint
  · refine prop_1_11C r.domain_isFull r r.absVal ?_
    intro x hx hr hr_abs
    rcases hx with ⟨_hdom, ⟨habs⟩⟩
    obtain ⟨hs_abs, hs_abs_eq⟩ := r.absVal_signed_value x hr
    have huniq : hr_abs.sum ≈ hs_abs.sum :=
      repSeriesSum_unique hr_abs hs_abs
    have hnonneg : RegularSeqNonneg hr.sum := hnn x habs hr
    have habs_eq : CReal.abs hr.sum ≈ hr.sum :=
      CReal.abs_of_nonneg_E hnonneg
    have hpoint : hr_abs.sum ≈ hr.sum :=
      relEventually_trans _ _ _ huniq
        (relEventually_trans _ _ _ hs_abs_eq habs_eq)
    exact regularSeqLe_of_relEventually (relEventually_symm _ _ hpoint)

#print axioms BishopSec1P.IntegrableRepC3.normL1_eq_integral_of_nonnegC

def IntegrableRepC3.prop_4_2_min_f_nC {X : Type*} {S : IntSpaceC X}
    (f : IntegrableRepC3 S) (n : Nat) : IntegrableRepC3 S :=
  f.cutNatVal n

#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_min_f_nC

theorem IntegrableRepC3.repNonneg_sub_of_min_valueC {X : Type*} {S : IntSpaceC X}
    (f g : IntegrableRepC3 S) (a : CReal)
    (hg_value :
      ∀ x (hf : RepSeriesSum (fun j => (f.fn j).toFun x)),
        { hg : RepSeriesSum (fun j => (g.fn j).toFun x) //
          hg.sum ≈ CReal.min hf.sum a }) :
    RepNonnegC (f.sub g) := by
  intro x habs hx
  have habs_sub :
      RepSeriesSum
        (fun j => absSeq (((f.add g.neg).fn j).toFun x)) := by
    simpa [IntegrableRepC3.sub] using habs
  have hf_abs : RepSeriesSum (fun j => absSeq ((f.fn j).toFun x)) :=
    add_absSeriesSum_leftC (r := f) (r' := g.neg) (x := x) habs_sub
  have hneg_abs :
      RepSeriesSum (fun j => absSeq (((g.neg).fn j).toFun x)) :=
    add_absSeriesSum_rightC (r := f) (r' := g.neg) (x := x) habs_sub
  have hg_abs :
      RepSeriesSum (fun j => absSeq ((g.fn j).toFun x)) :=
    neg_absSeriesSumC (r := g) (x := x) hneg_abs
  let hf : RepSeriesSum (fun j => (f.fn j).toFun x) :=
    seriesSum_of_absC hf_abs
  let hg : RepSeriesSum (fun j => (g.fn j).toFun x) :=
    seriesSum_of_absC hg_abs
  let hmodel :
      RepSeriesSum (fun j => ((f.sub g).fn j).toFun x) :=
    sub_seriesSum_valueC3 (r := f) (r' := g) (x := x) hf hg
  obtain ⟨hcut, hcut_eq⟩ := hg_value x hf
  have hg_to_cut : hg.sum ≈ hcut.sum :=
    repSeriesSum_unique hg hcut
  have hmodel_to_sub :
      hmodel.sum ≈ subSeq hf.sum hg.sum := by
    change relEventually (addSeq hf.sum (negSeq hg.sum)) (subSeq hf.sum hg.sum)
    exact add_sub_right_equiv hf.sum hg.sum
  have hx_to_min :
      hx.sum ≈ subSeq hf.sum (CReal.min hf.sum a) := by
    calc
      hx.sum ≈ hmodel.sum := repSeriesSum_unique hx hmodel
      _ ≈ subSeq hf.sum hg.sum := hmodel_to_sub
      _ ≈ subSeq hf.sum hcut.sum :=
          subSeq_respects_eventually hf.sum hf.sum hg.sum hcut.sum
            (relEventually_refl hf.sum) hg_to_cut
      _ ≈ subSeq hf.sum (CReal.min hf.sum a) :=
          subSeq_respects_eventually hf.sum hf.sum hcut.sum (CReal.min hf.sum a)
            (relEventually_refl hf.sum) hcut_eq
  exact
    regularSeqNonneg_of_eventual hx_to_min
      (CReal.min_le_leftC hf.sum a)

#print axioms BishopSec1P.IntegrableRepC3.repNonneg_sub_of_min_valueC

theorem IntegrableRepC3.repNonneg_sub_cutNatValC {X : Type*} {S : IntSpaceC X}
    (f : IntegrableRepC3 S) (n : Nat) :
    RepNonnegC (f.sub (f.cutNatVal n)) := by
  refine
    IntegrableRepC3.repNonneg_sub_of_min_valueC f (f.cutNatVal n)
      (constSeq (Nat.cast n)) ?_
  intro x hf
  simpa [IntegrableRepC3.cutNatVal] using
    f.cutConstVal_signed_valueC
      (constSeq (Nat.cast n)) (natCast_nonnegC n) x hf

#print axioms BishopSec1P.IntegrableRepC3.repNonneg_sub_cutNatValC

theorem IntegrableRepC3.normL1_sub_cutNatC {X : Type*} {S : IntSpaceC X}
    (f : IntegrableRepC3 S) (k n : Nat)
    (hk : f.cutNat_tendsto_rep.mod k ≤ n) :
    regularSeqLtProp ((f.sub (f.cutNatVal n)).normL1) (halfPow k) := by
  have hclose :
      RepCloseAtGauge (k + 1) ((f.cutNatVal n).integral) f.integral :=
    f.cutNat_tendsto_rep.close k n hk
  have htail_lt :
      regularSeqLtProp
        (subSeq f.integral (f.cutNatVal n).integral) (halfPow k) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ k hclose
  have hnn : RepNonnegC (f.sub (f.cutNatVal n)) :=
    f.repNonneg_sub_cutNatValC n
  have hnorm_eq :
      (f.sub (f.cutNatVal n)).normL1 ≈
        (f.sub (f.cutNatVal n)).integral :=
    (f.sub (f.cutNatVal n)).normL1_eq_integral_of_nonnegC hnn
  have hnorm_to_sub :
      (f.sub (f.cutNatVal n)).normL1 ≈
        subSeq f.integral (f.cutNatVal n).integral := by
    calc
      (f.sub (f.cutNatVal n)).normL1
          ≈ (f.sub (f.cutNatVal n)).integral := hnorm_eq
      _ = addSeq f.integral (negSeq (f.cutNatVal n).integral) :=
          IntegrableRepC3.integral_sub f (f.cutNatVal n)
      _ ≈ subSeq f.integral (f.cutNatVal n).integral :=
          add_sub_right_equiv f.integral (f.cutNatVal n).integral
  have hnorm_le :
      RegularSeqLe (f.sub (f.cutNatVal n)).normL1
        (subSeq f.integral (f.cutNatVal n).integral) :=
    regularSeqLe_of_left_eventual hnorm_to_sub
      (regularSeqLe_refl (subSeq f.integral (f.cutNatVal n).integral))
  exact regularSeqLtProp_of_le_of_lt hnorm_le htail_lt

#print axioms BishopSec1P.IntegrableRepC3.normL1_sub_cutNatC

def IntegrableRepC3.min2 {X : Type*} {S : IntSpaceC X}
    (r s : IntegrableRepC3 S) : IntegrableRepC3 S :=
  IntegrableRepC3.smul CReal.half ((r.add s).sub ((r.sub s).absVal))

#print axioms BishopSec1P.IntegrableRepC3.min2

def IntegrableRepC3.min2_valueC {X : Type*} {S : IntSpaceC X}
    (r s : IntegrableRepC3 S) (x : X)
    (hr : RepSeriesSum (fun n => (r.fn n).toFun x))
    (hs : RepSeriesSum (fun n => (s.fn n).toFun x)) :
    { hm : RepSeriesSum (fun n => ((r.min2 s).fn n).toFun x) //
        relEventually hm.sum (CReal.min hr.sum hs.sum) } := by
  let hadd : RepSeriesSum (fun n => (((r.add s).fn n).toFun x)) :=
    add_seriesSum_valueC3 (r := r) (r' := s) (x := x) hr hs
  let hsub_rs : RepSeriesSum (fun n => (((r.sub s).fn n).toFun x)) :=
    sub_seriesSum_valueC3 (r := r) (r' := s) (x := x) hr hs
  obtain ⟨habsv, habsveq⟩ := (r.sub s).absVal_signed_value x hsub_rs
  let hd : RepSeriesSum
      (fun n => ((((r.add s).sub ((r.sub s).absVal)).fn n).toFun x)) :=
    sub_seriesSum_valueC3 (r := r.add s) (r' := (r.sub s).absVal)
      (x := x) hadd habsv
  refine ⟨by
    simpa [IntegrableRepC3.min2] using
      (smul_seriesSum_valueC3 CReal.half
        (r := (r.add s).sub ((r.sub s).absVal)) (x := x) hd), ?_⟩
  change relEventually (CReal.mul CReal.half hd.sum)
    (CReal.min hr.sum hs.sum)
  have habsv_to_abs :
      habsv.sum ≈ CReal.abs (CReal.add hr.sum (CReal.neg hs.sum)) := by
    simpa [hsub_rs] using habsveq
  have hd_to_halfsum_body :
      hd.sum ≈
        CReal.add (CReal.add hr.sum hs.sum)
          (CReal.neg (CReal.abs (CReal.add hr.sum (CReal.neg hs.sum)))) := by
    change relEventually
      (CReal.add hadd.sum (CReal.neg habsv.sum))
      (CReal.add (CReal.add hr.sum hs.sum)
        (CReal.neg (CReal.abs (CReal.add hr.sum (CReal.neg hs.sum)))))
    exact add_congr (Setoid.refl _) (neg_congr habsv_to_abs)
  calc
    CReal.mul CReal.half hd.sum
        ≈ CReal.mul CReal.half
            (CReal.add (CReal.add hr.sum hs.sum)
              (CReal.neg (CReal.abs (CReal.add hr.sum (CReal.neg hs.sum))))) :=
          mul_congr (Setoid.refl CReal.half) hd_to_halfsum_body
    _ ≈ CReal.min hr.sum hs.sum :=
          Setoid.symm (CReal.min_halfsum hr.sum hs.sum)

#print axioms BishopSec1P.IntegrableRepC3.min2_valueC

theorem IntegrableRepC3.normL1_min2_leC {X : Type*} {S : IntSpaceC X}
    (u v : IntegrableRepC3 S) {D : Set X} (hD : IsFullC S D)
    (hDu : D ⊆ u.domain) (_hDv : D ⊆ v.domain)
    (hu : ∀ x ∈ D,
      ∀ (hx : RepSeriesSum (fun n => (u.fn n).toFun x)),
        RegularSeqNonneg hx.sum) :
    RegularSeqLe (u.min2 v).normL1 v.normL1 := by
  refine IntegrableRepC3.normL1_monoC hD (u.min2 v) v ?_
  intro x hx huv hv
  have hx_udom : x ∈ u.domain := hDu hx
  rcases hx_udom with ⟨_hdom_u, ⟨hu_abs⟩⟩
  let hu_sum : RepSeriesSum (fun n => (u.fn n).toFun x) :=
    seriesSum_of_absC hu_abs
  have hpos_u : ¬ CReal.ltE hu_sum.sum CReal.zero := by
    change RegularSeqNonneg hu_sum.sum
    exact hu x hx hu_sum
  obtain ⟨hm, hm_eq⟩ := IntegrableRepC3.min2_valueC u v x hu_sum hv
  have hsum :
      huv.sum ≈ CReal.min hu_sum.sum hv.sum :=
    relEventually_trans _ _ _
      (repSeriesSum_unique huv hm) hm_eq
  have hleft :
      absSeq huv.sum ≈ absSeq (CReal.min hu_sum.sum hv.sum) :=
    absSeq_respects_eventually huv.sum
      (CReal.min hu_sum.sum hv.sum) hsum
  exact regularSeqLe_of_left_eventual hleft
    (CReal.abs_min_le_abs_of_nonneg_leftC hu_sum.sum hv.sum hpos_u)

#print axioms BishopSec1P.IntegrableRepC3.normL1_min2_leC

noncomputable def IntegrableRepC3.prop_4_2_n_kC {X : Type*} {S : IntSpaceC X}
    (f : IntegrableRepC3 S) : Nat → Nat
  | 0 => f.cutNat_tendsto_rep.mod 1
  | k + 1 =>
      max (f.cutNat_tendsto_rep.mod (k + 2))
        (IntegrableRepC3.prop_4_2_n_kC f k + 1)

#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_n_kC

noncomputable def IntegrableRepC3.prop_4_2_lambda_kC {X : Type*}
    {S : IntSpaceC X} (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
    (f : IntegrableRepC3 S) (n_k : Nat → Nat) :
    Nat → IntegrableRepC3 S
  | 0 =>
      (IntegrableRepC3.smul (constSeq (Nat.cast (n_k 0))) hA.rep).min2
        (f.sub (f.cutNatVal 0))
  | k + 1 =>
      (IntegrableRepC3.smul
        (constSeq (Nat.cast (n_k (k + 1) - n_k k))) hA.rep).min2
        (f.sub (f.cutNatVal (n_k k)))

#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_lambda_kC

theorem IntegrableRepC3.lambda_k_norm_leC {X : Type*} {S : IntSpaceC X}
    (A : BishopC.BSet X) (hA : IntegrableSet1C S A) (f : IntegrableRepC3 S)
    (n_k : Nat → Nat)
    (hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_k k)
    (k : Nat) :
    RegularSeqLe
      ((IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k) (k + 1)).normL1
      (halfPow (k + 1)) := by
  let c : CReal := constSeq (Nat.cast (n_k (k + 1) - n_k k))
  let u : IntegrableRepC3 S := IntegrableRepC3.smul c hA.rep
  let v : IntegrableRepC3 S := f.sub (f.cutNatVal (n_k k))
  let D : Set X := Set.inter hA.rep.domain v.domain
  have hD : IsFullC S D := by
    dsimp [D]
    exact isFull_interC hA.rep.domain_isFull v.domain_isFull
  have hDu : D ⊆ u.domain := by
    intro x hx
    simpa [u] using
      (IntegrableRepC3.domain_subset_smulC hA.rep c hx.1)
  have hDv : D ⊆ v.domain := by
    intro x hx
    exact hx.2
  have hu_custom :
      ∀ x ∈ D,
        ∀ (hx_sum : RepSeriesSum (fun n => (u.fn n).toFun x)),
          RegularSeqNonneg hx_sum.sum := by
    intro x hx hx_sum
    have hx_rep_dom : x ∈ hA.rep.domain := hx.1
    rcases hx_rep_dom with ⟨_hdom_rep, ⟨habs_rep⟩⟩
    let hx_rep : RepSeriesSum (fun n => (hA.rep.fn n).toFun x) :=
      seriesSum_of_absC habs_rep
    have hpos_rep : RegularSeqNonneg hx_rep.sum :=
      IntegrableSet1_repNonnegC hA x habs_rep hx_rep
    let h_smul :
        RepSeriesSum
          (fun n => ((IntegrableRepC3.smul c hA.rep).fn n).toFun x) :=
      smul_seriesSum_valueC3 c (r := hA.rep) (x := x) hx_rep
    have huniq : hx_sum.sum ≈ h_smul.sum := by
      simpa [u] using (repSeriesSum_unique hx_sum h_smul)
    have hmodel_nonneg : RegularSeqNonneg h_smul.sum := by
      change ¬ CReal.ltE (CReal.mul c hx_rep.sum) CReal.zero
      have hc_nonneg : ¬ CReal.ltE c CReal.zero := by
        simpa [c] using natCast_nonnegC (n_k (k + 1) - n_k k)
      have hrep_nonneg : ¬ CReal.ltE hx_rep.sum CReal.zero := by
        change RegularSeqNonneg hx_rep.sum
        exact hpos_rep
      exact CReal.mul_nonneg_E hc_nonneg hrep_nonneg
    exact regularSeqNonneg_of_eventual huniq hmodel_nonneg
  have hl :
      RegularSeqLe (u.min2 v).normL1 v.normL1 :=
    IntegrableRepC3.normL1_min2_leC u v hD hDu hDv hu_custom
  have hlt_v : regularSeqLtProp v.normL1 (halfPow (k + 1)) := by
    simpa [v] using
      IntegrableRepC3.normL1_sub_cutNatC f (k + 1) (n_k k) (hnk_ge k)
  have hle_v : RegularSeqLe v.normL1 (halfPow (k + 1)) := by
    intro hcounter
    have hrev :
        regularSeqLtProp (halfPow (k + 1)) v.normL1 :=
      regularSeqLtProp_reverse_of_le_counterexample hcounter
    exact regularSeqLtProp_irrefl v.normL1
      (regularSeqLtProp_trans v.normL1 (halfPow (k + 1)) v.normL1
        hlt_v hrev)
  simpa [IntegrableRepC3.prop_4_2_lambda_kC, u, v, c] using
    regularSeqLe_trans hl hle_v

#print axioms BishopSec1P.IntegrableRepC3.lambda_k_norm_leC

noncomputable def IntegrableRepC3.opaque_lambda_normC {X : Type*}
    {S : IntSpaceC X} (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
    (f : IntegrableRepC3 S) (n_k : Nat → Nat) (l : Nat) : CReal :=
  (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k l).normL1

#print axioms BishopSec1P.IntegrableRepC3.opaque_lambda_normC

noncomputable def IntegrableRepC3.prop_4_2_lambda_sumC {X : Type*}
    {S : IntSpaceC X}
    (A : BishopC.BSet X) (hA : IntegrableSet1C S A) (f : IntegrableRepC3 S)
    (n_k : Nat → Nat)
    (hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_k k) :
    RepSeriesSum
      (fun k => IntegrableRepC3.opaque_lambda_normC A hA f n_k k) := by
  refine repSeriesSum_of_tailC 0 ?_
  refine repSeriesSum_of_le_halfPow ?_ ?_
  · intro l
    exact IntegrableRepC3.normL1_nonnegC
      (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k (0 + 1 + l))
  · intro l
    have hk := IntegrableRepC3.lambda_k_norm_leC A hA f n_k hnk_ge l
    have hhalf_le : RegularSeqLe (halfPow (l + 1)) (halfPow l) :=
      regularSeqLe_of_ltPropC (regularSeqLtProp_halfPow_succ l)
    have heq :
        IntegrableRepC3.opaque_lambda_normC A hA f n_k (0 + 1 + l)
          =
            (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k
              (l + 1)).normL1 := by
      change
        (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k
          (0 + 1 + l)).normL1
          =
            (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k
              (l + 1)).normL1
      congr 2
      omega
    rw [heq]
    exact regularSeqLe_trans hk hhalf_le

#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_lambda_sumC

noncomputable def IntegrableRepC3.prop_4_2_chi_f_repC {X : Type*}
    {S : IntSpaceC X} (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
    (f : IntegrableRepC3 S) : IntegrableRepC3 S :=
  let n_seq := f.prop_4_2_n_kC
  let hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_seq k :=
    fun k => by
      cases k with
      | zero => exact Nat.le_refl _
      | succ k' => exact Nat.le_max_left _ _
  seriesSumRep_L1C
    (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_seq)
    (IntegrableRepC3.prop_4_2_lambda_sumC A hA f n_seq hnk_ge)

#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_chi_f_repC

/-- The `L1` norm `Sum_n I(|f_n|)` of a clean characteristic representation is
non-negative.  Choice-free (hardness 4): each `I(|f_n|) >= 0` via
`concrete_I_nonneg`, finite partial sums are non-negative, and the represented
`tends` datum equals the sum to a finite partial sum. -/
theorem CleanCharDataC.norm_nonneg {Arch : ScalarMulArchimedeanData} {X : Type}
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (C : CleanCharDataC S) :
    RegularSeqNonneg C.rep.abs_integral_sum.sum := by
  have hterm : ∀ n,
      RegularSeqNonneg (S.core.I (BishopRegularSeqPFun.absf (C.rep.fn n))) :=
    fun n =>
      concrete_I_nonneg S (S.core.abs_mem (C.rep.fn_mem n))
        (absf_pointwiseNonneg (C.rep.fn n))
  have hN :
      relEventually
        (regularSeqFinSum
          (fun n => S.core.I (BishopRegularSeqPFun.absf (C.rep.fn n)))
          (C.rep.abs_integral_sum.tends.modulus 0))
        C.rep.abs_integral_sum.sum :=
    C.rep.abs_integral_sum.tends.close 0
      (C.rep.abs_integral_sum.tends.modulus 0) (Nat.le_refl _)
  exact regularSeqNonneg_of_eventual
    (relEventually_symm _ _ hN)
    (regularSeqFinSum_nonneg hterm (C.rep.abs_integral_sum.tends.modulus 0))

#print axioms BishopSec1P.CleanCharDataC.norm_nonneg

/- FRONTIER (μ(C) ≥ 0): the signed measure `mu(C) = C.rep.integral = Sum_n I(f_n)`
is NOT the L1 norm `Sum_n I(|f_n|)` (the representing series has signed terms), so
`norm_nonneg` (above, L1-norm ≥ 0) does not close `mu(C) ≥ 0` directly.  Per the
design audit, the honest route is the posPart/negPart series lift (steps (e)(f) of
§1.5): `I(posPart f_n) ≥ 0` series convergence → per-N limit → `lemma_1_7` (series
version) → `mu(C) ≥ 0`.  `norm_nonneg` and `absf_pointwiseNonneg` are the reusable
partial progress toward it.  Deliberately NOT closed with a fabricated certificate. -/

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem CReal.le_minC {a b c : CReal}
    (hca : RegularSeqLe c a) (hcb : RegularSeqLe c b) :
    RegularSeqLe c (CReal.min a b) := by
  -- `body = (a-c) + (b-c) - |a-b|`
  let body : CReal :=
    subSeq (addSeq (subSeq a c) (subSeq b c)) (absSeq (subSeq a b))
  -- `|a-b| ≤ (a-c) + (b-c)`  ( = `RegularSeqNonneg body`)
  have hbody_le :
      RegularSeqLe (absSeq (subSeq a b))
        (addSeq (subSeq a c) (subSeq b c)) := by
    have hd_eq :
        relEventually (subSeq a b)
          (addSeq (subSeq a c) (negSeq (subSeq b c))) := by
      have hq :
          mkQuot (subSeq a b)
            = mkQuot (addSeq (subSeq a c) (negSeq (subSeq b c))) := by
        change subQuot (mkQuot a) (mkQuot b)
          = addQuot (subQuot (mkQuot a) (mkQuot c))
              (negQuot (subQuot (mkQuot b) (mkQuot c)))
        letI : CommRing CRealQuot :=
          cRealQuotCommRingConcreteWith cRatScalarMulArch
        let A : CRealQuot := mkQuot a
        let B : CRealQuot := mkQuot b
        let C : CRealQuot := mkQuot c
        change A - B = (A - C) + -(B - C)
        ring
      exact Quotient.exact hq
    have hA :
        relEventually (absSeq (subSeq a b))
          (absSeq (addSeq (subSeq a c) (negSeq (subSeq b c)))) :=
      absSeq_respects_eventually _ _ hd_eq
    have htri :
        RegularSeqLe
          (absSeq (addSeq (subSeq a c) (negSeq (subSeq b c))))
          (addSeq (absSeq (subSeq a c))
            (absSeq (negSeq (subSeq b c)))) :=
      regularSeqLe_abs_add (subSeq a c) (negSeq (subSeq b c))
    have habs_ac : absSeq (subSeq a c) ≈ subSeq a c :=
      CReal.abs_of_nonneg_E hca
    have habs_negbc : absSeq (negSeq (subSeq b c)) ≈ subSeq b c :=
      relEventually_trans _ _ _
        (absSeq_negSeq_eventually (subSeq b c))
        (CReal.abs_of_nonneg_E hcb)
    have hRHS :
        relEventually
          (addSeq (absSeq (subSeq a c)) (absSeq (negSeq (subSeq b c))))
          (addSeq (subSeq a c) (subSeq b c)) :=
      addSeq_respects_eventually _ _ _ _ habs_ac habs_negbc
    exact regularSeqLe_of_left_eventual hA
      (regularSeqLe_of_right_eventual hRHS htri)
  have hbody_nonneg : RegularSeqNonneg body := hbody_le
  have hhalf_nonneg : ¬ CReal.ltE CReal.half CReal.zero := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero
      (CReal.ltE_trans CReal.half_pos_E hlt)
  have hprod_nonneg : RegularSeqNonneg (CReal.mul CReal.half body) := by
    change ¬ CReal.ltE (CReal.mul CReal.half body) CReal.zero
    exact CReal.mul_nonneg_E hhalf_nonneg hbody_nonneg
  have hto_prod :
      relEventually (subSeq (CReal.min a b) c)
        (CReal.mul CReal.half body) := by
    have hq :
        mkQuot (subSeq (CReal.min a b) c)
          = mkQuot (CReal.mul CReal.half body) := by
      change subQuot (mkQuot (minSeqWith cRatScalarMulArch a b)) (mkQuot c)
        = mulQuotConcreteWith cRatScalarMulArch halfQuot
            (subQuot
              (addQuot (subQuot (mkQuot a) (mkQuot c))
                (subQuot (mkQuot b) (mkQuot c)))
              (absQuot (subQuot (mkQuot a) (mkQuot b))))
      rw [mkQuot_minSeqWith_eq_minQuotCOFWith cRatScalarMulArch a b]
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let C : CRealQuot := mkQuot c
      let U : CRealQuot := absQuot (subQuot A B)
      change (halfQuot * ((A + B) + -U)) - C
        = halfQuot * (((A - C) + (B - C)) - U)
      have hhalf : (halfQuot : CRealQuot) + halfQuot = 1 := halfQuot_add_half
      linear_combination C * hhalf
    exact Quotient.exact hq
  change RegularSeqNonneg (subSeq (CReal.min a b) c)
  exact regularSeqNonneg_of_eventual hto_prod hprod_nonneg

#print axioms BishopSec1P.CReal.le_minC

/-- Technical lemma used in the public import closure. -/
theorem CReal.min_le_rightC (a b : CReal) :
    RegularSeqLe (CReal.min a b) b := by
  have hcomm : relEventually (CReal.min a b) (CReal.min b a) :=
    minSeqWith_comm_eventually cRatScalarMulArch a b
  exact regularSeqLe_of_left_eventual hcomm (CReal.min_le_leftC b a)

#print axioms BishopSec1P.CReal.min_le_rightC

/-- Technical lemma used in the public import closure. -/
private theorem sub_congrC {a a' b b' : CReal} (ha : a ≈ a') (hb : b ≈ b') :
    CReal.sub a b ≈ CReal.sub a' b' :=
  subSeq_respects_eventually a a' b b' ha hb

#print axioms sub_congrC

/-- Technical lemma used in the public import closure. -/
private theorem min_congrC {a a' b b' : CReal} (ha : a ≈ a') (hb : b ≈ b') :
    CReal.min a b ≈ CReal.min a' b' :=
  minSeqWith_respects_eventually cRatScalarMulArch a a' b b' ha hb

#print axioms min_congrC

/-- Technical lemma used in the public import closure. -/
def prevSeqC (m : Nat → CReal) : Nat → CReal
  | 0 => CReal.zero
  | k + 1 => m k

#print axioms prevSeqC

/-- Technical lemma used in the public import closure. -/
theorem CReal.prop42_term_chi1C (φ p q : CReal) (hpq : RegularSeqLe p q) :
    CReal.min (CReal.sub q p) (CReal.sub φ (CReal.min φ p))
      ≈ CReal.sub (CReal.min φ q) (CReal.min φ p) := by
  refine regularSeqLe_antisymm_eventuallyC ?_ ?_
  · -- ≤ direction: min(q−p, φ−min φ p) ≤ min φ q − min φ p
    apply regularSeqLe_cancel_add_right (c := CReal.min φ p)
    refine regularSeqLe_of_right_eventual
      (relEventually_symm _ _
        (addSeq_sub_right_cancel_eventually (CReal.min φ q) (CReal.min φ p))) ?_
    apply CReal.le_minC
    · -- ... + min φ p ≤ φ
      have h1 :
          RegularSeqLe
            (CReal.min (CReal.sub q p) (CReal.sub φ (CReal.min φ p)))
            (CReal.sub φ (CReal.min φ p)) :=
        CReal.min_le_rightC _ _
      have hsum :
          RegularSeqLe
            (addSeq
              (CReal.min (CReal.sub q p) (CReal.sub φ (CReal.min φ p)))
              (CReal.min φ p))
            (addSeq (CReal.sub φ (CReal.min φ p)) (CReal.min φ p)) :=
        regularSeqLe_add h1 (regularSeqLe_refl _)
      exact regularSeqLe_of_right_eventual
        (addSeq_sub_right_cancel_eventually φ (CReal.min φ p)) hsum
    · -- ... + min φ p ≤ q
      have h1 :
          RegularSeqLe
            (CReal.min (CReal.sub q p) (CReal.sub φ (CReal.min φ p)))
            (CReal.sub q p) :=
        CReal.min_le_leftC _ _
      have h2 : RegularSeqLe (CReal.min φ p) p := CReal.min_le_rightC _ _
      have hsum :
          RegularSeqLe
            (addSeq
              (CReal.min (CReal.sub q p) (CReal.sub φ (CReal.min φ p)))
              (CReal.min φ p))
            (addSeq (CReal.sub q p) p) :=
        regularSeqLe_add h1 h2
      exact regularSeqLe_of_right_eventual
        (addSeq_sub_right_cancel_eventually q p) hsum
  · -- ≥ direction: min φ q − min φ p ≤ min(q−p, φ−min φ p)
    apply CReal.le_minC
    · -- N ≤ q − p
      have h := abs_min_sub_min_leC q p φ
      have hcomm :
          CReal.sub (CReal.min q φ) (CReal.min p φ)
            ≈ CReal.sub (CReal.min φ q) (CReal.min φ p) :=
        sub_congrC
          (minSeqWith_comm_eventually cRatScalarMulArch q φ)
          (minSeqWith_comm_eventually cRatScalarMulArch p φ)
      have hLHS :
          CReal.abs (CReal.sub (CReal.min q φ) (CReal.min p φ))
            ≈ CReal.abs (CReal.sub (CReal.min φ q) (CReal.min φ p)) :=
        abs_congr hcomm
      have hRHS : CReal.abs (CReal.sub q p) ≈ CReal.sub q p :=
        CReal.abs_of_nonneg_E hpq
      have hle_abs :
          RegularSeqLe
            (CReal.abs (CReal.sub (CReal.min φ q) (CReal.min φ p)))
            (CReal.sub q p) :=
        regularSeqLe_of_right_eventual hRHS
          (regularSeqLe_of_left_eventual (relEventually_symm _ _ hLHS) h)
      exact regularSeqLe_trans
        (base_le_abs_base_regularSeqLe
          (CReal.sub (CReal.min φ q) (CReal.min φ p)))
        hle_abs
    · -- N ≤ φ − min φ p
      exact subSeq_monotone_left_regularSeqLe
        (CReal.min φ q) φ (CReal.min φ p) (CReal.min_le_leftC φ q)

#print axioms BishopSec1P.CReal.prop42_term_chi1C

/-- Technical lemma used in the public import closure. -/
theorem CReal.prop42_termC (φ χ p q : CReal) (hpq : RegularSeqLe p q)
    (hχ : χ ≈ CReal.zero ∨ χ ≈ CReal.one) :
    CReal.min (CReal.mul (CReal.sub q p) χ) (CReal.sub φ (CReal.min φ p))
      ≈ CReal.mul χ (CReal.sub (CReal.min φ q) (CReal.min φ p)) := by
  rcases hχ with h0 | h1
  · -- χ ≈ 0
    have hmul0 : CReal.mul (CReal.sub q p) χ ≈ CReal.zero :=
      relEventually_trans _ _ _
        (mul_congr (relEventually_refl _) h0)
        (mulSeqConcrete_zero_right_eventually cRatScalarMulArch (CReal.sub q p))
    have hminstep :
        CReal.min (CReal.mul (CReal.sub q p) χ) (CReal.sub φ (CReal.min φ p))
          ≈ CReal.min CReal.zero (CReal.sub φ (CReal.min φ p)) :=
      min_congrC hmul0 (relEventually_refl _)
    have hXnn : RegularSeqNonneg (CReal.sub φ (CReal.min φ p)) :=
      CReal.min_le_leftC φ p
    have hmin0 :
        CReal.min CReal.zero (CReal.sub φ (CReal.min φ p)) ≈ CReal.zero :=
      relEventually_trans _ _ _
        (minSeqWith_comm_eventually cRatScalarMulArch CReal.zero
          (CReal.sub φ (CReal.min φ p)))
        (CReal.min_zero_const hXnn)
    have hleft :
        CReal.min (CReal.mul (CReal.sub q p) χ) (CReal.sub φ (CReal.min φ p))
          ≈ CReal.zero :=
      relEventually_trans _ _ _ hminstep hmin0
    have hright :
        CReal.mul χ (CReal.sub (CReal.min φ q) (CReal.min φ p)) ≈ CReal.zero :=
      relEventually_trans _ _ _
        (mul_congr h0 (relEventually_refl _))
        (mulSeqConcrete_zero_left_eventually cRatScalarMulArch
          (CReal.sub (CReal.min φ q) (CReal.min φ p)))
    exact relEventually_trans _ _ _ hleft (relEventually_symm _ _ hright)
  · -- χ ≈ 1
    have hmul1 : CReal.mul (CReal.sub q p) χ ≈ CReal.sub q p :=
      relEventually_trans _ _ _
        (mul_congr (relEventually_refl _) h1)
        (CReal.mul_one (CReal.sub q p))
    have hleft :
        CReal.min (CReal.mul (CReal.sub q p) χ) (CReal.sub φ (CReal.min φ p))
          ≈ CReal.min (CReal.sub q p) (CReal.sub φ (CReal.min φ p)) :=
      min_congrC hmul1 (relEventually_refl _)
    have hmid :
        CReal.min (CReal.sub q p) (CReal.sub φ (CReal.min φ p))
          ≈ CReal.sub (CReal.min φ q) (CReal.min φ p) :=
      CReal.prop42_term_chi1C φ p q hpq
    have hright :
        CReal.mul χ (CReal.sub (CReal.min φ q) (CReal.min φ p))
          ≈ CReal.sub (CReal.min φ q) (CReal.min φ p) :=
      relEventually_trans _ _ _
        (mul_congr h1 (relEventually_refl _))
        (CReal.one_mul (CReal.sub (CReal.min φ q) (CReal.min φ p)))
    exact relEventually_trans _ _ _
      (relEventually_trans _ _ _ hleft hmid)
      (relEventually_symm _ _ hright)

#print axioms BishopSec1P.CReal.prop42_termC

/-- Technical lemma used in the public import closure. -/
theorem CReal.prop42_telescopeC (φ χ : CReal) (m : Nat → CReal)
    (hm0 : RegularSeqNonneg (m 0)) (hmono : ∀ k, RegularSeqLe (m k) (m (k + 1)))
    (hχ : χ ≈ CReal.zero ∨ χ ≈ CReal.one) :
    ∀ K,
      regularSeqFinSum
          (fun k =>
            CReal.min (CReal.mul (CReal.sub (m k) (prevSeqC m k)) χ)
              (CReal.sub φ (CReal.min φ (prevSeqC m k))))
          K
        ≈ CReal.mul χ
            (CReal.sub (CReal.min φ (m K)) (CReal.min φ CReal.zero)) := by
  intro K
  induction K with
  | zero =>
      have hpq0 : RegularSeqLe CReal.zero (m 0) :=
        regularSeqNonneg_of_eventual
          (subSeq_zero_right_eventually (m 0)) hm0
      exact CReal.prop42_termC φ χ CReal.zero (m 0) hpq0 hχ
  | succ K ih =>
      have hterm :
          CReal.min (CReal.mul (CReal.sub (m (K + 1)) (m K)) χ)
              (CReal.sub φ (CReal.min φ (m K)))
            ≈ CReal.mul χ
                (CReal.sub (CReal.min φ (m (K + 1))) (CReal.min φ (m K))) :=
        CReal.prop42_termC φ χ (m K) (m (K + 1)) (hmono K) hχ
      have hsum :
          CReal.add
              (regularSeqFinSum
                (fun k =>
                  CReal.min (CReal.mul (CReal.sub (m k) (prevSeqC m k)) χ)
                    (CReal.sub φ (CReal.min φ (prevSeqC m k))))
                K)
              (CReal.min (CReal.mul (CReal.sub (m (K + 1)) (m K)) χ)
                (CReal.sub φ (CReal.min φ (m K))))
            ≈ CReal.add
                (CReal.mul χ
                  (CReal.sub (CReal.min φ (m K)) (CReal.min φ CReal.zero)))
                (CReal.mul χ
                  (CReal.sub (CReal.min φ (m (K + 1))) (CReal.min φ (m K)))) :=
        add_congr ih hterm
      have hring :
          CReal.add
              (CReal.mul χ
                (CReal.sub (CReal.min φ (m K)) (CReal.min φ CReal.zero)))
              (CReal.mul χ
                (CReal.sub (CReal.min φ (m (K + 1))) (CReal.min φ (m K))))
            ≈ CReal.mul χ
                (CReal.sub (CReal.min φ (m (K + 1))) (CReal.min φ CReal.zero)) := by
        have hq :
            mkQuot
                (CReal.add
                  (CReal.mul χ
                    (CReal.sub (CReal.min φ (m K)) (CReal.min φ CReal.zero)))
                  (CReal.mul χ
                    (CReal.sub (CReal.min φ (m (K + 1))) (CReal.min φ (m K)))))
              = mkQuot
                  (CReal.mul χ
                    (CReal.sub (CReal.min φ (m (K + 1)))
                      (CReal.min φ CReal.zero))) := by
          change
              addQuot
                (mulQuotConcreteWith cRatScalarMulArch (mkQuot χ)
                  (subQuot (mkQuot (CReal.min φ (m K)))
                    (mkQuot (CReal.min φ CReal.zero))))
                (mulQuotConcreteWith cRatScalarMulArch (mkQuot χ)
                  (subQuot (mkQuot (CReal.min φ (m (K + 1))))
                    (mkQuot (CReal.min φ (m K)))))
            = mulQuotConcreteWith cRatScalarMulArch (mkQuot χ)
                (subQuot (mkQuot (CReal.min φ (m (K + 1))))
                  (mkQuot (CReal.min φ CReal.zero)))
          letI : CommRing CRealQuot :=
            cRealQuotCommRingConcreteWith cRatScalarMulArch
          let cc : CRealQuot := mkQuot χ
          let xX : CRealQuot := mkQuot (CReal.min φ (m K))
          let xY : CRealQuot := mkQuot (CReal.min φ CReal.zero)
          let xZ : CRealQuot := mkQuot (CReal.min φ (m (K + 1)))
          change (cc * (xX - xY)) + (cc * (xZ - xX)) = cc * (xZ - xY)
          ring
        exact Quotient.exact hq
      exact relEventually_trans _ _ _ hsum hring

#print axioms BishopSec1P.CReal.prop42_telescopeC

/-- Technical lemma used in the public import closure. -/
noncomputable def IntegrableRepC3.prop_4_2_term_valueC {X : Type*}
    {S : IntSpaceC X} {A : BishopC.BSet X} (hA : IntegrableSet1C S A)
    (f : IntegrableRepC3 S) (c a : CReal) (ha : ¬ CReal.ltE a CReal.zero) (x : X)
    (hχ : RepSeriesSum (fun n => (hA.rep.fn n).toFun x))
    (hf : RepSeriesSum (fun n => (f.fn n).toFun x)) :
    { hv : RepSeriesSum
            (fun n =>
              (((hA.rep.smul c).min2 (f.sub (f.cutConstVal a ha))).fn n).toFun x) //
        relEventually hv.sum
          (CReal.min (CReal.mul c hχ.sum)
            (CReal.sub hf.sum (CReal.min hf.sum a))) } := by
  obtain ⟨hg, hgeq⟩ := f.cutConstVal_signed_valueC a ha x hf
  obtain ⟨hm, hmeq⟩ :=
    IntegrableRepC3.min2_valueC (hA.rep.smul c) (f.sub (f.cutConstVal a ha)) x
      (smul_seriesSum_valueC3 c (r := hA.rep) (x := x) hχ)
      (sub_seriesSum_valueC3 (r := f) (r' := f.cutConstVal a ha) (x := x) hf hg)
  refine ⟨hm, ?_⟩
  refine relEventually_trans _ _ _ hmeq ?_
  refine min_congrC (relEventually_refl _) ?_
  -- `hf.sum + (-hg.sum) ≈ hf.sum − min(hf.sum, a)`
  have hstep1 :
      CReal.add hf.sum (CReal.neg hg.sum)
        ≈ CReal.add hf.sum (CReal.neg (CReal.min hf.sum a)) :=
    add_congr (relEventually_refl _) (neg_congr hgeq)
  have hstep2 :
      CReal.add hf.sum (CReal.neg (CReal.min hf.sum a))
        ≈ CReal.sub hf.sum (CReal.min hf.sum a) := by
    have hq :
        mkQuot (CReal.add hf.sum (CReal.neg (CReal.min hf.sum a)))
          = mkQuot (CReal.sub hf.sum (CReal.min hf.sum a)) := by
      change addQuot (mkQuot hf.sum) (negQuot (mkQuot (CReal.min hf.sum a)))
        = subQuot (mkQuot hf.sum) (mkQuot (CReal.min hf.sum a))
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let P : CRealQuot := mkQuot hf.sum
      let Q : CRealQuot := mkQuot (CReal.min hf.sum a)
      change P + -Q = P - Q
      ring
    exact Quotient.exact hq
  exact relEventually_trans _ _ _ hstep1 hstep2

#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_term_valueC

/-! Technical auxiliary material for the public import closure. -/

theorem constSeq_natCast_zeroC :
    relEventually (constSeq (Nat.cast 0)) CReal.zero := by
  intro k
  refine ⟨0, ?_⟩
  intro p _hp
  have hval : (constSeq (Nat.cast 0)).val p - CReal.zero.val p = (0 : Scalar) := by
    change (Nat.cast 0 : Scalar) - 0 = 0
    rw [Nat.cast_zero]; ring
  rw [hval]
  change BishopCReal.Le (BishopCRat.CRat.absF 0) (eps k)
  rw [scalarCOFOSeed.abs_zero]
  exact eps_nonneg k

#print axioms BishopSec1P.constSeq_natCast_zeroC

theorem constSeq_natCast_addC (m n : Nat) :
    relEventually (constSeq (Nat.cast (m + n)))
      (CReal.add (constSeq (Nat.cast m)) (constSeq (Nat.cast n))) := by
  intro k
  refine ⟨0, ?_⟩
  intro p _hp
  have hval : (constSeq (Nat.cast (m + n))).val p
            - (CReal.add (constSeq (Nat.cast m)) (constSeq (Nat.cast n))).val p = (0 : Scalar) := by
    change (Nat.cast (m + n) : Scalar) - (Nat.cast m + Nat.cast n) = 0
    rw [Nat.cast_add]; ring
  rw [hval]
  change BishopCReal.Le (BishopCRat.CRat.absF 0) (eps k)
  rw [scalarCOFOSeed.abs_zero]
  exact eps_nonneg k

#print axioms BishopSec1P.constSeq_natCast_addC

theorem constSeq_natCast_subC {m n : Nat} (h : n ≤ m) :
    relEventually (constSeq (Nat.cast (m - n)))
      (CReal.sub (constSeq (Nat.cast m)) (constSeq (Nat.cast n))) := by
  intro k
  refine ⟨0, ?_⟩
  intro p _hp
  have hval : (constSeq (Nat.cast (m - n))).val p
            - (CReal.sub (constSeq (Nat.cast m)) (constSeq (Nat.cast n))).val p = (0 : Scalar) := by
    change (Nat.cast (m - n) : Scalar) - (Nat.cast m - Nat.cast n) = 0
    rw [Nat.cast_sub h]; ring
  rw [hval]
  change BishopCReal.Le (BishopCRat.CRat.absF 0) (eps k)
  rw [scalarCOFOSeed.abs_zero]
  exact eps_nonneg k

#print axioms BishopSec1P.constSeq_natCast_subC

/-- Technical lemma used in the public import closure. -/
theorem CReal.sub_zeroC (a : CReal) : relEventually (CReal.sub a CReal.zero) a := by
  have hq : mkQuot (CReal.sub a CReal.zero) = mkQuot a := by
    change subQuot (mkQuot a) zeroQuot = mkQuot a
    exact subQuot_zero_right_mk a
  exact Quotient.exact hq

#print axioms BishopSec1P.CReal.sub_zeroC

/-- Technical lemma used in the public import closure. -/
noncomputable def IntegrableRepC3.prop_4_2_lambda_valueC {X : Type*} {S : IntSpaceC X}
    {A : BishopC.BSet X} (hA : IntegrableSet1C S A) (f : IntegrableRepC3 S)
    (n_k : Nat → Nat) (hmono : ∀ k, n_k k ≤ n_k (k + 1)) (x : X)
    (hχ : RepSeriesSum (fun n => (hA.rep.fn n).toFun x))
    (hf : RepSeriesSum (fun n => (f.fn n).toFun x)) (k : Nat) :
    { hv : RepSeriesSum
            (fun n => ((IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k k).fn n).toFun x) //
        relEventually hv.sum
          (CReal.min
            (CReal.mul
              (CReal.sub (constSeq (Nat.cast (n_k k)))
                (prevSeqC (fun j => constSeq (Nat.cast (n_k j))) k))
              hχ.sum)
            (CReal.sub hf.sum
              (CReal.min hf.sum
                (prevSeqC (fun j => constSeq (Nat.cast (n_k j))) k)))) } := by
  cases k with
  | zero =>
    obtain ⟨hv, hveq⟩ :=
      f.prop_4_2_term_valueC hA (constSeq (Nat.cast (n_k 0))) (constSeq (Nat.cast 0))
        (natCast_nonnegC 0) x hχ hf
    refine ⟨hv, ?_⟩
    refine relEventually_trans _ _ _ hveq ?_
    refine min_congrC
      (mul_congr
        (relEventually_symm _ _ (CReal.sub_zeroC (constSeq (Nat.cast (n_k 0)))))
        (relEventually_refl _))
      (sub_congrC (relEventually_refl _)
        (min_congrC (relEventually_refl _) constSeq_natCast_zeroC))
  | succ k =>
    obtain ⟨hv, hveq⟩ :=
      f.prop_4_2_term_valueC hA (constSeq (Nat.cast (n_k (k + 1) - n_k k)))
        (constSeq (Nat.cast (n_k k))) (natCast_nonnegC (n_k k)) x hχ hf
    refine ⟨hv, ?_⟩
    refine relEventually_trans _ _ _ hveq ?_
    refine min_congrC
      (mul_congr (constSeq_natCast_subC (hmono k)) (relEventually_refl _))
      (relEventually_refl _)

#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_lambda_valueC

/-- Technical lemma used in the public import closure. -/
theorem CReal.min_eq_left_of_leC {φ b : CReal} (h : RegularSeqLe φ b) :
    CReal.min φ b ≈ φ :=
  regularSeqLe_antisymm_eventuallyC (CReal.min_le_leftC φ b)
    (CReal.le_minC (regularSeqLe_refl φ) h)

#print axioms BishopSec1P.CReal.min_eq_left_of_leC

/-- Technical lemma used in the public import closure. -/
theorem nk_ge_self {n_k : Nat → Nat} (hsucc : ∀ k, n_k k + 1 ≤ n_k (k + 1)) :
    ∀ K, K ≤ n_k K := by
  intro K
  induction K with
  | zero => exact Nat.zero_le _
  | succ K ih => exact Nat.le_trans (Nat.succ_le_succ ih) (hsucc K)

#print axioms BishopSec1P.nk_ge_self

/-- Technical lemma used in the public import closure. -/
theorem natCast_le_of_leC {a b : Nat} (h : a ≤ b) :
    RegularSeqLe (constSeq (Nat.cast a)) (constSeq (Nat.cast b)) := by
  apply regularSeqLe_of_indexed_pointwise_le
  intro _m
  change BishopC.Le ((Nat.cast a : Scalar)) ((Nat.cast b : Scalar))
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [Nat.cast_add]
  have hd : BishopC.Le (0 : Scalar) ((Nat.cast d : Scalar)) := by
    clear h
    induction d with
    | zero => simpa using (BishopC.le_refl (0 : Scalar))
    | succ d ih =>
        have h1 : BishopC.Le (0 : Scalar) (1 : Scalar) :=
          scalar_nonneg_of_pos scalarCOFOSeed.one_pos
        have hsum : BishopC.Le ((0 : Scalar) + 0) ((Nat.cast d : Scalar) + 1) :=
          BishopC.le_add ih h1
        simpa [Nat.cast_succ] using hsum
  have hstep : BishopC.Le ((Nat.cast a : Scalar) + 0) ((Nat.cast a : Scalar) + Nat.cast d) :=
    BishopC.le_add (BishopC.le_refl _) hd
  simpa using hstep

#print axioms BishopSec1P.natCast_le_of_leC

/-- Scalar nonnegativity of a natural-number cast. -/
theorem scalar_natCast_nonneg (k : Nat) : BishopC.Le (0 : Scalar) (Nat.cast k) := by
  induction k with
  | zero => rw [Nat.cast_zero]; exact BishopC.le_refl 0
  | succ k ih =>
      rw [Nat.cast_succ]
      have h1 : BishopC.Le (0 : Scalar) 1 := scalar_nonneg_of_pos scalarCOFOSeed.one_pos
      have hsum : BishopC.Le ((0 : Scalar) + 0) ((Nat.cast k : Scalar) + 1) :=
        BishopC.le_add ih h1
      simpa using hsum

#print axioms BishopSec1P.scalar_natCast_nonneg

/-- The dyadic gauge cancels its natural-number reciprocal at the scalar level:
`eps m * (2^m) = 1`. -/
theorem eps_mul_natCast_twoPow (m : Nat) :
    eps m * (Nat.cast (2 ^ m) : Scalar) = 1 := by
  induction m with
  | zero =>
      rw [show (2 : Nat) ^ 0 = 1 from rfl, Nat.cast_one,
        show eps 0 = (1 : Scalar) from rfl, one_mul]
  | succ m ih =>
      rw [pow_succ, Nat.cast_mul]
      have h2 : (Nat.cast (2 : Nat) : Scalar) = 1 + 1 := by
        rw [show (2 : Nat) = 1 + 1 from rfl, Nat.cast_add, Nat.cast_one]
      rw [h2,
        show eps (m + 1) * (Nat.cast (2 ^ m) * (1 + 1))
            = (eps (m + 1) + eps (m + 1)) * Nat.cast (2 ^ m) from by ring,
        eps_succ_add_self m]
      exact ih

#print axioms BishopSec1P.eps_mul_natCast_twoPow

/-- Scalar Archimedean upper bound: every presented real is dominated by some
natural-number constant sequence (constructive, via the standard bound). -/
theorem exists_nat_geC (φ : CReal) :
    ∃ N : Nat, RegularSeqLe φ (constSeq (Nat.cast N)) := by
  obtain ⟨m, hspec⟩ :
      ∃ m : Nat, BishopC.Le ((COF.abs (φ.val 1) + 1) * eps m) 1 :=
    ⟨standardBoundWith cRatScalarMulArch φ,
      standardBoundWith_spec_base cRatScalarMulArch φ⟩
  refine ⟨2 ^ m, ?_⟩
  apply regularSeqLe_of_indexed_pointwise_le
  intro n
  change BishopC.Le (φ.val (n + 1)) ((Nat.cast (2 ^ m) : Scalar))
  -- (A) |φ.val 1| + 1 ≤ (2^m : Scalar), from `standardBoundWith_spec_base` by
  -- multiplying by the positive reciprocal `2^m`.
  have hbase : BishopC.Le (COF.abs (φ.val 1) + 1) ((Nat.cast (2 ^ m) : Scalar)) := by
    have hmul := scalar_mul_le_mul_right hspec (scalar_natCast_nonneg (2 ^ m))
    rw [show ((COF.abs (φ.val 1) + 1) * eps m) * Nat.cast (2 ^ m)
          = (COF.abs (φ.val 1) + 1) * (eps m * Nat.cast (2 ^ m)) from by ring,
        eps_mul_natCast_twoPow m, mul_one, one_mul] at hmul
    exact hmul
  -- (B) φ.val (n+1) ≤ |φ.val 1| + 1, uniformly from regularity.
  have htri := scalar_abs_sub_le_three (φ.val (n + 1)) (φ.val 1) 0 0
  rw [show φ.val (n + 1) - (0 : Scalar) = φ.val (n + 1) from by ring,
      show φ.val 1 - (0 : Scalar) = φ.val 1 from by ring,
      show COF.abs ((0 : Scalar) - 0) = 0 from by
        rw [show (0 : Scalar) - 0 = 0 from by ring]; exact scalarCOFOSeed.abs_zero,
      show COF.abs (φ.val 1) + (0 : Scalar) = COF.abs (φ.val 1) from by ring] at htri
  have hreg : BishopC.Le (COF.abs (φ.val (n + 1) - φ.val 1)) (eps (n + 1) + eps 1) :=
    φ.regular (n + 1) 1
  have hepsle : BishopC.Le (eps (n + 1) + eps 1) (1 : Scalar) := by
    have h1 : BishopC.Le (eps (n + 1)) (eps 1) :=
      eps_le_of_le (Nat.succ_le_succ (Nat.zero_le n))
    have hsum : BishopC.Le (eps (n + 1) + eps 1) (eps 1 + eps 1) :=
      BishopC.le_add h1 (BishopC.le_refl (eps 1))
    rw [eps_succ_add_self 0, show eps 0 = (1 : Scalar) from rfl] at hsum
    exact hsum
  have hbound : BishopC.Le (COF.abs (φ.val (n + 1)))
      ((eps (n + 1) + eps 1) + COF.abs (φ.val 1)) :=
    BishopC.le_trans htri (BishopC.le_add hreg (BishopC.le_refl _))
  have hbound2 : BishopC.Le (COF.abs (φ.val (n + 1))) ((1 : Scalar) + COF.abs (φ.val 1)) :=
    BishopC.le_trans hbound (BishopC.le_add hepsle (BishopC.le_refl _))
  have hval_abs : BishopC.Le (COF.abs (φ.val (n + 1))) (COF.abs (φ.val 1) + 1) := by
    rw [show (1 : Scalar) + COF.abs (φ.val 1) = COF.abs (φ.val 1) + 1 from by ring] at hbound2
    exact hbound2
  exact BishopC.le_trans (scalarCOFOSeed.le_abs_self (φ.val (n + 1)))
    (BishopC.le_trans hval_abs hbase)

#print axioms BishopSec1P.exists_nat_geC

/-- **P14** — eventual constancy of the truncated telescope value.  Once the
gauge `n_k K` dominates `φ` (which happens for all `K ≥ N` by the Archimedean
bound `exists_nat_geC` and `nk_ge_self`), the truncated integrand collapses to
`χ · φ`.  Presented (`≈`) mirror of the abstract `prop42_eventually_chi_phi`. -/
theorem prop42_eventually_chi_phiC {φ χ : CReal} (hφ : ¬ CReal.ltE φ CReal.zero)
    {n_k : Nat → Nat} (hsucc : ∀ k, n_k k + 1 ≤ n_k (k + 1)) :
    ∃ k₀ : Nat, ∀ K, k₀ ≤ K →
      CReal.mul χ
          (CReal.sub (CReal.min φ (constSeq (Nat.cast (n_k K)))) (CReal.min φ CReal.zero))
        ≈ CReal.mul χ φ := by
  obtain ⟨N, hN⟩ := exists_nat_geC φ
  refine ⟨N, fun K hK => ?_⟩
  have hKN : RegularSeqLe φ (constSeq (Nat.cast (n_k K))) :=
    regularSeqLe_trans hN
      (natCast_le_of_leC (Nat.le_trans hK (nk_ge_self hsucc K)))
  refine mul_congr (relEventually_refl χ) ?_
  refine relEventually_trans _ (CReal.sub φ CReal.zero) _ ?_ (CReal.sub_zeroC φ)
  exact sub_congrC (CReal.min_eq_left_of_leC hKN) (CReal.min_zero_const hφ)

#print axioms BishopSec1P.prop42_eventually_chi_phiC

/-- Technical lemma used in the public import closure. -/
theorem repSeriesSum_of_eventually_constC {u : Nat → CReal} {c : CReal}
    (h : RepSeriesSum u) (k : Nat)
    (hev : ∀ N, k ≤ N → relEventually (regularSeqFinSum u N) c) :
    relEventually h.sum c := by
  let hc : RepSeriesSum u :=
    { sum := c
      tends :=
        { mod := fun _ => k
          close := fun j n hn => bc1_repClose_of_relEventually (hev n hn) (j + 1) } }
  exact repSeriesSum_unique h hc

#print axioms BishopSec1P.repSeriesSum_of_eventually_constC

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.add_seriesSum_valueC {X : Type*} {S : IntSpaceC X}
    {r r' : IntegrableRepC3 S} {x : X}
    (hr : RepSeriesSum (fun k => (r.fn k).toFun x))
    (hr' : RepSeriesSum (fun k => (r'.fn k).toFun x)) :
    RepSeriesSum (fun n => ((r.add r').fn n).toFun x) := by
  refine repSeriesSum_congr (bc1_seriesSum_interleave hr hr') (fun n => ?_)
  have hmap : ((r.add r').fn n).toFun x
      = bc1_seqMerge (fun k => (r.fn k).toFun x) (fun k => (r'.fn k).toFun x) n := by
    change (bc1_seqMerge r.fn r'.fn n).toFun x
        = bc1_seqMerge (fun k => (r.fn k).toFun x) (fun k => (r'.fn k).toFun x) n
    exact bc1_seqMerge_map (fun g : BFunC X => g.toFun x) r.fn r'.fn n
  rw [hmap]
  exact relEventually_refl _

#print axioms BishopSec1P.IntegrableRepC3.add_seriesSum_valueC

/-- Technical lemma used in the public import closure. -/
theorem cellAt_seriesSum_leC {a : Nat → Nat → CReal}
    (ha : ∀ i j, RegularSeqNonneg (a i j))
    (hrow : ∀ i, RepSeriesSum (a i))
    (hrowsum : RepSeriesSum (fun i => (hrow i).sum)) :
    RegularSeqLe (cellAt_repSeriesSum ha hrow hrowsum).sum hrowsum.sum :=
  repLe_of_tendsto_le (cellAt_repSeriesSum ha hrow hrowsum) hrowsum.sum
    (fun N => by
      have hb_nn : ∀ k, RegularSeqNonneg (a (BishopC.cellAt k).1 (BishopC.cellAt k).2) :=
        fun k => ha (BishopC.cellAt k).1 (BishopC.cellAt k).2
      have hmono_shell :
          RegularSeqLe
            (regularSeqFinSum
              (fun k => a (BishopC.cellAt k).1 (BishopC.cellAt k).2) N)
            (regularSeqFinSum
              (fun k => a (BishopC.cellAt k).1 (BishopC.cellAt k).2) (N * N + 2 * N)) :=
        regularSeqFinSum_mono_of_nonneg hb_nn (BishopC.self_le_sq_add N (2 * N))
      have hshell_grid :
          RegularSeqLe
            (regularSeqFinSum
              (fun k => a (BishopC.cellAt k).1 (BishopC.cellAt k).2) (N * N + 2 * N))
            (gridSumC a N) :=
        regularSeqLe_of_relEventually (regularSeqFinSum_cellAt_eq_gridSumC a N)
      exact regularSeqLe_trans hmono_shell
        (regularSeqLe_trans hshell_grid (gridSum_le_TC ha hrow hrowsum N)))

#print axioms BishopSec1P.cellAt_seriesSum_leC

/-- Technical lemma used in the public import closure. -/
theorem cellAt_seriesSum_geC {a : Nat → Nat → CReal}
    (ha : ∀ i j, RegularSeqNonneg (a i j))
    (hrow : ∀ i, RepSeriesSum (a i))
    (hrowsum : RepSeriesSum (fun i => (hrow i).sum)) :
    RegularSeqLe hrowsum.sum (cellAt_repSeriesSum ha hrow hrowsum).sum := by
  intro hcounter
  have hpos_order :
      regularSeqLtProp (cellAt_repSeriesSum ha hrow hrowsum).sum hrowsum.sum :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hpos_sub :
      CReal.ltE CReal.zero
        (subSeq hrowsum.sum (cellAt_repSeriesSum ha hrow hrowsum).sum) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  obtain ⟨k, hk⟩ :=
    CReal.archimedean_E
      (subSeq hrowsum.sum (cellAt_repSeriesSum ha hrow hrowsum).sum) hpos_sub
  have hb_nn : ∀ j, RegularSeqNonneg (a (BishopC.cellAt j).1 (BishopC.cellAt j).2) :=
    fun j => ha (BishopC.cellAt j).1 (BishopC.cellAt j).2
  let g := gridSum_gapC ha hrow hrowsum k
  have hgrid_le :
      RegularSeqLe (gridSumC a g.val)
        (cellAt_repSeriesSum ha hrow hrowsum).sum :=
    regularSeqLe_of_left_eventual
      (relEventually_symm _ _ (regularSeqFinSum_cellAt_eq_gridSumC a g.val))
      (repPartialSum_le_sum hb_nn (cellAt_repSeriesSum ha hrow hrowsum)
        (g.val * g.val + 2 * g.val))
  have hle_gap :
      RegularSeqLe
        (subSeq hrowsum.sum (cellAt_repSeriesSum ha hrow hrowsum).sum)
        (subSeq hrowsum.sum (gridSumC a g.val)) :=
    regularSeqLe_subSeq_right hrowsum.sum hgrid_le
  have heps_lt_gap :
      regularSeqLtProp (CReal.epsSeq k)
        (subSeq hrowsum.sum (gridSumC a g.val)) :=
    regularSeqLtProp_of_lt_of_le hk hle_gap
  exact regularSeqLtProp_irrefl (CReal.epsSeq k)
    (regularSeqLtProp_trans (CReal.epsSeq k)
      (subSeq hrowsum.sum (gridSumC a g.val)) (CReal.epsSeq k)
      heps_lt_gap g.property)

#print axioms BishopSec1P.cellAt_seriesSum_geC

/-- Technical lemma used in the public import closure. -/
theorem cellAt_seriesSum_eqC {a : Nat → Nat → CReal}
    (ha : ∀ i j, RegularSeqNonneg (a i j))
    (hrow : ∀ i, RepSeriesSum (a i))
    (hrowsum : RepSeriesSum (fun i => (hrow i).sum)) :
    (cellAt_repSeriesSum ha hrow hrowsum).sum ≈ hrowsum.sum :=
  regularSeqLe_antisymm_eventuallyC
    (cellAt_seriesSum_leC ha hrow hrowsum)
    (cellAt_seriesSum_geC ha hrow hrowsum)

#print axioms BishopSec1P.cellAt_seriesSum_eqC

/-- Technical lemma used in the public import closure. -/
theorem repSeriesSum_comparison_leC {a b : Nat → CReal}
    (ha : ∀ n, RegularSeqNonneg (a n))
    (hab : ∀ n, RegularSeqLe (a n) (b n))
    (hb : RepSeriesSum b) :
    RegularSeqLe (repSeriesSum_comparison ha hab hb).sum hb.sum :=
  repLe_of_tendsto_le (repSeriesSum_comparison ha hab hb) hb.sum
    (fun N =>
      have hb_nn : ∀ n, RegularSeqNonneg (b n) :=
        fun n => regularSeqNonneg_of_zero_le
          (regularSeqLe_trans (regularSeqLe_zero_of_nonneg (ha n)) (hab n))
      regularSeqLe_trans
        (regularSeqFinSum_le_of_termwise_le hab N)
        (repPartialSum_le_sum hb_nn hb N))

#print axioms BishopSec1P.repSeriesSum_comparison_leC

set_option maxHeartbeats 4000000 in
-- Pure signed Fubini over a `Nat × Nat → CReal` matrix.  This factors the
-- heavy pos/neg decomposition out of both value and integral Fubini arguments.
def cellAt_signedFubiniC {A : Nat → Nat → CReal}
    (hRowAbs : ∀ i, RepSeriesSum (fun j => CReal.abs (A i j)))
    (hRowSumAbs : RepSeriesSum (fun i => (hRowAbs i).sum))
    (hflat : RepSeriesSum (fun k => A (BishopC.cellAt k).1 (BishopC.cellAt k).2)) :
    { hV : RepSeriesSum (fun m => (seriesSum_of_absC (hRowAbs m)).sum) //
        relEventually hflat.sum hV.sum } := by
  let hRowPos : ∀ i, RepSeriesSum (fun j => CReal.max (A i j) CReal.zero) :=
    fun i => repSeriesSum_comparison
      (fun j => CReal.max_zero_nonneg_E (A i j))
      (fun j => regularSeqLe_of_not_ltQuot _ _ (CReal.max_le_abs_E (A i j)))
      (hRowAbs i)
  let hRowNeg : ∀ i, RepSeriesSum (fun j => CReal.neg (CReal.min (A i j) CReal.zero)) :=
    fun i => repSeriesSum_comparison
      (fun j => CReal.neg_min_zero_nonneg_E (A i j))
      (fun j => regularSeqLe_of_not_ltQuot _ _ (CReal.neg_min_le_abs_E (A i j)))
      (hRowAbs i)
  let hRowSumPos : RepSeriesSum (fun i => (hRowPos i).sum) :=
    repSeriesSum_comparison
      (fun i => repSeriesSum_nonneg
        (fun j => CReal.max_zero_nonneg_E (A i j)) (hRowPos i))
      (fun i => repSeriesSum_comparison_leC _ _ _)
      hRowSumAbs
  let hRowSumNeg : RepSeriesSum (fun i => (hRowNeg i).sum) :=
    repSeriesSum_comparison
      (fun i => repSeriesSum_nonneg
        (fun j => CReal.neg_min_zero_nonneg_E (A i j)) (hRowNeg i))
      (fun i => repSeriesSum_comparison_leC _ _ _)
      hRowSumAbs
  have eqPos : relEventually
      (cellAt_repSeriesSum
        (fun i j => CReal.max_zero_nonneg_E (A i j)) hRowPos hRowSumPos).sum
      hRowSumPos.sum :=
    cellAt_seriesSum_eqC _ hRowPos hRowSumPos
  have eqNeg : relEventually
      (cellAt_repSeriesSum
        (fun i j => CReal.neg_min_zero_nonneg_E (A i j)) hRowNeg hRowSumNeg).sum
      hRowSumNeg.sum :=
    cellAt_seriesSum_eqC _ hRowNeg hRowSumNeg
  have hrowdecomp : ∀ m, relEventually
      (seriesSum_of_absC (hRowAbs m)).sum
      (repSeriesSum_sub (hRowPos m) (hRowNeg m)).sum := fun m =>
    repSeriesSum_unique (seriesSum_of_absC (hRowAbs m))
      (repSeriesSum_congr (repSeriesSum_sub (hRowPos m) (hRowNeg m))
        (fun j => relEventually_symm _ _
          (max_sub_negmin_eq_self (A m j))))
  refine ⟨repSeriesSum_congr (repSeriesSum_sub hRowSumPos hRowSumNeg)
    (fun m => hrowdecomp m), ?_⟩
  have hflat_eq : relEventually hflat.sum
      (CReal.sub
        (cellAt_repSeriesSum
          (fun i j => CReal.max_zero_nonneg_E (A i j)) hRowPos hRowSumPos).sum
        (cellAt_repSeriesSum
          (fun i j => CReal.neg_min_zero_nonneg_E (A i j)) hRowNeg hRowSumNeg).sum) :=
    repSeriesSum_unique hflat
      (repSeriesSum_congr
        (repSeriesSum_sub
          (cellAt_repSeriesSum
            (fun i j => CReal.max_zero_nonneg_E (A i j)) hRowPos hRowSumPos)
          (cellAt_repSeriesSum
            (fun i j => CReal.neg_min_zero_nonneg_E (A i j)) hRowNeg hRowSumNeg))
        (fun k => relEventually_symm _ _
          (max_sub_negmin_eq_self (A (BishopC.cellAt k).1 (BishopC.cellAt k).2))))
  exact relEventually_trans _ _ _ hflat_eq
    (subSeq_respects_eventually _ _ _ _ eqPos eqNeg)

#print axioms BishopSec1P.cellAt_signedFubiniC

set_option maxHeartbeats 4000000 in
-- Integral Fubini for `seriesIntegrableC`, reduced to pure signed Fubini over
-- the matrix `S.I ((H i).fn j)`.
def seriesIntegrable_integralC {X : Type*} {S : IntSpaceC X}
    (H : Nat → IntegrableRepC3 S)
    (hs : RepSeriesSum (fun m => (H m).abs_integral_sum.sum)) :
    { hI : RepSeriesSum (fun m => (H m).integral) //
        (seriesIntegrableC H hs).integral ≈ hI.sum } := by
  let hRowAbsI : ∀ i, RepSeriesSum (fun j => CReal.abs (S.I ((H i).fn j))) :=
    fun i => repSeriesSum_comparison
      (fun j => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe (S.I ((H i).fn j))))
      (fun j => S.I_abs_ge ((H i).fn_mem j))
      (H i).abs_integral_sum
  let hRowSumAbsI : RepSeriesSum (fun i => (hRowAbsI i).sum) :=
    repSeriesSum_comparison
      (fun i => repSeriesSum_nonneg
        (fun j => regularSeqNonneg_of_zero_le
          (absSeq_nonnegative_regularSeqLe (S.I ((H i).fn j)))) (hRowAbsI i))
      (fun i => repSeriesSum_comparison_leC
        (fun j => regularSeqNonneg_of_zero_le
          (absSeq_nonnegative_regularSeqLe (S.I ((H i).fn j))))
        (fun j => S.I_abs_ge ((H i).fn_mem j))
        (H i).abs_integral_sum)
      hs
  let hflat : RepSeriesSum
      (fun k => S.I ((H (BishopC.cellAt k).1).fn (BishopC.cellAt k).2)) := by
    simpa [seriesIntegrableC] using (seriesIntegrableC H hs).integral_sum
  let W := cellAt_signedFubiniC hRowAbsI hRowSumAbsI hflat
  let hI : RepSeriesSum (fun m => (H m).integral) :=
    repSeriesSum_congr W.val
      (fun m => repSeriesSum_unique (H m).integral_sum (seriesSum_of_absC (hRowAbsI m)))
  refine ⟨hI, ?_⟩
  simpa [hI, hflat] using W.property

#print axioms BishopSec1P.seriesIntegrable_integralC

set_option maxHeartbeats 1000000 in
-- L1 series representative preserves integrals: `I(sum F_m)=sum I(F_m)`.
def seriesSumRep_L1_integralC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S)
    (hsum : RepSeriesSum (fun m => (F m).normL1)) :
    { hI : RepSeriesSum (fun m => (F m).integral) //
        (seriesSumRep_L1C F hsum).integral ≈ hI.sum } := by
  obtain ⟨hIG, eG⟩ := seriesIntegrable_integralC (G_mC F) (G_m_abs_seriesSumC F hsum)
  obtain ⟨hIT, eT⟩ := seriesIntegrable_integralC (tail_mC F) (tail_m_abs_seriesSumC F)
  have hsplit : ∀ m,
      CReal.add (G_mC F m).integral (tail_mC F m).integral ≈ (F m).integral := fun m => by
    have hG : (G_mC F m).integral = S.I (psi_mC F m) := by
      simpa [G_mC] using
        (IntegrableRepC3.ofL_integral (S := S) (g := psi_mC F m) (psi_m_memC F m))
    have hT : (tail_mC F m).integral ≈ CReal.sub (F m).integral (S.I (psi_mC F m)) := by
      simpa [tail_mC, psi_mC] using IntegrableRepC3.tailFrom_integralC (F m) (NmC F m)
    have hleft : CReal.add (G_mC F m).integral (tail_mC F m).integral ≈
        CReal.add (S.I (psi_mC F m)) (CReal.sub (F m).integral (S.I (psi_mC F m))) := by
      rw [hG]
      exact addSeq_respects_eventually _ _ _ _ (relEventually_refl _) hT
    have hcancel : CReal.add (S.I (psi_mC F m))
          (CReal.sub (F m).integral (S.I (psi_mC F m))) ≈
        (F m).integral := by
      have hq : mkQuot (CReal.add (S.I (psi_mC F m))
            (CReal.sub (F m).integral (S.I (psi_mC F m)))) =
          mkQuot (F m).integral := by
        change addQuot (mkQuot (S.I (psi_mC F m)))
            (subQuot (mkQuot (F m).integral) (mkQuot (S.I (psi_mC F m)))) =
          mkQuot (F m).integral
        letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
        let P : CRealQuot := mkQuot (S.I (psi_mC F m))
        let B : CRealQuot := mkQuot (F m).integral
        change P + (B - P) = B
        ring
      exact Quotient.exact hq
    exact relEventually_trans _ _ _ hleft hcancel
  let hAdd : RepSeriesSum (fun m => CReal.add (G_mC F m).integral (tail_mC F m).integral) :=
    repSeriesSum_add hIG hIT
  let hI : RepSeriesSum (fun m => (F m).integral) :=
    repSeriesSum_congr hAdd (fun m => Setoid.symm (hsplit m))
  refine ⟨hI, ?_⟩
  have hadd : (seriesSumRep_L1C F hsum).integral =
      CReal.add (seriesIntegrableC (G_mC F) (G_m_abs_seriesSumC F hsum)).integral
        (seriesIntegrableC (tail_mC F) (tail_m_abs_seriesSumC F)).integral := by
    exact IntegrableRepC3.integral_add
      (seriesIntegrableC (G_mC F) (G_m_abs_seriesSumC F hsum))
      (seriesIntegrableC (tail_mC F) (tail_m_abs_seriesSumC F))
  have hsum_eq : CReal.add
        (seriesIntegrableC (G_mC F) (G_m_abs_seriesSumC F hsum)).integral
        (seriesIntegrableC (tail_mC F) (tail_m_abs_seriesSumC F)).integral ≈
      CReal.add hIG.sum hIT.sum :=
    addSeq_respects_eventually _ _ _ _ eG eT
  rw [hadd]
  simpa [hI, hAdd] using hsum_eq

#print axioms BishopSec1P.seriesSumRep_L1_integralC

set_option maxHeartbeats 4000000 in
/-- Technical lemma used in the public import closure. -/
def seriesIntegrable_valueC {X : Type*} {S : IntSpaceC X} (H : Nat → IntegrableRepC3 S)
    (hs : RepSeriesSum (fun m => (H m).abs_integral_sum.sum)) {x : X}
    (hRowAbsX : ∀ i, RepSeriesSum (fun j => absSeq (((H i).fn j).toFun x)))
    (hRowSumAbsX : RepSeriesSum (fun i => (hRowAbsX i).sum))
    (hflatX : RepSeriesSum (fun k => ((seriesIntegrableC H hs).fn k).toFun x)) :
    { hV : RepSeriesSum (fun m => (seriesSum_of_absC (hRowAbsX m)).sum) //
        relEventually hflatX.sum hV.sum } := by
  let hRowPos : ∀ i, RepSeriesSum (fun j => CReal.max (((H i).fn j).toFun x) CReal.zero) :=
    fun i => repSeriesSum_comparison
      (fun j => CReal.max_zero_nonneg_E (((H i).fn j).toFun x))
      (fun j => regularSeqLe_of_not_ltQuot _ _ (CReal.max_le_abs_E (((H i).fn j).toFun x)))
      (hRowAbsX i)
  let hRowNeg : ∀ i, RepSeriesSum (fun j => CReal.neg (CReal.min (((H i).fn j).toFun x) CReal.zero)) :=
    fun i => repSeriesSum_comparison
      (fun j => CReal.neg_min_zero_nonneg_E (((H i).fn j).toFun x))
      (fun j => regularSeqLe_of_not_ltQuot _ _ (CReal.neg_min_le_abs_E (((H i).fn j).toFun x)))
      (hRowAbsX i)
  let hRowSumPos : RepSeriesSum (fun i => (hRowPos i).sum) :=
    repSeriesSum_comparison
      (fun i => repSeriesSum_nonneg
        (fun j => CReal.max_zero_nonneg_E (((H i).fn j).toFun x)) (hRowPos i))
      (fun i => repSeriesSum_comparison_leC _ _ _)
      hRowSumAbsX
  let hRowSumNeg : RepSeriesSum (fun i => (hRowNeg i).sum) :=
    repSeriesSum_comparison
      (fun i => repSeriesSum_nonneg
        (fun j => CReal.neg_min_zero_nonneg_E (((H i).fn j).toFun x)) (hRowNeg i))
      (fun i => repSeriesSum_comparison_leC _ _ _)
      hRowSumAbsX
  have eqPos : relEventually
      (cellAt_repSeriesSum
        (fun i j => CReal.max_zero_nonneg_E (((H i).fn j).toFun x)) hRowPos hRowSumPos).sum
      hRowSumPos.sum :=
    cellAt_seriesSum_eqC _ hRowPos hRowSumPos
  have eqNeg : relEventually
      (cellAt_repSeriesSum
        (fun i j => CReal.neg_min_zero_nonneg_E (((H i).fn j).toFun x)) hRowNeg hRowSumNeg).sum
      hRowSumNeg.sum :=
    cellAt_seriesSum_eqC _ hRowNeg hRowSumNeg
  have hrowdecomp : ∀ m, relEventually
      (seriesSum_of_absC (hRowAbsX m)).sum
      (repSeriesSum_sub (hRowPos m) (hRowNeg m)).sum := fun m =>
    repSeriesSum_unique (seriesSum_of_absC (hRowAbsX m))
      (repSeriesSum_congr (repSeriesSum_sub (hRowPos m) (hRowNeg m))
        (fun j => relEventually_symm _ _
          (max_sub_negmin_eq_self (((H m).fn j).toFun x))))
  refine ⟨repSeriesSum_congr (repSeriesSum_sub hRowSumPos hRowSumNeg)
    (fun m => hrowdecomp m), ?_⟩
  have hflat_eq : relEventually hflatX.sum
      (CReal.sub
        (cellAt_repSeriesSum
          (fun i j => CReal.max_zero_nonneg_E (((H i).fn j).toFun x)) hRowPos hRowSumPos).sum
        (cellAt_repSeriesSum
          (fun i j => CReal.neg_min_zero_nonneg_E (((H i).fn j).toFun x)) hRowNeg hRowSumNeg).sum) :=
    repSeriesSum_unique hflatX
      (repSeriesSum_congr
        (repSeriesSum_sub
          (cellAt_repSeriesSum
            (fun i j => CReal.max_zero_nonneg_E (((H i).fn j).toFun x)) hRowPos hRowSumPos)
          (cellAt_repSeriesSum
            (fun i j => CReal.neg_min_zero_nonneg_E (((H i).fn j).toFun x)) hRowNeg hRowSumNeg))
        (fun k => relEventually_symm _ _
          (max_sub_negmin_eq_self (((seriesIntegrableC H hs).fn k).toFun x))))
  exact relEventually_trans _ _ _ hflat_eq (sub_congrC eqPos eqNeg)

#print axioms BishopSec1P.seriesIntegrable_valueC

/-- Technical lemma used in the public import closure. -/
def repSeriesTendsto_finSumC {f : Nat → Nat → CReal} {l : Nat → CReal}
    (h : ∀ a, RepSeriesTendsto (f a) (l a)) :
    ∀ N, RepSeriesTendsto (fun M => regularSeqFinSum (fun a => f a M) N)
      (regularSeqFinSum l N)
  | 0 => h 0
  | N + 1 => bc1_repSeriesTendsto_add (repSeriesTendsto_finSumC h N) (h (N + 1))

#print axioms BishopSec1P.repSeriesTendsto_finSumC

/-- Technical lemma used in the public import closure. -/
def cellAt_rowsumC {A : Nat → Nat → CReal} (hA : ∀ i j, RegularSeqNonneg (A i j))
    (hflat : RepSeriesSum (fun k => A (BishopC.cellAt k).1 (BishopC.cellAt k).2)) :
    RepSeriesSum (fun a => (row_seriesSumC hA hflat a).sum) := by
  let g : Nat → CReal := fun a => (row_seriesSumC hA hflat a).sum
  have hb_nn : ∀ k, RegularSeqNonneg (A (BishopC.cellAt k).1 (BishopC.cellAt k).2) :=
    fun k => hA (BishopC.cellAt k).1 (BishopC.cellAt k).2
  have hg_nn : ∀ a, RegularSeqNonneg (g a) :=
    fun a => repSeriesSum_nonneg (fun j => hA a j) (row_seriesSumC hA hflat a)
  -- gridSumC A P ≤ hflat.sum
  have hgrid_le : ∀ P, RegularSeqLe (gridSumC A P) hflat.sum := fun P =>
    regularSeqLe_of_left_eventual
      (relEventually_symm _ _ (regularSeqFinSum_cellAt_eq_gridSumC A P))
      (repPartialSum_le_sum hb_nn hflat (P * P + 2 * P))
  -- gridSumC A N ≤ Σ_{a<N} g a
  have hgrid_le_psg : ∀ N, RegularSeqLe (gridSumC A N) (regularSeqFinSum g N) := fun N =>
    regularSeqFinSum_le_of_termwise_le
      (fun i => repPartialSum_le_sum (fun j => hA i j) (row_seriesSumC hA hflat i) N) N
  refine repSeriesSum_of_partialCauchy (repIsCauchy_of_mono_bounded_gap
    (v := regularSeqFinSum g) (T := hflat.sum)
    (fun {_ _} hpq => regularSeqFinSum_mono_of_nonneg hg_nn hpq) ?_ ?_)
  · -- bounded: Σ_{a<N} g a ≤ hflat.sum
    intro N
    refine Le_of_tendstoHalf_leC
      (repSeriesTendsto_finSumC (fun a => (row_seriesSumC hA hflat a).tends) N)
      (repSeriesTendsto_constC hflat.sum) (fun M' => ?_)
    refine regularSeqLe_trans ?_ (hgrid_le (Nat.max N M'))
    refine regularSeqLe_trans
      (regularSeqFinSum_le_of_termwise_le
        (fun a => regularSeqFinSum_mono_of_nonneg (fun j => hA a j)
          (Nat.le_max_right N M')) N) ?_
    exact regularSeqFinSum_mono_of_nonneg
      (fun a => regularSeqFinSum_nonneg_of_terms (fun j => hA a j) (Nat.max N M'))
      (Nat.le_max_left N M')
  · -- gap: hflat.sum − Σ_{a<M} g a < halfPow k
    intro k
    refine ⟨hflat.tends.mod k, ?_⟩
    have hclose :
        regularSeqLtProp
          (subSeq hflat.sum
            (regularSeqFinSum (fun m => A (BishopC.cellAt m).1 (BishopC.cellAt m).2)
              (hflat.tends.mod k * hflat.tends.mod k + 2 * hflat.tends.mod k)))
          (constSeq (eps k)) :=
      regularSeqLtProp_sub_of_repClose_succ k
        (hflat.tends.close k
          (hflat.tends.mod k * hflat.tends.mod k + 2 * hflat.tends.mod k) (by omega))
    have hle2 :
        RegularSeqLe (subSeq hflat.sum (gridSumC A (hflat.tends.mod k)))
          (subSeq hflat.sum
            (regularSeqFinSum (fun m => A (BishopC.cellAt m).1 (BishopC.cellAt m).2)
              (hflat.tends.mod k * hflat.tends.mod k + 2 * hflat.tends.mod k))) :=
      regularSeqLe_subSeq_right hflat.sum
        (regularSeqLe_of_relEventually
          (regularSeqFinSum_cellAt_eq_gridSumC A (hflat.tends.mod k)))
    have hle1 :
        RegularSeqLe (subSeq hflat.sum (regularSeqFinSum g (hflat.tends.mod k)))
          (subSeq hflat.sum (gridSumC A (hflat.tends.mod k))) :=
      regularSeqLe_subSeq_right hflat.sum (hgrid_le_psg (hflat.tends.mod k))
    have hcombined :
        regularSeqLtProp
          (subSeq hflat.sum (regularSeqFinSum g (hflat.tends.mod k))) (constSeq (eps k)) :=
      regularSeqLtProp_of_le_of_lt (regularSeqLe_trans hle1 hle2) hclose
    simpa [halfPow, CReal.epsSeq] using hcombined

#print axioms BishopSec1P.cellAt_rowsumC

set_option maxHeartbeats 800000 in
/-- Technical lemma used in the public import closure. -/
def seriesIntegrable_value_of_flatC {X : Type*} {S : IntSpaceC X}
    (H : Nat → IntegrableRepC3 S)
    (hs : RepSeriesSum (fun m => (H m).abs_integral_sum.sum)) {x : X}
    (hflatabs : RepSeriesSum (fun k => absSeq (((seriesIntegrableC H hs).fn k).toFun x))) :=
  seriesIntegrable_valueC H hs
    (fun i => row_seriesSumC
      (fun p q => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe (((H p).fn q).toFun x))) hflatabs i)
    (cellAt_rowsumC
      (fun p q => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe (((H p).fn q).toFun x))) hflatabs)
    (seriesSum_of_absC hflatabs)
#print axioms BishopSec1P.seriesIntegrable_value_of_flatC

set_option maxHeartbeats 800000 in
/-- Technical lemma used in the public import closure. -/
def seriesSumRep_L1_valueC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S)
    (hsum : RepSeriesSum (fun m => (F m).normL1)) {x : X}
    (hflatabs : RepSeriesSum (fun n => absSeq (((seriesSumRep_L1C F hsum).fn n).toFun x))) :
    { hV : RepSeriesSum (fun m => addSeq
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe (((G_mC F p).fn q).toFun x)))
          (add_absSeriesSum_leftC hflatabs) m)).sum
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe (((tail_mC F p).fn q).toFun x)))
          (add_absSeriesSum_rightC hflatabs) m)).sum) //
        relEventually (seriesSum_of_absC hflatabs).sum hV.sum } := by
  obtain ⟨hVG, eG⟩ := seriesIntegrable_value_of_flatC (G_mC F) (G_m_abs_seriesSumC F hsum)
    (add_absSeriesSum_leftC hflatabs)
  obtain ⟨hVT, eT⟩ := seriesIntegrable_value_of_flatC (tail_mC F) (tail_m_abs_seriesSumC F)
    (add_absSeriesSum_rightC hflatabs)
  refine ⟨repSeriesSum_add hVG hVT, ?_⟩
  refine relEventually_trans _ _ _
    (repSeriesSum_unique (seriesSum_of_absC hflatabs)
      (IntegrableRepC3.add_seriesSum_valueC
        (seriesSum_of_absC (add_absSeriesSum_leftC hflatabs))
        (seriesSum_of_absC (add_absSeriesSum_rightC hflatabs)))) ?_
  exact addSeq_respects_eventually _ _ _ _ eG eT
#print axioms BishopSec1P.seriesSumRep_L1_valueC

/-- Technical lemma used in the public import closure. -/
theorem seriesSumRep_L1_hsplit_valueC {X : Type*} {S : IntSpaceC X}
    (F : Nat → IntegrableRepC3 S) (m : Nat) {x : X}
    (hFv : RepSeriesSum (fun n => ((F m).fn n).toFun x)) :
    CReal.add (IntegrableRepC3.ofL_value (psi_m_memC F m) x).1.sum
        (IntegrableRepC3.tailFrom_valueC (F m) (NmC F m) x hFv).1.sum
      ≈ hFv.sum := by
  have hG_eq := (IntegrableRepC3.ofL_value (psi_m_memC F m) x).2
  have hT_eq := (IntegrableRepC3.tailFrom_valueC (F m) (NmC F m) x hFv).2
  have hcancel :
      addSeq ((psi_mC F m).toFun x)
          (CReal.sub hFv.sum ((BFunC.seqSum (F m).fn (NmC F m)).toFun x))
        ≈ hFv.sum := by
    have hq :
        mkQuot (addSeq ((psi_mC F m).toFun x)
            (CReal.sub hFv.sum ((BFunC.seqSum (F m).fn (NmC F m)).toFun x)))
          = mkQuot hFv.sum := by
      change addQuot (mkQuot ((psi_mC F m).toFun x))
          (subQuot (mkQuot hFv.sum) (mkQuot ((BFunC.seqSum (F m).fn (NmC F m)).toFun x)))
        = mkQuot hFv.sum
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let P : CRealQuot := mkQuot ((psi_mC F m).toFun x)
      let B : CRealQuot := mkQuot hFv.sum
      change P + (B - P) = B
      ring
    exact Quotient.exact hq
  exact relEventually_trans _ _ _
    (addSeq_respects_eventually _ _ _ _ hG_eq hT_eq) hcancel
#print axioms BishopSec1P.seriesSumRep_L1_hsplit_valueC

set_option maxHeartbeats 1600000 in
/-- Technical lemma used in the public import closure. -/
noncomputable def IntegrableRepC3.prop_4_2_rep_value_seriesC {X : Type*} {S : IntSpaceC X}
    {A : BishopC.BSet X} (hA : IntegrableSet1C S A) (f : IntegrableRepC3 S) (n_k : Nat → Nat)
    (hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_k k)
    (hmono : ∀ k, n_k k ≤ n_k (k + 1)) {x : X}
    (hflatabs : RepSeriesSum (fun n => absSeq
      (((seriesSumRep_L1C (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k)
        (IntegrableRepC3.prop_4_2_lambda_sumC A hA f n_k hnk_ge)).fn n).toFun x)))
    (hχ : RepSeriesSum (fun n => (hA.rep.fn n).toFun x))
    (hf : RepSeriesSum (fun n => (f.fn n).toFun x)) :
    { hser : RepSeriesSum
        (fun m => (IntegrableRepC3.prop_4_2_lambda_valueC hA f n_k hmono x hχ hf m).1.sum) //
        relEventually (seriesSum_of_absC hflatabs).sum hser.sum } := by
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_valueC (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k)
    (IntegrableRepC3.prop_4_2_lambda_sumC A hA f n_k hnk_ge) hflatabs
  refine ⟨repSeriesSum_congr hV (fun m => ?_), eV⟩
  refine relEventually_trans _ _ _
    (relEventually_symm _ _
      (seriesSumRep_L1_hsplit_valueC (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k) m
        (IntegrableRepC3.prop_4_2_lambda_valueC hA f n_k hmono x hχ hf m).1)) ?_
  exact addSeq_respects_eventually _ _ _ _
    (relEventually_symm _ _
      (repSeriesSum_unique
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe
              (((G_mC (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k) p).fn q).toFun x)))
          (add_absSeriesSum_leftC hflatabs) m))
        (IntegrableRepC3.ofL_value
          (psi_m_memC (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k) m) x).1))
    (relEventually_symm _ _
      (repSeriesSum_unique
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe
              (((tail_mC (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k) p).fn q).toFun x)))
          (add_absSeriesSum_rightC hflatabs) m))
        (IntegrableRepC3.tailFrom_valueC
          (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k m)
          (NmC (IntegrableRepC3.prop_4_2_lambda_kC A hA f n_k) m) x
          (IntegrableRepC3.prop_4_2_lambda_valueC hA f n_k hmono x hχ hf m).1).1))
#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_rep_value_seriesC

set_option maxHeartbeats 1600000 in
/-- Technical lemma used in the public import closure. -/
theorem IntegrableRepC3.prop_4_2_chi_f_rep_valueC {X : Type*} {S : IntSpaceC X}
    {A : BishopC.BSet X} (hA : IntegrableSet1C S A) (f : IntegrableRepC3 S) (hnn : RepNonnegC f)
    {x : X}
    (hflatabs : RepSeriesSum (fun n =>
      absSeq (((IntegrableRepC3.prop_4_2_chi_f_repC A hA f).fn n).toFun x)))
    (hχabs : RepSeriesSum (fun n => absSeq ((hA.rep.fn n).toFun x)))
    (hfabs : RepSeriesSum (fun n => absSeq ((f.fn n).toFun x))) :
    (seriesSum_of_absC hflatabs).sum
      ≈ CReal.mul (seriesSum_of_absC hχabs).sum (seriesSum_of_absC hfabs).sum := by
  have hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ f.prop_4_2_n_kC k := by
    intro k; cases k with
    | zero => exact Nat.le_refl _
    | succ k' => exact Nat.le_max_left _ _
  have hsucc : ∀ k, f.prop_4_2_n_kC k + 1 ≤ f.prop_4_2_n_kC (k + 1) := fun k => Nat.le_max_right _ _
  have hmono : ∀ k, f.prop_4_2_n_kC k ≤ f.prop_4_2_n_kC (k + 1) :=
    fun k => Nat.le_trans (Nat.le_succ _) (hsucc k)
  let hχ := seriesSum_of_absC hχabs
  let hf := seriesSum_of_absC hfabs
  have hχ01 : hχ.sum ≈ CReal.zero ∨ hχ.sum ≈ CReal.one := by
    rcases (hA.valid x hχabs).1 with hS1 | hS2
    · exact Or.inr ((hA.valid x hχabs).2.1 hS1 hχ)
    · exact Or.inl ((hA.valid x hχabs).2.2 hS2 hχ)
  have hφnn : RegularSeqNonneg hf.sum := hnn x hfabs hf
  have hm0 : RegularSeqNonneg (constSeq (Nat.cast (f.prop_4_2_n_kC 0))) := natCast_nonnegC _
  have hmono_R : ∀ k, RegularSeqLe (constSeq (Nat.cast (f.prop_4_2_n_kC k)))
      (constSeq (Nat.cast (f.prop_4_2_n_kC (k + 1)))) := fun k => natCast_le_of_leC (hmono k)
  obtain ⟨hser, eser⟩ :=
    IntegrableRepC3.prop_4_2_rep_value_seriesC hA f f.prop_4_2_n_kC hnk_ge hmono hflatabs hχ hf
  have key : ∀ K, regularSeqFinSum
      (fun m => (IntegrableRepC3.prop_4_2_lambda_valueC hA f f.prop_4_2_n_kC hmono x hχ hf m).1.sum) K
      ≈ CReal.mul hχ.sum
          (CReal.sub (CReal.min hf.sum (constSeq (Nat.cast (f.prop_4_2_n_kC K))))
            (CReal.min hf.sum CReal.zero)) := by
    intro K
    exact relEventually_trans _ _ _
      (bc1_regularSeqFinSum_congr_terms _ _
        (fun m => (IntegrableRepC3.prop_4_2_lambda_valueC hA f f.prop_4_2_n_kC hmono x hχ hf m).2) K)
      (CReal.prop42_telescopeC hf.sum hχ.sum
        (fun j => constSeq (Nat.cast (f.prop_4_2_n_kC j))) hm0 hmono_R hχ01 K)
  obtain ⟨k₀, hk₀⟩ :=
    prop42_eventually_chi_phiC (φ := hf.sum) (χ := hχ.sum) (n_k := f.prop_4_2_n_kC) hφnn hsucc
  have hev : ∀ K, k₀ ≤ K → regularSeqFinSum
      (fun m => (IntegrableRepC3.prop_4_2_lambda_valueC hA f f.prop_4_2_n_kC hmono x hχ hf m).1.sum) K
      ≈ CReal.mul hχ.sum hf.sum :=
    fun K hK => relEventually_trans _ _ _ (key K) (hk₀ K hK)
  have efinal : hser.sum ≈ CReal.mul hχ.sum hf.sum :=
    repSeriesSum_of_eventually_constC hser k₀ hev
  exact relEventually_trans _ _ _ eser efinal
#print axioms BishopSec1P.IntegrableRepC3.prop_4_2_chi_f_rep_valueC

/-- Technical lemma used in the public import closure. -/
noncomputable def relIntegralC {X : Type*} {S : IntSpaceC X}
    (C : BishopC.BSet X) (hC : IntegrableSet1C S C) (f : IntegrableRepC3 S) : CReal :=
  (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral
#print axioms BishopSec1P.relIntegralC

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_complement_additiveC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C) (f : IntegrableRepC3 S) :
    CReal.add (relIntegralC C hC f)
        (f.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC f)).integral
      ≈ f.integral := by
  show CReal.add (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral
      (f.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC f)).integral ≈ f.integral
  rw [IntegrableRepC3.integral_sub]
  have hq : mkQuot (CReal.add (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral
        (addSeq f.integral (negSeq (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral)))
      = mkQuot f.integral := by
    change addQuot (mkQuot (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral)
        (addQuot (mkQuot f.integral)
          (negQuot (mkQuot (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral)))
      = mkQuot f.integral
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    let A : CRealQuot := mkQuot (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral
    let B : CRealQuot := mkQuot f.integral
    change A + (B + (-A)) = B
    ring
  exact Quotient.exact hq
#print axioms BishopSec1P.relIntegral_complement_additiveC

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_integralC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C) (f : IntegrableRepC3 S)
    (hnn : RepNonnegC f) :
    RegularSeqLe (relIntegralC C hC f) f.integral := by
  show RegularSeqLe (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).integral f.integral
  refine prop_1_11C
    (isFull_interC (isFull_interC
      (IntegrableRepC3.prop_4_2_chi_f_repC C hC f).domain_isFull f.domain_isFull)
      hC.rep.domain_isFull)
    (IntegrableRepC3.prop_4_2_chi_f_repC C hC f) f ?_
  intro x hx hr hr'
  obtain ⟨⟨hxrep, hxf⟩, hxχ⟩ := hx
  obtain ⟨_, ⟨hflatabs⟩⟩ := hxrep
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  have hval := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC f hnn hflatabs hχabs hfabs
  have eL : relEventually hr.sum (seriesSum_of_absC hflatabs).sum :=
    repSeriesSum_unique hr (seriesSum_of_absC hflatabs)
  have eR : relEventually hr'.sum (seriesSum_of_absC hfabs).sum :=
    repSeriesSum_unique hr' (seriesSum_of_absC hfabs)
  have hfnn : RegularSeqNonneg (seriesSum_of_absC hfabs).sum :=
    hnn x hfabs (seriesSum_of_absC hfabs)
  have hχ01 : relEventually (seriesSum_of_absC hχabs).sum CReal.zero
      ∨ relEventually (seriesSum_of_absC hχabs).sum CReal.one := by
    rcases (hC.valid x hχabs).1 with hS1 | hS2
    · exact Or.inr ((hC.valid x hχabs).2.1 hS1 (seriesSum_of_absC hχabs))
    · exact Or.inl ((hC.valid x hχabs).2.2 hS2 (seriesSum_of_absC hχabs))
  have hmid : RegularSeqLe
      (CReal.mul (seriesSum_of_absC hχabs).sum (seriesSum_of_absC hfabs).sum)
      (seriesSum_of_absC hfabs).sum := by
    rcases hχ01 with h0 | h1
    · have e0 : relEventually
          (CReal.mul (seriesSum_of_absC hχabs).sum (seriesSum_of_absC hfabs).sum)
          CReal.zero :=
        relEventually_trans _ _ _ (mul_congr h0 (Setoid.refl (seriesSum_of_absC hfabs).sum))
          (zero_mul_equivC (seriesSum_of_absC hfabs).sum)
      exact regularSeqLe_trans (regularSeqLe_of_relEventually e0)
        (regularSeqLe_zero_of_nonneg hfnn)
    · have e1 : relEventually
          (CReal.mul (seriesSum_of_absC hχabs).sum (seriesSum_of_absC hfabs).sum)
          (seriesSum_of_absC hfabs).sum :=
        relEventually_trans _ _ _ (mul_congr h1 (Setoid.refl (seriesSum_of_absC hfabs).sum))
          (CReal.one_mul (seriesSum_of_absC hfabs).sum)
      exact regularSeqLe_of_relEventually e1
  have hLeft : relEventually hr.sum
      (CReal.mul (seriesSum_of_absC hχabs).sum (seriesSum_of_absC hfabs).sum) :=
    relEventually_trans _ _ _ eL hval
  refine regularSeqLe_trans (regularSeqLe_of_relEventually hLeft) ?_
  refine regularSeqLe_trans hmid ?_
  exact regularSeqLe_of_relEventually (relEventually_symm _ _ eR)

#print axioms BishopSec1P.relIntegral_le_integralC

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLe_mul_right_of_nonnegC {a b c : CReal}
    (hab : RegularSeqLe a b) (hc : RegularSeqNonneg c) :
    RegularSeqLe (CReal.mul a c) (CReal.mul b c) := by
  have hd : RegularSeqNonneg (subSeq b a) := hab
  have hmul : RegularSeqNonneg (CReal.mul (subSeq b a) c) :=
    CReal.mul_nonneg_E hd hc
  have heq : relEventually
      (subSeq (CReal.mul b c) (CReal.mul a c))
      (CReal.mul (subSeq b a) c) := by
    have hq :
        mkQuot (subSeq (CReal.mul b c) (CReal.mul a c))
          = mkQuot (CReal.mul (subSeq b a) c) := by
      change subQuot
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot b) (mkQuot c))
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot a) (mkQuot c))
        = mulQuotConcreteWith cRatScalarMulArch
            (subQuot (mkQuot b) (mkQuot a)) (mkQuot c)
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let C : CRealQuot := mkQuot c
      change B * C - A * C = (B - A) * C
      ring
    exact Quotient.exact hq
  exact regularSeqNonneg_of_eventual heq hmul

#print axioms BishopSec1P.regularSeqLe_mul_right_of_nonnegC

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_mono_leC {X : Type*} {S : IntSpaceC X}
    {D D' : BishopC.BSet X}
    (hD : IntegrableSet1C S D) (hD' : IntegrableSet1C S D')
    (f : IntegrableRepC3 S) (hnn : RepNonnegC f)
    (hle : ∀ x, ∀ (hd : RepSeriesSum (fun n => (hD.rep.fn n).toFun x))
            (hd' : RepSeriesSum (fun n => (hD'.rep.fn n).toFun x)),
            RegularSeqLe hd.sum hd'.sum) :
    RegularSeqLe (relIntegralC D hD f) (relIntegralC D' hD' f) := by
  show RegularSeqLe (IntegrableRepC3.prop_4_2_chi_f_repC D hD f).integral
    (IntegrableRepC3.prop_4_2_chi_f_repC D' hD' f).integral
  refine prop_1_11C
    (isFull_interC (isFull_interC (isFull_interC (isFull_interC
      (IntegrableRepC3.prop_4_2_chi_f_repC D hD f).domain_isFull
      (IntegrableRepC3.prop_4_2_chi_f_repC D' hD' f).domain_isFull)
      f.domain_isFull) hD.rep.domain_isFull) hD'.rep.domain_isFull)
    (IntegrableRepC3.prop_4_2_chi_f_repC D hD f)
    (IntegrableRepC3.prop_4_2_chi_f_repC D' hD' f) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨hxrepD, hxrepD'⟩, hxf⟩, hxχD⟩, hxχD'⟩ := hx
  obtain ⟨_, ⟨hflatabsD⟩⟩ := hxrepD
  obtain ⟨_, ⟨hflatabsD'⟩⟩ := hxrepD'
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχDabs⟩⟩ := hxχD
  obtain ⟨_, ⟨hχD'abs⟩⟩ := hxχD'
  have hvalD := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hD f hnn hflatabsD hχDabs hfabs
  have hvalD' := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hD' f hnn hflatabsD' hχD'abs hfabs
  have hfnn : RegularSeqNonneg (seriesSum_of_absC hfabs).sum :=
    hnn x hfabs (seriesSum_of_absC hfabs)
  have hcc : RegularSeqLe (seriesSum_of_absC hχDabs).sum (seriesSum_of_absC hχD'abs).sum :=
    hle x (seriesSum_of_absC hχDabs) (seriesSum_of_absC hχD'abs)
  have hmono : RegularSeqLe
      (CReal.mul (seriesSum_of_absC hχDabs).sum (seriesSum_of_absC hfabs).sum)
      (CReal.mul (seriesSum_of_absC hχD'abs).sum (seriesSum_of_absC hfabs).sum) :=
    regularSeqLe_mul_right_of_nonnegC hcc hfnn
  have eLD : relEventually hr.sum
      (CReal.mul (seriesSum_of_absC hχDabs).sum (seriesSum_of_absC hfabs).sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr (seriesSum_of_absC hflatabsD)) hvalD
  have eLD' : relEventually hr'.sum
      (CReal.mul (seriesSum_of_absC hχD'abs).sum (seriesSum_of_absC hfabs).sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr' (seriesSum_of_absC hflatabsD')) hvalD'
  refine regularSeqLe_trans (regularSeqLe_of_relEventually eLD) ?_
  refine regularSeqLe_trans hmono ?_
  exact regularSeqLe_of_relEventually (relEventually_symm _ _ eLD')

#print axioms BishopSec1P.relIntegral_mono_leC

/-- Technical lemma used in the public import closure. -/
theorem CReal.one_nonnegC : ¬ CReal.ltE CReal.one CReal.zero := by
  intro hlt
  exact CReal.ltE_irrefl CReal.zero
    (CReal.ltE_trans CReal.one_pos_E hlt)

#print axioms BishopSec1P.CReal.one_nonnegC

/-- Technical lemma used in the public import closure. -/
theorem CReal.min_selfC (a : CReal) : CReal.min a a ≈ a :=
  regularSeqLe_antisymm_eventuallyC (CReal.min_le_leftC a a)
    (CReal.le_minC (regularSeqLe_refl a) (regularSeqLe_refl a))

#print axioms BishopSec1P.CReal.min_selfC

/-- Technical lemma used in the public import closure. -/
theorem CReal.min_zero_leftC {a : CReal} (ha : ¬ CReal.ltE a CReal.zero) :
    CReal.min CReal.zero a ≈ CReal.zero :=
  regularSeqLe_antisymm_eventuallyC (CReal.min_le_leftC CReal.zero a)
    (CReal.le_minC (regularSeqLe_refl CReal.zero)
      (regularSeqLe_zero_of_nonneg ha))

#print axioms BishopSec1P.CReal.min_zero_leftC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
def min2_absSeriesSum_innerC {X : Type*} {S : IntSpaceC X}
    {r s : IntegrableRepC3 S} {x : X}
    (habs : RepSeriesSum
      (fun n => absSeq (((r.min2 s).fn n).toFun x))) :
    RepSeriesSum
      (fun n =>
        absSeq ((((r.add s).sub ((r.sub s).absVal)).fn n).toFun x)) := by
  have hhalf_nonneg : ¬ CReal.ltE CReal.half CReal.zero := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero
      (CReal.ltE_trans CReal.half_pos_E hlt)
  refine repSeriesSum_congr
    (repSeriesSum_smul (CReal.add CReal.one CReal.one) habs)
    (fun n => ?_)
  refine relEventually_symm _ _ ?_
  set B : CReal :=
    (((r.add s).sub ((r.sub s).absVal)).fn n).toFun x
  have hmin_val :
      ((r.min2 s).fn n).toFun x = CReal.mul CReal.half B := rfl
  show CReal.mul (CReal.add CReal.one CReal.one)
      (absSeq (((r.min2 s).fn n).toFun x)) ≈ absSeq B
  rw [hmin_val]
  have hstep1 : absSeq (CReal.mul CReal.half B)
      ≈ CReal.mul CReal.half (absSeq B) :=
    relEventually_trans _ _ _ (CReal.abs_mul CReal.half B)
      (mul_congr (CReal.abs_of_nonneg_E hhalf_nonneg) (Setoid.refl (absSeq B)))
  refine relEventually_trans _ _ _
    (mul_congr (Setoid.refl (CReal.add CReal.one CReal.one)) hstep1) ?_
  have hq :
      mkQuot (CReal.mul (CReal.add CReal.one CReal.one)
          (CReal.mul CReal.half (absSeq B)))
        = mkQuot (absSeq B) := by
    change mulQuotConcreteWith cRatScalarMulArch
        (addQuot (mkQuot CReal.one) (mkQuot CReal.one))
        (mulQuotConcreteWith cRatScalarMulArch (mkQuot CReal.half)
          (mkQuot (absSeq B)))
      = mkQuot (absSeq B)
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    let U : CRealQuot := mkQuot (absSeq B)
    change ((1 : CRealQuot) + 1) * (halfQuot * U) = U
    have h2half : ((1 : CRealQuot) + 1) * halfQuot = 1 := by
      calc ((1 : CRealQuot) + 1) * halfQuot
          = halfQuot + halfQuot := by ring
        _ = 1 := halfQuot_add_half
    rw [← mul_assoc, h2half, one_mul]
  exact Quotient.exact hq

#print axioms BishopSec1P.min2_absSeriesSum_innerC

/-- Technical lemma used in the public import closure. -/
def min2_absSeriesSum_leftC {X : Type*} {S : IntSpaceC X}
    {r s : IntegrableRepC3 S} {x : X}
    (habs : RepSeriesSum
      (fun n => absSeq (((r.min2 s).fn n).toFun x))) :
    RepSeriesSum (fun k => absSeq ((r.fn k).toFun x)) :=
  add_absSeriesSum_leftC (add_absSeriesSum_leftC (min2_absSeriesSum_innerC habs))

#print axioms BishopSec1P.min2_absSeriesSum_leftC

/-- Technical lemma used in the public import closure. -/
def min2_absSeriesSum_rightC {X : Type*} {S : IntSpaceC X}
    {r s : IntegrableRepC3 S} {x : X}
    (habs : RepSeriesSum
      (fun n => absSeq (((r.min2 s).fn n).toFun x))) :
    RepSeriesSum (fun k => absSeq ((s.fn k).toFun x)) :=
  add_absSeriesSum_rightC (add_absSeriesSum_leftC (min2_absSeriesSum_innerC habs))

#print axioms BishopSec1P.min2_absSeriesSum_rightC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
noncomputable def IntegrableSet1_andC {X : Type*} {S : IntSpaceC X}
    {A B : BishopC.BSet X}
    (hA : IntegrableSet1C S A) (hB : IntegrableSet1C S B) :
    IntegrableSet1C S (BSet.and A B) where
  full := by
    have h : (BSet.and A B).S1 ∪ (BSet.and A B).S2
        = (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
      ext x
      change x ∈ (A.S1 ∩ B.S1) ∨
          x ∈ ((A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1) ∪ (A.S2 ∩ B.S2))
        ↔ (x ∈ A.S1 ∨ x ∈ A.S2) ∧ (x ∈ B.S1 ∨ x ∈ B.S2)
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
    exact isFull_interC hA.full hB.full
  rep := IntegrableRepC3.min2 hA.rep hB.rep
  valid := by
    intro x habs
    have hrA_abs := min2_absSeriesSum_leftC habs
    have hrB_abs := min2_absSeriesSum_rightC habs
    have hrA := seriesSum_of_absC hrA_abs
    have hrB := seriesSum_of_absC hrB_abs
    have hvA := hA.valid x hrA_abs
    have hvB := hB.valid x hrB_abs
    obtain ⟨hm, hmeq⟩ := IntegrableRepC3.min2_valueC hA.rep hB.rep x hrA hrB
    refine ⟨?_, ?_, ?_⟩
    · rcases hvA.1 with hxA1 | hxA2 <;> rcases hvB.1 with hxB1 | hxB2
      · exact Or.inl ⟨hxA1, hxB1⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hxA1, hxB2⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨hxA2, hxB1⟩))
      · exact Or.inr (Or.inr ⟨hxA2, hxB2⟩)
    · intro hx_S1 h_sum
      have e1 : relEventually h_sum.sum (CReal.min hrA.sum hrB.sum) :=
        relEventually_trans _ _ _ (repSeriesSum_unique h_sum hm) hmeq
      have e2 : relEventually (CReal.min hrA.sum hrB.sum)
          (CReal.min CReal.one CReal.one) :=
        min_congrC (hvA.2.1 hx_S1.1 hrA) (hvB.2.1 hx_S1.2 hrB)
      exact relEventually_trans _ _ _ e1
        (relEventually_trans _ _ _ e2 (CReal.min_selfC CReal.one))
    · intro hx_S2 h_sum
      have e1 : relEventually h_sum.sum (CReal.min hrA.sum hrB.sum) :=
        relEventually_trans _ _ _ (repSeriesSum_unique h_sum hm) hmeq
      rcases hx_S2 with (⟨hxA1, hxB2⟩ | ⟨hxA2, hxB1⟩) | ⟨hxA2, hxB2⟩
      · have e2 : relEventually (CReal.min hrA.sum hrB.sum)
            (CReal.min CReal.one CReal.zero) :=
          min_congrC (hvA.2.1 hxA1 hrA) (hvB.2.2 hxB2 hrB)
        exact relEventually_trans _ _ _ e1
          (relEventually_trans _ _ _ e2
            (CReal.min_zero_const CReal.one_nonnegC))
      · have e2 : relEventually (CReal.min hrA.sum hrB.sum)
            (CReal.min CReal.zero CReal.one) :=
          min_congrC (hvA.2.2 hxA2 hrA) (hvB.2.1 hxB1 hrB)
        exact relEventually_trans _ _ _ e1
          (relEventually_trans _ _ _ e2
            (CReal.min_zero_leftC CReal.one_nonnegC))
      · have e2 : relEventually (CReal.min hrA.sum hrB.sum)
            (CReal.min CReal.zero CReal.zero) :=
          min_congrC (hvA.2.2 hxA2 hrA) (hvB.2.2 hxB2 hrB)
        exact relEventually_trans _ _ _ e1
          (relEventually_trans _ _ _ e2 (CReal.min_selfC CReal.zero))

#print axioms BishopSec1P.IntegrableSet1_andC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem chi_and_value_validC {X : Type*} {S : IntSpaceC X}
    {A B : BishopC.BSet X}
    (hA : IntegrableSet1C S A) (hB : IntegrableSet1C S B)
    (hAB : IntegrableSet1C S (BSet.and A B)) {x : X}
    (hAabs : RepSeriesSum (fun n => absSeq ((hA.rep.fn n).toFun x)))
    (hBabs : RepSeriesSum (fun n => absSeq ((hB.rep.fn n).toFun x)))
    (hABabs : RepSeriesSum (fun n => absSeq ((hAB.rep.fn n).toFun x))) :
    relEventually (seriesSum_of_absC hABabs).sum
      (CReal.min (seriesSum_of_absC hAabs).sum
        (seriesSum_of_absC hBabs).sum) := by
  set sA := seriesSum_of_absC hAabs with hsA
  set sB := seriesSum_of_absC hBabs with hsB
  set sAB := seriesSum_of_absC hABabs with hsAB
  rcases (hAB.valid x hABabs).1 with hS1 | hS2
  · have hAB1 : relEventually sAB.sum CReal.one :=
      (hAB.valid x hABabs).2.1 hS1 sAB
    obtain ⟨xA1, xB1⟩ := hS1
    have hA1 : relEventually sA.sum CReal.one :=
      (hA.valid x hAabs).2.1 xA1 sA
    have hB1 : relEventually sB.sum CReal.one :=
      (hB.valid x hBabs).2.1 xB1 sB
    exact relEventually_trans _ _ _ hAB1
      (relEventually_symm _ _
        (relEventually_trans _ _ _ (min_congrC hA1 hB1)
          (CReal.min_selfC CReal.one)))
  · have hAB0 : relEventually sAB.sum CReal.zero :=
      (hAB.valid x hABabs).2.2 hS2 sAB
    refine relEventually_trans _ _ _ hAB0 (relEventually_symm _ _ ?_)
    rcases hS2 with (⟨xA1, xB2⟩ | ⟨xA2, xB1⟩) | ⟨xA2, xB2⟩
    · have hA1 : relEventually sA.sum CReal.one :=
        (hA.valid x hAabs).2.1 xA1 sA
      have hB0 : relEventually sB.sum CReal.zero :=
        (hB.valid x hBabs).2.2 xB2 sB
      exact relEventually_trans _ _ _ (min_congrC hA1 hB0)
        (CReal.min_zero_const CReal.one_nonnegC)
    · have hA0 : relEventually sA.sum CReal.zero :=
        (hA.valid x hAabs).2.2 xA2 sA
      have hB1 : relEventually sB.sum CReal.one :=
        (hB.valid x hBabs).2.1 xB1 sB
      exact relEventually_trans _ _ _ (min_congrC hA0 hB1)
        (CReal.min_zero_leftC CReal.one_nonnegC)
    · have hA0 : relEventually sA.sum CReal.zero :=
        (hA.valid x hAabs).2.2 xA2 sA
      have hB0 : relEventually sB.sum CReal.zero :=
        (hB.valid x hBabs).2.2 xB2 sB
      exact relEventually_trans _ _ _ (min_congrC hA0 hB0)
        (CReal.min_selfC CReal.zero)

#print axioms BishopSec1P.chi_and_value_validC

set_option maxHeartbeats 2000000 in
/-- Technical lemma used in the public import closure. -/
noncomputable def IntegrableSet1_orC {X : Type*} {S : IntSpaceC X}
    {A B : BishopC.BSet X} (hA : IntegrableSet1C S A) (hB : IntegrableSet1C S B) :
    IntegrableSet1C S (BishopC.BSet.or A B) where
  full := by
    have h : (BishopC.BSet.or A B).S1 ∪ (BishopC.BSet.or A B).S2
        = (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
      ext x
      change (x ∈ (A.S1 ∩ B.S1) ∪ (A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1)) ∨ x ∈ (A.S2 ∩ B.S2)
        ↔ (x ∈ A.S1 ∨ x ∈ A.S2) ∧ (x ∈ B.S1 ∨ x ∈ B.S2)
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
    exact isFull_interC hA.full hB.full
  rep := hA.rep.add hB.rep |>.sub (IntegrableRepC3.min2 hA.rep hB.rep)
  valid := by
    intro x habs
    have hrA_abs := add_absSeriesSum_leftC (add_absSeriesSum_leftC habs)
    have hrB_abs := add_absSeriesSum_rightC (add_absSeriesSum_leftC habs)
    have hrA := seriesSum_of_absC hrA_abs
    have hrB := seriesSum_of_absC hrB_abs
    have hvA := hA.valid x hrA_abs
    have hvB := hB.valid x hrB_abs
    obtain ⟨hm, hmeq⟩ := IntegrableRepC3.min2_valueC hA.rep hB.rep x hrA hrB
    let hor := add_seriesSum_valueC3 (add_seriesSum_valueC3 hrA hrB) (neg_seriesSum_valueC3 hm)
    refine ⟨?_, ?_, ?_⟩
    · rcases hvA.1 with hxA1 | hxA2 <;> rcases hvB.1 with hxB1 | hxB2
      · exact Or.inl (Or.inl (Or.inl ⟨hxA1, hxB1⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hxA1, hxB2⟩))
      · exact Or.inl (Or.inr ⟨hxA2, hxB1⟩)
      · exact Or.inr ⟨hxA2, hxB2⟩
    · intro hx_S1 h_sum
      refine relEventually_trans _ _ _ (repSeriesSum_unique h_sum hor) ?_
      show relEventually (addSeq (addSeq hrA.sum hrB.sum) (negSeq hm.sum)) CReal.one
      rcases hx_S1 with (⟨hxA1, hxB1⟩ | ⟨hxA1, hxB2⟩) | ⟨hxA2, hxB1⟩
      · have hmc : relEventually hm.sum CReal.one :=
          relEventually_trans _ _ _ hmeq
            (relEventually_trans _ _ _ (min_congrC (hvA.2.1 hxA1 hrA) (hvB.2.1 hxB1 hrB))
              (CReal.min_selfC CReal.one))
        have hq : mkQuot (addSeq (addSeq hrA.sum hrB.sum) (negSeq hm.sum)) = mkQuot CReal.one := by
          have qA : mkQuot hrA.sum = mkQuot CReal.one := Quotient.sound (hvA.2.1 hxA1 hrA)
          have qB : mkQuot hrB.sum = mkQuot CReal.one := Quotient.sound (hvB.2.1 hxB1 hrB)
          have qC : mkQuot hm.sum = mkQuot CReal.one := Quotient.sound hmc
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          change addQuot (addQuot (mkQuot hrA.sum) (mkQuot hrB.sum)) (negQuot (mkQuot hm.sum))
            = mkQuot CReal.one
          rw [qA, qB, qC]
          change ((1 : CRealQuot) + 1) + (-(1 : CRealQuot)) = 1
          ring
        exact Quotient.exact hq
      · have hmc : relEventually hm.sum CReal.zero :=
          relEventually_trans _ _ _ hmeq
            (relEventually_trans _ _ _ (min_congrC (hvA.2.1 hxA1 hrA) (hvB.2.2 hxB2 hrB))
              (CReal.min_zero_const CReal.one_nonnegC))
        have hq : mkQuot (addSeq (addSeq hrA.sum hrB.sum) (negSeq hm.sum)) = mkQuot CReal.one := by
          have qA : mkQuot hrA.sum = mkQuot CReal.one := Quotient.sound (hvA.2.1 hxA1 hrA)
          have qB : mkQuot hrB.sum = mkQuot CReal.zero := Quotient.sound (hvB.2.2 hxB2 hrB)
          have qC : mkQuot hm.sum = mkQuot CReal.zero := Quotient.sound hmc
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          change addQuot (addQuot (mkQuot hrA.sum) (mkQuot hrB.sum)) (negQuot (mkQuot hm.sum))
            = mkQuot CReal.one
          rw [qA, qB, qC]
          change ((1 : CRealQuot) + 0) + (-(0 : CRealQuot)) = 1
          ring
        exact Quotient.exact hq
      · have hmc : relEventually hm.sum CReal.zero :=
          relEventually_trans _ _ _ hmeq
            (relEventually_trans _ _ _ (min_congrC (hvA.2.2 hxA2 hrA) (hvB.2.1 hxB1 hrB))
              (CReal.min_zero_leftC CReal.one_nonnegC))
        have hq : mkQuot (addSeq (addSeq hrA.sum hrB.sum) (negSeq hm.sum)) = mkQuot CReal.one := by
          have qA : mkQuot hrA.sum = mkQuot CReal.zero := Quotient.sound (hvA.2.2 hxA2 hrA)
          have qB : mkQuot hrB.sum = mkQuot CReal.one := Quotient.sound (hvB.2.1 hxB1 hrB)
          have qC : mkQuot hm.sum = mkQuot CReal.zero := Quotient.sound hmc
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          change addQuot (addQuot (mkQuot hrA.sum) (mkQuot hrB.sum)) (negQuot (mkQuot hm.sum))
            = mkQuot CReal.one
          rw [qA, qB, qC]
          change ((0 : CRealQuot) + 1) + (-(0 : CRealQuot)) = 1
          ring
        exact Quotient.exact hq
    · intro hx_S2 h_sum
      refine relEventually_trans _ _ _ (repSeriesSum_unique h_sum hor) ?_
      show relEventually (addSeq (addSeq hrA.sum hrB.sum) (negSeq hm.sum)) CReal.zero
      obtain ⟨hxA2, hxB2⟩ := hx_S2
      have hmc : relEventually hm.sum CReal.zero :=
        relEventually_trans _ _ _ hmeq
          (relEventually_trans _ _ _ (min_congrC (hvA.2.2 hxA2 hrA) (hvB.2.2 hxB2 hrB))
            (CReal.min_selfC CReal.zero))
      have hq : mkQuot (addSeq (addSeq hrA.sum hrB.sum) (negSeq hm.sum)) = mkQuot CReal.zero := by
        have qA : mkQuot hrA.sum = mkQuot CReal.zero := Quotient.sound (hvA.2.2 hxA2 hrA)
        have qB : mkQuot hrB.sum = mkQuot CReal.zero := Quotient.sound (hvB.2.2 hxB2 hrB)
        have qC : mkQuot hm.sum = mkQuot CReal.zero := Quotient.sound hmc
        letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
        change addQuot (addQuot (mkQuot hrA.sum) (mkQuot hrB.sum)) (negQuot (mkQuot hm.sum))
          = mkQuot CReal.zero
        rw [qA, qB, qC]
        change ((0 : CRealQuot) + 0) + (-(0 : CRealQuot)) = 0
        ring
      exact Quotient.exact hq

#print axioms BishopSec1P.IntegrableSet1_orC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
noncomputable def IntegrableSet1_subC {X : Type*} {S : IntSpaceC X}
    {A B : BishopC.BSet X}
    (hA : IntegrableSet1C S A) (hB : IntegrableSet1C S B) :
    IntegrableSet1C S (BSet.sub A B) where
  full := by
    have h : (BSet.sub A B).S1 ∪ (BSet.sub A B).S2 = (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
      ext x
      change x ∈ (A.S1 ∩ B.S2) ∨ x ∈ ((A.S1 ∩ B.S1) ∪ (A.S2 ∩ B.S2) ∪ (A.S2 ∩ B.S1)) ↔
        (x ∈ A.S1 ∨ x ∈ A.S2) ∧ (x ∈ B.S1 ∨ x ∈ B.S2)
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
    exact isFull_interC hA.full hB.full
  rep := hA.rep.sub (IntegrableRepC3.min2 hA.rep hB.rep)
  valid := by
    intro x habs
    have hrA_abs := add_absSeriesSum_leftC habs
    have hmin_abs := neg_absSeriesSumC (add_absSeriesSum_rightC habs)
    have hrB_abs := min2_absSeriesSum_rightC hmin_abs
    have hrA := seriesSum_of_absC hrA_abs
    have hrB := seriesSum_of_absC hrB_abs
    have hvA := hA.valid x hrA_abs
    have hvB := hB.valid x hrB_abs
    obtain ⟨hm, hmeq⟩ := IntegrableRepC3.min2_valueC hA.rep hB.rep x hrA hrB
    let hsub := add_seriesSum_valueC3 hrA (neg_seriesSum_valueC3 hm)
    refine ⟨?_, ?_, ?_⟩
    · rcases hvA.1 with hxA1 | hxA2 <;> rcases hvB.1 with hxB1 | hxB2
      · exact Or.inr (Or.inl (Or.inl ⟨hxA1, hxB1⟩))
      · exact Or.inl ⟨hxA1, hxB2⟩
      · exact Or.inr (Or.inr ⟨hxA2, hxB1⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨hxA2, hxB2⟩))
    · intro hx_S1 h_sum
      refine relEventually_trans _ _ _ (repSeriesSum_unique h_sum hsub) ?_
      show relEventually (addSeq hrA.sum (negSeq hm.sum)) CReal.one
      have hmc : relEventually hm.sum CReal.zero :=
        relEventually_trans _ _ _ hmeq
          (relEventually_trans _ _ _ (min_congrC (hvA.2.1 hx_S1.1 hrA) (hvB.2.2 hx_S1.2 hrB))
            (CReal.min_zero_const CReal.one_nonnegC))
      have hq : mkQuot (addSeq hrA.sum (negSeq hm.sum)) = mkQuot CReal.one := by
        have qA : mkQuot hrA.sum = mkQuot CReal.one := Quotient.sound (hvA.2.1 hx_S1.1 hrA)
        have qC : mkQuot hm.sum = mkQuot CReal.zero := Quotient.sound hmc
        letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
        change addQuot (mkQuot hrA.sum) (negQuot (mkQuot hm.sum)) = mkQuot CReal.one
        rw [qA, qC]
        change (1 : CRealQuot) + (-(0 : CRealQuot)) = 1
        ring
      exact Quotient.exact hq
    · intro hx_S2 h_sum
      refine relEventually_trans _ _ _ (repSeriesSum_unique h_sum hsub) ?_
      show relEventually (addSeq hrA.sum (negSeq hm.sum)) CReal.zero
      rcases hx_S2 with (⟨hxA1, hxB1⟩ | ⟨hxA2, hxB2⟩) | ⟨hxA2, hxB1⟩
      · have hmc : relEventually hm.sum CReal.one :=
          relEventually_trans _ _ _ hmeq
            (relEventually_trans _ _ _ (min_congrC (hvA.2.1 hxA1 hrA) (hvB.2.1 hxB1 hrB))
              (CReal.min_selfC CReal.one))
        have hq : mkQuot (addSeq hrA.sum (negSeq hm.sum)) = mkQuot CReal.zero := by
          have qA : mkQuot hrA.sum = mkQuot CReal.one := Quotient.sound (hvA.2.1 hxA1 hrA)
          have qC : mkQuot hm.sum = mkQuot CReal.one := Quotient.sound hmc
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          change addQuot (mkQuot hrA.sum) (negQuot (mkQuot hm.sum)) = mkQuot CReal.zero
          rw [qA, qC]
          change (1 : CRealQuot) + (-(1 : CRealQuot)) = 0
          ring
        exact Quotient.exact hq
      · have hmc : relEventually hm.sum CReal.zero :=
          relEventually_trans _ _ _ hmeq
            (relEventually_trans _ _ _ (min_congrC (hvA.2.2 hxA2 hrA) (hvB.2.2 hxB2 hrB))
              (CReal.min_selfC CReal.zero))
        have hq : mkQuot (addSeq hrA.sum (negSeq hm.sum)) = mkQuot CReal.zero := by
          have qA : mkQuot hrA.sum = mkQuot CReal.zero := Quotient.sound (hvA.2.2 hxA2 hrA)
          have qC : mkQuot hm.sum = mkQuot CReal.zero := Quotient.sound hmc
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          change addQuot (mkQuot hrA.sum) (negQuot (mkQuot hm.sum)) = mkQuot CReal.zero
          rw [qA, qC]
          change (0 : CRealQuot) + (-(0 : CRealQuot)) = 0
          ring
        exact Quotient.exact hq
      · have hmc : relEventually hm.sum CReal.zero :=
          relEventually_trans _ _ _ hmeq
            (relEventually_trans _ _ _ (min_congrC (hvA.2.2 hxA2 hrA) (hvB.2.1 hxB1 hrB))
              (CReal.min_zero_leftC CReal.one_nonnegC))
        have hq : mkQuot (addSeq hrA.sum (negSeq hm.sum)) = mkQuot CReal.zero := by
          have qA : mkQuot hrA.sum = mkQuot CReal.zero := Quotient.sound (hvA.2.2 hxA2 hrA)
          have qC : mkQuot hm.sum = mkQuot CReal.zero := Quotient.sound hmc
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          change addQuot (mkQuot hrA.sum) (negQuot (mkQuot hm.sum)) = mkQuot CReal.zero
          rw [qA, qC]
          change (0 : CRealQuot) + (-(0 : CRealQuot)) = 0
          ring
        exact Quotient.exact hq

#print axioms BishopSec1P.IntegrableSet1_subC

/-- Technical lemma used in the public import closure. -/
def IsMeasurableSetC {X : Type*} (S : IntSpaceC X) (B : BishopC.BSet X) : Type _ :=
  ∀ (A : BishopC.BSet X), IntegrableSet1C S A → IntegrableSet1C S (BishopC.BSet.and A B)

/-- Technical lemma used in the public import closure. -/
noncomputable def isMeasurableSet_of_integrableC {X : Type*} {S : IntSpaceC X}
    {B : BishopC.BSet X} (hB : IntegrableSet1C S B) : IsMeasurableSetC S B :=
  fun A hA => IntegrableSet1_andC hA hB

#print axioms BishopSec1P.isMeasurableSet_of_integrableC

set_option maxHeartbeats 2000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_and_mono_or_stepC {X : Type*} {S : IntSpaceC X} {B : BishopC.BSet X}
    (hB : IsMeasurableSetC S B) {D A : BishopC.BSet X}
    (hD : IntegrableSet1C S D) (hA : IntegrableSet1C S A)
    (f : IntegrableRepC3 S) (hnn : RepNonnegC f) :
    RegularSeqLe (relIntegralC (BishopC.BSet.and D B) (hB D hD) f)
      (relIntegralC (BishopC.BSet.and (BishopC.BSet.or D A) B)
        (hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)) f) := by
  show RegularSeqLe
    (IntegrableRepC3.prop_4_2_chi_f_repC (BishopC.BSet.and D B) (hB D hD) f).integral
    (IntegrableRepC3.prop_4_2_chi_f_repC (BishopC.BSet.and (BishopC.BSet.or D A) B)
      (hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)) f).integral
  refine prop_1_11C
    (isFull_interC (isFull_interC (isFull_interC (isFull_interC (isFull_interC
      (IntegrableRepC3.prop_4_2_chi_f_repC (BishopC.BSet.and D B) (hB D hD) f).domain_isFull
      (IntegrableRepC3.prop_4_2_chi_f_repC (BishopC.BSet.and (BishopC.BSet.or D A) B)
        (hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)) f).domain_isFull)
      f.domain_isFull)
      (hB D hD).rep.domain_isFull)
      (hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)).rep.domain_isFull)
      hA.rep.domain_isFull)
    (IntegrableRepC3.prop_4_2_chi_f_repC (BishopC.BSet.and D B) (hB D hD) f)
    (IntegrableRepC3.prop_4_2_chi_f_repC (BishopC.BSet.and (BishopC.BSet.or D A) B)
      (hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)) f) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨⟨hxDB, hxDAB⟩, hxf⟩, hxχDB⟩, hxχDAB⟩, hxχA⟩ := hx
  obtain ⟨_, ⟨hflatabsDB⟩⟩ := hxDB
  obtain ⟨_, ⟨hflatabsDAB⟩⟩ := hxDAB
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχDBabs⟩⟩ := hxχDB
  obtain ⟨_, ⟨hχDABabs⟩⟩ := hxχDAB
  obtain ⟨_, ⟨hχAabs⟩⟩ := hxχA
  have hvalDB := IntegrableRepC3.prop_4_2_chi_f_rep_valueC (hB D hD) f hnn hflatabsDB hχDBabs hfabs
  have hvalDAB := IntegrableRepC3.prop_4_2_chi_f_rep_valueC
    (hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)) f hnn hflatabsDAB hχDABabs hfabs
  have hfnn : RegularSeqNonneg (seriesSum_of_absC hfabs).sum :=
    hnn x hfabs (seriesSum_of_absC hfabs)
  have hcc : RegularSeqLe (seriesSum_of_absC hχDBabs).sum (seriesSum_of_absC hχDABabs).sum := by
    rcases ((hB D hD).valid x hχDBabs).1 with hS1 | hS2
    · have hDB1 : relEventually (seriesSum_of_absC hχDBabs).sum CReal.one :=
        ((hB D hD).valid x hχDBabs).2.1 hS1 (seriesSum_of_absC hχDBabs)
      obtain ⟨xD1, xB1⟩ := hS1
      have hxDA1 : x ∈ (BishopC.BSet.or D A).S1 := by
        rcases (hA.valid x hχAabs).1 with hA1 | hA2
        · exact Or.inl (Or.inl ⟨xD1, hA1⟩)
        · exact Or.inl (Or.inr ⟨xD1, hA2⟩)
      have hDAB1 : relEventually (seriesSum_of_absC hχDABabs).sum CReal.one :=
        ((hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)).valid x hχDABabs).2.1
          ⟨hxDA1, xB1⟩ (seriesSum_of_absC hχDABabs)
      exact regularSeqLe_trans (regularSeqLe_of_relEventually hDB1)
        (regularSeqLe_of_relEventually (relEventually_symm _ _ hDAB1))
    · have hDB0 : relEventually (seriesSum_of_absC hχDBabs).sum CReal.zero :=
        ((hB D hD).valid x hχDBabs).2.2 hS2 (seriesSum_of_absC hχDBabs)
      refine regularSeqLe_trans (regularSeqLe_of_relEventually hDB0) ?_
      rcases ((hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)).valid x hχDABabs).1
        with hS1' | hS2'
      · have hDAB1 : relEventually (seriesSum_of_absC hχDABabs).sum CReal.one :=
          ((hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)).valid x hχDABabs).2.1 hS1'
            (seriesSum_of_absC hχDABabs)
        exact regularSeqLe_trans (regularSeqLe_zero_of_nonneg CReal.one_nonnegC)
          (regularSeqLe_of_relEventually (relEventually_symm _ _ hDAB1))
      · have hDAB0 : relEventually (seriesSum_of_absC hχDABabs).sum CReal.zero :=
          ((hB (BishopC.BSet.or D A) (IntegrableSet1_orC hD hA)).valid x hχDABabs).2.2 hS2'
            (seriesSum_of_absC hχDABabs)
        exact regularSeqLe_of_relEventually (relEventually_symm _ _ hDAB0)
  have hmono : RegularSeqLe
      (CReal.mul (seriesSum_of_absC hχDBabs).sum (seriesSum_of_absC hfabs).sum)
      (CReal.mul (seriesSum_of_absC hχDABabs).sum (seriesSum_of_absC hfabs).sum) :=
    regularSeqLe_mul_right_of_nonnegC hcc hfnn
  have eLD : relEventually hr.sum
      (CReal.mul (seriesSum_of_absC hχDBabs).sum (seriesSum_of_absC hfabs).sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr (seriesSum_of_absC hflatabsDB)) hvalDB
  have eLD' : relEventually hr'.sum
      (CReal.mul (seriesSum_of_absC hχDABabs).sum (seriesSum_of_absC hfabs).sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr' (seriesSum_of_absC hflatabsDAB)) hvalDAB
  refine regularSeqLe_trans (regularSeqLe_of_relEventually eLD) ?_
  refine regularSeqLe_trans hmono ?_
  exact regularSeqLe_of_relEventually (relEventually_symm _ _ eLD')

#print axioms BishopSec1P.relIntegral_and_mono_or_stepC

/-- Technical lemma used in the public import closure. -/
def bigOrFinC {X : Type*} (A : Nat → BishopC.BSet X) : Nat → BishopC.BSet X
  | 0 => A 0
  | n + 1 => BishopC.BSet.or (bigOrFinC A n) (A (n + 1))

/-- Technical lemma used in the public import closure. -/
noncomputable def bigOrFin_intC {X : Type*} {S : IntSpaceC X} (A : Nat → BishopC.BSet X)
    (hA : ∀ k, IntegrableSet1C S (A k)) : ∀ n, IntegrableSet1C S (bigOrFinC A n)
  | 0 => hA 0
  | n + 1 => IntegrableSet1_orC (bigOrFin_intC A hA n) (hA (n + 1))

#print axioms BishopSec1P.bigOrFin_intC

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_bigOrFin_monoC {X : Type*} {S : IntSpaceC X} {B : BishopC.BSet X}
    (hB : IsMeasurableSetC S B) (A : Nat → BishopC.BSet X) (hA : ∀ k, IntegrableSet1C S (A k))
    (f : IntegrableRepC3 S) (hnn : RepNonnegC f) (k : Nat) :
    RegularSeqLe
      (relIntegralC (BishopC.BSet.and (bigOrFinC A k) B) (hB (bigOrFinC A k) (bigOrFin_intC A hA k)) f)
      (relIntegralC (BishopC.BSet.and (bigOrFinC A (k + 1)) B)
        (hB (bigOrFinC A (k + 1)) (bigOrFin_intC A hA (k + 1))) f) :=
  relIntegral_and_mono_or_stepC hB (bigOrFin_intC A hA k) (hA (k + 1)) f hnn

#print axioms BishopSec1P.relIntegral_bigOrFin_monoC

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_bigOrFin_le_integralC {X : Type*} {S : IntSpaceC X} {B : BishopC.BSet X}
    (hB : IsMeasurableSetC S B) (A : Nat → BishopC.BSet X) (hA : ∀ k, IntegrableSet1C S (A k))
    (f : IntegrableRepC3 S) (hnn : RepNonnegC f) (k : Nat) :
    RegularSeqLe
      (relIntegralC (BishopC.BSet.and (bigOrFinC A k) B) (hB (bigOrFinC A k) (bigOrFin_intC A hA k)) f)
      f.integral :=
  relIntegral_le_integralC (hB (bigOrFinC A k) (bigOrFin_intC A hA k)) f hnn

#print axioms BishopSec1P.relIntegral_bigOrFin_le_integralC

set_option maxHeartbeats 1200000 in
/-- Technical lemma used in the public import closure. -/
theorem const_measure_diff_midC (a b c nn : CReal)
    (hnn_nonneg : RegularSeqNonneg nn) (hcb : RegularSeqLe c b) (hcn : RegularSeqLe c nn)
    (h01 : relEventually a CReal.zero ∨ relEventually a CReal.one) :
    RegularSeqLe (CReal.mul a b) (addSeq (CReal.mul nn a) (subSeq b c)) := by
  rcases h01 with h0 | h1
  · have e_lhs : CReal.mul a b ≈ CReal.zero :=
      Setoid.trans (mul_congr h0 (Setoid.refl b)) (zero_mul_equivC b)
    have hann : RegularSeqNonneg a :=
      regularSeqNonneg_of_eventual h0 regularSeqNonneg_zero
    have hprod_nn : RegularSeqNonneg (CReal.mul nn a) := CReal.mul_nonneg_E hnn_nonneg hann
    have hrhs_nn : RegularSeqNonneg (addSeq (CReal.mul nn a) (subSeq b c)) :=
      regularSeqNonneg_add hprod_nn hcb
    have hev : relEventually
        (subSeq (addSeq (CReal.mul nn a) (subSeq b c)) (CReal.mul a b))
        (addSeq (CReal.mul nn a) (subSeq b c)) :=
      Setoid.trans (sub_congrC (Setoid.refl _) e_lhs) (subSeq_zero_right_eventually _)
    exact regularSeqNonneg_of_eventual hev hrhs_nn
  · have e_lhs : CReal.mul a b ≈ b :=
      Setoid.trans (mul_congr h1 (Setoid.refl b)) (CReal.one_mul b)
    have e_na : CReal.mul nn a ≈ nn :=
      Setoid.trans (mul_congr (Setoid.refl _) h1) (CReal.mul_one nn)
    have hD : relEventually
        (subSeq (addSeq (CReal.mul nn a) (subSeq b c)) (CReal.mul a b)) (subSeq nn c) := by
      have s1 : relEventually
          (subSeq (addSeq (CReal.mul nn a) (subSeq b c)) (CReal.mul a b))
          (subSeq (addSeq nn (subSeq b c)) b) :=
        sub_congrC (add_congr e_na (Setoid.refl _)) e_lhs
      have s2 : relEventually (subSeq (addSeq nn (subSeq b c)) b) (subSeq nn c) := by
        have hq : mkQuot (subSeq (addSeq nn (subSeq b c)) b) = mkQuot (subSeq nn c) := by
          change subQuot (addQuot (mkQuot nn) (subQuot (mkQuot b) (mkQuot c))) (mkQuot b)
            = subQuot (mkQuot nn) (mkQuot c)
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          let N : CRealQuot := mkQuot nn
          let B : CRealQuot := mkQuot b
          let Cc : CRealQuot := mkQuot c
          change (N + (B - Cc)) - B = N - Cc
          ring
        exact Quotient.exact hq
      exact relEventually_trans _ _ _ s1 s2
    exact regularSeqNonneg_of_eventual hD hcn

#print axioms BishopSec1P.const_measure_diff_midC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_const_measure_plus_diffC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C) (g : IntegrableRepC3 S)
    (hnn : RepNonnegC g) (n : Nat) :
    RegularSeqLe (relIntegralC C hC g)
      (((hC.rep.smul (constSeq (Nat.cast n))).add (g.sub (g.cutNatVal n))).integral) := by
  show RegularSeqLe (IntegrableRepC3.prop_4_2_chi_f_repC C hC g).integral
    (((hC.rep.smul (constSeq (Nat.cast n))).add (g.sub (g.cutNatVal n))).integral)
  refine prop_1_11C
    (isFull_interC (isFull_interC
      (IntegrableRepC3.prop_4_2_chi_f_repC C hC g).domain_isFull g.domain_isFull)
      hC.rep.domain_isFull)
    (IntegrableRepC3.prop_4_2_chi_f_repC C hC g)
    ((hC.rep.smul (constSeq (Nat.cast n))).add (g.sub (g.cutNatVal n))) ?_
  intro x hx hr hr'
  obtain ⟨⟨hxrep, hxg⟩, hxχ⟩ := hx
  obtain ⟨_, ⟨hflatabs⟩⟩ := hxrep
  obtain ⟨_, ⟨hgabs⟩⟩ := hxg
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  let χv := seriesSum_of_absC hχabs
  let gv := seriesSum_of_absC hgabs
  -- LHS = χ_C·g
  have hval := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC g hnn hflatabs hχabs hgabs
  have eL : relEventually hr.sum (CReal.mul χv.sum gv.sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr (seriesSum_of_absC hflatabs)) hval
  -- Technical note.
  obtain ⟨hgcut, hgcut_eq⟩ :=
    g.cutConstVal_signed_valueC (constSeq (Nat.cast n)) (natCast_nonnegC n) x gv
  -- Technical note.
  let hmodel : RepSeriesSum
      (fun k => (((hC.rep.smul (constSeq (Nat.cast n))).add (g.sub (g.cutNatVal n))).fn k).toFun x) :=
    add_seriesSum_valueC3 (r := hC.rep.smul (constSeq (Nat.cast n)))
      (r' := g.sub (g.cutNatVal n)) (x := x)
      (smul_seriesSum_valueC3 (constSeq (Nat.cast n)) (r := hC.rep) (x := x) χv)
      (sub_seriesSum_valueC3 (r := g) (r' := g.cutNatVal n) (x := x) gv hgcut)
  have eR : relEventually hr'.sum
      (addSeq (CReal.mul (constSeq (Nat.cast n)) χv.sum) (subSeq gv.sum hgcut.sum)) := by
    refine relEventually_trans _ _ _ (repSeriesSum_unique hr' hmodel) ?_
    change relEventually
      (addSeq (CReal.mul (constSeq (Nat.cast n)) χv.sum) (addSeq gv.sum (negSeq hgcut.sum)))
      (addSeq (CReal.mul (constSeq (Nat.cast n)) χv.sum) (subSeq gv.sum hgcut.sum))
    exact add_congr (Setoid.refl _) (add_sub_right_equiv gv.sum hgcut.sum)
  -- cut ≤ g, cut ≤ ↑n
  have hcut_le_g : RegularSeqLe hgcut.sum gv.sum :=
    regularSeqLe_trans (regularSeqLe_of_relEventually hgcut_eq)
      (CReal.min_le_leftC gv.sum (constSeq (Nat.cast n)))
  have hcut_le_n : RegularSeqLe hgcut.sum (constSeq (Nat.cast n)) :=
    regularSeqLe_trans (regularSeqLe_of_relEventually hgcut_eq)
      (CReal.min_le_rightC gv.sum (constSeq (Nat.cast n)))
  -- χ ∈ {0,1}
  have hχ01 : relEventually χv.sum CReal.zero ∨ relEventually χv.sum CReal.one := by
    rcases (hC.valid x hχabs).1 with hS1 | hS2
    · exact Or.inr ((hC.valid x hχabs).2.1 hS1 χv)
    · exact Or.inl ((hC.valid x hχabs).2.2 hS2 χv)
  have hmid : RegularSeqLe (CReal.mul χv.sum gv.sum)
      (addSeq (CReal.mul (constSeq (Nat.cast n)) χv.sum) (subSeq gv.sum hgcut.sum)) :=
    const_measure_diff_midC χv.sum gv.sum hgcut.sum (constSeq (Nat.cast n))
      (natCast_nonnegC n) hcut_le_g hcut_le_n hχ01
  exact regularSeqLe_trans (regularSeqLe_of_relEventually eL)
    (regularSeqLe_trans hmid (regularSeqLe_of_relEventually (relEventually_symm _ _ eR)))

#print axioms BishopSec1P.relIntegral_le_const_measure_plus_diffC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_cut_boundC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C) (g : IntegrableRepC3 S)
    (hnn : RepNonnegC g) (k : Nat) :
    RegularSeqLe (relIntegralC C hC g)
      (addSeq (CReal.mul (constSeq (Nat.cast (g.cutNat_tendsto_rep.mod k))) hC.rep.integral)
        (halfPow k)) := by
  have h1 := relIntegral_le_const_measure_plus_diffC hC g hnn (g.cutNat_tendsto_rep.mod k)
  have htail :
      RegularSeqLe (g.sub (g.cutNatVal (g.cutNat_tendsto_rep.mod k))).integral (halfPow k) := by
    have hlt := g.normL1_sub_cutNatC k (g.cutNat_tendsto_rep.mod k) (Nat.le_refl _)
    have heq : (g.sub (g.cutNatVal (g.cutNat_tendsto_rep.mod k))).normL1
        ≈ (g.sub (g.cutNatVal (g.cutNat_tendsto_rep.mod k))).integral :=
      (g.sub (g.cutNatVal (g.cutNat_tendsto_rep.mod k))).normL1_eq_integral_of_nonnegC
        (g.repNonneg_sub_cutNatValC (g.cutNat_tendsto_rep.mod k))
    exact regularSeqLe_of_left_eventual (relEventually_symm _ _ heq) (regularSeqLe_of_ltPropC hlt)
  refine regularSeqLe_trans h1 ?_
  show RegularSeqLe
    (((hC.rep.smul (constSeq (Nat.cast (g.cutNat_tendsto_rep.mod k)))).add
        (g.sub (g.cutNatVal (g.cutNat_tendsto_rep.mod k)))).integral)
    (addSeq (CReal.mul (constSeq (Nat.cast (g.cutNat_tendsto_rep.mod k))) hC.rep.integral)
      (halfPow k))
  rw [IntegrableRepC3.integral_add, IntegrableRepC3.integral_smul]
  exact regularSeqLe_add (regularSeqLe_refl _) htail

#print axioms BishopSec1P.relIntegral_le_cut_boundC

/-- Technical lemma used in the public import closure. -/
theorem mul_lt_mul_of_pos_leftC {a b c : CReal}
    (hab : regularSeqLtProp a b) (hc : regularSeqLtProp CReal.zero c) :
    regularSeqLtProp (CReal.mul c a) (CReal.mul c b) := by
  have hba : CReal.ltE CReal.zero (subSeq b a) := regularSeqLtProp_zero_lt_sub hab
  have hprod : CReal.ltE CReal.zero (CReal.mul c (subSeq b a)) := CReal.mul_pos_E hc hba
  have heq : relEventually (CReal.mul c (subSeq b a))
      (subSeq (CReal.mul c b) (CReal.mul c a)) := by
    have hq : mkQuot (CReal.mul c (subSeq b a))
        = mkQuot (subSeq (CReal.mul c b) (CReal.mul c a)) := by
      change mulQuotConcreteWith cRatScalarMulArch (mkQuot c) (subQuot (mkQuot b) (mkQuot a))
        = subQuot (mulQuotConcreteWith cRatScalarMulArch (mkQuot c) (mkQuot b))
                  (mulQuotConcreteWith cRatScalarMulArch (mkQuot c) (mkQuot a))
      letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let C : CRealQuot := mkQuot c
      change C * (B - A) = C * B - C * A
      ring
    exact Quotient.exact hq
  show PosEventually (subSeq (CReal.mul c b) (CReal.mul c a))
  have e1 : relEventually (subSeq (CReal.mul c (subSeq b a)) zeroSeq)
      (subSeq (CReal.mul c b) (CReal.mul c a)) :=
    relEventually_trans _ _ _
      (subSeq_zero_right_eventually (CReal.mul c (subSeq b a))) heq
  exact posEventually_respects _ _ e1 hprod

#print axioms BishopSec1P.mul_lt_mul_of_pos_leftC

/-- Technical lemma used in the public import closure. -/
theorem mul_invPos_scale_cancelC (c x : CReal) (h : PosEventuallyData c) :
    CReal.mul c (CReal.mul x (CReal.invPos c h)) ≈ x := by
  have hreassoc : CReal.mul c (CReal.mul x (CReal.invPos c h))
      ≈ CReal.mul x (CReal.mul c (CReal.invPos c h)) := by
    have hq : mkQuot (CReal.mul c (CReal.mul x (CReal.invPos c h)))
        = mkQuot (CReal.mul x (CReal.mul c (CReal.invPos c h))) := by
      change mulQuotConcreteWith cRatScalarMulArch (mkQuot c)
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot x) (mkQuot (CReal.invPos c h)))
        = mulQuotConcreteWith cRatScalarMulArch (mkQuot x)
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot c) (mkQuot (CReal.invPos c h)))
      letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
      let C : CRealQuot := mkQuot c
      let X : CRealQuot := mkQuot x
      let Cinv : CRealQuot := mkQuot (CReal.invPos c h)
      change C * (X * Cinv) = X * (C * Cinv)
      ring
    exact Quotient.exact hq
  have hcancel : CReal.mul c (CReal.invPos c h) ≈ CReal.one :=
    CReal.mul_invPos_eventually_one c h
  have h2 : CReal.mul x (CReal.mul c (CReal.invPos c h)) ≈ CReal.mul x CReal.one :=
    mul_congr (Setoid.refl x) hcancel
  have h3 : CReal.mul x CReal.one ≈ x := CReal.mul_one x
  exact Setoid.trans hreassoc (Setoid.trans h2 h3)

#print axioms BishopSec1P.mul_invPos_scale_cancelC

/-- Technical lemma used in the public import closure. -/
def natCast_succ_posDataC (n : Nat) :
    PosEventuallyData (constSeq (Nat.cast (n + 1) : Scalar)) where
  k := 1
  N := 1
  tail_pos := by
    intro m _hm
    change COF.lt (eps 1) (Nat.cast (n + 1) : Scalar)
    have heps : COF.lt (eps 1) (eps 0) := eps_succ_lt_eps 0
    have hle : BishopC.Le (eps 0) (Nat.cast (n + 1) : Scalar) := by
      rw [show eps 0 = (1 : Scalar) from rfl, Nat.cast_succ]
      have h0 : BishopC.Le (0 : Scalar) (Nat.cast n : Scalar) := scalar_natCast_nonneg n
      have hsum : BishopC.Le ((0 : Scalar) + 1) ((Nat.cast n : Scalar) + 1) :=
        BishopC.le_add h0 (BishopC.le_refl 1)
      simpa using hsum
    exact BishopC.lt_of_lt_of_le heps hle

#print axioms BishopSec1P.natCast_succ_posDataC

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_abs_continuous_deltaC {X : Type*} {S : IntSpaceC X}
    (g : IntegrableRepC3 S) (hnn : RepNonnegC g) (eps : CReal)
    (heps : regularSeqLtProp CReal.zero eps) :
    ∃ delta : CReal, regularSeqLtProp CReal.zero delta ∧
      ∀ (C : BishopC.BSet X) (hC : IntegrableSet1C S C),
        regularSeqLtProp (hC.rep.integral) delta →
          regularSeqLtProp (relIntegralC C hC g) eps := by
  -- Technical note.
  have posData_lt : ∀ (y : CReal), PosEventuallyData y → regularSeqLtProp CReal.zero y := by
    intro y hy
    show PosEventually (subSeq y CReal.zero)
    exact posEventually_respects y (subSeq y CReal.zero)
      (relEventually_symm _ _ (subSeq_zero_right_eventually y)) hy.toProp
  -- Technical note.
  obtain ⟨k0, hk0⟩ := CReal.archimedean_E eps heps
  let k : Nat := k0 + 1
  let n : Nat := g.cutNat_tendsto_rep.mod k
  let denom : CReal := constSeq (Nat.cast (n + 1))
  let hpos : PosEventuallyData denom := natCast_succ_posDataC n
  let delta : CReal := CReal.mul (halfPow k) (CReal.invPos denom hpos)
  have hdenom_lt : regularSeqLtProp CReal.zero denom := posData_lt denom hpos
  have hdelta_pos : regularSeqLtProp CReal.zero delta :=
    CReal.mul_pos_E (regularSeqLtProp_zero_halfPow k)
      (posData_lt _ (CReal.invPos_posData denom hpos))
  refine ⟨delta, hdelta_pos, ?_⟩
  intro C hC hmu
  -- Technical note.
  have hmain := relIntegral_le_cut_boundC hC g hnn k
  -- μ(C) ≥ 0
  have hmu_nonneg : RegularSeqNonneg (hC.rep.integral) := by
    have hrepnn : RepNonnegC hC.rep := IntegrableSet1_repNonnegC hC
    have heq : hC.rep.normL1 ≈ hC.rep.integral :=
      hC.rep.normL1_eq_integral_of_nonnegC hrepnn
    exact regularSeqNonneg_of_eventual (Setoid.symm heq)
      (IntegrableRepC3.normL1_nonnegC hC.rep)
  -- ↑(n+1)·μ(C) < ↑(n+1)·δ
  have h1 : regularSeqLtProp (CReal.mul denom hC.rep.integral) (CReal.mul denom delta) :=
    mul_lt_mul_of_pos_leftC hmu hdenom_lt
  -- ↑(n+1)·δ ≈ ½^k
  have h2 : CReal.mul denom delta ≈ halfPow k :=
    mul_invPos_scale_cancelC denom (halfPow k) hpos
  -- ↑(n+1)·μ(C) < ½^k
  have h3 : regularSeqLtProp (CReal.mul denom hC.rep.integral) (halfPow k) :=
    regularSeqLtProp_of_right_eventual h2 h1
  -- n·μ(C) ≤ ↑(n+1)·μ(C)
  have hn_le : RegularSeqLe (constSeq (Nat.cast n)) (constSeq (Nat.cast (n + 1))) :=
    natCast_le_of_leC (Nat.le_succ n)
  have h4 : RegularSeqLe (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral)
      (CReal.mul denom hC.rep.integral) :=
    regularSeqLe_mul_right_of_nonnegC hn_le hmu_nonneg
  -- n·μ(C) < ½^k
  have h5 : regularSeqLtProp (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k) :=
    regularSeqLtProp_of_le_of_lt h4 h3
  -- n·μ(C) + ½^k < ½^k + ½^k
  have h6 : regularSeqLtProp
      (addSeq (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k))
      (addSeq (halfPow k) (halfPow k)) := by
    have hL := regularSeqLtProp_add_left (halfPow k)
      (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k) h5
    exact regularSeqLtProp_of_left_eventual
      (addSeq_comm_eventually
        (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k)) hL
  -- ½^k + ½^k ≈ ½^k0
  have h7 : addSeq (halfPow k) (halfPow k) ≈ halfPow k0 := halfPow_succ_add_self k0
  -- n·μ(C) + ½^k < ½^k0
  have h8 : regularSeqLtProp
      (addSeq (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k)) (halfPow k0) :=
    regularSeqLtProp_of_right_eventual h7 h6
  -- n·μ(C) + ½^k < eps
  have h9 : regularSeqLtProp
      (addSeq (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k)) eps :=
    regularSeqLtProp_trans _ _ _ h8 hk0
  -- I_C(g) ≤ (n·μ(C)+½^k) < eps
  exact regularSeqLtProp_of_le_of_lt hmain h9

#print axioms BishopSec1P.relIntegral_abs_continuous_deltaC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_abs_continuous_setdiffC {X : Type*} {S : IntSpaceC X}
    (g : IntegrableRepC3 S) (hnn : RepNonnegC g) (eps : CReal)
    (heps : regularSeqLtProp CReal.zero eps) :
    ∃ delta : CReal, regularSeqLtProp CReal.zero delta ∧
      ∀ (A B : BishopC.BSet X) (hA : IntegrableSet1C S A) (hB : IntegrableSet1C S B),
        regularSeqLtProp ((IntegrableSet1_subC hA hB).rep.integral) delta →
          regularSeqLtProp (relIntegralC (BSet.sub A B) (IntegrableSet1_subC hA hB) g) eps := by
  obtain ⟨delta, hdelta_pos, hsmall⟩ := relIntegral_abs_continuous_deltaC g hnn eps heps
  refine ⟨delta, hdelta_pos, ?_⟩
  intro A B hA hB hmu
  exact hsmall (BSet.sub A B) (IntegrableSet1_subC hA hB) hmu

#print axioms BishopSec1P.relIntegral_abs_continuous_setdiffC

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLe_mul_left_of_nonnegC {a b c : CReal}
    (hab : RegularSeqLe a b) (hc : RegularSeqNonneg c) :
    RegularSeqLe (CReal.mul c a) (CReal.mul c b) := by
  have hd : RegularSeqNonneg (subSeq b a) := hab
  have hmul : RegularSeqNonneg (CReal.mul c (subSeq b a)) :=
    CReal.mul_nonneg_E hc hd
  have heq : relEventually
      (subSeq (CReal.mul c b) (CReal.mul c a))
      (CReal.mul c (subSeq b a)) := by
    have hq :
        mkQuot (subSeq (CReal.mul c b) (CReal.mul c a))
          = mkQuot (CReal.mul c (subSeq b a)) := by
      change subQuot
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot c) (mkQuot b))
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot c) (mkQuot a))
        = mulQuotConcreteWith cRatScalarMulArch
            (mkQuot c) (subQuot (mkQuot b) (mkQuot a))
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let C : CRealQuot := mkQuot c
      change C * B - C * A = C * (B - A)
      ring
    exact Quotient.exact hq
  exact regularSeqNonneg_of_eventual heq hmul

#print axioms BishopSec1P.regularSeqLe_mul_left_of_nonnegC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_of_le_funC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C) (g g' : IntegrableRepC3 S)
    (hnn : RepNonnegC g) (hnn' : RepNonnegC g')
    (hle : ∀ (x : X) (gv : RepSeriesSum (fun k => (g.fn k).toFun x))
             (gv' : RepSeriesSum (fun k => (g'.fn k).toFun x)),
             RegularSeqLe gv.sum gv'.sum) :
    RegularSeqLe (relIntegralC C hC g) (relIntegralC C hC g') := by
  show RegularSeqLe (IntegrableRepC3.prop_4_2_chi_f_repC C hC g).integral
    (IntegrableRepC3.prop_4_2_chi_f_repC C hC g').integral
  refine prop_1_11C
    (isFull_interC (isFull_interC (isFull_interC (isFull_interC
      (IntegrableRepC3.prop_4_2_chi_f_repC C hC g).domain_isFull
      (IntegrableRepC3.prop_4_2_chi_f_repC C hC g').domain_isFull)
      g.domain_isFull) g'.domain_isFull) hC.rep.domain_isFull)
    (IntegrableRepC3.prop_4_2_chi_f_repC C hC g)
    (IntegrableRepC3.prop_4_2_chi_f_repC C hC g') ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨hxLg, hxLg'⟩, hxg⟩, hxg'⟩, hxχ⟩ := hx
  obtain ⟨_, ⟨hLgabs⟩⟩ := hxLg
  obtain ⟨_, ⟨hLg'abs⟩⟩ := hxLg'
  obtain ⟨_, ⟨hgabs⟩⟩ := hxg
  obtain ⟨_, ⟨hg'abs⟩⟩ := hxg'
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  let χv := seriesSum_of_absC hχabs
  let gv := seriesSum_of_absC hgabs
  let gv' := seriesSum_of_absC hg'abs
  have hvalL := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC g hnn hLgabs hχabs hgabs
  have hvalL' := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC g' hnn' hLg'abs hχabs hg'abs
  have eL : relEventually hr.sum (CReal.mul χv.sum gv.sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr (seriesSum_of_absC hLgabs)) hvalL
  have eL' : relEventually hr'.sum (CReal.mul χv.sum gv'.sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr' (seriesSum_of_absC hLg'abs)) hvalL'
  have hχnn : RegularSeqNonneg χv.sum := IntegrableSet1_repNonnegC hC x hχabs χv
  have hgg' : RegularSeqLe gv.sum gv'.sum := hle x gv gv'
  have hmid : RegularSeqLe (CReal.mul χv.sum gv.sum) (CReal.mul χv.sum gv'.sum) :=
    regularSeqLe_mul_left_of_nonnegC hgg' hχnn
  exact regularSeqLe_trans (regularSeqLe_of_relEventually eL)
    (regularSeqLe_trans hmid (regularSeqLe_of_relEventually (relEventually_symm _ _ eL')))

#print axioms BishopSec1P.relIntegral_le_of_le_funC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_const_mul_measureC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C) (h : IntegrableRepC3 S)
    (hnn : RepNonnegC h) (M : CReal) (hM : RegularSeqNonneg M)
    (hle : ∀ (x : X) (hv : RepSeriesSum (fun k => (h.fn k).toFun x)),
             x ∈ C.S1 → RegularSeqLe hv.sum M) :
    RegularSeqLe (relIntegralC C hC h) ((hC.rep.smul M).integral) := by
  show RegularSeqLe (IntegrableRepC3.prop_4_2_chi_f_repC C hC h).integral
    ((hC.rep.smul M).integral)
  refine prop_1_11C
    (isFull_interC (isFull_interC
      (IntegrableRepC3.prop_4_2_chi_f_repC C hC h).domain_isFull h.domain_isFull)
      hC.rep.domain_isFull)
    (IntegrableRepC3.prop_4_2_chi_f_repC C hC h)
    (hC.rep.smul M) ?_
  intro x hx hr hr'
  obtain ⟨⟨hxrep, hxh⟩, hxχ⟩ := hx
  obtain ⟨_, ⟨hflatabs⟩⟩ := hxrep
  obtain ⟨_, ⟨hhabs⟩⟩ := hxh
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  let χv := seriesSum_of_absC hχabs
  let hv := seriesSum_of_absC hhabs
  have hval := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC h hnn hflatabs hχabs hhabs
  have eL : relEventually hr.sum (CReal.mul χv.sum hv.sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr (seriesSum_of_absC hflatabs)) hval
  let hRmodel : RepSeriesSum (fun k => ((hC.rep.smul M).fn k).toFun x) :=
    smul_seriesSum_valueC3 M (r := hC.rep) (x := x) χv
  have eR : relEventually hr'.sum (CReal.mul M χv.sum) :=
    repSeriesSum_unique hr' hRmodel
  have hmid : RegularSeqLe (CReal.mul χv.sum hv.sum) (CReal.mul M χv.sum) := by
    rcases (hC.valid x hχabs).1 with hS1 | hS2
    · have hχ1 : relEventually χv.sum CReal.one := (hC.valid x hχabs).2.1 hS1 χv
      have hhM : RegularSeqLe hv.sum M := hle x hv hS1
      have e_lhs : CReal.mul χv.sum hv.sum ≈ hv.sum :=
        Setoid.trans (mul_congr hχ1 (Setoid.refl _)) (CReal.one_mul _)
      have e_rhs : CReal.mul M χv.sum ≈ M :=
        Setoid.trans (mul_congr (Setoid.refl M) hχ1) (CReal.mul_one M)
      have hev : relEventually
          (subSeq (CReal.mul M χv.sum) (CReal.mul χv.sum hv.sum)) (subSeq M hv.sum) :=
        sub_congrC e_rhs e_lhs
      exact regularSeqNonneg_of_eventual hev hhM
    · have hχ0 : relEventually χv.sum CReal.zero := (hC.valid x hχabs).2.2 hS2 χv
      have e_lhs : CReal.mul χv.sum hv.sum ≈ CReal.zero :=
        Setoid.trans (mul_congr hχ0 (Setoid.refl _)) (zero_mul_equivC _)
      have hχnn : RegularSeqNonneg χv.sum :=
        regularSeqNonneg_of_eventual hχ0 regularSeqNonneg_zero
      have hrhs_nn : RegularSeqNonneg (CReal.mul M χv.sum) := CReal.mul_nonneg_E hM hχnn
      have hev : relEventually
          (subSeq (CReal.mul M χv.sum) (CReal.mul χv.sum hv.sum)) (CReal.mul M χv.sum) :=
        Setoid.trans (sub_congrC (Setoid.refl _) e_lhs) (subSeq_zero_right_eventually _)
      exact regularSeqNonneg_of_eventual hev hrhs_nn
  exact regularSeqLe_trans (regularSeqLe_of_relEventually eL)
    (regularSeqLe_trans hmid (regularSeqLe_of_relEventually (relEventually_symm _ _ eR)))

#print axioms BishopSec1P.relIntegral_le_const_mul_measureC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_setC_plus_setdiffC {X : Type*} {S : IntSpaceC X}
    {A C : BishopC.BSet X} (hA : IntegrableSet1C S A) (hC : IntegrableSet1C S C)
    (h : IntegrableRepC3 S) (hnn : RepNonnegC h) :
    RegularSeqLe (relIntegralC A hA h)
      (addSeq (relIntegralC C hC h)
        (relIntegralC (BSet.sub A C) (IntegrableSet1_subC hA hC) h)) := by
  let hAmC := IntegrableSet1_subC hA hC
  let repA := IntegrableRepC3.prop_4_2_chi_f_repC A hA h
  let repC := IntegrableRepC3.prop_4_2_chi_f_repC C hC h
  let repAmC := IntegrableRepC3.prop_4_2_chi_f_repC (BSet.sub A C) hAmC h
  show RegularSeqLe repA.integral (repC.add repAmC).integral
  refine prop_1_11C
    (isFull_interC (isFull_interC (isFull_interC (isFull_interC (isFull_interC
      repA.domain_isFull (repC.add repAmC).domain_isFull) h.domain_isFull)
      hA.rep.domain_isFull) hC.rep.domain_isFull) hAmC.rep.domain_isFull)
    repA (repC.add repAmC) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨⟨hxLA, hxRHS⟩, hxh⟩, hxχA⟩, hxχC⟩, hxχAmC⟩ := hx
  obtain ⟨_, ⟨hLAabs⟩⟩ := hxLA
  obtain ⟨_, ⟨hRHSabs⟩⟩ := hxRHS
  obtain ⟨_, ⟨hhabs⟩⟩ := hxh
  obtain ⟨_, ⟨hχAabs⟩⟩ := hxχA
  obtain ⟨_, ⟨hχCabs⟩⟩ := hxχC
  obtain ⟨_, ⟨hχAmCabs⟩⟩ := hxχAmC
  have hCabs : RepSeriesSum (fun k => absSeq ((repC.fn k).toFun x)) :=
    add_absSeriesSum_leftC (r := repC) (r' := repAmC) hRHSabs
  have hAmCabs : RepSeriesSum (fun k => absSeq ((repAmC.fn k).toFun x)) :=
    add_absSeriesSum_rightC (r := repC) (r' := repAmC) hRHSabs
  let hv := seriesSum_of_absC hhabs
  let χAv := seriesSum_of_absC hχAabs
  let χCv := seriesSum_of_absC hχCabs
  let χAmCv := seriesSum_of_absC hχAmCabs
  let hrCval := seriesSum_of_absC hCabs
  let hrAmCval := seriesSum_of_absC hAmCabs
  have hvalA := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hA h hnn hLAabs hχAabs hhabs
  have hvalC := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC h hnn hCabs hχCabs hhabs
  have hvalAmC := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hAmC h hnn hAmCabs hχAmCabs hhabs
  have eL : relEventually hr.sum (CReal.mul χAv.sum hv.sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr (seriesSum_of_absC hLAabs)) hvalA
  have eR : relEventually hr'.sum
      (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum)) := by
    refine relEventually_trans _ _ _
      (repSeriesSum_unique hr' (add_seriesSum_valueC3 hrCval hrAmCval)) ?_
    show relEventually (addSeq hrCval.sum hrAmCval.sum)
      (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum))
    exact add_congr hvalC hvalAmC
  have hmid : RegularSeqLe (CReal.mul χAv.sum hv.sum)
      (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum)) := by
    have hhnn : RegularSeqNonneg hv.sum := hnn x hhabs hv
    rcases (hA.valid x hχAabs).1 with hxAS1 | hxAS2
    · have hχA1 : relEventually χAv.sum CReal.one := (hA.valid x hχAabs).2.1 hxAS1 χAv
      have eLA : CReal.mul χAv.sum hv.sum ≈ hv.sum :=
        Setoid.trans (mul_congr hχA1 (Setoid.refl _)) (CReal.one_mul _)
      rcases (hC.valid x hχCabs).1 with hxCS1 | hxCS2
      · have hχC1 : relEventually χCv.sum CReal.one := (hC.valid x hχCabs).2.1 hxCS1 χCv
        have hχAmC0 : relEventually χAmCv.sum CReal.zero :=
          (hAmC.valid x hχAmCabs).2.2 (Or.inl (Or.inl ⟨hxAS1, hxCS1⟩)) χAmCv
        have eC : CReal.mul χCv.sum hv.sum ≈ hv.sum :=
          Setoid.trans (mul_congr hχC1 (Setoid.refl _)) (CReal.one_mul _)
        have eAmC : CReal.mul χAmCv.sum hv.sum ≈ CReal.zero :=
          Setoid.trans (mul_congr hχAmC0 (Setoid.refl _)) (zero_mul_equivC _)
        have hRHSh : relEventually
            (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum)) hv.sum := by
          have qC : mkQuot (CReal.mul χCv.sum hv.sum) = mkQuot hv.sum := Quotient.sound eC
          have qAmC : mkQuot (CReal.mul χAmCv.sum hv.sum) = mkQuot CReal.zero :=
            Quotient.sound eAmC
          have hq : mkQuot (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum))
              = mkQuot hv.sum := by
            letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
            change addQuot (mkQuot (CReal.mul χCv.sum hv.sum))
              (mkQuot (CReal.mul χAmCv.sum hv.sum)) = mkQuot hv.sum
            rw [qC, qAmC]
            change mkQuot hv.sum + (0 : CRealQuot) = mkQuot hv.sum
            ring
          exact Quotient.exact hq
        exact regularSeqLe_of_relEventually (Setoid.trans eLA (relEventually_symm _ _ hRHSh))
      · have hχC0 : relEventually χCv.sum CReal.zero := (hC.valid x hχCabs).2.2 hxCS2 χCv
        have hχAmC1 : relEventually χAmCv.sum CReal.one :=
          (hAmC.valid x hχAmCabs).2.1 ⟨hxAS1, hxCS2⟩ χAmCv
        have eC : CReal.mul χCv.sum hv.sum ≈ CReal.zero :=
          Setoid.trans (mul_congr hχC0 (Setoid.refl _)) (zero_mul_equivC _)
        have eAmC : CReal.mul χAmCv.sum hv.sum ≈ hv.sum :=
          Setoid.trans (mul_congr hχAmC1 (Setoid.refl _)) (CReal.one_mul _)
        have hRHSh : relEventually
            (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum)) hv.sum := by
          have qC : mkQuot (CReal.mul χCv.sum hv.sum) = mkQuot CReal.zero := Quotient.sound eC
          have qAmC : mkQuot (CReal.mul χAmCv.sum hv.sum) = mkQuot hv.sum := Quotient.sound eAmC
          have hq : mkQuot (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum))
              = mkQuot hv.sum := by
            letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
            change addQuot (mkQuot (CReal.mul χCv.sum hv.sum))
              (mkQuot (CReal.mul χAmCv.sum hv.sum)) = mkQuot hv.sum
            rw [qC, qAmC]
            change (0 : CRealQuot) + mkQuot hv.sum = mkQuot hv.sum
            ring
          exact Quotient.exact hq
        exact regularSeqLe_of_relEventually (Setoid.trans eLA (relEventually_symm _ _ hRHSh))
    · have hχA0 : relEventually χAv.sum CReal.zero := (hA.valid x hχAabs).2.2 hxAS2 χAv
      have eLA0 : CReal.mul χAv.sum hv.sum ≈ CReal.zero :=
        Setoid.trans (mul_congr hχA0 (Setoid.refl _)) (zero_mul_equivC _)
      have hCnn : RegularSeqNonneg χCv.sum := IntegrableSet1_repNonnegC hC x hχCabs χCv
      have hAmCnn : RegularSeqNonneg χAmCv.sum :=
        IntegrableSet1_repNonnegC hAmC x hχAmCabs χAmCv
      have hRHSnn : RegularSeqNonneg
          (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum)) :=
        regularSeqNonneg_add (CReal.mul_nonneg_E hCnn hhnn) (CReal.mul_nonneg_E hAmCnn hhnn)
      have hev : relEventually
          (subSeq (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum))
            (CReal.mul χAv.sum hv.sum))
          (addSeq (CReal.mul χCv.sum hv.sum) (CReal.mul χAmCv.sum hv.sum)) :=
        Setoid.trans (sub_congrC (Setoid.refl _) eLA0) (subSeq_zero_right_eventually _)
      exact regularSeqNonneg_of_eventual hev hRHSnn
  exact regularSeqLe_trans (regularSeqLe_of_relEventually eL)
    (regularSeqLe_trans hmid (regularSeqLe_of_relEventually (relEventually_symm _ _ eR)))

#print axioms BishopSec1P.relIntegral_le_setC_plus_setdiffC

/-- Technical lemma used in the public import closure. -/
def ConvergeInMeasureC {X : Type*} (S : IntSpaceC X)
    (fn : Nat → DataPFunRC X) (f : DataPFunRC X) : Prop :=
  ∀ (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
    (eps : CReal) (_heps : regularSeqLtProp CReal.zero eps),
    ∃ N : Nat, ∀ n ≥ N,
      ∃ (B : BishopC.BSet X) (hB : IntegrableSet1C S B),
        (B.S1 ⊆ A.S1 ∩ f.domain ∩ (fn n).domain) ∧
        regularSeqLtProp ((IntegrableSet1_subC hA hB).rep.integral) eps ∧
        ∀ x (_hxB : x ∈ B.S1) (exf : f.domData x) (exfn : (fn n).domData x),
          regularSeqLtProp
            (CReal.abs (CReal.sub (f.toFun x exf) ((fn n).toFun x exfn))) eps

#print axioms BishopSec1P.ConvergeInMeasureC

/-- Technical lemma used in the public import closure. -/
def IntegrableRepC3.toDataPFunRC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : DataPFunRC X where
  domData := fun x => RepSeriesSum (fun k => absSeq ((r.fn k).toFun x))
  toFun := fun x habs => (seriesSum_of_absC habs).sum

#print axioms BishopSec1P.IntegrableRepC3.toDataPFunRC

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRepC3.toDataPFunRC_value {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (x : X)
    (habs : RepSeriesSum (fun k => absSeq ((r.fn k).toFun x)))
    (hv : RepSeriesSum (fun k => (r.fn k).toFun x)) :
    relEventually ((r.toDataPFunRC).toFun x habs) hv.sum :=
  repSeriesSum_unique (seriesSum_of_absC habs) hv

#print axioms BishopSec1P.IntegrableRepC3.toDataPFunRC_value

/-- Technical lemma used in the public import closure. -/
structure Lemma414UniformComplementDataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (_hnn : ∀ n, RepNonnegC (fn n)) (eps : CReal) : Type _ where
  A : BishopC.BSet X
  hA : IntegrableSet1C S A
  N : Nat
  delta : CReal
  delta_pos : regularSeqLtProp CReal.zero delta
  small : ∀ n, N ≤ n → ∀ (C : BishopC.BSet X) (hC : IntegrableSet1C S C),
    regularSeqLtProp ((IntegrableSet1_subC hA hC).rep.integral) delta →
      regularSeqLtProp
        ((fn n).sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC (fn n))).integral eps

#print axioms BishopSec1P.Lemma414UniformComplementDataC

/-- Technical lemma used in the public import closure. -/
structure Lemma414ConvergeInMeasureToZeroDataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) : Type _ where
  close : ∀ (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
      (eps : CReal), regularSeqLtProp CReal.zero eps →
    Sigma (fun N : Nat =>
      ∀ n, N ≤ n →
        Sigma (fun C : BishopC.BSet X =>
          Sigma (fun hC : IntegrableSet1C S C =>
            PProd (C.S1 ⊆ A.S1)
              (PProd
                (regularSeqLtProp ((IntegrableSet1_subC hA hC).rep.integral) eps)
                (∀ (x : X)
                  (hfabs : RepSeriesSum (fun m => absSeq (((fn n).fn m).toFun x)))
                  (hχabs : RepSeriesSum (fun m => absSeq ((hC.rep.fn m).toFun x))),
                  relEventually (seriesSum_of_absC hχabs).sum CReal.one →
                    regularSeqLtProp (CReal.abs (seriesSum_of_absC hfabs).sum) eps)))))

#print axioms BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC

/-- Technical lemma used in the public import closure. -/
structure Lemma414RepConvergeToZeroDataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) : Type _ where
  close : ∀ (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
      (delta eta : CReal),
      regularSeqLtProp CReal.zero delta → regularSeqLtProp CReal.zero eta →
    Sigma (fun N : Nat =>
      ∀ n, N ≤ n →
        Sigma (fun C : BishopC.BSet X =>
          Sigma (fun hC : IntegrableSet1C S C =>
            PProd (C.S1 ⊆ A.S1)
              (PProd
                (regularSeqLtProp ((IntegrableSet1_subC hA hC).rep.integral) delta)
                (∀ (x : X)
                  (hfabs : RepSeriesSum (fun m => absSeq (((fn n).fn m).toFun x)))
                  (hχabs : RepSeriesSum (fun m => absSeq ((hC.rep.fn m).toFun x))),
                  relEventually (seriesSum_of_absC hχabs).sum CReal.one →
                    RegularSeqLe (seriesSum_of_absC hfabs).sum eta)))))

#print axioms BishopSec1P.Lemma414RepConvergeToZeroDataC

/-- Base brick for `min_posC` (the presented instance of `lemma34_min_pos`,
    i.e. the COF.min positivity field requirement that the abstract route gets for free but
    `CReal` must prove): strict positivity of a presented real yields a strictly
    smaller dyadic constant strictly below it, `0 < a → ∃ K, halfPow K < a`.
    Choice-free (`dependency audit reports only the expected core dependencies`).  Proof: unfold the
    `subSeq` value pointwise (halfPow's value is the constant `eps K`, `CReal.zero`
    is `zeroSeq`), then pure scalar arithmetic via `eps_succ_add_self` (dyadic
    halving) and `eps_succ_lt_eps`. -/
theorem posC_imp_halfPow_lt {a : CReal}
    (ha : regularSeqLtProp CReal.zero a) :
    ∃ K : Nat, regularSeqLtProp (halfPow K) a := by
  obtain ⟨k, N, hN⟩ := ha
  refine ⟨k + 2, k + 2, N, fun n hn => ?_⟩
  -- `hgap : eps k < a.val (addIndex n) - 0`  (unfold `subSeq a CReal.zero`)
  have hgap : COF.lt (eps k) (a.val (addIndex n) - (0 : Scalar)) := hN n hn
  rw [show a.val (addIndex n) - (0 : Scalar) = a.val (addIndex n) from by ring] at hgap
  -- goal: `eps (k+2) < a.val (addIndex n) - eps (k+2)`  (unfold `subSeq a (halfPow (k+2))`)
  change COF.lt (eps (k + 2)) (a.val (addIndex n) - eps (k + 2))
  have hsum : COF.lt (eps (k + 2) + eps (k + 2)) (a.val (addIndex n)) := by
    rw [eps_succ_add_self (k + 1)]
    exact scalarCOFOSeed.lt_trans (eps_succ_lt_eps k) hgap
  have ht := COF.lt_add_left (-(eps (k + 2))) hsum
  rwa [show -(eps (k + 2)) + (eps (k + 2) + eps (k + 2)) = eps (k + 2) from by ring,
    show -(eps (k + 2)) + a.val (addIndex n) = a.val (addIndex n) - eps (k + 2) from by ring] at ht

#print axioms BishopSec1P.posC_imp_halfPow_lt

/-- Dyadic constants are antitone in the presented order: `j ≤ k → halfPow k ≤ halfPow j`.
    One-step `regularSeqLtProp_halfPow_succ` (via `regularSeqLe_of_ltPropC`) + `Nat.le`
    induction with `regularSeqLe_trans`.  Choice-free (`dependency audit reports only the expected core dependencies`). -/
theorem halfPow_antitone_leC {j k : Nat} (hjk : j ≤ k) :
    RegularSeqLe (halfPow k) (halfPow j) := by
  induction hjk with
  | refl => exact regularSeqLe_refl _
  | step _ ih =>
      exact regularSeqLe_trans
        (regularSeqLe_of_ltPropC (regularSeqLtProp_halfPow_succ _)) ih

#print axioms BishopSec1P.halfPow_antitone_leC

/-- Presented instance of the abstract `lemma34_min_pos` (the `COF.min` positivity field
    requirement): `0 < a → 0 < b → 0 < min a b`.  Take the common dyadic lower bound
    `halfPow (max Ka Kb)` for both `a` and `b` (via `posC_imp_halfPow_lt` + antitone),
    push into `min` by `CReal.le_minC`.  Choice-free (`dependency audit reports only the expected core dependencies`). -/
theorem min_posC {a b : CReal}
    (ha : regularSeqLtProp CReal.zero a) (hb : regularSeqLtProp CReal.zero b) :
    regularSeqLtProp CReal.zero (CReal.min a b) := by
  obtain ⟨Ka, hKa⟩ := posC_imp_halfPow_lt ha
  obtain ⟨Kb, hKb⟩ := posC_imp_halfPow_lt hb
  refine regularSeqLtProp_of_lt_of_le (regularSeqLtProp_zero_halfPow (max Ka Kb)) ?_
  refine CReal.le_minC ?_ ?_
  · exact regularSeqLe_of_ltPropC
      (regularSeqLtProp_of_le_of_lt (halfPow_antitone_leC (Nat.le_max_left Ka Kb)) hKa)
  · exact regularSeqLe_of_ltPropC
      (regularSeqLtProp_of_le_of_lt (halfPow_antitone_leC (Nat.le_max_right Ka Kb)) hKb)

#print axioms BishopSec1P.min_posC

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_rep_converge_from_source_measure_converge_zeroC
    {X : Type*} {S : IntSpaceC X} (fn : Nat → IntegrableRepC3 S)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (S := S) fn) :
    Lemma414RepConvergeToZeroDataC (S := S) fn where
  close := by
    intro A hA delta eta hdelta heta
    have hrho : regularSeqLtProp CReal.zero (CReal.min delta eta) := min_posC hdelta heta
    obtain ⟨N, hN⟩ := hconv.close A hA (CReal.min delta eta) hrho
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hsub1, hmeasure, hsmall⟩ := hN n hn
    refine ⟨C, hC, hsub1, ?_, ?_⟩
    · -- measure field: `... integral < delta`  from  `< min delta eta ≤ delta`
      exact regularSeqLtProp_of_lt_of_le hmeasure (CReal.min_le_leftC delta eta)
    · -- value field: `sum ≤ eta`  from  `sum ≤ |sum| < min delta eta ≤ eta`
      intro x hfabs hχabs hχone
      have hpt := hsmall x hfabs hχabs hχone
      have hlt : regularSeqLtProp (seriesSum_of_absC hfabs).sum (CReal.min delta eta) :=
        regularSeqLtProp_of_le_of_lt
          (base_le_abs_base_regularSeqLe (seriesSum_of_absC hfabs).sum) hpt
      exact regularSeqLe_of_ltPropC
        (regularSeqLtProp_of_lt_of_le hlt (CReal.min_le_rightC delta eta))

#print axioms BishopSec1P.lemma_4_14_rep_converge_from_source_measure_converge_zeroC

/-- Data → Prop direction of positivity (extraction of the δ-wrapper's local
    `posData_lt`): a `PosEventuallyData` witness gives strict `0 < y`.
    Choice-free (`≈` transport only). -/
theorem regularSeqLtProp_zero_of_posData {y : CReal}
    (hy : PosEventuallyData y) : regularSeqLtProp CReal.zero y := by
  show PosEventually (subSeq y CReal.zero)
  exact posEventually_respects y (subSeq y CReal.zero)
    (relEventually_symm _ _ (subSeq_zero_right_eventually y)) hy.toProp

#print axioms BishopSec1P.regularSeqLtProp_zero_of_posData

/-- Technical lemma used in the public import closure. -/
def posStrongWitnessC (x : RegularSeq) (n : Nat) : Prop :=
  COF.lt (eps n + eps n) (x.val n)

instance posStrongWitnessCDecidable (x : RegularSeq) :
    DecidablePred (posStrongWitnessC x) :=
  fun n => by
    unfold posStrongWitnessC
    change Decidable (BishopCRat.CRat.lt (eps n + eps n) (x.val n))
    exact BishopCRat.CRat.ltDecidable (eps n + eps n) (x.val n)

/-- Strong single-witness positivity existential. -/
def posStrongC (x : RegularSeq) : Prop :=
  ∃ n : Nat, posStrongWitnessC x n

/-- Choice-free data extraction from the decidable strong existential (`Nat.find`). -/
def strongGaugeC {x : RegularSeq} (hx : posStrongC x) :
    { n : Nat // posStrongWitnessC x n } :=
  ⟨Nat.find hx, Nat.find_spec hx⟩

/-- Old tail positivity (`PosEventually`) implies strong single-witness positivity.
    The tail existential is eliminated only while proving another `Prop`;
    `strongGaugeC` performs the data extraction afterward (choice-free). -/
theorem posEventually_to_strongC {x : RegularSeq}
    (hx : PosEventually x) : posStrongC x := by
  rcases hx with ⟨k, N, hN⟩
  let n0 : Nat := N + k + 2
  refine ⟨n0, ?_⟩
  have hNle : N ≤ n0 := by unfold n0; omega
  have hkle : k + 1 ≤ n0 := by unfold n0; omega
  have htail : COF.lt (eps k) (x.val n0) := hN n0 hNle
  have hsmall : BishopC.Le (eps n0 + eps n0) (eps k) := by
    have hle : BishopC.Le (eps n0) (eps (k + 1)) := eps_le_of_le hkle
    have hsum := BishopC.le_add hle hle
    rwa [eps_succ_add_self k] at hsum
  exact scalar_lt_of_le_of_lt hsmall htail

/-- A strong point witness gives a late point suitable for
    `posEventuallyData_of_late_point`. -/
theorem strongGauge_late_pointC
    {x : RegularSeq} (g : { n : Nat // posStrongWitnessC x n }) :
    COF.lt (eps (g.val + 1)) (x.val (g.val + 3)) := by
  let n : Nat := g.val
  let M : Nat := n + 3
  have hg : COF.lt (eps n + eps n) (x.val n) := by
    simpa [n, posStrongWitnessC] using g.property
  have htailSmall : COF.lt (eps M) (eps (n + 1)) := by
    have hle : BishopC.Le (eps M) (eps (n + 2)) := eps_le_of_le (by unfold M; omega)
    exact scalar_lt_of_le_of_lt hle (eps_succ_lt_eps (n + 1))
  have hsmall1 : COF.lt (eps (n + 1) + eps M) (eps n) := by
    have h := COF.lt_add_left (eps (n + 1)) htailSmall
    rwa [eps_succ_add_self n] at h
  have hsmall2 :
      COF.lt (eps (n + 1) + (eps n + eps M)) (eps n + eps n) := by
    have h := COF.lt_add_left (eps n) hsmall1
    rwa [show eps n + (eps (n + 1) + eps M) =
        eps (n + 1) + (eps n + eps M) from by ring] at h
  have hpre : COF.lt (eps (n + 1) + (eps n + eps M)) (x.val n) :=
    scalarCOFOSeed.lt_trans hsmall2 hg
  have hshift : COF.lt (eps (n + 1)) (x.val n - (eps n + eps M)) := by
    have h := COF.lt_add_left (-(eps n + eps M)) hpre
    rwa [show -(eps n + eps M) + (eps (n + 1) + (eps n + eps M)) =
        eps (n + 1) from by ring,
      show -(eps n + eps M) + x.val n =
        x.val n - (eps n + eps M) from by ring] at h
  have hdist : BishopC.Le (COF.abs (x.val n - x.val M)) (eps n + eps M) :=
    x.regular n M
  have hlower : BishopC.Le (x.val n - (eps n + eps M)) (x.val M) :=
    scalar_point_lower_of_abs_le hdist
  have hposM : COF.lt (eps (n + 1)) (x.val M) :=
    BishopC.lt_of_lt_of_le hshift hlower
  simpa [n, M]

/-- Strong gauge data supplies the older positive-tail data (choice-free). -/
def posEventuallyData_of_strongGaugeC
    {x : RegularSeq} (g : { n : Nat // posStrongWitnessC x n }) :
    PosEventuallyData x :=
  posEventuallyData_of_late_point x
    (j := g.val + 1) (M := g.val + 3)
    (by omega)
    (strongGauge_late_pointC g)

/-- Prop → Data direction of positivity: a strict `0 < x` (a `regularSeqLtProp`,
    defeq `PosEventually (subSeq x 0)`) is upgraded to a `PosEventuallyData`
    witness through the choice-free strong gauge (`Nat.find`) bridge.
    This is the presented mirror of the abstract COFOC `inv`-witness plumbing
    (abstract gets the witness for free from `COFO.inv`; `CReal.invPos` is partial
    and needs a `PosEventuallyData`).  Choice-free. -/
def posEventuallyData_of_pos_zeroC {x : CReal}
    (h : regularSeqLtProp CReal.zero x) : PosEventuallyData x :=
  posEventuallyData_of_strongGaugeC
    (strongGaugeC (posEventually_to_strongC
      (posEventually_respects (subSeq x CReal.zero) x
        (subSeq_zero_right_eventually x) h)))

#print axioms BishopSec1P.posEventuallyData_of_pos_zeroC

/-- Positivity witness for `μ(A) + 1` from `μ(A) ≥ 0` (the abstract source uses
    `measure1 hA + 1` inside `COFO.inv`; presented needs the `PosEventuallyData`).
    Route: `0 ≤ μ < μ + 1` (with `0 < 1` from `0 < halfPow 0 ≈ 1`) via
    `regularSeqLtProp_of_le_of_lt`, then Prop → Data bridge.  Choice-free. -/
def measure_add_one_posDataC {measure : CReal}
    (hnn : RegularSeqNonneg measure) :
    PosEventuallyData (CReal.add measure CReal.one) :=
  posEventuallyData_of_pos_zeroC (by
    apply regularSeqLtProp_of_le_of_lt (regularSeqLe_zero_of_nonneg hnn)
    have h01 : regularSeqLtProp CReal.zero CReal.one :=
      regularSeqLtProp_of_right_eventual halfPow_zero (regularSeqLtProp_zero_halfPow 0)
    have hadd : regularSeqLtProp (addSeq measure CReal.zero)
        (addSeq measure CReal.one) :=
      regularSeqLtProp_add_left measure CReal.zero CReal.one h01
    exact regularSeqLtProp_of_left_eventual
      (relEventually_symm _ _ (addSeq_zero_right_eventually measure)) hadd)

#print axioms BishopSec1P.measure_add_one_posDataC

/-- Nonnegativity of the presented set measure `μ(A) = hA.rep.integral`
    (exact copy of the δ-wrapper's `hmu_nonneg` pattern, hC → hA):
    `normL1 ≈ integral` for a nonnegative representative, and `normL1 ≥ 0`.
    Choice-free. -/
theorem measure_nonnegC {X : Type*} {S : IntSpaceC X} {A : BishopC.BSet X}
    (hA : IntegrableSet1C S A) : RegularSeqNonneg (hA.rep.integral) := by
  have hrepnn : RepNonnegC hA.rep := IntegrableSet1_repNonnegC hA
  have heq : hA.rep.normL1 ≈ hA.rep.integral :=
    hA.rep.normL1_eq_integral_of_nonnegC hrepnn
  exact regularSeqNonneg_of_eventual (Setoid.symm heq)
    (IntegrableRepC3.normL1_nonnegC hA.rep)

#print axioms BishopSec1P.measure_nonnegC

/-- The presented good-set value bound `eps · (μ(A) + 1)⁻¹` (mirror of the
    abstract `eps * COFO.inv (measure1 hA + 1)`, `Lemma414GoodSetData`@600).
    The `μ(A)+1` positivity witness is supplied by `measure_add_one_posDataC`. -/
noncomputable def goodSetBoundC {X : Type*} {S : IntSpaceC X}
    {A : BishopC.BSet X} (hA : IntegrableSet1C S A) (eps : CReal) : CReal :=
  CReal.mul eps
    (CReal.invPos (CReal.add hA.rep.integral CReal.one)
      (measure_add_one_posDataC (measure_nonnegC hA)))

/-- Strict positivity of the good-set bound `0 < eps · (μ(A)+1)⁻¹`
    (from `eps > 0` and `(μ(A)+1)⁻¹ > 0` via `CReal.mul_pos_E`).  Choice-free. -/
theorem goodSetBoundC_pos {X : Type*} {S : IntSpaceC X}
    {A : BishopC.BSet X} (hA : IntegrableSet1C S A) {eps : CReal}
    (heps : regularSeqLtProp CReal.zero eps) :
    regularSeqLtProp CReal.zero (goodSetBoundC hA eps) := by
  show regularSeqLtProp CReal.zero (CReal.mul eps
    (CReal.invPos (CReal.add hA.rep.integral CReal.one)
      (measure_add_one_posDataC (measure_nonnegC hA))))
  exact CReal.mul_pos_E heps
    (regularSeqLtProp_zero_of_posData
      (CReal.invPos_posData (CReal.add hA.rep.integral CReal.one)
        (measure_add_one_posDataC (measure_nonnegC hA))))

#print axioms BishopSec1P.goodSetBoundC_pos

/-- Technical lemma used in the public import closure. -/
structure Lemma414GoodSetDataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S)
    (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
    (delta eps : CReal) : Type _ where
  N : Nat
  close : ∀ n, N ≤ n →
    Sigma (fun C : BishopC.BSet X =>
      Sigma (fun hC : IntegrableSet1C S C =>
        PProd (C.S1 ⊆ A.S1)
          (PProd
            (regularSeqLtProp ((IntegrableSet1_subC hA hC).rep.integral) delta)
            (∀ (x : X)
              (hfabs : RepSeriesSum (fun m => absSeq (((fn n).fn m).toFun x)))
              (hχabs : RepSeriesSum (fun m => absSeq ((hC.rep.fn m).toFun x))),
              relEventually (seriesSum_of_absC hχabs).sum CReal.one →
                RegularSeqLe (seriesSum_of_absC hfabs).sum (goodSetBoundC hA eps)))))

#print axioms BishopSec1P.Lemma414GoodSetDataC

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_good_set_data_from_rep_convergeC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S)
    (hconv : Lemma414RepConvergeToZeroDataC (S := S) fn)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps)
    (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
    (delta : CReal) (hdelta : regularSeqLtProp CReal.zero delta) :
    Lemma414GoodSetDataC (S := S) fn A hA delta eps :=
  let d := hconv.close A hA delta (goodSetBoundC hA eps) hdelta (goodSetBoundC_pos hA heps)
  { N := d.1, close := d.2 }

#print axioms BishopSec1P.lemma_4_14_good_set_data_from_rep_convergeC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_const_mul_measure_absC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C) (h : IntegrableRepC3 S)
    (hnn : RepNonnegC h) (M : CReal) (hM : RegularSeqNonneg M)
    (hle_abs : ∀ (x : X)
             (hfabs : RepSeriesSum (fun k => absSeq ((h.fn k).toFun x)))
             (hχabs : RepSeriesSum (fun k => absSeq ((hC.rep.fn k).toFun x))),
             relEventually (seriesSum_of_absC hχabs).sum CReal.one →
               RegularSeqLe (seriesSum_of_absC hfabs).sum M) :
    RegularSeqLe (relIntegralC C hC h) ((hC.rep.smul M).integral) := by
  show RegularSeqLe (IntegrableRepC3.prop_4_2_chi_f_repC C hC h).integral
    ((hC.rep.smul M).integral)
  refine prop_1_11C
    (isFull_interC (isFull_interC
      (IntegrableRepC3.prop_4_2_chi_f_repC C hC h).domain_isFull h.domain_isFull)
      hC.rep.domain_isFull)
    (IntegrableRepC3.prop_4_2_chi_f_repC C hC h)
    (hC.rep.smul M) ?_
  intro x hx hr hr'
  obtain ⟨⟨hxrep, hxh⟩, hxχ⟩ := hx
  obtain ⟨_, ⟨hflatabs⟩⟩ := hxrep
  obtain ⟨_, ⟨hhabs⟩⟩ := hxh
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  let χv := seriesSum_of_absC hχabs
  let hv := seriesSum_of_absC hhabs
  have hval := IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC h hnn hflatabs hχabs hhabs
  have eL : relEventually hr.sum (CReal.mul χv.sum hv.sum) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr (seriesSum_of_absC hflatabs)) hval
  let hRmodel : RepSeriesSum (fun k => ((hC.rep.smul M).fn k).toFun x) :=
    smul_seriesSum_valueC3 M (r := hC.rep) (x := x) χv
  have eR : relEventually hr'.sum (CReal.mul M χv.sum) :=
    repSeriesSum_unique hr' hRmodel
  have hmid : RegularSeqLe (CReal.mul χv.sum hv.sum) (CReal.mul M χv.sum) := by
    rcases (hC.valid x hχabs).1 with hS1 | hS2
    · have hχ1 : relEventually χv.sum CReal.one := (hC.valid x hχabs).2.1 hS1 χv
      have hhM : RegularSeqLe hv.sum M := hle_abs x hhabs hχabs hχ1
      have e_lhs : CReal.mul χv.sum hv.sum ≈ hv.sum :=
        Setoid.trans (mul_congr hχ1 (Setoid.refl _)) (CReal.one_mul _)
      have e_rhs : CReal.mul M χv.sum ≈ M :=
        Setoid.trans (mul_congr (Setoid.refl M) hχ1) (CReal.mul_one M)
      have hev : relEventually
          (subSeq (CReal.mul M χv.sum) (CReal.mul χv.sum hv.sum)) (subSeq M hv.sum) :=
        sub_congrC e_rhs e_lhs
      exact regularSeqNonneg_of_eventual hev hhM
    · have hχ0 : relEventually χv.sum CReal.zero := (hC.valid x hχabs).2.2 hS2 χv
      have e_lhs : CReal.mul χv.sum hv.sum ≈ CReal.zero :=
        Setoid.trans (mul_congr hχ0 (Setoid.refl _)) (zero_mul_equivC _)
      have hχnn : RegularSeqNonneg χv.sum :=
        regularSeqNonneg_of_eventual hχ0 regularSeqNonneg_zero
      have hrhs_nn : RegularSeqNonneg (CReal.mul M χv.sum) := CReal.mul_nonneg_E hM hχnn
      have hev : relEventually
          (subSeq (CReal.mul M χv.sum) (CReal.mul χv.sum hv.sum)) (CReal.mul M χv.sum) :=
        Setoid.trans (sub_congrC (Setoid.refl _) e_lhs) (subSeq_zero_right_eventually _)
      exact regularSeqNonneg_of_eventual hev hrhs_nn
  exact regularSeqLe_trans (regularSeqLe_of_relEventually eL)
    (regularSeqLe_trans hmid (regularSeqLe_of_relEventually (relEventually_symm _ _ eR)))

#print axioms BishopSec1P.relIntegral_le_const_mul_measure_absC

/-- Technical lemma used in the public import closure. -/
theorem measure1_mono_s1_subsetC {X : Type*} {S : IntSpaceC X}
    {C A : BishopC.BSet X} (hC : IntegrableSet1C S C) (hA : IntegrableSet1C S A)
    (hsub1 : C.S1 ⊆ A.S1) :
    RegularSeqLe (hC.rep.integral) (hA.rep.integral) := by
  refine prop_1_11C (isFull_interC hC.rep.domain_isFull hA.rep.domain_isFull)
    hC.rep hA.rep ?_
  intro x hx hcx hax
  obtain ⟨hxC, hxA⟩ := hx
  obtain ⟨_, ⟨hCabs⟩⟩ := hxC
  obtain ⟨_, ⟨hAabs⟩⟩ := hxA
  rcases (hC.valid x hCabs).1 with hxC1 | hxC2
  · have hcv : relEventually hcx.sum CReal.one := (hC.valid x hCabs).2.1 hxC1 hcx
    have hav : relEventually hax.sum CReal.one := (hA.valid x hAabs).2.1 (hsub1 hxC1) hax
    exact regularSeqLe_of_relEventually
      (relEventually_trans _ _ _ hcv (relEventually_symm _ _ hav))
  · have hcv : relEventually hcx.sum CReal.zero := (hC.valid x hCabs).2.2 hxC2 hcx
    rcases (hA.valid x hAabs).1 with hxA1 | hxA2
    · have hav : relEventually hax.sum CReal.one := (hA.valid x hAabs).2.1 hxA1 hax
      have hev : relEventually (subSeq hax.sum hcx.sum) (subSeq CReal.one CReal.zero) :=
        sub_congrC hav hcv
      have h01 : RegularSeqNonneg (subSeq CReal.one CReal.zero) :=
        regularSeqLe_of_ltPropC
          (regularSeqLtProp_of_right_eventual halfPow_zero (regularSeqLtProp_zero_halfPow 0))
      exact regularSeqNonneg_of_eventual hev h01
    · have hav : relEventually hax.sum CReal.zero := (hA.valid x hAabs).2.2 hxA2 hax
      exact regularSeqLe_of_relEventually
        (relEventually_trans _ _ _ hcv (relEventually_symm _ _ hav))

#print axioms BishopSec1P.measure1_mono_s1_subsetC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem scaled_bound_lt {denom eps mc : CReal} (hd : PosEventuallyData denom)
    (heps : regularSeqLtProp CReal.zero eps)
    (hmc_lt : regularSeqLtProp mc denom) :
    regularSeqLtProp (CReal.mul (CReal.mul eps (CReal.invPos denom hd)) mc) eps := by
  have hinv_pos : regularSeqLtProp CReal.zero (CReal.invPos denom hd) :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData denom hd)
  have hcancel : CReal.mul (CReal.invPos denom hd) denom ≈ CReal.one := by
    have hcomm : CReal.mul (CReal.invPos denom hd) denom
        ≈ CReal.mul denom (CReal.invPos denom hd) := by
      have hq : mkQuot (CReal.mul (CReal.invPos denom hd) denom)
          = mkQuot (CReal.mul denom (CReal.invPos denom hd)) := by
        change mulQuotConcreteWith cRatScalarMulArch (mkQuot (CReal.invPos denom hd)) (mkQuot denom)
          = mulQuotConcreteWith cRatScalarMulArch (mkQuot denom) (mkQuot (CReal.invPos denom hd))
        letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
        let I : CRealQuot := mkQuot (CReal.invPos denom hd)
        let D : CRealQuot := mkQuot denom
        change I * D = D * I
        ring
      exact Quotient.exact hq
    exact Setoid.trans hcomm (CReal.mul_invPos_eventually_one denom hd)
  have hmul : regularSeqLtProp (CReal.mul (CReal.invPos denom hd) mc)
      (CReal.mul (CReal.invPos denom hd) denom) :=
    mul_lt_mul_of_pos_leftC hmc_lt hinv_pos
  have hinvC1 : regularSeqLtProp (CReal.mul (CReal.invPos denom hd) mc) CReal.one :=
    regularSeqLtProp_of_lt_of_le hmul (regularSeqLe_of_relEventually hcancel)
  have hscaled : regularSeqLtProp
      (CReal.mul eps (CReal.mul (CReal.invPos denom hd) mc)) (CReal.mul eps CReal.one) :=
    mul_lt_mul_of_pos_leftC hinvC1 heps
  have hR := regularSeqLtProp_of_right_eventual (CReal.mul_one eps) hscaled
  have hLeq : CReal.mul (CReal.mul eps (CReal.invPos denom hd)) mc
      ≈ CReal.mul eps (CReal.mul (CReal.invPos denom hd) mc) := by
    have hq : mkQuot (CReal.mul (CReal.mul eps (CReal.invPos denom hd)) mc)
        = mkQuot (CReal.mul eps (CReal.mul (CReal.invPos denom hd) mc)) := by
      change mulQuotConcreteWith cRatScalarMulArch
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot eps) (mkQuot (CReal.invPos denom hd)))
          (mkQuot mc)
        = mulQuotConcreteWith cRatScalarMulArch (mkQuot eps)
          (mulQuotConcreteWith cRatScalarMulArch (mkQuot (CReal.invPos denom hd)) (mkQuot mc))
      letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
      let E : CRealQuot := mkQuot eps
      let I : CRealQuot := mkQuot (CReal.invPos denom hd)
      let Mc : CRealQuot := mkQuot mc
      change (E * I) * Mc = E * (I * Mc)
      ring
    exact Quotient.exact hq
  exact regularSeqLtProp_of_left_eventual hLeq hR

#print axioms BishopSec1P.scaled_bound_lt

/-- Technical lemma used in the public import closure. -/
theorem scaled_measure_lt_of_s1_subsetC {X : Type*} {S : IntSpaceC X}
    {C A : BishopC.BSet X} (hC : IntegrableSet1C S C) (hA : IntegrableSet1C S A)
    (hsub1 : C.S1 ⊆ A.S1) (eps : CReal) (heps : regularSeqLtProp CReal.zero eps) :
    regularSeqLtProp (CReal.mul (goodSetBoundC hA eps) (hC.rep.integral)) eps := by
  have hA_lt_den : regularSeqLtProp hA.rep.integral (CReal.add hA.rep.integral CReal.one) := by
    have h01 : regularSeqLtProp CReal.zero CReal.one :=
      regularSeqLtProp_of_right_eventual halfPow_zero (regularSeqLtProp_zero_halfPow 0)
    have hadd : regularSeqLtProp (addSeq hA.rep.integral CReal.zero)
        (addSeq hA.rep.integral CReal.one) :=
      regularSeqLtProp_add_left hA.rep.integral CReal.zero CReal.one h01
    exact regularSeqLtProp_of_left_eventual
      (relEventually_symm _ _ (addSeq_zero_right_eventually hA.rep.integral)) hadd
  have hC_lt_den : regularSeqLtProp hC.rep.integral (CReal.add hA.rep.integral CReal.one) :=
    regularSeqLtProp_of_le_of_lt (measure1_mono_s1_subsetC hC hA hsub1) hA_lt_den
  unfold goodSetBoundC
  exact scaled_bound_lt (measure_add_one_posDataC (measure_nonnegC hA)) heps hC_lt_den

#print axioms BishopSec1P.scaled_measure_lt_of_s1_subsetC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_goodSet_small_of_s1_subsetC {X : Type*} {S : IntSpaceC X}
    {C A : BishopC.BSet X} (hC : IntegrableSet1C S C) (hA : IntegrableSet1C S A)
    (hsub1 : C.S1 ⊆ A.S1)
    (h : IntegrableRepC3 S) (hnn : RepNonnegC h)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps)
    (hbound : ∀ (x : X)
      (hfabs : RepSeriesSum (fun k => absSeq ((h.fn k).toFun x)))
      (hχabs : RepSeriesSum (fun k => absSeq ((hC.rep.fn k).toFun x))),
      relEventually (seriesSum_of_absC hχabs).sum CReal.one →
        RegularSeqLe (seriesSum_of_absC hfabs).sum (goodSetBoundC hA eps)) :
    regularSeqLtProp (relIntegralC C hC h) eps := by
  have hgb_nn : RegularSeqNonneg (goodSetBoundC hA eps) :=
    regularSeqNonneg_of_eventual
      (relEventually_symm _ _ (subSeq_zero_right_eventually (goodSetBoundC hA eps)))
      (regularSeqLe_of_ltPropC (goodSetBoundC_pos hA heps))
  have hle : RegularSeqLe (relIntegralC C hC h)
      ((hC.rep.smul (goodSetBoundC hA eps)).integral) :=
    relIntegral_le_const_mul_measure_absC hC h hnn (goodSetBoundC hA eps) hgb_nn hbound
  rw [IntegrableRepC3.integral_smul] at hle
  exact regularSeqLtProp_of_le_of_lt hle
    (scaled_measure_lt_of_s1_subsetC hC hA hsub1 eps heps)

#print axioms BishopSec1P.relIntegral_goodSet_small_of_s1_subsetC

set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem relIntegral_complement_lt_addC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C)
    (f : IntegrableRepC3 S) (eps : CReal)
    (hgood : regularSeqLtProp (relIntegralC C hC f) eps)
    (hbad : regularSeqLtProp
      (f.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC f)).integral eps) :
    regularSeqLtProp f.integral (CReal.add eps eps) := by
  have hsum : regularSeqLtProp
      (addSeq (relIntegralC C hC f)
        (f.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC f)).integral)
      (addSeq eps eps) := regularSeqLtProp_add hgood hbad
  exact regularSeqLtProp_of_left_eventual
    (relEventually_symm _ _ (relIntegral_complement_additiveC hC f)) hsum

#print axioms BishopSec1P.relIntegral_complement_lt_addC

/-- Technical lemma used in the public import closure. -/
structure Lemma414LocalDataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n)) (eps : CReal) : Type _ where
  A : BishopC.BSet X
  hA : IntegrableSet1C S A
  N : Nat
  close : ∀ n, N ≤ n →
    Sigma (fun C : BishopC.BSet X =>
      Sigma (fun hC : IntegrableSet1C S C =>
        PProd (C.S1 ⊆ A.S1)
          (PProd
            (∀ (x : X)
              (hfabs : RepSeriesSum (fun k => absSeq (((fn n).fn k).toFun x)))
              (hχabs : RepSeriesSum (fun k => absSeq ((hC.rep.fn k).toFun x))),
              relEventually (seriesSum_of_absC hχabs).sum CReal.one →
                RegularSeqLe (seriesSum_of_absC hfabs).sum (goodSetBoundC hA eps))
            (regularSeqLtProp
              ((fn n).sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC (fn n))).integral
              eps))))

/-- Technical lemma used in the public import closure. -/
theorem lemma_4_14_local_two_epsilonC {X : Type*} {S : IntSpaceC X}
    (C A : BishopC.BSet X) (hC : IntegrableSet1C S C) (hA : IntegrableSet1C S A)
    (hsub1 : C.S1 ⊆ A.S1)
    (f : IntegrableRepC3 S) (hnn : RepNonnegC f)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps)
    (hbound : ∀ (x : X)
      (hfabs : RepSeriesSum (fun k => absSeq ((f.fn k).toFun x)))
      (hχabs : RepSeriesSum (fun k => absSeq ((hC.rep.fn k).toFun x))),
      relEventually (seriesSum_of_absC hχabs).sum CReal.one →
        RegularSeqLe (seriesSum_of_absC hfabs).sum (goodSetBoundC hA eps))
    (hbad : regularSeqLtProp
      (f.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC f)).integral eps) :
    regularSeqLtProp f.integral (CReal.add eps eps) :=
  relIntegral_complement_lt_addC hC f eps
    (relIntegral_goodSet_small_of_s1_subsetC hC hA hsub1 f hnn eps heps hbound)
    hbad

#print axioms BishopSec1P.lemma_4_14_local_two_epsilonC

/-- Technical lemma used in the public import closure. -/
def lemma_4_14_tendsto_zero_from_local_dataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (hdata : ∀ eps, regularSeqLtProp CReal.zero eps →
      Lemma414LocalDataC (S := S) fn hnn eps) :
    RepSeriesTendsto (fun n => (fn n).integral) CReal.zero where
  mod := fun k => (hdata (halfPow (k + 2)) (regularSeqLtProp_zero_halfPow (k + 2))).N
  close := by
    intro k n hn
    let D := hdata (halfPow (k + 2)) (regularSeqLtProp_zero_halfPow (k + 2))
    obtain ⟨C, hC, hpack⟩ := D.close n hn
    obtain ⟨hsub1, hpack2⟩ := hpack
    obtain ⟨hbound, hbad⟩ := hpack2
    have hlt_two : regularSeqLtProp (fn n).integral
        (CReal.add (halfPow (k + 2)) (halfPow (k + 2))) :=
      lemma_4_14_local_two_epsilonC C D.A hC D.hA hsub1 (fn n) (hnn n)
        (halfPow (k + 2)) (regularSeqLtProp_zero_halfPow (k + 2)) hbound hbad
    have hlt_half : regularSeqLtProp (fn n).integral (halfPow (k + 1)) :=
      regularSeqLtProp_of_right_eventual (halfPow_succ_add_self (k + 1)) hlt_two
    have hnon : RegularSeqNonneg ((fn n).integral) :=
      regularSeqNonneg_of_eventual
        (relEventually_symm _ _ (IntegrableRepC3.normL1_eq_integral_of_nonnegC (fn n) (hnn n)))
        (IntegrableRepC3.normL1_nonnegC (fn n))
    exact repCloseAtGauge_zero_of_nonneg_le_ltC hnon (regularSeqLe_refl _) hlt_half

#print axioms BishopSec1P.lemma_4_14_tendsto_zero_from_local_dataC

/-- Technical lemma used in the public import closure. -/
def lemma_4_14_local_data_from_uniform_and_goodC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (hui : ∀ eps, regularSeqLtProp CReal.zero eps →
      Lemma414UniformComplementDataC (S := S) fn hnn eps)
    (hgood : ∀ eps, regularSeqLtProp CReal.zero eps → ∀ (A : BishopC.BSet X)
        (hA : IntegrableSet1C S A) (delta : CReal),
        regularSeqLtProp CReal.zero delta →
          Lemma414GoodSetDataC (S := S) fn A hA delta eps) :
    ∀ eps, regularSeqLtProp CReal.zero eps → Lemma414LocalDataC (S := S) fn hnn eps := by
  intro eps heps
  let U := hui eps heps
  let G := hgood eps heps U.A U.hA U.delta U.delta_pos
  exact
    { A := U.A
      hA := U.hA
      N := Nat.max U.N G.N
      close := by
        intro n hn
        have hnU : U.N ≤ n := Nat.le_trans (Nat.le_max_left U.N G.N) hn
        have hnG : G.N ≤ n := Nat.le_trans (Nat.le_max_right U.N G.N) hn
        obtain ⟨C, hC, hpack⟩ := G.close n hnG
        obtain ⟨hsub1, hpack2⟩ := hpack
        obtain ⟨hmeasure, hbound⟩ := hpack2
        have hbad := U.small n hnU C hC hmeasure
        exact ⟨C, hC, ⟨hsub1, ⟨hbound, hbad⟩⟩⟩ }

#print axioms BishopSec1P.lemma_4_14_local_data_from_uniform_and_goodC

/-- Technical lemma used in the public import closure. -/
def lemma_4_14_tendsto_zero_from_uniform_and_good_dataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (hui : ∀ eps, regularSeqLtProp CReal.zero eps →
      Lemma414UniformComplementDataC (S := S) fn hnn eps)
    (hgood : ∀ eps, regularSeqLtProp CReal.zero eps → ∀ (A : BishopC.BSet X)
        (hA : IntegrableSet1C S A) (delta : CReal),
        regularSeqLtProp CReal.zero delta →
          Lemma414GoodSetDataC (S := S) fn A hA delta eps) :
    RepSeriesTendsto (fun n => (fn n).integral) CReal.zero :=
  lemma_4_14_tendsto_zero_from_local_dataC fn hnn
    (lemma_4_14_local_data_from_uniform_and_goodC fn hnn hui hgood)

#print axioms BishopSec1P.lemma_4_14_tendsto_zero_from_uniform_and_good_dataC

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_uniform_and_rep_convergeC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (hui : ∀ eps, regularSeqLtProp CReal.zero eps →
      Lemma414UniformComplementDataC (S := S) fn hnn eps)
    (hconv : Lemma414RepConvergeToZeroDataC (S := S) fn) :
    RepSeriesTendsto (fun n => (fn n).integral) CReal.zero :=
  lemma_4_14_tendsto_zero_from_uniform_and_good_dataC fn hnn hui
    (fun eps heps A hA delta hdelta =>
      lemma_4_14_good_set_data_from_rep_convergeC fn hconv eps heps A hA delta hdelta)

#print axioms BishopSec1P.lemma_4_14_tendsto_zero_from_uniform_and_rep_convergeC

/-- Technical lemma used in the public import closure. -/
def thm_4_15_integral_convergence_dctC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (h5 : RepSeriesTendsto (fun n => ((fn n).sub f).absVal.integral) CReal.zero) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral where
  mod := fun k => h5.mod (k + 1)
  close := by
    intro k n hn
    have hclose : RepCloseAtGauge (k + 2) (((fn n).sub f).absVal.integral) CReal.zero :=
      h5.close (k + 1) n hn
    refine repCloseAtGauge_of_absdiff_le (k + 1) ?_ hclose
    have hLHS : relEventually
        (absSeq (subSeq (fn n).integral f.integral))
        (CReal.abs ((fn n).sub f).integral) :=
      absSeq_respects_eventually _ _
        (subSeq_eq_add_neg_eventually (fn n).integral f.integral)
    have htri : RegularSeqLe (CReal.abs ((fn n).sub f).integral)
        (((fn n).sub f).absVal.integral) :=
      IntegrableRepC3.abs_integral_le_normL1C ((fn n).sub f)
    have hle_absu : RegularSeqLe (((fn n).sub f).absVal.integral)
        (absSeq (((fn n).sub f).absVal.integral)) :=
      base_le_abs_base_regularSeqLe _
    have hRHS : relEventually
        (absSeq (((fn n).sub f).absVal.integral))
        (absSeq (subSeq (((fn n).sub f).absVal.integral) CReal.zero)) :=
      relEventually_symm _ _
        (absSeq_respects_eventually _ _
          (subSeq_zero_right_eventually (((fn n).sub f).absVal.integral)))
    exact regularSeqLe_of_right_eventual hRHS
      (regularSeqLe_of_left_eventual hLHS
        (regularSeqLe_trans htri hle_absu))

#print axioms BishopSec1P.thm_4_15_integral_convergence_dctC

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_15_abs_errorC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S) :
    Nat → IntegrableRepC3 S :=
  fun n => ((fn n).sub f).absVal

#print axioms BishopSec1P.thm_4_15_abs_errorC

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_15_integral_convergence_from_uniform_and_rep_convergeC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (hnn : ∀ n, RepNonnegC (thm_4_15_abs_errorC fn f n))
    (hui : (eps : CReal) → regularSeqLtProp CReal.zero eps →
      Lemma414UniformComplementDataC (thm_4_15_abs_errorC fn f) hnn eps)
    (hconv : Lemma414RepConvergeToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_dctC fn f
    (lemma_4_14_tendsto_zero_from_uniform_and_rep_convergeC
      (thm_4_15_abs_errorC fn f) hnn hui hconv)

#print axioms BishopSec1P.thm_4_15_integral_convergence_from_uniform_and_rep_convergeC

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_15_integral_convergence_from_uniform_and_measure_convergeC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (hnn : ∀ n, RepNonnegC (thm_4_15_abs_errorC fn f n))
    (hui : (eps : CReal) → regularSeqLtProp CReal.zero eps →
      Lemma414UniformComplementDataC (thm_4_15_abs_errorC fn f) hnn eps)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_uniform_and_rep_convergeC fn f hnn hui
    (lemma_4_14_rep_converge_from_source_measure_converge_zeroC
      (thm_4_15_abs_errorC fn f) hconv)

#print axioms BishopSec1P.thm_4_15_integral_convergence_from_uniform_and_measure_convergeC

-- >>>v7:I.9

end BishopSec1P
