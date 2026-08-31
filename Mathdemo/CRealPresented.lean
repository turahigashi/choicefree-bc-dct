import Mathdemo.Internal.Measure.Close46ValueTargetFixed

namespace BishopCReal

open BishopC BishopCRat

private def qHalfPow : Nat -> BishopCRat.Q
  | 0 => BishopCRat.Q.one
  | Nat.succ n => BishopCRat.Q.mul BishopCRat.Q.half (qHalfPow n)

private theorem qHalfPow_num (n : Nat) : (qHalfPow n).num = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (1 : Int) * (qHalfPow n).num = 1
      rw [ih]
      rfl

private theorem qHalfPow_den (n : Nat) : (qHalfPow n).den = (2 : Int) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (2 : Int) * (qHalfPow n).den = (2 : Int) ^ (n + 1)
      rw [ih, pow_succ']

private theorem crat_halfPow_mk (n : Nat) :
    COF.halfPow (R := Scalar) n = BishopCRat.CRat.mk (qHalfPow n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change BishopCRat.CRat.half * COF.halfPow (R := Scalar) n =
        BishopCRat.CRat.mk (qHalfPow (n + 1))
      rw [ih]
      rfl

private theorem two_pow_pos_int (k : Nat) : (0 : Int) < (2 : Int) ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [pow_succ']
      exact Int.mul_pos (by decide : (0 : Int) < 2) ih

private theorem natCast_le_two_pow_int (k : Nat) : (k : Int) <= (2 : Int) ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [pow_succ']
      have hpow : (1 : Int) <= (2 : Int) ^ k := by
        have hp := two_pow_pos_int k
        omega
      omega

private theorem q_abs_num_le_two_pow (q : BishopCRat.Q) :
    (BishopCRat.Q.abs q).num <= (2 : Int) ^ q.num.natAbs := by
  unfold BishopCRat.Q.abs
  by_cases h : 0 <= q.num
  · simp only [h, if_true]
    have hnum : q.num = (q.num.natAbs : Int) := by
      exact (Int.natAbs_of_nonneg h).symm
    rw [hnum]
    exact natCast_le_two_pow_int q.num.natAbs
  · simp only [h, if_false]
    change -q.num <= (2 : Int) ^ q.num.natAbs
    have hneg_nonneg : 0 <= -q.num := by omega
    have hnum : -q.num = ((-q.num).natAbs : Int) := by
      exact (Int.natAbs_of_nonneg hneg_nonneg).symm
    rw [hnum, Int.natAbs_neg]
    exact natCast_le_two_pow_int q.num.natAbs

private theorem q_abs_mul_halfPow_not_gt_one (q : BishopCRat.Q) :
    Not (BishopCRat.Q.lt BishopCRat.Q.one
      (BishopCRat.Q.mul (BishopCRat.Q.abs q) (qHalfPow q.num.natAbs))) := by
  intro hlt
  simp only [BishopCRat.Q.lt, BishopCRat.Q.one, BishopCRat.Q.ofInt, BishopCRat.Q.mul] at hlt
  rw [qHalfPow_num, qHalfPow_den] at hlt
  have hden : (1 : Int) <= (BishopCRat.Q.abs q).den := by
    have hd := (BishopCRat.Q.abs q).den_pos
    omega
  have hpowpos : (0 : Int) <= (2 : Int) ^ q.num.natAbs := by
    have hp := two_pow_pos_int q.num.natAbs
    omega
  have hpow_le_prod : (2 : Int) ^ q.num.natAbs <=
      (BishopCRat.Q.abs q).den * ((2 : Int) ^ q.num.natAbs) := by
    have h := Int.mul_le_mul_of_nonneg_right hden hpowpos
    change (1 : Int) * ((2 : Int) ^ q.num.natAbs) <=
      (BishopCRat.Q.abs q).den * ((2 : Int) ^ q.num.natAbs) at h
    omega
  have hnum := q_abs_num_le_two_pow q
  have hprod : (BishopCRat.Q.abs q).num <=
      (BishopCRat.Q.abs q).den * ((2 : Int) ^ q.num.natAbs) :=
    Int.le_trans hnum hpow_le_prod
  omega

instance scalarMulArchPredDecidable (x : Scalar) :
    DecidablePred (fun m : Nat => Le (COF.abs x * eps m) 1) :=
  fun m => by
    unfold Le BishopC.Le
    change Decidable (Not (BishopCRat.CRat.lt (1 : Scalar) (COF.abs x * eps m)))
    infer_instance

theorem scalar_mul_arch_exists (x : Scalar) :
    Exists (fun m : Nat => Le (COF.abs x * eps m) 1) := by
  induction x using Quotient.inductionOn with
  | h q =>
      refine ⟨q.num.natAbs, ?_⟩
      unfold Le BishopC.Le eps
      rw [crat_halfPow_mk]
      change Not (BishopCRat.Q.lt BishopCRat.Q.one
        (BishopCRat.Q.mul (BishopCRat.Q.abs q) (qHalfPow q.num.natAbs)))
      exact q_abs_mul_halfPow_not_gt_one q

def cRatScalarMulArch : ScalarMulArchimedeanData where
  witness := fun x =>
    ⟨Nat.find (scalar_mul_arch_exists x),
      Nat.find_spec (scalar_mul_arch_exists x)⟩

#print axioms BishopCReal.cRatScalarMulArch
#print axioms BishopCReal.scalar_mul_arch_exists

/-- Presented constructive reals are regular sequences, with Bishop equality
provided separately by `cRealSetoid`. -/
abbrev CReal : Type := RegularSeq

/-- Bishop equality for presented constructive reals. -/
instance cRealSetoid : Setoid CReal := eventualSetoid

/-- A choice-free multiplicative Archimedean bound for a presented real. -/
def CReal.mulArchBound (x : CReal) : Nat :=
  standardBoundWith cRatScalarMulArch x

theorem CReal.mulArchBound_spec (x : CReal) :
    Le (COF.abs (COF.abs (x.val 1) + 1) * eps (CReal.mulArchBound x)) 1 :=
  standardBoundWith_spec cRatScalarMulArch x

/-- Extract a positivity gauge from a raw positivity witness. -/
def CReal.posGauge (x : CReal) (h : PosRaw x) : Nat := by
  letI : DecidablePred (fun n : Nat => COF.lt (eps n) (x.val n)) := fun n => by
    change Decidable (BishopCRat.CRat.lt (eps n) (x.val n))
    infer_instance
  exact Nat.find h

theorem CReal.posGauge_spec (x : CReal) (h : PosRaw x) :
    COF.lt (eps (CReal.posGauge x h)) (x.val (CReal.posGauge x h)) := by
  unfold CReal.posGauge
  letI : DecidablePred (fun n : Nat => COF.lt (eps n) (x.val n)) := fun n => by
    change Decidable (BishopCRat.CRat.lt (eps n) (x.val n))
    infer_instance
  exact Nat.find_spec h

theorem CReal.equiv_iff_rel (x y : CReal) : x ≈ y ↔ relEventually x y :=
  Iff.rfl

#print axioms BishopCReal.CReal
#print axioms BishopCReal.cRealSetoid
#print axioms BishopCReal.CReal.mulArchBound
#print axioms BishopCReal.CReal.mulArchBound_spec
#print axioms BishopCReal.CReal.posGauge
#print axioms BishopCReal.CReal.posGauge_spec
#print axioms BishopCReal.CReal.equiv_iff_rel

end BishopCReal

namespace BishopCReal

open BishopC BishopCRat

/-! ## Step C: presented-real ring operations over the implementation setoid -/

def CReal.zero : CReal := zeroSeq

def CReal.one : CReal := oneSeq

def CReal.neg (x : CReal) : CReal := negSeq x

def CReal.add (x y : CReal) : CReal := addSeq x y

def CReal.sub (x y : CReal) : CReal := subSeq x y

def CReal.mul (x y : CReal) : CReal :=
  mulSeqConcreteWith cRatScalarMulArch x y

theorem CReal.neg_respects_rel (x y : CReal) (hxy : rel x y) :
    rel (CReal.neg x) (CReal.neg y) := by
  change relVal (negVal x.val) (negVal y.val)
  exact neg_respects x y hxy

theorem CReal.add_respects_rel (x x' y y' : CReal)
    (hxx : rel x x') (hyy : rel y y') :
    rel (CReal.add x y) (CReal.add x' y') := by
  change relVal (addVal x.val y.val) (addVal x'.val y'.val)
  exact add_respects x x' y y' hxx hyy

theorem CReal.sub_respects_rel (x x' y y' : CReal)
    (hxx : rel x x') (hyy : rel y y') :
    rel (CReal.sub x y) (CReal.sub x' y') := by
  change relVal (subVal x.val y.val) (subVal x'.val y'.val)
  exact sub_respects x x' y y' hxx hyy

theorem CReal.neg_respects_equiv (x y : CReal) (hxy : x ≈ y) :
    CReal.neg x ≈ CReal.neg y :=
  negSeq_respects_eventually x y hxy

theorem CReal.add_respects_equiv (x x' y y' : CReal)
    (hxx : x ≈ x') (hyy : y ≈ y') :
    CReal.add x y ≈ CReal.add x' y' :=
  addSeq_respects_eventually x x' y y' hxx hyy

theorem CReal.sub_respects_equiv (x x' y y' : CReal)
    (hxx : x ≈ x') (hyy : y ≈ y') :
    CReal.sub x y ≈ CReal.sub x' y' :=
  subSeq_respects_eventually x x' y y' hxx hyy

theorem CReal.mul_respects_equiv (x x' y y' : CReal)
    (hxx : x ≈ x') (hyy : y ≈ y') :
    CReal.mul x y ≈ CReal.mul x' y' :=
  mulSeqConcrete_respects_eventually cRatScalarMulArch x x' y y' hxx hyy

theorem CReal.mul_comm_rel (x y : CReal) :
    rel (CReal.mul x y) (CReal.mul y x) := by
  change relVal
    (boundedMulValWith cRatScalarMulArch x y)
    (boundedMulValWith cRatScalarMulArch y x)
  exact bounded_mul_comm_raw_with cRatScalarMulArch x y

theorem CReal.mul_comm_equiv (x y : CReal) :
    CReal.mul x y ≈ CReal.mul y x :=
  mulSeqConcrete_comm_eventually cRatScalarMulArch x y

#print axioms BishopCReal.CReal.zero
#print axioms BishopCReal.CReal.one
#print axioms BishopCReal.CReal.neg
#print axioms BishopCReal.CReal.add
#print axioms BishopCReal.CReal.sub
#print axioms BishopCReal.CReal.mul
#print axioms BishopCReal.CReal.neg_respects_rel
#print axioms BishopCReal.CReal.add_respects_rel
#print axioms BishopCReal.CReal.sub_respects_rel
#print axioms BishopCReal.CReal.neg_respects_equiv
#print axioms BishopCReal.CReal.add_respects_equiv
#print axioms BishopCReal.CReal.sub_respects_equiv
#print axioms BishopCReal.CReal.mul_respects_equiv
#print axioms BishopCReal.CReal.mul_comm_rel
#print axioms BishopCReal.CReal.mul_comm_equiv

end BishopCReal

namespace BishopCReal

open BishopC BishopCRat

/-! ## Step D: presented-real ordered-field surface over Bishop equality -/

/-- Non-strict order on presented constructive reals. -/
def CReal.le (x y : CReal) : Prop :=
  RegularSeqNonneg (subSeq y x)

/-- Strict order on presented constructive reals, using the raw positivity
surface already available for representatives. -/
def CReal.lt (x y : CReal) : Prop :=
  PosRaw (subSeq y x)

theorem CReal.le_refl (x : CReal) : CReal.le x x := by
  change RegularSeqLe x x
  exact regularSeqLe_refl x

theorem CReal.le_trans {x y z : CReal} :
    CReal.le x y → CReal.le y z → CReal.le x z := by
  intro hxy hyz
  change RegularSeqLe x y at hxy
  change RegularSeqLe y z at hyz
  change RegularSeqLe x z
  exact regularSeqLe_trans hxy hyz

theorem CReal.le_respects_equiv {x x' y y' : CReal}
    (hx : x ≈ x') (hy : y ≈ y') :
    CReal.le x y ↔ CReal.le x' y' := by
  constructor
  · intro hxy
    change RegularSeqLe x y at hxy
    change RegularSeqLe x' y'
    have hxle : RegularSeqLe x' x :=
      regularSeqLe_of_right_eventual
        (relEventually_symm x x' hx)
        (regularSeqLe_refl x')
    have hx_y' : RegularSeqLe x y' :=
      regularSeqLe_of_right_eventual hy hxy
    exact regularSeqLe_trans hxle hx_y'
  · intro hxy
    change RegularSeqLe x' y' at hxy
    change RegularSeqLe x y
    have hxle : RegularSeqLe x x' :=
      regularSeqLe_of_right_eventual hx (regularSeqLe_refl x)
    have hx'_y : RegularSeqLe x' y :=
      regularSeqLe_of_right_eventual
        (relEventually_symm y y' hy)
        hxy
    exact regularSeqLe_trans hxle hx'_y

theorem CReal.add_comm (x y : CReal) :
    CReal.add x y ≈ CReal.add y x :=
  addSeq_comm_eventually x y

theorem CReal.add_assoc (x y z : CReal) :
    CReal.add (CReal.add x y) z ≈ CReal.add x (CReal.add y z) :=
  addSeq_assoc_eventually x y z

theorem CReal.zero_add (x : CReal) :
    CReal.add CReal.zero x ≈ x :=
  addSeq_zero_left_eventually x

theorem CReal.add_zero (x : CReal) :
    CReal.add x CReal.zero ≈ x :=
  addSeq_zero_right_eventually x

theorem CReal.add_left_neg (x : CReal) :
    CReal.add (CReal.neg x) x ≈ CReal.zero :=
  addSeq_neg_left_eventually x

theorem CReal.mul_comm (x y : CReal) :
    CReal.mul x y ≈ CReal.mul y x :=
  mulSeqConcrete_comm_eventually cRatScalarMulArch x y

theorem CReal.mul_assoc (x y z : CReal) :
    CReal.mul (CReal.mul x y) z ≈ CReal.mul x (CReal.mul y z) :=
  mulSeqConcrete_assoc_eventually cRatScalarMulArch x y z

theorem CReal.one_mul (x : CReal) :
    CReal.mul CReal.one x ≈ x :=
  mulSeqConcrete_one_left_eventually cRatScalarMulArch x

theorem CReal.mul_one (x : CReal) :
    CReal.mul x CReal.one ≈ x :=
  mulSeqConcrete_one_right_eventually cRatScalarMulArch x

theorem CReal.left_distrib (x y z : CReal) :
    CReal.mul x (CReal.add y z) ≈
      CReal.add (CReal.mul x y) (CReal.mul x z) :=
  mulSeqConcrete_left_distrib_eventually cRatScalarMulArch x y z

theorem CReal.right_distrib (x y z : CReal) :
    CReal.mul (CReal.add x y) z ≈
      CReal.add (CReal.mul x z) (CReal.mul y z) :=
  mulSeqConcrete_right_distrib_eventually cRatScalarMulArch x y z

theorem CReal.eq_of_small (x y : CReal)
    (hsmall : ∀ k : Nat,
      ¬ PosEventually
        (subSeq (absSeq (subSeq x y)) (constSeq (eps k)))) :
    x ≈ y :=
  relEventually_of_no_const_lt_abs_sub x y (by
    intro k
    change ¬ PosEventually
      (subSeq (absSeq (subSeq x y)) (constSeq (eps k)))
    exact hsmall k)

theorem CReal.complete_repCarrying
    (w : Nat → CReal) (hc : CRealRepSequenceCauchyData w) :
    ∃ limit : CReal, ∃ lmod : Nat → Nat,
      ∀ k n : Nat, lmod k ≤ n →
        RepCloseAtGauge (k + 1) (w n) limit := by
  refine
    ⟨cRealRepSequenceCompleteLayer.limit w hc,
      cRealRepSequenceCompleteLayer.lmod w hc, ?_⟩
  exact cRealRepSequenceCompleteLayer.close_to_limit w hc

#print axioms BishopCReal.CReal.le
#print axioms BishopCReal.CReal.lt
#print axioms BishopCReal.CReal.le_refl
#print axioms BishopCReal.CReal.le_trans
#print axioms BishopCReal.CReal.le_respects_equiv
#print axioms BishopCReal.CReal.add_comm
#print axioms BishopCReal.CReal.add_assoc
#print axioms BishopCReal.CReal.zero_add
#print axioms BishopCReal.CReal.add_zero
#print axioms BishopCReal.CReal.add_left_neg
#print axioms BishopCReal.CReal.mul_comm
#print axioms BishopCReal.CReal.mul_assoc
#print axioms BishopCReal.CReal.one_mul
#print axioms BishopCReal.CReal.mul_one
#print axioms BishopCReal.CReal.left_distrib
#print axioms BishopCReal.CReal.right_distrib
#print axioms BishopCReal.CReal.eq_of_small
#print axioms BishopCReal.CReal.complete_repCarrying

end BishopCReal

namespace BishopCReal

open BishopC BishopCRat

/-! ## Step E: positivity-data inverse for presented reals -/

/-- Multiplicative inverse of a positive/apart presented real, from a
positivity witness. -/
def CReal.invPos (x : CReal) (h : PosEventuallyData x) : CReal :=
  positiveTailInvSeqWithBound cRatScalarMulArch x h

/-- `x * x⁻¹ ≈ 1`: the field cancellation, on positivity-witness data. -/
theorem CReal.mul_invPos_eventually_one (x : CReal) (h : PosEventuallyData x) :
    CReal.mul x (CReal.invPos x h) ≈ CReal.one := by
  change relEventually
    (mulSeqConcreteWith cRatScalarMulArch x
      (positiveTailInvSeqWithBound cRatScalarMulArch x h))
    oneSeq
  exact regularSeqPositiveInvData_mul_cancel cRatScalarMulArch h

/-- The inverse's own positivity witness, so data-indexed inverses compose. -/
def CReal.invPos_posData (x : CReal) (h : PosEventuallyData x) :
    PosEventuallyData (CReal.invPos x h) where
  k := standardBoundWith cRatScalarMulArch x + 1
  N := 1
  tail_pos := by
    intro n hn
    cases n with
    | zero => cases hn
    | succ m =>
        change COF.lt (eps (standardBoundWith cRatScalarMulArch x + 1))
          (positiveTailInvValWithBound cRatScalarMulArch x h (m + 1))
        exact positiveTailInvValWithBound_uniform_lower_succ
          cRatScalarMulArch x h m

/-- The inverse respects Bishop equality `≈`, given positivity witnesses. -/
theorem CReal.invPos_respects (x y : CReal)
    (hx : PosEventuallyData x) (hy : PosEventuallyData y) (hxy : x ≈ y) :
    CReal.invPos x hx ≈ CReal.invPos y hy := by
  change relEventually
    (positiveTailInvSeqWithBound cRatScalarMulArch x hx)
    (positiveTailInvSeqWithBound cRatScalarMulArch y hy)
  exact regularSeqPositiveInvData_respects cRatScalarMulArch hx hy hxy

#print axioms BishopCReal.CReal.invPos
#print axioms BishopCReal.CReal.mul_invPos_eventually_one
#print axioms BishopCReal.CReal.invPos_posData
#print axioms BishopCReal.CReal.invPos_respects

end BishopCReal

namespace BishopCReal

open BishopC BishopCRat

/-! ## Step F: setoid-presented reduced ordered-field bridge -/

/-- Reduced constructive ordered-field core over a setoid carrier.

The data fields live on representatives, while equational laws are stated
using the setoid equality.  This avoids quotient representative selection for
data fields such as multiplicative Archimedean bounds. -/
class PresentedReducedCore (C : Type) [Setoid C] where
  add : C → C → C
  mul : C → C → C
  neg : C → C
  zero : C
  one : C
  half : C
  lt : C → C → Prop
  abs : C → C
  max : C → C → C
  min : C → C → C
  eps : Nat → C
  add_comm : ∀ a b : C, add a b ≈ add b a
  add_assoc : ∀ a b c : C, add (add a b) c ≈ add a (add b c)
  add_zero : ∀ a : C, add a zero ≈ a
  zero_add : ∀ a : C, add zero a ≈ a
  add_left_neg : ∀ a : C, add (neg a) a ≈ zero
  mul_comm : ∀ a b : C, mul a b ≈ mul b a
  mul_assoc : ∀ a b c : C, mul (mul a b) c ≈ mul a (mul b c)
  one_mul : ∀ a : C, mul one a ≈ a
  mul_one : ∀ a : C, mul a one ≈ a
  left_distrib : ∀ a b c : C, mul a (add b c) ≈ add (mul a b) (mul a c)
  right_distrib : ∀ a b c : C, mul (add a b) c ≈ add (mul a c) (mul b c)
  half_add_half : add half half ≈ one
  max_halfsum :
    ∀ a b : C, max a b ≈
      mul half (add (add a b) (abs (add a (neg b))))
  min_halfsum :
    ∀ a b : C, min a b ≈
      mul half (add (add a b) (neg (abs (add a (neg b)))))
  abs_zero : abs zero ≈ zero
  abs_neg : ∀ a : C, abs (neg a) ≈ abs a
  abs_mul : ∀ a b : C, abs (mul a b) ≈ mul (abs a) (abs b)
  lt_irrefl : ∀ a : C, ¬ lt a a
  neg_le_abs : ∀ a : C, ¬ lt (abs a) (neg a)
  le_abs_self : ∀ a : C, ¬ lt (abs a) a
  one_pos : lt zero one
  half_pos : lt zero half
  abs_add_le : ∀ a b : C, ¬ lt (add (abs a) (abs b)) (abs (add a b))
  eq_of_small :
    ∀ {a b : C},
      (∀ k : Nat, ¬ lt (eps k) (abs (add a (neg b)))) → a ≈ b
  mul_archimedean :
    ∀ x : C, {m : Nat // ¬ lt one (mul (abs x) (eps m))}

def CReal.half : CReal := halfSeq

def CReal.abs (x : CReal) : CReal := absSeq x

def CReal.max (x y : CReal) : CReal :=
  maxSeqWith cRatScalarMulArch x y

def CReal.min (x y : CReal) : CReal :=
  minSeqWith cRatScalarMulArch x y

def CReal.epsSeq (n : Nat) : CReal :=
  constSeq (BishopCReal.eps n)

theorem CReal.half_add_half :
    CReal.add CReal.half CReal.half ≈ CReal.one := by
  change relEventually (addSeq halfSeq halfSeq) oneSeq
  exact addSeq_half_half_eventually_one

theorem CReal.max_halfsum (x y : CReal) :
    CReal.max x y ≈
      CReal.mul CReal.half
        (CReal.add (CReal.add x y) (CReal.abs (CReal.add x (CReal.neg y)))) := by
  change relEventually
    (maxSeqWith cRatScalarMulArch x y)
    (mulSeqConcreteWith cRatScalarMulArch halfSeq
      (addSeq (addSeq x y) (absSeq (addSeq x (negSeq y)))))
  unfold maxSeqWith
  have hsub : relEventually (subSeq x y) (addSeq x (negSeq y)) :=
    subSeq_eq_add_neg_eventually x y
  have habs :
      relEventually (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y))) :=
    absSeq_respects_eventually (subSeq x y) (addSeq x (negSeq y)) hsub
  have hbody :
      relEventually
        (addSeq (addSeq x y) (absSeq (subSeq x y)))
        (addSeq (addSeq x y) (absSeq (addSeq x (negSeq y)))) :=
    addSeq_respects_eventually
      (addSeq x y) (addSeq x y)
      (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y)))
      (relEventually_refl (addSeq x y)) habs
  exact mulSeqConcrete_respects_eventually cRatScalarMulArch
    halfSeq halfSeq
    (addSeq (addSeq x y) (absSeq (subSeq x y)))
    (addSeq (addSeq x y) (absSeq (addSeq x (negSeq y))))
    (relEventually_refl halfSeq) hbody

theorem CReal.min_halfsum (x y : CReal) :
    CReal.min x y ≈
      CReal.mul CReal.half
        (CReal.add (CReal.add x y)
          (CReal.neg (CReal.abs (CReal.add x (CReal.neg y))))) := by
  change relEventually
    (minSeqWith cRatScalarMulArch x y)
    (mulSeqConcreteWith cRatScalarMulArch halfSeq
      (addSeq (addSeq x y) (negSeq (absSeq (addSeq x (negSeq y))))))
  unfold minSeqWith
  have hsub : relEventually (subSeq x y) (addSeq x (negSeq y)) :=
    subSeq_eq_add_neg_eventually x y
  have habs :
      relEventually (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y))) :=
    absSeq_respects_eventually (subSeq x y) (addSeq x (negSeq y)) hsub
  have hsubBody :
      relEventually
        (subSeq (addSeq x y) (absSeq (subSeq x y)))
        (addSeq (addSeq x y) (negSeq (absSeq (subSeq x y)))) :=
    subSeq_eq_add_neg_eventually (addSeq x y) (absSeq (subSeq x y))
  have hneg :
      relEventually
        (negSeq (absSeq (subSeq x y)))
        (negSeq (absSeq (addSeq x (negSeq y)))) :=
    negSeq_respects_eventually
      (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y))) habs
  have hadd :
      relEventually
        (addSeq (addSeq x y) (negSeq (absSeq (subSeq x y))))
        (addSeq (addSeq x y) (negSeq (absSeq (addSeq x (negSeq y))))) :=
    addSeq_respects_eventually
      (addSeq x y) (addSeq x y)
      (negSeq (absSeq (subSeq x y)))
      (negSeq (absSeq (addSeq x (negSeq y))))
      (relEventually_refl (addSeq x y)) hneg
  have hbody :
      relEventually
        (subSeq (addSeq x y) (absSeq (subSeq x y)))
        (addSeq (addSeq x y) (negSeq (absSeq (addSeq x (negSeq y))))) :=
    relEventually_trans
      (subSeq (addSeq x y) (absSeq (subSeq x y)))
      (addSeq (addSeq x y) (negSeq (absSeq (subSeq x y))))
      (addSeq (addSeq x y) (negSeq (absSeq (addSeq x (negSeq y)))))
      hsubBody hadd
  exact mulSeqConcrete_respects_eventually cRatScalarMulArch
    halfSeq halfSeq
    (subSeq (addSeq x y) (absSeq (subSeq x y)))
    (addSeq (addSeq x y) (negSeq (absSeq (addSeq x (negSeq y)))))
    (relEventually_refl halfSeq) hbody

theorem CReal.abs_zero : CReal.abs CReal.zero ≈ CReal.zero := by
  change relEventually (absSeq zeroSeq) zeroSeq
  exact rel_to_relEventually (absSeq zeroSeq) zeroSeq abs_zero_raw

theorem CReal.abs_neg (x : CReal) :
    CReal.abs (CReal.neg x) ≈ CReal.abs x := by
  change relEventually (absSeq (negSeq x)) (absSeq x)
  exact rel_to_relEventually (absSeq (negSeq x)) (absSeq x) (abs_neg_raw x)

theorem CReal.abs_mul (x y : CReal) :
    CReal.abs (CReal.mul x y) ≈
      CReal.mul (CReal.abs x) (CReal.abs y) := by
  change relEventually
    (absSeq (mulSeqConcreteWith cRatScalarMulArch x y))
    (mulSeqConcreteWith cRatScalarMulArch (absSeq x) (absSeq y))
  exact
    BishopRegularSeqChapter2.Prop24HalfTermLaw.abs_mulSeqConcrete_eventually
      cRatScalarMulArch x y

theorem CReal.lt_irrefl (x : CReal) : ¬ CReal.lt x x := by
  intro h
  change PosVal (subVal x.val x.val) at h
  exact lt_irrefl_raw x h

theorem CReal.one_pos : CReal.lt CReal.zero CReal.one := by
  change PosRaw (subSeq oneSeq zeroSeq)
  rcases one_pos_raw with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change COF.lt (BishopCReal.eps k) ((1 : Scalar) - 0)
  simpa [sub_zero] using hk

theorem CReal.half_pos : CReal.lt CReal.zero CReal.half := by
  change PosRaw (subSeq halfSeq zeroSeq)
  rcases half_pos_raw with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  change COF.lt (BishopCReal.eps k) ((COF.half : Scalar) - 0)
  simpa [sub_zero] using hk

theorem CReal.not_posRaw_sub_neg_abs (x : CReal) :
    ¬ PosRaw (subSeq (negSeq x) (absSeq x)) := by
  intro h
  rcases h with ⟨n, hpoint⟩
  have hpoint' : COF.lt (BishopCReal.eps n)
      ((-x.val (n + 1)) - COF.abs (x.val (n + 1))) := by
    simpa [subSeq, subVal, addIndex, negSeq, negVal, absSeq, absVal]
      using hpoint
  have hzero :
      COF.lt (0 : Scalar) ((-x.val (n + 1)) - COF.abs (x.val (n + 1))) :=
    scalarCOFOSeed.lt_trans (eps_pos n) hpoint'
  have hbad : COF.lt (COF.abs (x.val (n + 1))) (-x.val (n + 1)) := by
    have t := COF.lt_add_left (COF.abs (x.val (n + 1))) hzero
    rwa [show COF.abs (x.val (n + 1)) + (0 : Scalar) =
          COF.abs (x.val (n + 1)) from by ring,
      show COF.abs (x.val (n + 1)) +
            ((-x.val (n + 1)) - COF.abs (x.val (n + 1))) =
          -x.val (n + 1) from by ring] at t
  exact scalarCOFOSeed.neg_le_abs (x.val (n + 1)) hbad

theorem CReal.neg_le_abs (x : CReal) :
    ¬ CReal.lt (CReal.abs x) (CReal.neg x) := by
  change ¬ PosRaw (subSeq (negSeq x) (absSeq x))
  exact CReal.not_posRaw_sub_neg_abs x

theorem CReal.not_posRaw_sub_self_abs (x : CReal) :
    ¬ PosRaw (subSeq x (absSeq x)) := by
  intro h
  rcases h with ⟨n, hpoint⟩
  have hpoint' : COF.lt (BishopCReal.eps n)
      (x.val (n + 1) - COF.abs (x.val (n + 1))) := by
    simpa [subSeq, subVal, addIndex, absSeq, absVal] using hpoint
  have hzero :
      COF.lt (0 : Scalar) (x.val (n + 1) - COF.abs (x.val (n + 1))) :=
    scalarCOFOSeed.lt_trans (eps_pos n) hpoint'
  have hbad : COF.lt (COF.abs (x.val (n + 1))) (x.val (n + 1)) := by
    have t := COF.lt_add_left (COF.abs (x.val (n + 1))) hzero
    rwa [show COF.abs (x.val (n + 1)) + (0 : Scalar) =
          COF.abs (x.val (n + 1)) from by ring,
      show COF.abs (x.val (n + 1)) +
            (x.val (n + 1) - COF.abs (x.val (n + 1))) =
          x.val (n + 1) from by ring] at t
  exact scalarCOFOSeed.le_abs_self (x.val (n + 1)) hbad

theorem CReal.le_abs_self (x : CReal) :
    ¬ CReal.lt (CReal.abs x) x := by
  change ¬ PosRaw (subSeq x (absSeq x))
  exact CReal.not_posRaw_sub_self_abs x

theorem CReal.not_posRaw_abs_add_reverse (x y : CReal) :
    ¬ PosRaw
      (subSeq (absSeq (addSeq x y)) (addSeq (absSeq x) (absSeq y))) := by
  intro h
  rcases h with ⟨n, hpoint⟩
  have hpoint' : COF.lt (BishopCReal.eps n)
      (COF.abs (x.val ((n + 1) + 1) + y.val ((n + 1) + 1)) -
        (COF.abs (x.val ((n + 1) + 1)) +
          COF.abs (y.val ((n + 1) + 1)))) := by
    simpa [subSeq, subVal, addIndex, absSeq, absVal, addSeq, addVal]
      using hpoint
  have hzero : COF.lt (0 : Scalar)
      (COF.abs (x.val ((n + 1) + 1) + y.val ((n + 1) + 1)) -
        (COF.abs (x.val ((n + 1) + 1)) +
          COF.abs (y.val ((n + 1) + 1)))) :=
    scalarCOFOSeed.lt_trans (eps_pos n) hpoint'
  have hbad : COF.lt
      (COF.abs (x.val ((n + 1) + 1)) + COF.abs (y.val ((n + 1) + 1)))
      (COF.abs (x.val ((n + 1) + 1) + y.val ((n + 1) + 1))) := by
    have t := COF.lt_add_left
      (COF.abs (x.val ((n + 1) + 1)) + COF.abs (y.val ((n + 1) + 1)))
      hzero
    rwa [show
        (COF.abs (x.val ((n + 1) + 1)) + COF.abs (y.val ((n + 1) + 1))) +
            (0 : Scalar) =
          COF.abs (x.val ((n + 1) + 1)) + COF.abs (y.val ((n + 1) + 1))
        from by ring,
      show
        (COF.abs (x.val ((n + 1) + 1)) + COF.abs (y.val ((n + 1) + 1))) +
            (COF.abs (x.val ((n + 1) + 1) + y.val ((n + 1) + 1)) -
              (COF.abs (x.val ((n + 1) + 1)) +
                COF.abs (y.val ((n + 1) + 1)))) =
          COF.abs (x.val ((n + 1) + 1) + y.val ((n + 1) + 1))
        from by ring] at t
  have htri : Le
      (COF.abs (x.val ((n + 1) + 1) + y.val ((n + 1) + 1)))
      (COF.abs (x.val ((n + 1) + 1)) + COF.abs (y.val ((n + 1) + 1))) :=
    scalar_abs_add_le (x.val ((n + 1) + 1)) (y.val ((n + 1) + 1))
  exact htri hbad

theorem CReal.abs_add_le (x y : CReal) :
    ¬ CReal.lt
      (CReal.add (CReal.abs x) (CReal.abs y))
      (CReal.abs (CReal.add x y)) := by
  change ¬ PosRaw
    (subSeq (absSeq (addSeq x y)) (addSeq (absSeq x) (absSeq y)))
  exact CReal.not_posRaw_abs_add_reverse x y

theorem CReal.posEventually_to_posRaw {x : CReal}
    (hx : PosEventually x) : PosRaw x := by
  rcases hx with ⟨k, N, hN⟩
  let n0 : Nat := N + k + 1
  refine ⟨n0, ?_⟩
  have hNle : N ≤ n0 := by
    unfold n0
    omega
  have hkStep : k + 1 ≤ n0 := by
    unfold n0
    omega
  have htail : COF.lt (BishopCReal.eps k) (x.val n0) := hN n0 hNle
  have hle : Le (BishopCReal.eps n0) (BishopCReal.eps (k + 1)) :=
    eps_le_of_le hkStep
  have hstrict : COF.lt (BishopCReal.eps n0) (BishopCReal.eps k) :=
    scalar_lt_of_le_of_lt hle (eps_succ_lt_eps k)
  exact scalarCOFOSeed.lt_trans hstrict htail

theorem CReal.eq_of_small_posRaw (x y : CReal)
    (hsmall : ∀ k : Nat,
      ¬ CReal.lt (CReal.epsSeq k)
        (CReal.abs (CReal.add x (CReal.neg y)))) :
    x ≈ y := by
  apply CReal.eq_of_small x y
  intro k hp
  have hsub : relEventually (subSeq x y) (addSeq x (negSeq y)) :=
    subSeq_eq_add_neg_eventually x y
  have habs :
      relEventually (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y))) :=
    absSeq_respects_eventually (subSeq x y) (addSeq x (negSeq y)) hsub
  have hseq :
      relEventually
        (subSeq (absSeq (subSeq x y)) (constSeq (BishopCReal.eps k)))
        (subSeq (absSeq (addSeq x (negSeq y))) (constSeq (BishopCReal.eps k))) :=
    subSeq_respects_eventually
      (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y)))
      (constSeq (BishopCReal.eps k)) (constSeq (BishopCReal.eps k))
      habs (relEventually_refl (constSeq (BishopCReal.eps k)))
  have hp' :
      PosEventually
        (subSeq (absSeq (addSeq x (negSeq y))) (constSeq (BishopCReal.eps k))) :=
    posEventually_respects
      (subSeq (absSeq (subSeq x y)) (constSeq (BishopCReal.eps k)))
      (subSeq (absSeq (addSeq x (negSeq y))) (constSeq (BishopCReal.eps k)))
      hseq hp
  apply hsmall k
  change PosRaw
    (subSeq (absSeq (addSeq x (negSeq y))) (constSeq (BishopCReal.eps k)))
  exact CReal.posEventually_to_posRaw hp'

theorem CReal.not_posRaw_abs_mul_standard_sub_one (x : CReal) :
    ¬ PosRaw
      (subSeq
        (mulSeqConcreteWith cRatScalarMulArch (absSeq x)
          (constSeq (BishopCReal.eps (standardBoundWith cRatScalarMulArch x))))
        oneSeq) := by
  intro h
  rcases h with ⟨n, hpoint⟩
  set m : Nat := standardBoundWith cRatScalarMulArch x with hmdef
  set K : Nat := mulBoundWith cRatScalarMulArch (absSeq x)
    (constSeq (BishopCReal.eps m))
    with hKdef
  set q : Nat := mulIndexFromBound K (n + 1) with hqdef
  have hpoint' : COF.lt (BishopCReal.eps n)
      ((COF.abs (x.val q) * BishopCReal.eps m) - 1) := by
    simpa [subSeq, subVal, oneSeq, constSeq, oneVal, constVal,
      mulSeqConcreteWith, mulSeqWith, boundedMulValWith, mulValWithBound,
      absSeq, absVal, hKdef, hqdef, hmdef] using hpoint
  have hzero : COF.lt (0 : Scalar)
      ((COF.abs (x.val q) * BishopCReal.eps m) - 1) :=
    scalarCOFOSeed.lt_trans (eps_pos n) hpoint'
  have hbad : COF.lt (1 : Scalar) (COF.abs (x.val q) * BishopCReal.eps m) := by
    have t := COF.lt_add_left (1 : Scalar) hzero
    rwa [show (1 : Scalar) + 0 = 1 from by ring,
      show (1 : Scalar) + ((COF.abs (x.val q) * BishopCReal.eps m) - 1) =
          COF.abs (x.val q) * BishopCReal.eps m from by ring] at t
  have hle : Le (COF.abs (x.val q) * BishopCReal.eps m) 1 := by
    rw [hmdef, hqdef]
    exact abs_sample_mul_standard_eps_le_one cRatScalarMulArch x K (n + 1)
  exact hle hbad

def CReal.mul_archimedean (x : CReal) :
    {m : Nat //
      ¬ CReal.lt CReal.one
        (CReal.mul (CReal.abs x) (CReal.epsSeq m))} := by
  refine ⟨standardBoundWith cRatScalarMulArch x, ?_⟩
  change ¬ PosRaw
    (subSeq
      (mulSeqConcreteWith cRatScalarMulArch (absSeq x)
        (constSeq (BishopCReal.eps (standardBoundWith cRatScalarMulArch x))))
      oneSeq)
  exact CReal.not_posRaw_abs_mul_standard_sub_one x

instance instPresentedReducedCoreCReal : PresentedReducedCore CReal where
  add := CReal.add
  mul := CReal.mul
  neg := CReal.neg
  zero := CReal.zero
  one := CReal.one
  half := CReal.half
  lt := CReal.lt
  abs := CReal.abs
  max := CReal.max
  min := CReal.min
  eps := CReal.epsSeq
  add_comm := CReal.add_comm
  add_assoc := CReal.add_assoc
  add_zero := CReal.add_zero
  zero_add := CReal.zero_add
  add_left_neg := CReal.add_left_neg
  mul_comm := CReal.mul_comm
  mul_assoc := CReal.mul_assoc
  one_mul := CReal.one_mul
  mul_one := CReal.mul_one
  left_distrib := CReal.left_distrib
  right_distrib := CReal.right_distrib
  half_add_half := CReal.half_add_half
  max_halfsum := CReal.max_halfsum
  min_halfsum := CReal.min_halfsum
  abs_zero := CReal.abs_zero
  abs_neg := CReal.abs_neg
  abs_mul := CReal.abs_mul
  lt_irrefl := CReal.lt_irrefl
  neg_le_abs := CReal.neg_le_abs
  le_abs_self := CReal.le_abs_self
  one_pos := CReal.one_pos
  half_pos := CReal.half_pos
  abs_add_le := CReal.abs_add_le
  eq_of_small := by
    intro a b hsmall
    exact CReal.eq_of_small_posRaw a b hsmall
  mul_archimedean := CReal.mul_archimedean

#print axioms BishopCReal.PresentedReducedCore
#print axioms BishopCReal.PresentedReducedCore.add_comm
#print axioms BishopCReal.PresentedReducedCore.mul_archimedean
#print axioms BishopCReal.CReal.half
#print axioms BishopCReal.CReal.abs
#print axioms BishopCReal.CReal.max
#print axioms BishopCReal.CReal.min
#print axioms BishopCReal.CReal.epsSeq
#print axioms BishopCReal.CReal.half_add_half
#print axioms BishopCReal.CReal.max_halfsum
#print axioms BishopCReal.CReal.min_halfsum
#print axioms BishopCReal.CReal.abs_zero
#print axioms BishopCReal.CReal.abs_neg
#print axioms BishopCReal.CReal.abs_mul
#print axioms BishopCReal.CReal.lt_irrefl
#print axioms BishopCReal.CReal.one_pos
#print axioms BishopCReal.CReal.half_pos
#print axioms BishopCReal.CReal.not_posRaw_sub_neg_abs
#print axioms BishopCReal.CReal.neg_le_abs
#print axioms BishopCReal.CReal.not_posRaw_sub_self_abs
#print axioms BishopCReal.CReal.le_abs_self
#print axioms BishopCReal.CReal.not_posRaw_abs_add_reverse
#print axioms BishopCReal.CReal.abs_add_le
#print axioms BishopCReal.CReal.posEventually_to_posRaw
#print axioms BishopCReal.CReal.eq_of_small_posRaw
#print axioms BishopCReal.CReal.not_posRaw_abs_mul_standard_sub_one
#print axioms BishopCReal.CReal.mul_archimedean
#print axioms BishopCReal.instPresentedReducedCoreCReal

end BishopCReal

namespace BishopCReal

open BishopC BishopCRat

/-! ## Step G: invariant strict order for presented reals -/

/-- The invariant strict order on presented constructive reals. -/
def CReal.ltE (x y : CReal) : Prop :=
  regularSeqLtProp x y

/-- Data form of the invariant strict order on presented constructive reals. -/
def CReal.ltED (x y : CReal) : Type :=
  regularSeqLtData x y

theorem CReal.ltE_irrefl (x : CReal) : ¬ CReal.ltE x x := by
  change ¬ regularSeqLtProp x x
  exact regularSeqLtProp_irrefl x

theorem CReal.ltE_cotrans {a b : CReal}
    (h : CReal.ltE a b) (c : CReal) :
    CReal.ltE a c ∨ CReal.ltE c b := by
  change regularSeqLtProp a c ∨ regularSeqLtProp c b
  exact regularSeqLtProp_cotrans a b c h

theorem CReal.ltE_add_left (c : CReal) {a b : CReal}
    (h : CReal.ltE a b) :
    CReal.ltE (CReal.add c a) (CReal.add c b) := by
  change regularSeqLtProp (addSeq c a) (addSeq c b)
  exact regularSeqLtProp_add_left c a b h

theorem CReal.ltE_trans {a b c : CReal}
    (hab : CReal.ltE a b) (hbc : CReal.ltE b c) :
    CReal.ltE a c := by
  change regularSeqLtProp a c
  exact regularSeqLtProp_trans a b c hab hbc

theorem CReal.one_pos_E : CReal.ltE CReal.zero CReal.one := by
  change ltQuot zeroQuot oneQuot
  exact ltQuot_zero_one

theorem CReal.half_pos_E : CReal.ltE CReal.zero CReal.half := by
  change ltQuot zeroQuot halfQuot
  exact ltQuot_zero_half

theorem CReal.neg_le_abs_E (x : CReal) :
    ¬ CReal.ltE (CReal.abs x) (CReal.neg x) := by
  change ¬ ltQuot (absQuot (mkQuot x)) (negQuot (mkQuot x))
  exact neg_le_absQuot (mkQuot x)

theorem CReal.le_abs_self_E (x : CReal) :
    ¬ CReal.ltE (CReal.abs x) x := by
  change ¬ ltQuot (absQuot (mkQuot x)) (mkQuot x)
  exact le_abs_selfQuot (mkQuot x)

theorem CReal.abs_add_le_E (x y : CReal) :
    ¬ CReal.ltE
      (CReal.add (CReal.abs x) (CReal.abs y))
      (CReal.abs (CReal.add x y)) := by
  change ¬ ltQuot
    (addQuot (absQuot (mkQuot x)) (absQuot (mkQuot y)))
    (absQuot (addQuot (mkQuot x) (mkQuot y)))
  exact abs_add_leQuot (mkQuot x) (mkQuot y)

theorem CReal.eq_of_small_E (x y : CReal)
    (hsmall : ∀ k : Nat,
      ¬ CReal.ltE (CReal.epsSeq k)
        (CReal.abs (CReal.add x (CReal.neg y)))) :
    x ≈ y := by
  apply CReal.eq_of_small x y
  intro k hp
  have hsub : relEventually (subSeq x y) (addSeq x (negSeq y)) :=
    subSeq_eq_add_neg_eventually x y
  have habs :
      relEventually (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y))) :=
    absSeq_respects_eventually (subSeq x y) (addSeq x (negSeq y)) hsub
  have hseq :
      relEventually
        (subSeq (absSeq (subSeq x y)) (constSeq (BishopCReal.eps k)))
        (subSeq (absSeq (addSeq x (negSeq y))) (constSeq (BishopCReal.eps k))) :=
    subSeq_respects_eventually
      (absSeq (subSeq x y)) (absSeq (addSeq x (negSeq y)))
      (constSeq (BishopCReal.eps k)) (constSeq (BishopCReal.eps k))
      habs (relEventually_refl (constSeq (BishopCReal.eps k)))
  have hp' :
      PosEventually
        (subSeq (absSeq (addSeq x (negSeq y))) (constSeq (BishopCReal.eps k))) :=
    posEventually_respects
      (subSeq (absSeq (subSeq x y)) (constSeq (BishopCReal.eps k)))
      (subSeq (absSeq (addSeq x (negSeq y))) (constSeq (BishopCReal.eps k)))
      hseq hp
  exact hsmall k hp'

def CReal.mul_archimedean_E (x : CReal) :
    {m : Nat //
      ¬ CReal.ltE CReal.one
        (CReal.mul (CReal.abs x) (CReal.epsSeq m))} := by
  change {m : Nat //
      ¬ regularSeqLtProp oneSeq
        (mulSeqConcreteWith cRatScalarMulArch (absSeq x)
          (constSeq (BishopCReal.eps m)))}
  exact regularSeqMulArchimedean_const_data cRatScalarMulArch x

theorem CReal.mul_pos_E {a b : CReal}
    (ha : CReal.ltE CReal.zero a) (hb : CReal.ltE CReal.zero b) :
    CReal.ltE CReal.zero (CReal.mul a b) := by
  change PosEventually
    (subSeq (mulSeqConcreteWith cRatScalarMulArch a b) zeroSeq)
  exact posEventually_sub_zero_of_pos (mulSeqConcreteWith cRatScalarMulArch a b)
    (posEventually_mul_concrete_from_sub_zero_with
      cRatScalarMulArch a b ha hb)

theorem CReal.archimedean_E (t : CReal)
    (ht : CReal.ltE CReal.zero t) :
    ∃ k : Nat, CReal.ltE (CReal.epsSeq k) t := by
  change PosEventually (subSeq t zeroSeq) at ht
  rcases ht with ⟨k, N, hN⟩
  refine ⟨k + 1, ?_⟩
  change PosEventually (subSeq t (constSeq (BishopCReal.eps (k + 1))))
  refine ⟨k + 1, N, ?_⟩
  intro n hn
  have hx := hN n hn
  change COF.lt (BishopCReal.eps k) (t.val (n + 1) - 0) at hx
  have hshift : COF.lt (BishopCReal.eps (k + 1))
      ((t.val (n + 1) - 0) - BishopCReal.eps (k + 1)) := by
    have s := COF.lt_add_left (-(BishopCReal.eps (k + 1))) hx
    rwa [← eps_succ_add_self k,
      show -(BishopCReal.eps (k + 1)) +
          (BishopCReal.eps (k + 1) + BishopCReal.eps (k + 1)) =
          BishopCReal.eps (k + 1)
        from by ring,
      show -(BishopCReal.eps (k + 1)) + (t.val (n + 1) - 0) =
          (t.val (n + 1) - 0) - BishopCReal.eps (k + 1)
        from by ring] at s
  change COF.lt (BishopCReal.eps (k + 1))
    (t.val (n + 1) - BishopCReal.eps (k + 1))
  rwa [show (t.val (n + 1) - 0) - BishopCReal.eps (k + 1) =
      t.val (n + 1) - BishopCReal.eps (k + 1) from by ring] at hshift

/-- Deterministic gauge read from a late positive point witness. -/
def CReal.archWitnessGauge (n : Nat) : Nat :=
  n / 2

/-- Decidable late-point witness strong enough to produce positive-tail data. -/
def CReal.archPosWitness (t : CReal) (n : Nat) : Prop :=
  CReal.archWitnessGauge n + 2 ≤ n ∧
    COF.lt (BishopCReal.eps (CReal.archWitnessGauge n))
      ((subSeq t zeroSeq).val n)

theorem CReal.archPosWitness_exists (t : CReal)
    (ht : CReal.ltE CReal.zero t) :
    ∃ n : Nat, CReal.archPosWitness t n := by
  change PosEventually (subSeq t zeroSeq) at ht
  rcases ht with ⟨k, N, hN⟩
  let n0 : Nat := N + 2 * k + 4
  refine ⟨n0, ?_⟩
  constructor
  · unfold CReal.archWitnessGauge n0
    omega
  · have hNn : N ≤ n0 := by
      unfold n0
      omega
    have htail := hN n0 hNn
    have hle : Le (BishopCReal.eps (CReal.archWitnessGauge n0))
        (BishopCReal.eps k) := by
      exact eps_le_of_le (by
        unfold CReal.archWitnessGauge n0
        omega)
    exact scalar_lt_of_le_of_lt hle htail

def CReal.archimedean_pos_E (t : CReal)
    (ht : CReal.ltE CReal.zero t) :
    {k : Nat // CReal.ltE (CReal.epsSeq k) t} := by
  letI : DecidablePred (CReal.archPosWitness t) := fun n => by
    unfold CReal.archPosWitness CReal.archWitnessGauge
    letI : Decidable
        (COF.lt (BishopCReal.eps (n / 2)) ((subSeq t zeroSeq).val n)) := by
      change Decidable
        (BishopCRat.CRat.lt
          (BishopCReal.eps (n / 2)) ((subSeq t zeroSeq).val n))
      infer_instance
    infer_instance
  let n : Nat := Nat.find (CReal.archPosWitness_exists t ht)
  have hn : CReal.archPosWitness t n :=
    Nat.find_spec (CReal.archPosWitness_exists t ht)
  let hxdata : PosEventuallyData (subSeq t zeroSeq) :=
    posEventuallyData_of_late_point (subSeq t zeroSeq)
      (j := CReal.archWitnessGauge n) (M := n) hn.1 hn.2
  refine ⟨hxdata.k + 1, ?_⟩
  change PosEventually
    (subSeq t (constSeq (BishopCReal.eps (hxdata.k + 1))))
  refine
    ({ k := hxdata.k + 1
       N := hxdata.N
       tail_pos := ?_ } :
      PosEventuallyData
        (subSeq t (constSeq (BishopCReal.eps (hxdata.k + 1))))).toProp
  intro m hm
  have hxpos := hxdata.tail_pos m hm
  change COF.lt (BishopCReal.eps hxdata.k)
    (t.val (m + 1) - 0) at hxpos
  have hshift : COF.lt (BishopCReal.eps (hxdata.k + 1))
      ((t.val (m + 1) - 0) - BishopCReal.eps (hxdata.k + 1)) := by
    have s := COF.lt_add_left (-(BishopCReal.eps (hxdata.k + 1))) hxpos
    rwa [← eps_succ_add_self hxdata.k,
      show -(BishopCReal.eps (hxdata.k + 1)) +
          (BishopCReal.eps (hxdata.k + 1) +
            BishopCReal.eps (hxdata.k + 1)) =
          BishopCReal.eps (hxdata.k + 1)
        from by ring,
      show -(BishopCReal.eps (hxdata.k + 1)) + (t.val (m + 1) - 0) =
          (t.val (m + 1) - 0) - BishopCReal.eps (hxdata.k + 1)
        from by ring] at s
  change COF.lt (BishopCReal.eps (hxdata.k + 1))
    (t.val (m + 1) - BishopCReal.eps (hxdata.k + 1))
  rwa [show (t.val (m + 1) - 0) - BishopCReal.eps (hxdata.k + 1) =
      t.val (m + 1) - BishopCReal.eps (hxdata.k + 1) from by ring] at hshift

theorem CReal.abs_of_nonneg_E {a : CReal}
    (ha : ¬ CReal.ltE a CReal.zero) :
    CReal.abs a ≈ a := by
  have haq : ¬ ltQuot (mkQuot a) zeroQuot := by
    change ¬ PosEventually (subSeq zeroSeq a)
    exact ha
  have hq : mkQuot (absSeq a) = mkQuot a := by
    change absQuot (mkQuot a) = mkQuot a
    exact absQuot_of_nonneg (mkQuot a) haq
  exact Quotient.exact hq

theorem CReal.abs_le_of_E {a b : CReal}
    (hba : ¬ CReal.ltE b a)
    (hbna : ¬ CReal.ltE b (CReal.neg a)) :
    ¬ CReal.ltE b (CReal.abs a) := by
  change ¬ ltQuot (mkQuot b) (absQuot (mkQuot a))
  exact absQuot_le_of (a := mkQuot a) (b := mkQuot b)
    (by
      change ¬ regularSeqLtProp b a
      exact hba)
    (by
      change ¬ regularSeqLtProp b (negSeq a)
      exact hbna)

theorem CReal.max_zero_nonneg_E (a : CReal) :
    ¬ CReal.ltE (CReal.max a CReal.zero) CReal.zero := by
  change ¬ ltQuot (maxQuotCOFWith cRatScalarMulArch (mkQuot a) zeroQuot) zeroQuot
  exact maxQuotCOF_zero_nonneg_with cRatScalarMulArch (mkQuot a)

theorem CReal.max_le_abs_E (a : CReal) :
    ¬ CReal.ltE (CReal.abs a) (CReal.max a CReal.zero) := by
  change ¬ ltQuot (absQuot (mkQuot a))
    (maxQuotCOFWith cRatScalarMulArch (mkQuot a) zeroQuot)
  exact maxQuotCOF_le_abs_with cRatScalarMulArch (mkQuot a)

theorem CReal.neg_min_zero_nonneg_E (a : CReal) :
    ¬ CReal.ltE (CReal.neg (CReal.min a CReal.zero)) CReal.zero := by
  change ¬ ltQuot
    (negQuot (minQuotCOFWith cRatScalarMulArch (mkQuot a) zeroQuot))
    zeroQuot
  exact neg_minQuotCOF_zero_nonneg_with cRatScalarMulArch (mkQuot a)

theorem CReal.neg_min_le_abs_E (a : CReal) :
    ¬ CReal.ltE (CReal.abs a) (CReal.neg (CReal.min a CReal.zero)) := by
  change ¬ ltQuot (absQuot (mkQuot a))
    (negQuot (minQuotCOFWith cRatScalarMulArch (mkQuot a) zeroQuot))
  exact neg_minQuotCOF_le_abs_with cRatScalarMulArch (mkQuot a)

theorem CReal.lt_or_lt_of_abs_pos_E {c : CReal}
    (hc : CReal.ltE CReal.zero (CReal.abs c)) :
    CReal.ltE CReal.zero c ∨ CReal.ltE c CReal.zero := by
  change ltQuot zeroQuot (mkQuot c) ∨ ltQuot (mkQuot c) zeroQuot
  exact ltQuot_zero_abs_split (mkQuot c) (by
    change CReal.ltE CReal.zero (CReal.abs c)
    exact hc)

theorem CReal.mul_nonneg_E {a b : CReal}
    (ha : ¬ CReal.ltE a CReal.zero)
    (hb : ¬ CReal.ltE b CReal.zero) :
    ¬ CReal.ltE (CReal.mul a b) CReal.zero := by
  change ¬ ltQuot
    (mulQuotConcreteWith cRatScalarMulArch (mkQuot a) (mkQuot b))
    zeroQuot
  exact mul_nonnegQuotConcreteWith cRatScalarMulArch
    (by
      change ¬ CReal.ltE a CReal.zero
      exact ha)
    (by
      change ¬ CReal.ltE b CReal.zero
      exact hb)

/-- Fuller constructive ordered-field core over a setoid carrier, using the
invariant strict order and the recovered strict-order fields. -/
class PresentedCore (C : Type) [Setoid C] extends PresentedReducedCore C where
  lt_cotrans : ∀ {a b : C}, lt a b → ∀ c : C, lt a c ∨ lt c b
  lt_add_left : ∀ (c : C) {a b : C}, lt a b → lt (add c a) (add c b)
  lt_trans : ∀ {a b c : C}, lt a b → lt b c → lt a c
  mul_pos : ∀ {a b : C}, lt zero a → lt zero b → lt zero (mul a b)
  archimedean : ∀ t : C, lt zero t → ∃ k : Nat, lt (eps k) t
  archimedean_pos : ∀ t : C, lt zero t → {k : Nat // lt (eps k) t}
  abs_of_nonneg : ∀ {a : C}, ¬ lt a zero → abs a ≈ a
  abs_le_of : ∀ {a b : C}, ¬ lt b a → ¬ lt b (neg a) → ¬ lt b (abs a)
  max_zero_nonneg : ∀ a : C, ¬ lt (max a zero) zero
  max_le_abs : ∀ a : C, ¬ lt (abs a) (max a zero)
  neg_min_zero_nonneg : ∀ a : C, ¬ lt (neg (min a zero)) zero
  neg_min_le_abs : ∀ a : C, ¬ lt (abs a) (neg (min a zero))
  lt_or_lt_of_abs_pos : ∀ {c : C}, lt zero (abs c) → lt zero c ∨ lt c zero
  mul_nonneg : ∀ {a b : C}, ¬ lt a zero → ¬ lt b zero → ¬ lt (mul a b) zero

instance instPresentedCoreCReal : PresentedCore CReal where
  add := CReal.add
  mul := CReal.mul
  neg := CReal.neg
  zero := CReal.zero
  one := CReal.one
  half := CReal.half
  lt := CReal.ltE
  abs := CReal.abs
  max := CReal.max
  min := CReal.min
  eps := CReal.epsSeq
  add_comm := CReal.add_comm
  add_assoc := CReal.add_assoc
  add_zero := CReal.add_zero
  zero_add := CReal.zero_add
  add_left_neg := CReal.add_left_neg
  mul_comm := CReal.mul_comm
  mul_assoc := CReal.mul_assoc
  one_mul := CReal.one_mul
  mul_one := CReal.mul_one
  left_distrib := CReal.left_distrib
  right_distrib := CReal.right_distrib
  half_add_half := CReal.half_add_half
  max_halfsum := CReal.max_halfsum
  min_halfsum := CReal.min_halfsum
  abs_zero := CReal.abs_zero
  abs_neg := CReal.abs_neg
  abs_mul := CReal.abs_mul
  lt_irrefl := CReal.ltE_irrefl
  neg_le_abs := CReal.neg_le_abs_E
  le_abs_self := CReal.le_abs_self_E
  one_pos := CReal.one_pos_E
  half_pos := CReal.half_pos_E
  abs_add_le := CReal.abs_add_le_E
  eq_of_small := by
    intro a b hsmall
    exact CReal.eq_of_small_E a b hsmall
  mul_archimedean := CReal.mul_archimedean_E
  lt_cotrans := by
    intro a b h c
    exact CReal.ltE_cotrans h c
  lt_add_left := by
    intro c a b h
    exact CReal.ltE_add_left c h
  lt_trans := by
    intro a b c hab hbc
    exact CReal.ltE_trans hab hbc
  mul_pos := by
    intro a b ha hb
    exact CReal.mul_pos_E ha hb
  archimedean := CReal.archimedean_E
  archimedean_pos := CReal.archimedean_pos_E
  abs_of_nonneg := by
    intro a ha
    exact CReal.abs_of_nonneg_E ha
  abs_le_of := by
    intro a b hba hbna
    exact CReal.abs_le_of_E hba hbna
  max_zero_nonneg := CReal.max_zero_nonneg_E
  max_le_abs := CReal.max_le_abs_E
  neg_min_zero_nonneg := CReal.neg_min_zero_nonneg_E
  neg_min_le_abs := CReal.neg_min_le_abs_E
  lt_or_lt_of_abs_pos := by
    intro c hc
    exact CReal.lt_or_lt_of_abs_pos_E hc
  mul_nonneg := by
    intro a b ha hb
    exact CReal.mul_nonneg_E ha hb

#print axioms BishopCReal.CReal.ltE
#print axioms BishopCReal.CReal.ltED
#print axioms BishopCReal.CReal.ltE_irrefl
#print axioms BishopCReal.CReal.ltE_cotrans
#print axioms BishopCReal.CReal.ltE_add_left
#print axioms BishopCReal.CReal.ltE_trans
#print axioms BishopCReal.CReal.one_pos_E
#print axioms BishopCReal.CReal.half_pos_E
#print axioms BishopCReal.CReal.neg_le_abs_E
#print axioms BishopCReal.CReal.le_abs_self_E
#print axioms BishopCReal.CReal.abs_add_le_E
#print axioms BishopCReal.CReal.eq_of_small_E
#print axioms BishopCReal.CReal.mul_archimedean_E
#print axioms BishopCReal.CReal.mul_pos_E
#print axioms BishopCReal.CReal.archimedean_E
#print axioms BishopCReal.CReal.archWitnessGauge
#print axioms BishopCReal.CReal.archPosWitness
#print axioms BishopCReal.CReal.archPosWitness_exists
#print axioms BishopCReal.CReal.archimedean_pos_E
#print axioms BishopCReal.CReal.abs_of_nonneg_E
#print axioms BishopCReal.CReal.abs_le_of_E
#print axioms BishopCReal.CReal.max_zero_nonneg_E
#print axioms BishopCReal.CReal.max_le_abs_E
#print axioms BishopCReal.CReal.neg_min_zero_nonneg_E
#print axioms BishopCReal.CReal.neg_min_le_abs_E
#print axioms BishopCReal.CReal.lt_or_lt_of_abs_pos_E
#print axioms BishopCReal.CReal.mul_nonneg_E
#print axioms BishopCReal.PresentedCore
#print axioms BishopCReal.PresentedCore.lt_cotrans
#print axioms BishopCReal.PresentedCore.mul_nonneg
#print axioms BishopCReal.instPresentedCoreCReal

end BishopCReal
