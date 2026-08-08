import Mathdemo.Internal.CRat_iter55

/-!
# Quotient multiplication positivity

`CRat_iter55` closed the absolute-value multiplication field.  This file closes
the next local `COFO` field:

* if `0 < x` and `0 < y`, then `0 < x * y`.

The proof derives local scalar strict monotonicity of multiplication by a
positive scalar.  It then uses the product sampling index directly against the
tail witnesses for `x - 0` and `y - 0`, avoiding representative extraction or
choice.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The core predecessor of `mulIndexFromBound K n`. -/
def mulIndexCoreFromBound (K n : Nat) : Nat :=
  2 * (K + 1) * (n + 1)

/-- The core multiplication index is still at least the output index. -/
theorem le_mulIndexCoreFromBound (K n : Nat) : n ≤ mulIndexCoreFromBound K n := by
  unfold mulIndexCoreFromBound
  have hn : n ≤ n + 1 := Nat.le_succ n
  have hcoef : 0 < 2 * (K + 1) := Nat.mul_pos (by decide) (Nat.succ_pos K)
  have hmul : n + 1 ≤ (2 * (K + 1)) * (n + 1) :=
    Nat.le_mul_of_pos_left (n + 1) hcoef
  exact Nat.le_trans hn hmul

/-- `mulIndexFromBound` is the successor of its core predecessor. -/
theorem mulIndexFromBound_eq_core_succ (K n : Nat) :
    mulIndexFromBound K n = mulIndexCoreFromBound K n + 1 := by
  rfl

/-- A strict scalar inequality gives positivity of the difference. -/
theorem scalar_pos_sub_of_lt {a b : Scalar} (h : COF.lt a b) :
    COF.lt (0 : Scalar) (b - a) := by
  have t := COF.lt_add_left (-a) h
  rwa [show -a + a = (0 : Scalar) from by ring,
    show -a + b = b - a from by ring] at t

/-- Strict multiplication by a positive scalar is monotone on the left. -/
theorem scalar_mul_lt_mul_left {a b c : Scalar}
    (hab : COF.lt a b) (hc : COF.lt 0 c) : COF.lt (c * a) (c * b) := by
  have hba : COF.lt (0 : Scalar) (b - a) := scalar_pos_sub_of_lt hab
  have hpos : COF.lt (0 : Scalar) (c * (b - a)) :=
    scalarCOFOSeed.mul_pos hc hba
  have t := COF.lt_add_left (c * a) hpos
  rwa [show c * a + (0 : Scalar) = c * a from by ring,
    show c * a + c * (b - a) = c * b from by ring] at t

/-- Strict multiplication by a positive scalar is monotone on the right. -/
theorem scalar_mul_lt_mul_right {a b c : Scalar}
    (hab : COF.lt a b) (hc : COF.lt 0 c) : COF.lt (a * c) (b * c) := by
  have h := scalar_mul_lt_mul_left (c := c) hab hc
  rwa [mul_comm c a, mul_comm c b] at h

/-- Product lower bound from two positive lower bounds. -/
theorem scalar_mul_lt_mul_of_pos_bounds {a b c d : Scalar}
    (hac : COF.lt a c) (hbd : COF.lt b d)
    (ha : COF.lt 0 a) (hb : COF.lt 0 b) : COF.lt (a * b) (c * d) := by
  have h1 : COF.lt (a * b) (c * b) := scalar_mul_lt_mul_right hac hb
  have hc : COF.lt (0 : Scalar) c := scalarCOFOSeed.lt_trans ha hac
  have h2 : COF.lt (c * b) (c * d) := scalar_mul_lt_mul_left hbd hc
  exact scalarCOFOSeed.lt_trans h1 h2

/-- Positivity of `x` gives positivity of `x - 0`. -/
theorem posEventually_sub_zero_of_pos (x : RegularSeq) :
    PosEventually x → PosEventually (subSeq x zeroSeq) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  refine ⟨k, N, ?_⟩
  intro n hn
  have hn' : N ≤ n + 1 := Nat.le_trans hn (Nat.le_succ n)
  have hx := hN (n + 1) hn'
  change COF.lt (eps k) (x.val (n + 1) - 0)
  rwa [sub_zero]

/-- Product positivity from positivity of `x - 0` and `y - 0`. -/
theorem posEventually_mul_concrete_from_sub_zero_with
    (A : ScalarMulArchimedeanData) (x y : RegularSeq) :
    PosEventually (subSeq x zeroSeq) → PosEventually (subSeq y zeroSeq) →
      PosEventually (mulSeqConcreteWith A x y) := by
  intro hx hy
  rcases hx with ⟨kx, Nx, hNx⟩
  rcases hy with ⟨ky, Ny, hNy⟩
  refine ⟨kx + ky, Nx + Ny, ?_⟩
  intro n hn
  have hnX : Nx ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hnY : Ny ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  set q : Nat := mulIndexCoreFromBound (mulBoundWith A x y) n with hqdef
  have hnq : n ≤ q := by
    rw [hqdef]
    exact le_mulIndexCoreFromBound (mulBoundWith A x y) n
  have hqX : Nx ≤ q := Nat.le_trans hnX hnq
  have hqY : Ny ≤ q := Nat.le_trans hnY hnq
  have hxraw := hNx q hqX
  have hyraw := hNy q hqY
  have hidx : mulIndexFromBound (mulBoundWith A x y) n = q + 1 := by
    rw [hqdef]
    exact mulIndexFromBound_eq_core_succ (mulBoundWith A x y) n
  have hxpoint : COF.lt (eps kx)
      (x.val (mulIndexFromBound (mulBoundWith A x y) n)) := by
    rw [hidx]
    change COF.lt (eps kx) (x.val (q + 1) - 0) at hxraw
    rwa [sub_zero] at hxraw
  have hypoint : COF.lt (eps ky)
      (y.val (mulIndexFromBound (mulBoundWith A x y) n)) := by
    rw [hidx]
    change COF.lt (eps ky) (y.val (q + 1) - 0) at hyraw
    rwa [sub_zero] at hyraw
  change COF.lt (eps (kx + ky))
    (x.val (mulIndexFromBound (mulBoundWith A x y) n) *
      y.val (mulIndexFromBound (mulBoundWith A x y) n))
  rw [eps_add_mul_local kx ky]
  exact scalar_mul_lt_mul_of_pos_bounds hxpoint hypoint (eps_pos kx) (eps_pos ky)

/-- Quotient-level concrete multiplication preserves positivity. -/
theorem mul_posQuotConcreteWith
    (A : ScalarMulArchimedeanData) {x y : CRealQuot} :
    ltQuot zeroQuot x → ltQuot zeroQuot y →
      ltQuot zeroQuot (mulQuotConcreteWith A x y) := by
  refine Quotient.inductionOn x ?_
  intro xr
  refine Quotient.inductionOn y ?_
  intro yr hx hy
  change PosEventually (subSeq xr zeroSeq) at hx
  change PosEventually (subSeq yr zeroSeq) at hy
  change PosEventually (subSeq (mulSeqConcreteWith A xr yr) zeroSeq)
  exact posEventually_sub_zero_of_pos (mulSeqConcreteWith A xr yr)
    (posEventually_mul_concrete_from_sub_zero_with A xr yr hx hy)

/-- Basic quotient `COFO` fields through multiplication positivity. -/
structure CRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicTransAbsSplitTriangleMulFieldData cof where
  mul_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b : CRealQuot}, COF.lt 0 a → COF.lt 0 b → COF.lt 0 (a * b)

/-- Data-order/representative branch package including multiplication
positivity. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulFieldDataWith A rep ltDataOf
  mul_pos := by
    intro a b ha hb
    change ltQuot zeroQuot (mulQuotConcreteWith A a b)
    exact mul_posQuotConcreteWith A ha hb

/-- Decidable-order branch package including multiplication positivity. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulFieldDataWithDecidableLT A hdec
  mul_pos := by
    intro a b ha hb
    change ltQuot zeroQuot (mulQuotConcreteWith A a b)
    exact mul_posQuotConcreteWith A ha hb

/-- Frontier after multiplication positivity is closed. -/
structure CRealQuotCOFOAfterMulPosFrontier : Type where
  abs_le_of : Prop
  max_min_laws : Prop
  mul_nonneg : Prop
  archimedean_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterMulPosFrontier :
    CRealQuotCOFOAfterMulPosFrontier where
  abs_le_of := True
  max_min_laws := True
  mul_nonneg := True
  archimedean_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

