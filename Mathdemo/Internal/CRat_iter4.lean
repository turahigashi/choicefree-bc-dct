import Mathdemo.Internal.CRat_iter5

/-!
# CReal regular-sequence layer over the live `CRat` scalar

This is the current, non-stale Phase 3 boundary for the concrete CReal work.
Unlike the previous `BishopC_CReal.lean`, it is based on the project-local
choice-free rational scalar `BishopCRat.CRat`, already connected to the live
`BishopB.COF` interface.

This file deliberately does not emit `instance : COFOC CReal`.  The remaining
frontier is recorded as data structures below: setoid laws, operation closure
and quotient-respect lemmas, COFO order laws, and the diagonal completeness
construction.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The rational scalar currently known to satisfy the live `BishopB.COF`
interface. -/
abbrev Scalar : Type := BishopCRat.CRat

/-- Current audited scalar seed for the concrete CReal development. -/
def scalarCOFOSeed : BishopCRat.CRat.COFOSeed :=
  BishopCRat.CRat.cofoSeed


/-- Dyadic Bishop gauge.  We use the project-wide `halfPow`, avoiding any
general rational inverse. -/
def eps (n : Nat) : Scalar :=
  COF.halfPow (R := Scalar) n


/-- Equality tolerance for regular sequences. -/
def tol (n : Nat) : Scalar :=
  eps n + eps n


/-- Constructive non-strict order induced by the live strict order. -/
def Le (a b : Scalar) : Prop :=
  BishopC.Le a b


/-- Dyadic regularity for a rational sequence. -/
def RegularVal (x : Nat → Scalar) : Prop :=
  ∀ m n : Nat, Le (COF.abs (x m - x n)) (eps m + eps n)


/-- Raw CReal representative: a dyadically regular sequence of `CRat`s. -/
structure RegularSeq where
  val : Nat → Scalar
  regular : RegularVal val


/-- Bishop equality tolerance between representative values. -/
def relVal (x y : Nat → Scalar) : Prop :=
  ∀ n : Nat, Le (COF.abs (x n - y n)) (tol n)


/-- Bishop equality of bundled regular sequences. -/
def rel (x y : RegularSeq) : Prop :=
  relVal x.val y.val


/-- Positivity on raw representatives. -/
def PosRaw (x : RegularSeq) : Prop :=
  ∃ n : Nat, COF.lt (eps n) (x.val n)


/-- Value-level positivity, useful before quotienting. -/
def PosVal (x : Nat → Scalar) : Prop :=
  ∃ n : Nat, COF.lt (eps n) (x n)


/-! ## Operation shapes -/

/-- Addition uses a finer index to recover the original dyadic modulus. -/
def addIndex (n : Nat) : Nat :=
  n + 1


def constVal (q : Scalar) (_n : Nat) : Scalar :=
  q


def zeroVal : Nat → Scalar :=
  constVal 0


def oneVal : Nat → Scalar :=
  constVal 1


def halfVal : Nat → Scalar :=
  constVal (COF.half : Scalar)


def negVal (x : Nat → Scalar) (n : Nat) : Scalar :=
  - x n


def addVal (x y : Nat → Scalar) (n : Nat) : Scalar :=
  x (addIndex n) + y (addIndex n)


def subVal (x y : Nat → Scalar) (n : Nat) : Scalar :=
  x (addIndex n) - y (addIndex n)


def absVal (x : Nat → Scalar) (n : Nat) : Scalar :=
  COF.abs (x n)


def maxVal (x y : Nat → Scalar) (n : Nat) : Scalar :=
  COF.max (x n) (y n)


def minVal (x y : Nat → Scalar) (n : Nat) : Scalar :=
  COF.min (x n) (y n)


/-- Multiplication needs a bound-sensitive reindexing.  This placeholder records
the operation shape after a constructive bound has been computed. -/
def mulIndexFromBound (K n : Nat) : Nat :=
  2 * (K + 1) * (n + 1) + 1


def mulValWithBound (K : Nat) (x y : Nat → Scalar) (n : Nat) : Scalar :=
  let m := mulIndexFromBound K n
  x m * y m


/-! ## Remaining proof frontiers before emitting `COFOC CReal` -/

/-- Setoid laws for Bishop equality on regular sequences. -/
structure CRealSetoidFrontier : Type where
  rel_refl : ∀ x : RegularSeq, rel x x
  rel_symm : ∀ x y : RegularSeq, rel x y → rel y x
  rel_trans : ∀ x y z : RegularSeq, rel x y → rel y z → rel x z


/-- Additive and lattice-like operation closure and respect lemmas. -/
structure CRealAdditiveFrontier : Type where
  const_regular : ∀ q : Scalar, RegularVal (constVal q)
  neg_regular : ∀ x : RegularSeq, RegularVal (negVal x.val)
  add_regular : ∀ x y : RegularSeq, RegularVal (addVal x.val y.val)
  abs_regular : ∀ x : RegularSeq, RegularVal (absVal x.val)
  neg_respects : ∀ x y : RegularSeq, rel x y → relVal (negVal x.val) (negVal y.val)
  add_respects : ∀ x x' y y' : RegularSeq,
    rel x x' → rel y y' →
      relVal (addVal x.val y.val) (addVal x'.val y'.val)
  abs_respects : ∀ x y : RegularSeq, rel x y → relVal (absVal x.val) (absVal y.val)


/-- Multiplicative closure and quotient respect. -/
structure CRealMultiplicativeFrontier : Type where
  bound : RegularSeq → RegularSeq → Nat
  mul_regular : ∀ x y : RegularSeq,
    RegularVal (mulValWithBound (bound x y) x.val y.val)
  mul_respects : ∀ x x' y y' : RegularSeq,
    rel x x' → rel y y' →
      relVal
        (mulValWithBound (bound x y) x.val y.val)
        (mulValWithBound (bound x' y') x'.val y'.val)


/-- Order and positivity laws needed for `COF CReal`. -/
structure CRealOrderFrontier : Type where
  pos_respects : ∀ x y : RegularSeq, rel x y → PosRaw x → PosRaw y
  lt_irrefl_raw : ∀ x : RegularSeq, ¬ PosVal (subVal x.val x.val)
  lt_cotrans_raw : ∀ a b c : RegularSeq,
    PosVal (subVal b.val a.val) →
      PSum (PosVal (subVal c.val a.val)) (PosVal (subVal b.val c.val))
  lt_add_left_raw : ∀ c a b : RegularSeq,
    PosVal (subVal b.val a.val) →
      PosVal (subVal (addVal c.val b.val) (addVal c.val a.val))


/-- The additional laws required by the live `COFO` interface after `COF` is
available on the quotient. -/
structure CRealCOFOFrontier : Type where
  lt_trans : ∀ {a b c : RegularSeq},
    PosVal (subVal b.val a.val) →
    PosVal (subVal c.val b.val) →
      PosVal (subVal c.val a.val)
  abs_zero_raw : relVal (absVal zeroVal) zeroVal
  abs_neg_raw : ∀ x : RegularSeq, relVal (absVal (negVal x.val)) (absVal x.val)
  one_pos_raw : PosVal oneVal
  half_pos_raw : PosVal halfVal
  mul_pos_raw : ∀ x y : RegularSeq,
    PosRaw x → PosRaw y →
      PosVal (mulValWithBound 0 x.val y.val)
  archimedean_pos_raw : ∀ x : RegularSeq,
    PosRaw x → { k : Nat // PosVal (subVal x.val (constVal (eps k))) }
  abs_add_le_raw : ∀ x y : RegularSeq,
    Le (COF.abs ((absVal x.val) 0 + (absVal y.val) 0))
      (COF.abs ((addVal x.val y.val) 0))
  eq_of_small_raw : ∀ x y : RegularSeq,
    (∀ k : Nat, Le (eps k) (COF.abs (x.val k - y.val k))) → rel x y
  inv_pos_raw : ∀ x : RegularSeq, PosRaw x → PosRaw x


/-- Diagonal completeness frontier for the eventual `COFOC CReal` instance. -/
structure CRealCompletenessFrontier : Type where
  diagonal_limit : ∀ (v : Nat → RegularSeq),
    (∀ k m n : Nat, k ≤ m → k ≤ n → relVal (v m).val (v n).val) →
      RegularSeq
  diagonal_tends : ∀ (v : Nat → RegularSeq)
    (hv : ∀ k m n : Nat, k ≤ m → k ≤ n → relVal (v m).val (v n).val),
      ∀ k : Nat, relVal (v k).val ((diagonal_limit v hv).val)


/-- Complete list of proof frontiers before the concrete `COFOC CReal` instance
can be honestly emitted. -/
structure ReadyForCOFOC : Type where
  setoid : CRealSetoidFrontier
  additive : CRealAdditiveFrontier
  multiplicative : CRealMultiplicativeFrontier
  order : CRealOrderFrontier
  cofo : CRealCOFOFrontier
  complete : CRealCompletenessFrontier


end BishopCReal
