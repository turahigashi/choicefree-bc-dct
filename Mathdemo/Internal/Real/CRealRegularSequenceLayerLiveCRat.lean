import Mathdemo.Internal.Rat.CRatCOFOSeedLemmas

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






/-- Multiplication needs a bound-sensitive reindexing.  This placeholder records
the operation shape after a constructive bound has been computed. -/
def mulIndexFromBound (K n : Nat) : Nat :=
  2 * (K + 1) * (n + 1) + 1


def mulValWithBound (K : Nat) (x y : Nat → Scalar) (n : Nat) : Scalar :=
  let m := mulIndexFromBound K n
  x m * y m


/-! ## Remaining proof frontiers before emitting `COFOC CReal` -/















end BishopCReal
