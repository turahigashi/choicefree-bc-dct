import Mathdemo.Internal.Real.CRealFirstRawLawsAuditedCRat

/-!
# CReal constant raw laws over the audited CRat seed

This file adds the scalar dyadic positivity facts needed to prove that constant
sequences are regular, and closes the raw `abs zero` fact for the CReal
frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A positive scalar is nonnegative in Bishop's `Le` sense. -/
theorem scalar_nonneg_of_pos {a : Scalar} (ha : COF.lt 0 a) : Le 0 a := by
  intro hlt
  exact COF.lt_irrefl (0 : Scalar) (scalarCOFOSeed.lt_trans ha hlt)

/-- Sum of two positive CRat scalars is positive. -/
theorem scalar_add_pos {a b : Scalar} (ha : COF.lt 0 a) (hb : COF.lt 0 b) :
    COF.lt 0 (a + b) := by
  have hstep : COF.lt b (a + b) := by
    have t := COF.lt_add_left b ha
    rwa [show b + (0 : Scalar) = b from by ring,
      show b + a = a + b from by ring] at t
  exact scalarCOFOSeed.lt_trans hb hstep

/-- Dyadic gauges are positive. -/
theorem eps_pos : ∀ n : Nat, COF.lt 0 (eps n)
  | 0 => by
      change COF.lt (0 : Scalar) (1 : Scalar)
      exact scalarCOFOSeed.one_pos
  | Nat.succ n => by
      change COF.lt (0 : Scalar) (COF.half * COF.halfPow (R := Scalar) n)
      exact scalarCOFOSeed.mul_pos scalarCOFOSeed.half_pos (eps_pos n)

theorem eps_nonneg (n : Nat) : Le 0 (eps n) :=
  scalar_nonneg_of_pos (eps_pos n)

theorem eps_add_pos (m n : Nat) : COF.lt 0 (eps m + eps n) :=
  scalar_add_pos (eps_pos m) (eps_pos n)

theorem eps_add_nonneg (m n : Nat) : Le 0 (eps m + eps n) :=
  scalar_nonneg_of_pos (eps_add_pos m n)

theorem tol_pos (n : Nat) : COF.lt 0 (tol n) := by
  unfold tol
  exact eps_add_pos n n

theorem tol_nonneg (n : Nat) : Le 0 (tol n) :=
  scalar_nonneg_of_pos (tol_pos n)

/-- Constant rational sequences are regular. -/
theorem const_regular (q : Scalar) : RegularVal (constVal q) := by
  intro m n
  unfold constVal
  change Le (BishopCRat.CRat.absF (q - q)) (eps m + eps n)
  rw [show q - q = (0 : Scalar) from by ring, scalarCOFOSeed.abs_zero]
  exact eps_add_nonneg m n

theorem zero_regular : RegularVal zeroVal := by
  change RegularVal (constVal (0 : Scalar))
  exact const_regular 0

theorem one_regular : RegularVal oneVal := by
  change RegularVal (constVal (1 : Scalar))
  exact const_regular 1

theorem half_regular : RegularVal halfVal := by
  change RegularVal (constVal (COF.half : Scalar))
  exact const_regular COF.half

/-- Raw CReal `abs 0 = 0` at the representative level. -/
theorem abs_zero_raw : relVal (absVal zeroVal) zeroVal := by
  intro n
  change Le (BishopCRat.CRat.absF (BishopCRat.CRat.absF 0 - 0)) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  rw [show (0 : Scalar) - 0 = 0 from by ring, scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Audited constant-sequence seed. -/
structure CRealConstantSeed : Type where
  eps_pos : ∀ n : Nat, COF.lt 0 (eps n)
  eps_nonneg : ∀ n : Nat, Le 0 (eps n)
  const_regular : ∀ q : Scalar, RegularVal (constVal q)
  zero_regular : RegularVal zeroVal
  one_regular : RegularVal oneVal
  half_regular : RegularVal halfVal
  abs_zero_raw : relVal (absVal zeroVal) zeroVal

def cRealConstantSeed : CRealConstantSeed where
  eps_pos := eps_pos
  eps_nonneg := eps_nonneg
  const_regular := const_regular
  zero_regular := zero_regular
  one_regular := one_regular
  half_regular := half_regular
  abs_zero_raw := abs_zero_raw

end BishopCReal

