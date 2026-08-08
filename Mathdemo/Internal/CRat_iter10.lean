import Mathdemo.Internal.CRat_iter9

/-!
# CReal raw positivity of half

This file closes the representative-level positivity of the constant-half
sequence.  The only new ingredient is the dyadic comparison
`eps (n+1) < eps n`, proved from the audited scalar positivity of `eps`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The next dyadic gauge adds to itself to recover the previous gauge. -/
theorem eps_succ_add_self (n : Nat) : eps (n + 1) + eps (n + 1) = eps n := by
  unfold eps
  change
    (COF.half : Scalar) * COF.halfPow (R := Scalar) n
      + (COF.half : Scalar) * COF.halfPow (R := Scalar) n
      = COF.halfPow (R := Scalar) n
  rw [show (COF.half : Scalar) * COF.halfPow (R := Scalar) n
      + (COF.half : Scalar) * COF.halfPow (R := Scalar) n
      = ((COF.half : Scalar) + (COF.half : Scalar)) * COF.halfPow (R := Scalar) n
      from by ring, COF.half_add_half, one_mul]

/-- Dyadic gauges strictly decrease. -/
theorem eps_succ_lt_eps (n : Nat) : COF.lt (eps (n + 1)) (eps n) := by
  have h := COF.lt_add_left (eps (n + 1)) (eps_pos (n + 1))
  rwa [show eps (n + 1) + 0 = eps (n + 1) from by ring,
    eps_succ_add_self n] at h

/-- `eps 2 < half` for the CRat scalar. -/
theorem eps_two_lt_half : COF.lt (eps 2) (COF.half : Scalar) := by
  have h := eps_succ_lt_eps 1
  rwa [show eps 1 = (COF.half : Scalar) from by
    unfold eps
    change (COF.half : Scalar) * 1 = COF.half
    ring] at h

/-- Raw CReal positivity of the constant-half representative. -/
theorem half_pos_raw : PosVal halfVal := by
  refine ⟨2, ?_⟩
  change COF.lt (eps 2) (COF.half : Scalar)
  exact eps_two_lt_half

/-- Audited dyadic comparison and constant-half positivity seed. -/
structure CRealHalfPosSeed : Type where
  eps_succ_add_self : ∀ n : Nat, eps (n + 1) + eps (n + 1) = eps n
  eps_succ_lt_eps : ∀ n : Nat, COF.lt (eps (n + 1)) (eps n)
  eps_two_lt_half : COF.lt (eps 2) (COF.half : Scalar)
  half_pos_raw : PosVal halfVal

def cRealHalfPosSeed : CRealHalfPosSeed where
  eps_succ_add_self := eps_succ_add_self
  eps_succ_lt_eps := eps_succ_lt_eps
  eps_two_lt_half := eps_two_lt_half
  half_pos_raw := half_pos_raw

end BishopCReal

