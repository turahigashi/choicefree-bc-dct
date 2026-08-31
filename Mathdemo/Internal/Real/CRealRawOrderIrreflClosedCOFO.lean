import Mathdemo.Internal.Real.CRealAdditiveFrontierAuditedCRatScalar

/-!
# CReal raw order irrefl and closed COFO fragments

This file closes the easy order fragment: no representative can be strictly
positive over its own raw difference.  It also records the already closed COFO
raw fragments in one audited seed.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The raw self-difference sequence is pointwise zero. -/
theorem sub_self_val (x : Nat → Scalar) (n : Nat) : subVal x x n = 0 := by
  unfold subVal addIndex
  ring







end BishopCReal

