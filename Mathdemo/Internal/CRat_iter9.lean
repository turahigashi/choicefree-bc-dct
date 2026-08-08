import Mathdemo.Internal.CRat_iter8

/-!
# CReal raw positivity of one

This closes the representative-level positivity of the constant-one sequence.
The constant-half positivity is left for the next dyadic comparison layer.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- `half < 1` for the CRat scalar. -/
theorem scalar_half_lt_one : COF.lt (COF.half : Scalar) 1 := by
  have h := COF.lt_add_left (COF.half : Scalar) scalarCOFOSeed.half_pos
  rwa [show (COF.half : Scalar) + 0 = COF.half from by ring,
    show (COF.half : Scalar) + BishopCRat.CRat.half = 1 from by
      change (COF.half : Scalar) + (COF.half : Scalar) = 1
      exact COF.half_add_half] at h

/-- Raw CReal positivity of the constant-one representative. -/
theorem one_pos_raw : PosVal oneVal := by
  refine ⟨1, ?_⟩
  change COF.lt ((COF.half : Scalar) * 1) (1 : Scalar)
  rw [mul_one]
  exact scalar_half_lt_one

/-- Audited raw positivity seed currently closed without extra dyadic
comparison lemmas. -/
structure CRealPosSeed : Type where
  scalar_half_lt_one : COF.lt (COF.half : Scalar) 1
  one_pos_raw : PosVal oneVal

def cRealPosSeed : CRealPosSeed where
  scalar_half_lt_one := scalar_half_lt_one
  one_pos_raw := one_pos_raw

end BishopCReal

