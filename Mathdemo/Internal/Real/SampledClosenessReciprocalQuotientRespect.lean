import Mathdemo.Internal.Real.MixedReciprocalEstimatesQuotientRespect

/-!
# Sampled closeness for reciprocal quotient respect

`MixedReciprocalEstimatesQuotientRespect` reduced reciprocal-tail respect to a sampled closeness
obligation.  This file closes that obligation from eventual Bishop equality of
the source representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat


/-- If a sample index is beyond a scalar Archimedean bound, multiplication by
the scalar is absorbed by the target dyadic gauge. -/
theorem scalar_bound_eps_le_of_ge
    (A : ScalarMulArchimedeanData) (B : Scalar) {p r : Nat}
    (hp : scalarBoundWith A B + r ≤ p) :
    Le (COF.abs B * eps p) (eps r) := by
  have heps : Le (eps p) (eps (scalarBoundWith A B + r)) :=
    eps_le_of_le hp
  have hmul :
      Le (COF.abs B * eps p)
        (COF.abs B * eps (scalarBoundWith A B + r)) :=
    scalar_mul_le_mul_left heps (scalar_abs_nonneg B)
  exact BishopC.le_trans hmul (scalar_bound_tail_eps_le A B r)

/-- Reciprocal-tail output indices are at least the original output index. -/
theorem reciprocalTailIndex_ge_self
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    n ≤ reciprocalTailIndexWith A x h n := by
  have hbase : n ≤ reciprocalTailBoundWith A x h + n := by
    omega
  exact Nat.le_trans hbase (reciprocalTailIndex_bound A x h n)








end BishopCReal

