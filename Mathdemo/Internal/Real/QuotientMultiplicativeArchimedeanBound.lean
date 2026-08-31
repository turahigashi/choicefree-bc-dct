import Mathdemo.Internal.Real.QuotientMultiplicationPreservesNonnegativity

/-!
# Quotient multiplicative Archimedean bound

`QuotientMultiplicationPreservesNonnegativity` closed `mul_nonneg`.  This file closes the next `COFO` field:

* for every quotient real `x`, some dyadic gauge makes `|x| * halfPow m`
  not exceed `1`.

This is the first remaining field that genuinely uses the representative
witness carried by the conditional quotient branch.  Given `x = mk xr`, choose
`m = standardBoundWith A xr`.  The standard representative bound controls all
multiplication samples of `|xr| * eps m`, so an eventual positive tail above
`1` is impossible.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A representative's standard bound controls every sampled product
`|x_q| * eps m`. -/
theorem abs_sample_mul_standard_eps_le_one
    (A : ScalarMulArchimedeanData) (x : RegularSeq) (K n : Nat) :
    Le (COF.abs (x.val (mulIndexFromBound K n)) *
        eps (standardBoundWith A x)) 1 := by
  have hx : Le (COF.abs (x.val (mulIndexFromBound K n)))
      (COF.abs (x.val 1) + 1) :=
    regular_value_bound_from_one x K n
  have hmul : Le
      (COF.abs (x.val (mulIndexFromBound K n)) *
        eps (standardBoundWith A x))
      ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x)) :=
    scalar_mul_le_mul_right hx (eps_nonneg (standardBoundWith A x))
  exact BishopC.le_trans hmul (standardBoundWith_spec_base A x)







end BishopCReal

