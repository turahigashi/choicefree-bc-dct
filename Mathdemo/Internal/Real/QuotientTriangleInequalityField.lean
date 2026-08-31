import Mathdemo.Internal.Real.QuotientAbsoluteValuePositivitySplit

/-!
# Quotient triangle inequality field

`QuotientAbsoluteValuePositivitySplit` closed the absolute-value positivity split.  This file closes
the next local `COFO` field:

* `¬ (|x| + |y| < |x + y|)`.

The proof is again representative-level.  A hypothetical eventual positive
gap `|x+y| - (|x|+|y|)` gives one scalar point where the reverse strict
triangle inequality holds, contradicting the audited scalar triangle
inequality `scalar_abs_add_le`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative form of the triangle inequality as a no-strict-reverse law. -/
theorem not_posEventually_abs_add_reverse (x y : RegularSeq) :
    ¬ PosEventually
      (subSeq (absSeq (addSeq x y)) (addSeq (absSeq x) (absSeq y))) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  change COF.lt (eps k)
    (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)) -
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))))
    at hpoint
  have hzero : COF.lt (0 : Scalar)
    (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)) -
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1)))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint
  have hbad : COF.lt
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1)))
      (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1))) := by
    have t := COF.lt_add_left
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1)))
      hzero
    rwa [show
        (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))) +
            (0 : Scalar) =
          COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))
        from by ring,
      show
        (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))) +
            (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)) -
              (COF.abs (x.val ((N + 1) + 1)) +
                COF.abs (y.val ((N + 1) + 1)))) =
          COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1))
        from by ring] at t
  have htri : Le
      (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)))
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))) :=
    scalar_abs_add_le (x.val ((N + 1) + 1)) (y.val ((N + 1) + 1))
  exact htri hbad

/-- Quotient-level `¬ (|x| + |y| < |x+y|)`. -/
theorem abs_add_leQuot (x y : CRealQuot) :
    ¬ ltQuot (addQuot (absQuot x) (absQuot y)) (absQuot (addQuot x y)) := by
  refine Quotient.inductionOn x ?_
  intro xr
  refine Quotient.inductionOn y ?_
  intro yr
  change ¬ PosEventually
    (subSeq (absSeq (addSeq xr yr)) (addSeq (absSeq xr) (absSeq yr)))
  exact not_posEventually_abs_add_reverse xr yr






end BishopCReal

