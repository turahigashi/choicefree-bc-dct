import Mathdemo.Internal.Real.ConditionalCRealQuotientCOFOCOFOCAssembly

/-!
# First concrete CReal quotient COFO fields

`ConditionalCRealQuotientCOFOCOFOCAssembly` isolated the full `COFO` field data needed after a quotient
`COF` record is available.  This file starts filling that field data with
actual quotient-level proofs that are already local:

* `abs 0 = 0`;
* `abs (-x) = abs x`;
* `0 < 1`;
* `0 < half`.

The remaining `COFO` obligations are still not claimed here.
-/

namespace BishopCReal

open BishopC
open BishopCRat


/-- Quotient-level absolute value is invariant under negation. -/
theorem absQuot_neg (x : CRealQuot) : absQuot (negQuot x) = absQuot x := by
  refine Quotient.inductionOn x ?_
  intro a
  change mkQuot (absSeq (negSeq a)) = mkQuot (absSeq a)
  exact Quotient.sound
    (rel_to_relEventually (absSeq (negSeq a)) (absSeq a) (abs_neg_raw a))

/-- Quotient order sees the constant one as positive. -/
theorem ltQuot_zero_one : ltQuot zeroQuot oneQuot := by
  change PosEventually (subSeq oneSeq zeroSeq)
  rcases one_pos_raw with ⟨k, hk⟩
  refine ⟨k, 0, ?_⟩
  intro n _hn
  change COF.lt (eps k) ((1 : Scalar) - 0)
  rwa [sub_zero]

/-- Quotient order sees the constant half as positive. -/
theorem ltQuot_zero_half : ltQuot zeroQuot halfQuot := by
  change PosEventually (subSeq halfSeq zeroSeq)
  rcases half_pos_raw with ⟨k, hk⟩
  refine ⟨k, 0, ?_⟩
  intro n _hn
  change COF.lt (eps k) ((COF.half : Scalar) - 0)
  rwa [sub_zero]






end BishopCReal

