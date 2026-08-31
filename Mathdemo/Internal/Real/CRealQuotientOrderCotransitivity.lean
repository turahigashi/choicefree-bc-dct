import Mathdemo.Internal.Real.CRealQuotientOrderAdditiveTransport

/-!
# CReal quotient order cotransitivity

This closes the constructive cotransitivity shape for the quotient order.  The
proof uses the scalar cotransitivity law to split a positive gap
`eps k < (c - a) + (b - c)` into one of the two directed positive gaps, then
uses regularity to extend a sufficiently late point witness to a tail witness.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar split: if two summands are jointly above two copies of `e`, then one
summand is above `e`. -/
theorem scalar_lt_split_add {e u v : Scalar} (h : COF.lt (e + e) (u + v)) :
    COF.lt e u ∨ COF.lt e v := by
  rcases COF.lt_cotrans h (e + v) with hleft | hright
  · right
    have t := COF.lt_add_left (-e) hleft
    rwa [show -e + (e + e) = e from by ring,
      show -e + (e + v) = v from by ring] at t
  · left
    have t := COF.lt_add_left (-v) hright
    rwa [show -v + (e + v) = e from by ring,
      show -v + (u + v) = u from by ring] at t

/-- A sufficiently late pointwise positive witness extends to eventual
positivity by regularity. -/
theorem posEventually_of_late_point (x : RegularSeq) {j M : Nat}
    (hM : j + 2 ≤ M) (hpos : COF.lt (eps j) (x.val M)) :
    PosEventually x := by
  refine ⟨j + 1, M, ?_⟩
  intro n hn
  have hnlarge : j + 2 ≤ n := Nat.le_trans hM hn
  have hMle : Le (eps M) (eps (j + 2)) := eps_le_of_le hM
  have hnle : Le (eps n) (eps (j + 2)) := eps_le_of_le hnlarge
  have hsum := BishopC.le_add hMle hnle
  have hbudget : Le (eps M + eps n) (eps (j + 1)) := by
    rwa [eps_succ_add_self (j + 1)] at hsum
  have hdist : Le (COF.abs (x.val M - x.val n)) (eps (j + 1)) :=
    BishopC.le_trans (x.regular M n) hbudget
  have hlower : Le (x.val M - eps (j + 1)) (x.val n) :=
    scalar_point_lower_of_abs_le hdist
  have hshift : COF.lt (eps (j + 1)) (x.val M - eps (j + 1)) := by
    have t := COF.lt_add_left (-(eps (j + 1))) hpos
    rwa [← eps_succ_add_self j,
      show -(eps (j + 1)) + (eps (j + 1) + eps (j + 1)) = eps (j + 1)
        from by ring,
      show -(eps (j + 1)) + x.val M = x.val M - eps (j + 1)
        from by ring] at t
  exact BishopC.lt_of_lt_of_le hshift hlower

/-- Representative-level cotransitivity for the quotient order. -/
theorem ltQuot_cotrans_mk (a b c : RegularSeq) :
    ltQuot (mkQuot a) (mkQuot b) →
    ltQuot (mkQuot a) (mkQuot c) ∨ ltQuot (mkQuot c) (mkQuot b) := by
  change PosEventually (subSeq b a) →
    PosEventually (subSeq c a) ∨ PosEventually (subSeq b c)
  intro hpos
  rcases hpos with ⟨k, N, hN⟩
  let M : Nat := N + (k + 3)
  have hNM : N ≤ M := by
    unfold M
    omega
  have hMlate : k + 3 ≤ M := by
    unfold M
    omega
  have hba := hN M hNM
  change COF.lt (eps k) (b.val (M + 1) - a.val (M + 1)) at hba
  have hsplitInput :
      COF.lt (eps (k + 1) + eps (k + 1))
        ((c.val (M + 1) - a.val (M + 1)) + (b.val (M + 1) - c.val (M + 1))) := by
    rw [eps_succ_add_self k]
    rwa [show
        (c.val (M + 1) - a.val (M + 1)) + (b.val (M + 1) - c.val (M + 1))
          = b.val (M + 1) - a.val (M + 1)
        from by ring]
  rcases scalar_lt_split_add hsplitInput with hca | hbc
  · left
    change COF.lt (eps (k + 1)) ((subSeq c a).val M) at hca
    exact posEventually_of_late_point (subSeq c a) hMlate hca
  · right
    change COF.lt (eps (k + 1)) ((subSeq b c).val M) at hbc
    exact posEventually_of_late_point (subSeq b c) hMlate hbc

/-- Quotient cotransitivity for the induced strict order. -/
theorem ltQuot_cotrans (a b c : CRealQuot) (h : ltQuot a b) :
    ltQuot a c ∨ ltQuot c b := by
  revert b c
  refine Quotient.inductionOn a ?_
  intro a' b c h
  revert c h
  refine Quotient.inductionOn b ?_
  intro b' c h
  revert h
  refine Quotient.inductionOn c ?_
  intro c' h
  exact ltQuot_cotrans_mk a' b' c' h



end BishopCReal

