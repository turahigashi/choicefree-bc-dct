import Mathdemo.Internal.Real.CRealQuotientCOFPreInstancePackage

/-!
# CReal quotient cotransitivity data bridge

`CRealQuotientCOFPreInstancePackage` identified the remaining `COF` blocker: the live interface asks
for a Type-valued cotransitivity split

```
∀ {a b : CRealQuot}, ltQuot a b → ∀ c : CRealQuot,
  PSum (ltQuot a c) (ltQuot c b)
```

The current quotient order stores positivity as a `Prop`, so extracting the
tail witness hidden in `ltQuot a b` would itself be a new constructive
witness-extraction theorem.  This file closes the data-cotransitivity argument
once representative and positivity witnesses are supplied explicitly, and
records the exact remaining quotient witness frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Type-valued tail-stable positivity witness. -/
structure PosEventuallyData (x : RegularSeq) : Type where
  k : Nat
  N : Nat
  tail_pos : ∀ n : Nat, N ≤ n → COF.lt (eps k) (x.val n)

def PosEventuallyData.toProp {x : RegularSeq} (h : PosEventuallyData x) :
    PosEventually x :=
  ⟨h.k, h.N, h.tail_pos⟩

/-- Data-valued scalar split, using the live scalar `COF.lt_cotrans_data`
instead of the Prop-valued cotransitivity shadow. -/
def scalar_lt_split_add_data {e u v : Scalar}
    (h : COF.lt (e + e) (u + v)) : PSum (COF.lt e u) (COF.lt e v) := by
  cases COF.lt_cotrans_data h (e + v) with
  | inl hleft =>
      exact PSum.inr (by
        have t := COF.lt_add_left (-e) hleft
        rwa [show -e + (e + e) = e from by ring,
          show -e + (e + v) = v from by ring] at t)
  | inr hright =>
      exact PSum.inl (by
        have t := COF.lt_add_left (-v) hright
        rwa [show -v + (e + v) = e from by ring,
          show -v + (u + v) = u from by ring] at t)

/-- Data version of `posEventually_of_late_point`. -/
def posEventuallyData_of_late_point (x : RegularSeq) {j M : Nat}
    (hM : j + 2 ≤ M) (hpos : COF.lt (eps j) (x.val M)) :
    PosEventuallyData x where
  k := j + 1
  N := M
  tail_pos := by
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

/-- Representative-level Type-valued cotransitivity split. -/
def ltQuot_cotrans_mk_data (a b c : RegularSeq)
    (hpos : PosEventuallyData (subSeq b a)) :
    PSum (PosEventuallyData (subSeq c a)) (PosEventuallyData (subSeq b c)) := by
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
  cases scalar_lt_split_add_data hsplitInput with
  | inl hca =>
      exact PSum.inl (by
        change COF.lt (eps (k + 1)) ((subSeq c a).val M) at hca
        exact posEventuallyData_of_late_point (subSeq c a) hMlate hca)
  | inr hbc =>
      exact PSum.inr (by
        change COF.lt (eps (k + 1)) ((subSeq b c).val M) at hbc
        exact posEventuallyData_of_late_point (subSeq b c) hMlate hbc)











end BishopCReal

