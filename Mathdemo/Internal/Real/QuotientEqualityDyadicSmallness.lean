import Mathdemo.Internal.Real.QuotientMultiplicativeArchimedeanBound

/-!
# Quotient equality from dyadic smallness

`QuotientMultiplicativeArchimedeanBound` closed `mul_archimedean`.  This file closes the missing
separation field:

* if `|a - b|` is not eventually above any dyadic gauge, then `a = b`.

The representative proof uses a two-step shift.  The quotient strict order for
`eps k < |a - b|` samples the raw representatives two indices later, so we
first prove eventual equality for the double-shifted representatives and then
transport back along the already-audited shift equivalences.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- One-step shifted regular representative. -/
def shiftSeq (x : RegularSeq) : RegularSeq where
  val := shiftVal x.val
  regular := shift_regular x

/-- A representative is eventually equal to its one-step shift. -/
theorem relEventually_self_shiftSeq (x : RegularSeq) :
    relEventually x (shiftSeq x) :=
  rel_to_relEventually x (shiftSeq x) (self_respects_shift x)

/-- A one-step shift is eventually equal to the original representative. -/
theorem relEventually_shiftSeq_self (x : RegularSeq) :
    relEventually (shiftSeq x) x :=
  rel_to_relEventually (shiftSeq x) x (shift_respects_self x)

/-- A representative is eventually equal to its two-step shift. -/
theorem relEventually_self_shiftSeq2 (x : RegularSeq) :
    relEventually x (shiftSeq (shiftSeq x)) :=
  relEventually_trans x (shiftSeq x) (shiftSeq (shiftSeq x))
    (relEventually_self_shiftSeq x)
    (relEventually_self_shiftSeq (shiftSeq x))

/-- A two-step shift is eventually equal to the original representative. -/
theorem relEventually_shiftSeq2_self (x : RegularSeq) :
    relEventually (shiftSeq (shiftSeq x)) x :=
  relEventually_trans (shiftSeq (shiftSeq x)) (shiftSeq x) x
    (relEventually_shiftSeq_self (shiftSeq x))
    (relEventually_shiftSeq_self x)

/-- If the quotient absolute difference is not above any dyadic constant, then
the double-shifted representatives are eventually equal. -/
theorem relEventually_shiftSeq2_of_no_const_lt_abs_sub
    (x y : RegularSeq)
    (hsmall : ∀ k : Nat,
      ¬ ltQuot (constQuot (eps k))
        (absQuot (subQuot (mkQuot x) (mkQuot y)))) :
    relEventually (shiftSeq (shiftSeq x)) (shiftSeq (shiftSeq y)) := by
  intro k
  refine ⟨k + 3, ?_⟩
  intro n hn
  change Le (COF.abs (x.val (n + 2) - y.val (n + 2))) (eps k)
  intro hbad
  have hshift : COF.lt (eps (k + 1))
      (COF.abs (x.val (n + 2) - y.val (n + 2)) - eps (k + 1)) := by
    have t := COF.lt_add_left (-(eps (k + 1))) hbad
    rwa [← eps_succ_add_self k,
      show -(eps (k + 1)) + (eps (k + 1) + eps (k + 1)) =
          eps (k + 1) from by ring,
      show -(eps (k + 1)) + COF.abs (x.val (n + 2) - y.val (n + 2)) =
          COF.abs (x.val (n + 2) - y.val (n + 2)) - eps (k + 1) from by ring] at t
  have hpoint : COF.lt (eps (k + 1))
      ((subSeq (absSeq (subSeq x y)) (constSeq (eps (k + 1)))).val n) := by
    change COF.lt (eps (k + 1))
      (COF.abs (x.val (n + 2) - y.val (n + 2)) - eps (k + 1))
    exact hshift
  have hlate : (k + 1) + 2 <= n := by
    omega
  have hpos : PosEventually
      (subSeq (absSeq (subSeq x y)) (constSeq (eps (k + 1)))) :=
    posEventually_of_late_point
      (subSeq (absSeq (subSeq x y)) (constSeq (eps (k + 1))))
      hlate hpoint
  have hlt : ltQuot (constQuot (eps (k + 1)))
      (absQuot (subQuot (mkQuot x) (mkQuot y))) := by
    change PosEventually
      (subSeq (absSeq (subSeq x y)) (constSeq (eps (k + 1))))
    exact hpos
  exact hsmall (k + 1) hlt

/-- Representative-level equality from the quotient dyadic smallness test. -/
theorem relEventually_of_no_const_lt_abs_sub
    (x y : RegularSeq)
    (hsmall : ∀ k : Nat,
      ¬ ltQuot (constQuot (eps k))
        (absQuot (subQuot (mkQuot x) (mkQuot y)))) :
    relEventually x y := by
  have hx : relEventually x (shiftSeq (shiftSeq x)) :=
    relEventually_self_shiftSeq2 x
  have hxy : relEventually (shiftSeq (shiftSeq x)) (shiftSeq (shiftSeq y)) :=
    relEventually_shiftSeq2_of_no_const_lt_abs_sub x y hsmall
  have hy : relEventually (shiftSeq (shiftSeq y)) y :=
    relEventually_shiftSeq2_self y
  exact relEventually_trans x (shiftSeq (shiftSeq x)) y hx
    (relEventually_trans (shiftSeq (shiftSeq x)) (shiftSeq (shiftSeq y)) y hxy hy)






end BishopCReal

