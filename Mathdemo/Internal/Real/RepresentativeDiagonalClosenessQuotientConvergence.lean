import Mathdemo.Internal.Real.ClosingRepresentativeGapCloseStep

/-!
# Representative diagonal closeness to quotient convergence

`ClosingRepresentativeGapCloseStep` closed quotient-Cauchy to representative-Cauchy extraction for
the positive-inverse conditional branch.  The remaining completeness input is
the diagonal limit.  This file refines that input: it is enough to construct a
representative limit and prove representative tail closeness one dyadic step
finer than the requested quotient convergence gauge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- If `a ≤ eps (k+1)`, then there is a strict positive dyadic gap below
`eps k`. -/
theorem scalar_eps_gap_of_le_succ {a : Scalar} (k : Nat)
    (ha : Le a (eps (k + 1))) :
    COF.lt (eps (k + 2)) (eps k - a) := by
  have htail : COF.lt (eps (k + 1)) (eps k - eps (k + 2)) := by
    have t := COF.lt_add_left (eps (k + 1)) (eps_pos (k + 2))
    rwa [show eps (k + 1) + 0 = eps (k + 1) from by ring,
      show eps (k + 1) + eps (k + 2) = eps k - eps (k + 2) from by
        rw [← eps_succ_add_self k, ← eps_succ_add_self (k + 1)]
        ring] at t
  have ha_strict : COF.lt a (eps k - eps (k + 2)) :=
    scalar_lt_of_le_of_lt ha htail
  have hsum : COF.lt (eps (k + 2) + a) (eps k) := by
    have t := COF.lt_add_left (eps (k + 2)) ha_strict
    rwa [show eps (k + 2) + (eps k - eps (k + 2)) = eps k from by ring]
      at t
  have t := COF.lt_add_left (-a) hsum
  rwa [show -a + (eps (k + 2) + a) = eps (k + 2) from by ring,
    show -a + eps k = eps k - a from by ring] at t

/-- Representative closeness at gauge `k+1` gives quotient strict closeness at
gauge `k`. -/
theorem ltQuot_abs_sub_const_of_repClose_succ
    (x y : RegularSeq) (k : Nat)
    (hclose : RepCloseAtGauge (k + 1) x y) :
    ltQuot
      (absQuot (subQuot (mkQuot x) (mkQuot y)))
      (constQuot (eps k)) := by
  rcases hclose with ⟨N, hN⟩
  change PosEventually
    (subSeq (constSeq (eps k)) (absSeq (subSeq x y)))
  refine ⟨k + 2, N, ?_⟩
  intro n hn
  have hle :
      Le (COF.abs (x.val (n + 2) - y.val (n + 2))) (eps (k + 1)) :=
    hN (n + 2) (Nat.le_trans hn (Nat.le_add_right n 2))
  have hgap :=
    scalar_eps_gap_of_le_succ (a := COF.abs (x.val (n + 2) - y.val (n + 2)))
      k hle
  simpa [subSeq, subVal, constSeq, constVal, absSeq, absVal, addIndex]
    using hgap

/-- Representative diagonal-limit data stated with representative closeness
rather than quotient strict convergence. -/
structure CRealRepDiagonalLimitCloseData : Type 1 where
  limit : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → RegularSeq
  lmod : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → Nat → Nat
  close_to_limit :
    ∀ (w : Nat → RegularSeq) (hc : CRealRepSequenceCauchyData w),
      ∀ k n : Nat, lmod w hc k ≤ n →
        RepCloseAtGauge (k + 1) (w n) (limit w hc)





end BishopCReal

