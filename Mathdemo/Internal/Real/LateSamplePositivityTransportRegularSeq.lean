import Mathdemo.Internal.Real.PointwiseNonnegativityBridgeRegularSeqOrderSurface

set_option linter.style.longLine false

/-!
# G120: late-sample positivity transport for RegularSeq

Line 735's remaining `minSeqWith` monotonicity proof has to handle the bounded
multiplication sampling index inside `mulSeqConcreteWith A halfSeq ...`.

This file closes the general RegularSeq bridge needed for that index drift:
if a regular representative is eventually positive along a cofinal late
sampling function, then it is positive in the ordinary `PosEventually` sense.
No quotient representative extraction and no `PosEventually -> Data` selector
is used.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Positivity along a late cofinal sample sequence transports back to ordinary
eventual positivity by regularity. -/
theorem posEventually_of_late_sample_pos
    (x : RegularSeq)
    (F : Nat -> Nat)
    (hF : forall n : Nat, n <= F n)
    (hpos : ∃ k N : Nat, ∀ n : Nat, N <= n -> COF.lt (eps k) (x.val (F n))) :
    PosEventually x := by
  rcases hpos with ⟨k, N, hN⟩
  refine ⟨k + 1, N + (k + 2), ?_⟩
  intro n hn
  have hNn : N <= n :=
    Nat.le_trans (Nat.le_add_right _ _) hn
  have hk2n : k + 2 <= n :=
    Nat.le_trans (Nat.le_add_left _ _) hn
  have hsample : COF.lt (eps k) (x.val (F n)) :=
    hN n hNn
  have hFbound : k + 2 <= F n :=
    Nat.le_trans hk2n (hF n)
  have hleft : Le (eps (F n)) (eps (k + 2)) :=
    eps_le_of_le hFbound
  have hright : Le (eps n) (eps (k + 2)) :=
    eps_le_of_le hk2n
  have hsum : Le (eps (F n) + eps n) (eps (k + 2) + eps (k + 2)) :=
    BishopC.le_add hleft hright
  have hbudget : Le (eps (F n) + eps n) (eps (k + 1)) := by
    rwa [eps_succ_add_self (k + 1)] at hsum
  have hdist : Le (COF.abs (x.val (F n) - x.val n)) (eps (k + 1)) :=
    BishopC.le_trans (x.regular (F n) n) hbudget
  have hlower : Le (x.val (F n) - eps (k + 1)) (x.val n) :=
    scalar_point_lower_of_abs_le hdist
  have hshift : COF.lt (eps (k + 1)) (x.val (F n) - eps (k + 1)) := by
    have t := COF.lt_add_left (-(eps (k + 1))) hsample
    rwa [← eps_succ_add_self k,
      show -(eps (k + 1)) + (eps (k + 1) + eps (k + 1)) = eps (k + 1)
        from by ring,
      show -(eps (k + 1)) + x.val (F n) = x.val (F n) - eps (k + 1)
        from by ring] at t
  exact BishopC.lt_of_lt_of_le hshift hlower

/-- A specialized version for represented differences. -/
theorem posEventually_subSeq_of_late_sample_pos
    (x y : RegularSeq)
    (F : Nat -> Nat)
    (hF : forall n : Nat, n <= F n)
    (hpos :
      ∃ k N : Nat,
        ∀ n : Nat, N <= n -> COF.lt (eps k) ((subSeq y x).val (F n))) :
    PosEventually (subSeq y x) :=
  posEventually_of_late_sample_pos (subSeq y x) F hF hpos

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}





end BishopRegularSeqTheorem118





end BishopCReal
