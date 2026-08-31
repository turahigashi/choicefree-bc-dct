import Mathdemo.Internal.Real.CRealQuotientOrderSanityLemmas

/-!
# CReal quotient order and additive transport

This file adds the first order-operation compatibility law on the
eventual-equality quotient: strict order is preserved by adding the same
quotient element on the left.  The representative proof is only an index shift.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Positivity of `b - a` transports to positivity of `(c + b) - (c + a)`. -/
theorem posEventually_sub_add_left (c a b : RegularSeq) :
    PosEventually (subSeq b a) →
    PosEventually (subSeq (addSeq c b) (addSeq c a)) := by
  intro hpos
  rcases hpos with ⟨k, N, hN⟩
  refine ⟨k, N, ?_⟩
  intro n hn
  have hn' : N ≤ n + 1 := Nat.le_trans hn (Nat.le_succ n)
  have h := hN (n + 1) hn'
  change COF.lt (eps k) (b.val ((n + 1) + 1) - a.val ((n + 1) + 1)) at h
  change COF.lt (eps k)
    ((c.val ((n + 1) + 1) + b.val ((n + 1) + 1)) -
      (c.val ((n + 1) + 1) + a.val ((n + 1) + 1)))
  rwa [show
      (c.val ((n + 1) + 1) + b.val ((n + 1) + 1) -
          (c.val ((n + 1) + 1) + a.val ((n + 1) + 1)))
        = b.val ((n + 1) + 1) - a.val ((n + 1) + 1)
      from by ring]







end BishopCReal

