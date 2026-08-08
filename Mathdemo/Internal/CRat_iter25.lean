import Mathdemo.Internal.CRat_iter24

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

/-- Representative-level left-additive transport of quotient strict order. -/
theorem ltQuot_add_left_mk (c a b : RegularSeq) :
    ltQuot (mkQuot a) (mkQuot b) →
    ltQuot (addQuot (mkQuot c) (mkQuot a)) (addQuot (mkQuot c) (mkQuot b)) := by
  change PosEventually (subSeq b a) →
    PosEventually (subSeq (addSeq c b) (addSeq c a))
  exact posEventually_sub_add_left c a b

/-- Quotient strict order is preserved by adding a common left term. -/
theorem ltQuot_add_left (c a b : CRealQuot) :
    ltQuot a b → ltQuot (addQuot c a) (addQuot c b) := by
  refine Quotient.inductionOn c ?_
  intro c'
  refine Quotient.inductionOn a ?_
  intro a'
  refine Quotient.inductionOn b ?_
  intro b'
  exact ltQuot_add_left_mk c' a' b'

/-- A directed strict inequality gives apartness. -/
theorem apartQuot_of_lt {x y : CRealQuot} (h : ltQuot x y) : apartQuot x y :=
  Or.inl h

/-- Apartness is symmetric for the disjunctive quotient predicate. -/
theorem apartQuot_symm {x y : CRealQuot} : apartQuot x y → apartQuot y x := by
  intro h
  rcases h with hxy | hyx
  · exact Or.inr hxy
  · exact Or.inl hyx

/-- Audited additive transport seed for the quotient order layer. -/
structure CRealQuotOrderAddSeed : Type where
  lt_add_left : ∀ c a b : CRealQuot, ltQuot a b → ltQuot (addQuot c a) (addQuot c b)
  apart_of_lt : ∀ {x y : CRealQuot}, ltQuot x y → apartQuot x y
  apart_symm : ∀ {x y : CRealQuot}, apartQuot x y → apartQuot y x

def cRealQuotOrderAddSeed : CRealQuotOrderAddSeed where
  lt_add_left := ltQuot_add_left
  apart_of_lt := apartQuot_of_lt
  apart_symm := apartQuot_symm

end BishopCReal

