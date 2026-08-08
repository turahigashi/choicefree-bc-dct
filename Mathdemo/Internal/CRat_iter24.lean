import Mathdemo.Internal.CRat_iter23

/-!
# CReal quotient order sanity lemmas

This file proves the first quotient-level order facts available from the
eventual positivity layer: zero is not positive, self-subtraction is zero, and
the induced strict order is irreflexive.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The zero representative is not eventually positive. -/
theorem not_posEventually_zero : ¬ PosEventually zeroSeq := by
  intro hz
  rcases hz with ⟨k, N, hN⟩
  have hlt : COF.lt (eps k) (0 : Scalar) := by
    have h := hN N (Nat.le_refl N)
    unfold zeroSeq constSeq constVal at h
    exact h
  exact COF.lt_irrefl (0 : Scalar) (scalarCOFOSeed.lt_trans (eps_pos k) hlt)

/-- Self-subtraction is eventually equal to zero. -/
theorem subSeq_self_eventually (x : RegularSeq) :
    relEventually (subSeq x x) zeroSeq := by
  apply rel_to_relEventually
  change relVal (subVal x.val x.val) zeroVal
  exact sub_self_raw x

/-- Self-subtraction is zero on the quotient, for representatives. -/
theorem subQuot_self_mk (x : RegularSeq) :
    subQuot (mkQuot x) (mkQuot x) = zeroQuot :=
  Quotient.sound (subSeq_self_eventually x)

/-- Quotient zero is not positive. -/
theorem not_posQuot_zero : ¬ posQuot zeroQuot := by
  change ¬ PosEventually zeroSeq
  exact not_posEventually_zero

/-- Irreflexivity for quotient representatives. -/
theorem ltQuot_irrefl_mk (x : RegularSeq) : ¬ ltQuot (mkQuot x) (mkQuot x) := by
  unfold ltQuot
  rw [subQuot_self_mk x]
  exact not_posQuot_zero

/-- Irreflexivity for the quotient order. -/
theorem ltQuot_irrefl (x : CRealQuot) : ¬ ltQuot x x := by
  refine Quotient.inductionOn x ?_
  intro a
  exact ltQuot_irrefl_mk a

/-- A quotient element is not apart from itself. -/
theorem not_apartQuot_self (x : CRealQuot) : ¬ apartQuot x x := by
  intro hx
  rcases hx with h | h
  · exact ltQuot_irrefl x h
  · exact ltQuot_irrefl x h

/-- Audited sanity seed for the quotient order layer. -/
structure CRealQuotOrderSanitySeed : Type where
  not_pos_zero : ¬ posQuot zeroQuot
  sub_self_mk : ∀ x : RegularSeq, subQuot (mkQuot x) (mkQuot x) = zeroQuot
  lt_irrefl : ∀ x : CRealQuot, ¬ ltQuot x x
  not_apart_self : ∀ x : CRealQuot, ¬ apartQuot x x

def cRealQuotOrderSanitySeed : CRealQuotOrderSanitySeed where
  not_pos_zero := not_posQuot_zero
  sub_self_mk := subQuot_self_mk
  lt_irrefl := ltQuot_irrefl
  not_apart_self := not_apartQuot_self

end BishopCReal

