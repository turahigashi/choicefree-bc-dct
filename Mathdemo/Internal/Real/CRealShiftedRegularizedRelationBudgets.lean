import Mathdemo.Internal.Real.CRealRelationPositivityBudgetLemmas

/-!
# CReal shifted and regularized relation budgets

The current Bishop equality budget is intentionally tight.  Exact transitivity
requires the standard Bishop move: pass to finer approximants and then make the
extra regularity budget arbitrarily small.  This file records the checked
reindexing lemmas and the finite regularized budget that form that route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- One-step finer representative values. -/
def shiftVal (x : Nat → Scalar) (n : Nat) : Scalar :=
  x (n + 1)

/-- Reindexing a regular representative by one step remains regular. -/
theorem shift_regular (x : RegularSeq) : RegularVal (shiftVal x.val) := by
  intro m n
  unfold shiftVal
  have hx := x.regular (m + 1) (n + 1)
  have hbudget : Le (eps (m + 1) + eps (n + 1)) (eps m + eps n) :=
    BishopC.le_add (eps_succ_le_eps m) (eps_succ_le_eps n)
  exact BishopC.le_trans hx hbudget

/-- A one-step finer representative is Bishop-close to the original one. -/
theorem shift_respects_self (x : RegularSeq) : relVal (shiftVal x.val) x.val := by
  intro n
  unfold shiftVal
  exact BishopC.le_trans (x.regular (n + 1) n) (eps_succ_add_le_tol n)

/-- The original representative is Bishop-close to its one-step shift. -/
theorem self_respects_shift (x : RegularSeq) : relVal x.val (shiftVal x.val) := by
  intro n
  unfold shiftVal
  have hbudget : Le (eps n + eps (n + 1)) (tol n) := by
    rw [show eps n + eps (n + 1) = eps (n + 1) + eps n from by ring]
    exact eps_succ_add_le_tol n
  exact BishopC.le_trans (x.regular n (n + 1)) hbudget





end BishopCReal

