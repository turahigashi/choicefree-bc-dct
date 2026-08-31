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

/-- Transitivity closes at the next finer approximant with the original budget.
This is the immediate reindexing form of the triangle inequality. -/
theorem rel_trans_shifted_budget (x y z : RegularSeq) (hxy : rel x y) (hyz : rel y z) :
    ∀ n : Nat, Le (COF.abs (x.val (n + 1) - z.val (n + 1))) (tol n) := by
  intro n
  have h := rel_trans_double_budget x y z hxy hyz (n + 1)
  rwa [tol_succ_add_self n] at h

/-- Regularized finite-index transitivity budget.  For any comparison index
`n` and any finer index `j`, the usual four-term Bishop estimate separates the
fixed target budget from the shrinkable regularity tails. -/
theorem rel_trans_regularized_budget (x y z : RegularSeq) (hxy : rel x y) (hyz : rel y z)
    (n j : Nat) :
    Le (COF.abs (x.val n - z.val n))
      (((eps n + eps j) + tol j) + (tol j + (eps j + eps n))) := by
  have htri : Le (COF.abs (x.val n - z.val n))
      (COF.abs (x.val n - y.val j) + COF.abs (y.val j - z.val n)) := by
    have h := scalar_abs_add_le (x.val n - y.val j) (y.val j - z.val n)
    rwa [show (x.val n - y.val j) + (y.val j - z.val n) = x.val n - z.val n
      from by ring] at h
  have hleft : Le (COF.abs (x.val n - y.val j))
      (COF.abs (x.val n - x.val j) + COF.abs (x.val j - y.val j)) := by
    have h := scalar_abs_add_le (x.val n - x.val j) (x.val j - y.val j)
    rwa [show (x.val n - x.val j) + (x.val j - y.val j) = x.val n - y.val j
      from by ring] at h
  have hright : Le (COF.abs (y.val j - z.val n))
      (COF.abs (y.val j - z.val j) + COF.abs (z.val j - z.val n)) := by
    have h := scalar_abs_add_le (y.val j - z.val j) (z.val j - z.val n)
    rwa [show (y.val j - z.val j) + (z.val j - z.val n) = y.val j - z.val n
      from by ring] at h
  have hbudget_left : Le
      (COF.abs (x.val n - x.val j) + COF.abs (x.val j - y.val j))
      ((eps n + eps j) + tol j) :=
    BishopC.le_add (x.regular n j) (hxy j)
  have hbudget_right : Le
      (COF.abs (y.val j - z.val j) + COF.abs (z.val j - z.val n))
      (tol j + (eps j + eps n)) :=
    BishopC.le_add (hyz j) (z.regular j n)
  exact BishopC.le_trans htri
    (BishopC.le_trans (BishopC.le_add hleft hright)
      (BishopC.le_add hbudget_left hbudget_right))

/-- Audited seed for the reindexing route toward exact relation transitivity. -/
structure CRealRelationShiftSeed : Type where
  shift_regular : ∀ x : RegularSeq, RegularVal (shiftVal x.val)
  shift_respects_self : ∀ x : RegularSeq, relVal (shiftVal x.val) x.val
  self_respects_shift : ∀ x : RegularSeq, relVal x.val (shiftVal x.val)
  rel_trans_shifted_budget : ∀ x y z : RegularSeq, rel x y → rel y z →
    ∀ n : Nat, Le (COF.abs (x.val (n + 1) - z.val (n + 1))) (tol n)
  rel_trans_regularized_budget : ∀ x y z : RegularSeq, rel x y → rel y z →
    ∀ n j : Nat,
      Le (COF.abs (x.val n - z.val n))
        (((eps n + eps j) + tol j) + (tol j + (eps j + eps n)))

def cRealRelationShiftSeed : CRealRelationShiftSeed where
  shift_regular := shift_regular
  shift_respects_self := shift_respects_self
  self_respects_shift := self_respects_shift
  rel_trans_shifted_budget := rel_trans_shifted_budget
  rel_trans_regularized_budget := rel_trans_regularized_budget

end BishopCReal

