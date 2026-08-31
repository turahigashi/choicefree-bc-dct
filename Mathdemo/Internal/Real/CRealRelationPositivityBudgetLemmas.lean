import Mathdemo.Internal.Real.CRealFixedBoundMultiplicationNegation

/-!
# CReal relation and positivity budget lemmas

The current `relVal` and `PosRaw` frontiers are tight enough that the full
`rel_trans` and `pos_respects` fields should not be faked.  This file records
the honest budget facts available from the current definitions:

* transitivity gives a doubled tolerance immediately;
* positivity is relation-invariant when the positive witness has an explicit
  extra tolerance margin.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Current raw equality composes with doubled tolerance.  This is the honest
triangle-inequality budget behind the still-open exact `rel_trans` field. -/
theorem rel_trans_double_budget (x y z : RegularSeq) (hxy : rel x y) (hyz : rel y z) :
    ∀ n : Nat, Le (COF.abs (x.val n - z.val n)) (tol n + tol n) := by
  intro n
  have htri : Le (COF.abs (x.val n - z.val n))
      (COF.abs (x.val n - y.val n) + COF.abs (y.val n - z.val n)) := by
    have h := scalar_abs_add_le (x.val n - y.val n) (y.val n - z.val n)
    rwa [show (x.val n - y.val n) + (y.val n - z.val n)
        = x.val n - z.val n from by ring] at h
  have hbudget := BishopC.le_add (hxy n) (hyz n)
  exact BishopC.le_trans htri hbudget

/-- Positivity with a full equality-tolerance margin. -/
def PosRawMargin (x : RegularSeq) : Prop :=
  ∃ n : Nat, COF.lt (tol n + eps n) (x.val n)

/-- Scalar rearrangement: from `a - b ≤ c`, derive `a - c ≤ b`. -/
theorem scalar_le_sub_of_sub_le {a b c : Scalar} (h : Le (a - b) c) :
    Le (a - c) b := by
  intro hbad
  apply h
  have t := COF.lt_add_left (c - b) hbad
  rwa [show (c - b) + b = c from by ring,
    show (c - b) + (a - c) = a - b from by ring] at t

/-- A relation bound gives the usual one-sided lower estimate. -/
theorem rel_point_lower (x y : RegularSeq) (hxy : rel x y) (n : Nat) :
    Le (x.val n - tol n) (y.val n) := by
  have hself : Le (x.val n - y.val n) (COF.abs (x.val n - y.val n)) := by
    change ¬ COF.lt (COF.abs (x.val n - y.val n)) (x.val n - y.val n)
    exact scalarCOFOSeed.le_abs_self (x.val n - y.val n)
  exact scalar_le_sub_of_sub_le (BishopC.le_trans hself (hxy n))

/-- Margin positivity is invariant under the current raw relation. -/
theorem pos_respects_margin (x y : RegularSeq) (hxy : rel x y) :
    PosRawMargin x → PosRaw y := by
  intro hx
  rcases hx with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have heps : COF.lt (eps n) (x.val n - tol n) := by
    have t := COF.lt_add_left (-(tol n)) hn
    rwa [show -(tol n) + (tol n + eps n) = eps n from by ring,
      show -(tol n) + x.val n = x.val n - tol n from by ring] at t
  exact BishopC.lt_of_lt_of_le heps (rel_point_lower x y hxy n)

/-- Audited relation/positivity budget seed. -/
structure CRealRelationBudgetSeed : Type where
  rel_trans_double_budget : ∀ x y z : RegularSeq, rel x y → rel y z →
    ∀ n : Nat, Le (COF.abs (x.val n - z.val n)) (tol n + tol n)
  PosRawMargin : RegularSeq → Prop
  pos_respects_margin : ∀ x y : RegularSeq, rel x y → PosRawMargin x → PosRaw y

def cRealRelationBudgetSeed : CRealRelationBudgetSeed where
  rel_trans_double_budget := rel_trans_double_budget
  PosRawMargin := PosRawMargin
  pos_respects_margin := pos_respects_margin

end BishopCReal

