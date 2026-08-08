import Mathdemo.Internal.CRat_iter19

/-!
# CReal eventual Bishop equality

The raw pointwise relation `relVal` is useful as a boundary, but its exact
transitivity needs a squeeze argument.  This file follows the source-approved
eventual-closeness route: two regular representatives are equal when their
tails are arbitrarily close in the dyadic gauge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Eventual Bishop equality for regular representatives. -/
def relEventually (x y : RegularSeq) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n → Le (COF.abs (x.val n - y.val n)) (eps k)

/-- If `k+1 ≤ n`, the current pointwise equality budget at `n` is within
the target `eps k`. -/
theorem tol_le_eps_of_succ_le {k n : Nat} (hkn : k + 1 ≤ n) : Le (tol n) (eps k) := by
  unfold tol
  have h1 : Le (eps n) (eps (k + 1)) := eps_le_of_le hkn
  have hsum := BishopC.le_add h1 h1
  rwa [eps_succ_add_self k] at hsum

/-- The existing raw equality relation implies eventual Bishop equality. -/
theorem rel_to_relEventually (x y : RegularSeq) (hxy : rel x y) : relEventually x y := by
  intro k
  refine ⟨k + 1, ?_⟩
  intro n hn
  exact BishopC.le_trans (hxy n) (tol_le_eps_of_succ_le hn)

/-- Eventual equality is reflexive. -/
theorem relEventually_refl (x : RegularSeq) : relEventually x x := by
  intro k
  refine ⟨0, ?_⟩
  intro n _hn
  rw [show x.val n - x.val n = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (eps k)
  rw [scalarCOFOSeed.abs_zero]
  exact eps_nonneg k

/-- Eventual equality is symmetric. -/
theorem relEventually_symm (x y : RegularSeq) (hxy : relEventually x y) : relEventually y x := by
  intro k
  rcases hxy k with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  rw [show y.val n - x.val n = -(x.val n - y.val n) from by ring]
  change Le (BishopCRat.CRat.absF (-(x.val n - y.val n))) (eps k)
  rw [scalarCOFOSeed.abs_neg (x.val n - y.val n)]
  exact h

/-- Eventual equality is transitive by taking both witnesses at gauge `k+1`. -/
theorem relEventually_trans (x y z : RegularSeq)
    (hxy : relEventually x y) (hyz : relEventually y z) : relEventually x z := by
  intro k
  rcases hxy (k + 1) with ⟨Nxy, hNxy⟩
  rcases hyz (k + 1) with ⟨Nyz, hNyz⟩
  refine ⟨Nxy + Nyz, ?_⟩
  intro n hn
  have hnxy : Nxy ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hnyz : Nyz ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have htri : Le (COF.abs (x.val n - z.val n))
      (COF.abs (x.val n - y.val n) + COF.abs (y.val n - z.val n)) := by
    have h := scalar_abs_add_le (x.val n - y.val n) (y.val n - z.val n)
    rwa [show (x.val n - y.val n) + (y.val n - z.val n) = x.val n - z.val n
      from by ring] at h
  have hsum := BishopC.le_add (hNxy n hnxy) (hNyz n hnyz)
  have hbudget : Le
      (COF.abs (x.val n - y.val n) + COF.abs (y.val n - z.val n)) (eps k) := by
    rwa [eps_succ_add_self k] at hsum
  exact BishopC.le_trans htri hbudget

/-- Audited setoid-style seed for eventual Bishop equality. -/
structure CRealEventualSetoidSeed : Type where
  relEventually : RegularSeq → RegularSeq → Prop
  raw_to_eventual : ∀ x y : RegularSeq, rel x y → relEventually x y
  refl : ∀ x : RegularSeq, relEventually x x
  symm : ∀ x y : RegularSeq, relEventually x y → relEventually y x
  trans : ∀ x y z : RegularSeq,
    relEventually x y → relEventually y z → relEventually x z

def cRealEventualSetoidSeed : CRealEventualSetoidSeed where
  relEventually := relEventually
  raw_to_eventual := rel_to_relEventually
  refl := relEventually_refl
  symm := relEventually_symm
  trans := relEventually_trans

end BishopCReal

