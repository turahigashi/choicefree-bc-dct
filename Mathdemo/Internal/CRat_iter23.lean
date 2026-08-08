import Mathdemo.Internal.CRat_iter22

/-!
# CReal eventual positivity

This file starts the order layer on the eventual-equality quotient.  The raw
`PosRaw` predicate is too tight for direct quotient transport, so we use a
tail-stable positive lower bound and then lift it to the quotient.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Tail-stable positivity: eventually the representative is bounded below by
a fixed positive Bishop gauge. -/
def PosEventually (x : RegularSeq) : Prop :=
  ∃ k N : Nat, ∀ n : Nat, N ≤ n → COF.lt (eps k) (x.val n)

/-- A scalar absolute-value bound gives a one-sided lower estimate. -/
theorem scalar_point_lower_of_abs_le {a b c : Scalar}
    (h : Le (COF.abs (a - b)) c) : Le (a - c) b := by
  have hself : Le (a - b) (COF.abs (a - b)) := by
    change ¬ COF.lt (COF.abs (a - b)) (a - b)
    exact scalarCOFOSeed.le_abs_self (a - b)
  exact scalar_le_sub_of_sub_le (BishopC.le_trans hself h)

/-- Eventual equality gives eventual one-sided lower estimates at each gauge. -/
theorem relEventually_point_lower (x y : RegularSeq) (hxy : relEventually x y) (k : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → Le (x.val n - eps k) (y.val n) := by
  rcases hxy k with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact scalar_point_lower_of_abs_le (hN n hn)

/-- Eventual positivity is invariant under eventual Bishop equality. -/
theorem posEventually_respects (x y : RegularSeq) (hxy : relEventually x y) :
    PosEventually x → PosEventually y := by
  intro hx
  rcases hx with ⟨k, Nx, hxN⟩
  rcases relEventually_point_lower x y hxy (k + 1) with ⟨Ny, hyN⟩
  refine ⟨k + 1, Nx + Ny, ?_⟩
  intro n hn
  have hnx : Nx ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hny : Ny ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have hshift : COF.lt (eps (k + 1)) (x.val n - eps (k + 1)) := by
    have t := COF.lt_add_left (-(eps (k + 1))) (hxN n hnx)
    rwa [← eps_succ_add_self k,
      show -(eps (k + 1)) + (eps (k + 1) + eps (k + 1)) = eps (k + 1)
        from by ring,
      show -(eps (k + 1)) + x.val n = x.val n - eps (k + 1)
        from by ring] at t
  exact BishopC.lt_of_lt_of_le hshift (hyN n hny)

/-- Positivity on the eventual-equality quotient. -/
def posQuot : CRealQuot → Prop :=
  Quotient.lift PosEventually
    (fun x y hxy =>
      propext ⟨posEventually_respects x y hxy,
        posEventually_respects y x (relEventually_symm x y hxy)⟩)

/-- Quotient order: `x < y` means `y - x` is positive. -/
def ltQuot (x y : CRealQuot) : Prop :=
  posQuot (subQuot y x)

/-- Quotient nonnegativity in constructive order style. -/
def nonnegQuot (x : CRealQuot) : Prop :=
  ¬ posQuot (negQuot x)

/-- Quotient apartness, recorded as a disjunction of directed positivity. -/
def apartQuot (x y : CRealQuot) : Prop :=
  ltQuot x y ∨ ltQuot y x

/-- Audited first-order seed for the quotient order layer. -/
structure CRealQuotPositiveSeed : Type where
  PosEventually : RegularSeq → Prop
  pos_respects : ∀ x y : RegularSeq, relEventually x y → PosEventually x → PosEventually y
  posQuot : CRealQuot → Prop
  ltQuot : CRealQuot → CRealQuot → Prop
  nonnegQuot : CRealQuot → Prop
  apartQuot : CRealQuot → CRealQuot → Prop

def cRealQuotPositiveSeed : CRealQuotPositiveSeed where
  PosEventually := PosEventually
  pos_respects := posEventually_respects
  posQuot := posQuot
  ltQuot := ltQuot
  nonnegQuot := nonnegQuot
  apartQuot := apartQuot

end BishopCReal

