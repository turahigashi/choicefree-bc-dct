import Mathdemo.Internal.CRat_iter20

/-!
# CReal representation arithmetic over eventual equality

This file promotes the additive/absolute-value representative operations to
the eventual-equality relation.  It is still a representation/quotient-prep
layer, not a claimed `CommRing` or `COFOC` instance.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Eventual Bishop equality as a Lean setoid on representatives. -/
instance eventualSetoid : Setoid RegularSeq where
  r := relEventually
  iseqv := ⟨relEventually_refl,
    (by intro x y hxy; exact relEventually_symm x y hxy),
    (by intro x y z hxy hyz; exact relEventually_trans x y z hxy hyz)⟩

/-- Quotient carrier for the eventual-equality route. -/
def CRealQuot : Type := Quotient eventualSetoid

/-- Constant representative. -/
def constSeq (q : Scalar) : RegularSeq where
  val := constVal q
  regular := const_regular q

def zeroSeq : RegularSeq := constSeq 0
def oneSeq : RegularSeq := constSeq 1
def halfSeq : RegularSeq := constSeq (COF.half : Scalar)

/-- Negated representative. -/
def negSeq (x : RegularSeq) : RegularSeq where
  val := negVal x.val
  regular := neg_regular x

/-- Sum representative. -/
def addSeq (x y : RegularSeq) : RegularSeq where
  val := addVal x.val y.val
  regular := add_regular x y

/-- Difference representative. -/
def subSeq (x y : RegularSeq) : RegularSeq where
  val := subVal x.val y.val
  regular := sub_regular x y

/-- Absolute-value representative. -/
def absSeq (x : RegularSeq) : RegularSeq where
  val := absVal x.val
  regular := abs_regular x

/-- Negation respects eventual equality. -/
theorem negSeq_respects_eventually (x y : RegularSeq) (hxy : relEventually x y) :
    relEventually (negSeq x) (negSeq y) := by
  intro k
  rcases hxy k with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  unfold negSeq negVal
  rw [show -x.val n - -y.val n = -(x.val n - y.val n) from by ring]
  change Le (BishopCRat.CRat.absF (-(x.val n - y.val n))) (eps k)
  rw [scalarCOFOSeed.abs_neg (x.val n - y.val n)]
  exact h

/-- Addition respects eventual equality. -/
theorem addSeq_respects_eventually (x x' y y' : RegularSeq)
    (hxx : relEventually x x') (hyy : relEventually y y') :
    relEventually (addSeq x y) (addSeq x' y') := by
  intro k
  rcases hxx (k + 1) with ⟨Nx, hNx⟩
  rcases hyy (k + 1) with ⟨Ny, hNy⟩
  refine ⟨Nx + Ny, ?_⟩
  intro n hn
  have hnx : Nx ≤ n + 1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) hn) (Nat.le_succ n)
  have hny : Ny ≤ n + 1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) hn) (Nat.le_succ n)
  unfold addSeq addVal addIndex
  have htri : Le
      (COF.abs ((x.val (n + 1) + y.val (n + 1)) - (x'.val (n + 1) + y'.val (n + 1))))
      (COF.abs (x.val (n + 1) - x'.val (n + 1))
        + COF.abs (y.val (n + 1) - y'.val (n + 1))) := by
    have h := scalar_abs_add_le
      (x.val (n + 1) - x'.val (n + 1))
      (y.val (n + 1) - y'.val (n + 1))
    rwa [show (x.val (n + 1) - x'.val (n + 1))
        + (y.val (n + 1) - y'.val (n + 1))
        = (x.val (n + 1) + y.val (n + 1)) - (x'.val (n + 1) + y'.val (n + 1))
        from by ring] at h
  have hsum := BishopC.le_add (hNx (n + 1) hnx) (hNy (n + 1) hny)
  have hbudget : Le
      (COF.abs (x.val (n + 1) - x'.val (n + 1))
        + COF.abs (y.val (n + 1) - y'.val (n + 1))) (eps k) := by
    rwa [eps_succ_add_self k] at hsum
  exact BishopC.le_trans htri hbudget

/-- Subtraction respects eventual equality. -/
theorem subSeq_respects_eventually (x x' y y' : RegularSeq)
    (hxx : relEventually x x') (hyy : relEventually y y') :
    relEventually (subSeq x y) (subSeq x' y') := by
  intro k
  rcases hxx (k + 1) with ⟨Nx, hNx⟩
  rcases hyy (k + 1) with ⟨Ny, hNy⟩
  refine ⟨Nx + Ny, ?_⟩
  intro n hn
  have hnx : Nx ≤ n + 1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) hn) (Nat.le_succ n)
  have hny : Ny ≤ n + 1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) hn) (Nat.le_succ n)
  unfold subSeq subVal addIndex
  have htri : Le
      (COF.abs ((x.val (n + 1) - y.val (n + 1)) - (x'.val (n + 1) - y'.val (n + 1))))
      (COF.abs (x.val (n + 1) - x'.val (n + 1))
        + COF.abs (y.val (n + 1) - y'.val (n + 1))) := by
    have h := scalar_abs_add_le
      (x.val (n + 1) - x'.val (n + 1))
      (-(y.val (n + 1) - y'.val (n + 1)))
    rw [show (x.val (n + 1) - x'.val (n + 1))
        + -(y.val (n + 1) - y'.val (n + 1))
        = (x.val (n + 1) - y.val (n + 1)) - (x'.val (n + 1) - y'.val (n + 1))
        from by ring] at h
    rwa [show COF.abs (-(y.val (n + 1) - y'.val (n + 1)))
        = COF.abs (y.val (n + 1) - y'.val (n + 1)) from by
          exact scalarCOFOSeed.abs_neg (y.val (n + 1) - y'.val (n + 1))] at h
  have hsum := BishopC.le_add (hNx (n + 1) hnx) (hNy (n + 1) hny)
  have hbudget : Le
      (COF.abs (x.val (n + 1) - x'.val (n + 1))
        + COF.abs (y.val (n + 1) - y'.val (n + 1))) (eps k) := by
    rwa [eps_succ_add_self k] at hsum
  exact BishopC.le_trans htri hbudget

/-- Absolute value respects eventual equality. -/
theorem absSeq_respects_eventually (x y : RegularSeq) (hxy : relEventually x y) :
    relEventually (absSeq x) (absSeq y) := by
  intro k
  rcases hxy k with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  unfold absSeq absVal
  exact BishopC.le_trans (scalar_abs_abs_sub_abs_le (x.val n) (y.val n)) (hN n hn)

/-- Audited representation arithmetic seed for eventual equality. -/
structure CRealEventualAdditiveSeed : Type where
  setoid : Setoid RegularSeq
  constSeq : Scalar → RegularSeq
  zeroSeq : RegularSeq
  oneSeq : RegularSeq
  halfSeq : RegularSeq
  negSeq : RegularSeq → RegularSeq
  addSeq : RegularSeq → RegularSeq → RegularSeq
  subSeq : RegularSeq → RegularSeq → RegularSeq
  absSeq : RegularSeq → RegularSeq
  neg_respects : ∀ x y : RegularSeq, relEventually x y → relEventually (negSeq x) (negSeq y)
  add_respects : ∀ x x' y y' : RegularSeq,
    relEventually x x' → relEventually y y' → relEventually (addSeq x y) (addSeq x' y')
  sub_respects : ∀ x x' y y' : RegularSeq,
    relEventually x x' → relEventually y y' → relEventually (subSeq x y) (subSeq x' y')
  abs_respects : ∀ x y : RegularSeq, relEventually x y → relEventually (absSeq x) (absSeq y)

def cRealEventualAdditiveSeed : CRealEventualAdditiveSeed where
  setoid := eventualSetoid
  constSeq := constSeq
  zeroSeq := zeroSeq
  oneSeq := oneSeq
  halfSeq := halfSeq
  negSeq := negSeq
  addSeq := addSeq
  subSeq := subSeq
  absSeq := absSeq
  neg_respects := negSeq_respects_eventually
  add_respects := addSeq_respects_eventually
  sub_respects := subSeq_respects_eventually
  abs_respects := absSeq_respects_eventually

end BishopCReal

