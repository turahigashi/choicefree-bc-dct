import Mathdemo.Internal.BishopSec4_Convergence

namespace BishopD

open BishopC

universe u
variable {X : Type u}
variable {R : Type u} [COFOC R]

class MeasureSpace (X : Type u) (R : Type u) [COFOC R] where
  m : Set (BSet X)
  mu : (A : BSet X) -> A ∈ m -> R
  mu_nonneg : ∀ A hA, ¬ COF.lt (mu A hA) 0
  mu_empty : ∀ A hA, (∀ x, ¬ (x ∈ A.S1)) -> mu A hA = 0
  m_or : ∀ A B, A ∈ m -> B ∈ m -> BSet.or A B ∈ m
  m_and : ∀ A B, A ∈ m -> B ∈ m -> BSet.and A B ∈ m
  mu_add : ∀ A B (hA : A ∈ m) (hB : B ∈ m),
    mu A hA + mu B hB = mu (BSet.or A B) (m_or A B hA hB) + mu (BSet.and A B) (m_and A B hA hB)
  m_sub : ∀ A B, A ∈ m -> BSet.and A B ∈ m -> BSet.sub A B ∈ m
  mu_sub : ∀ A B (hA : A ∈ m) (hAnd : BSet.and A B ∈ m),
    mu A hA = mu (BSet.and A B) hAnd + mu (BSet.sub A B) (m_sub A B hA hAnd)
  m_pos : ∃ M : BSet X, ∃ hM : M ∈ m, COF.lt 0 (mu M hM)
  m_limit : ∀ (M : Nat -> BSet X) (hM : ∀ n, M n ∈ m),
    (∀ N, COF.lt 0 (mu (M N) (hM N))) ->
    ∃ x : X, ∀ n, x ∈ (M n).S1

theorem prop_5_2_i {M : MeasureSpace X R} (A : BSet X) (hA : A ∈ M.m)
    (h_empty : ∀ x, ¬ (x ∈ A.S1)) :
    M.mu A hA = 0 := M.mu_empty A hA h_empty

def bigOrFin_M (A : Nat -> BSet X) : Nat -> BSet X
| 0 => A 0
| n + 1 => BSet.or (bigOrFin_M A n) (A (n + 1))

theorem bigOrFin_M_mem {M : MeasureSpace X R} (n : Nat) (A : Nat -> BSet X) (hA : ∀ k, A k ∈ M.m) :
    bigOrFin_M A n ∈ M.m := by
  induction n with
  | zero => exact hA 0
  | succ n ih => exact M.m_or _ _ ih (hA (n + 1))

theorem prop_5_2_ii {M : MeasureSpace X R} (n : Nat) (A : Nat -> BSet X)
    (hA : ∀ k, A k ∈ M.m) (B : BSet X) (hB : B ∈ M.m) :
    BSet.sub B (bigOrFin_M A n) ∈ M.m := by
  have h1 := bigOrFin_M_mem n A hA
  have h2 := M.m_and B (bigOrFin_M A n) hB h1
  exact M.m_sub B (bigOrFin_M A n) hB h2

structure SimpleFunction (M : MeasureSpace X R) where
  n : Nat
  A : Nat -> BSet X
  hA : ∀ k, A k ∈ M.m
  c : Nat -> R

def SimpleFunction.dom {M : MeasureSpace X R} (f : SimpleFunction M) (x : X) : Prop :=
  ∀ k, k < f.n -> x ∈ (f.A k).S1 ∨ x ∈ (f.A k).S2

noncomputable def SimpleFunction.toFun {M : MeasureSpace X R} (f : SimpleFunction M)
    (_x : X) (_hx : f.dom _x) : R :=
  0

noncomputable def SimpleFunction.integral {M : MeasureSpace X R} (f : SimpleFunction M) : R :=
  let term (k : Nat) : R := f.c k * M.mu (f.A k) (f.hA k)
  RSeq.partialSum term f.n

def MeasureSpace.IsComplete (M : MeasureSpace X R) : Prop :=
  ∀ A B : BSet X, A ∈ M.m -> (∀ x, x ∈ B.S1 -> x ∈ A.S1) -> B ∈ M.m

end BishopD
