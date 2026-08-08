import Mathdemo.Internal.CRat_iter88

/-!
# Representative closeness calculus for the diagonal frontier

`CRat_iter88` reduced the remaining completeness work to constructing
`CRealRepDiagonalLimitCloseData`.  This file adds the small representative-level
tools needed for that construction:

* weakening a representative close estimate to a coarser dyadic gauge;
* symmetry and a one-step triangle rule for `RepCloseAtGauge`;
* a finite monotone envelope for the Cauchy modulus `cmod`.

No diagonal limit is claimed here.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative closeness at a finer gauge implies closeness at any coarser
gauge. -/
theorem repCloseAtGauge_weaken
    {k l : Nat} {x y : RegularSeq}
    (hkl : k ≤ l) (hclose : RepCloseAtGauge l x y) :
    RepCloseAtGauge k x y := by
  rcases hclose with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact BishopC.le_trans (hN n hn) (eps_le_of_le hkl)

/-- Representative closeness is symmetric. -/
theorem repCloseAtGauge_symm
    {k : Nat} {x y : RegularSeq}
    (hclose : RepCloseAtGauge k x y) :
    RepCloseAtGauge k y x := by
  rcases hclose with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  rw [show y.val n - x.val n = -(x.val n - y.val n) from by ring]
  change Le (BishopCRat.CRat.absF (-(x.val n - y.val n))) (eps k)
  rw [scalarCOFOSeed.abs_neg (x.val n - y.val n)]
  exact h

/-- Two tail-closeness estimates at gauge `k+1` compose to one at gauge `k`. -/
theorem repCloseAtGauge_triangle_succ
    (k : Nat) {x y z : RegularSeq}
    (hxy : RepCloseAtGauge (k + 1) x y)
    (hyz : RepCloseAtGauge (k + 1) y z) :
    RepCloseAtGauge k x z := by
  rcases hxy with ⟨Nxy, hNxy⟩
  rcases hyz with ⟨Nyz, hNyz⟩
  refine ⟨Nxy + Nyz, ?_⟩
  intro n hn
  have hnxy : Nxy ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hnyz : Nyz ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have htri :
      Le (COF.abs (x.val n - z.val n))
        (COF.abs (x.val n - y.val n) + COF.abs (y.val n - z.val n)) := by
    have h := scalar_abs_add_le (x.val n - y.val n) (y.val n - z.val n)
    rwa [show (x.val n - y.val n) + (y.val n - z.val n) = x.val n - z.val n
      from by ring] at h
  have hsum := BishopC.le_add (hNxy n hnxy) (hNyz n hnyz)
  have hbudget :
      Le (COF.abs (x.val n - y.val n) + COF.abs (y.val n - z.val n))
        (eps k) := by
    rwa [eps_succ_add_self k] at hsum
  exact BishopC.le_trans htri hbudget

/-- Finite max envelope of a natural-valued modulus. -/
def natMaxUpTo (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => Nat.max (natMaxUpTo f n) (f (n + 1))

/-- Every entry up to `n` is bounded by the finite max envelope. -/
theorem le_natMaxUpTo_self
    (f : Nat → Nat) {i n : Nat} (hi : i ≤ n) :
    f i ≤ natMaxUpTo f n := by
  induction n with
  | zero =>
      have hi0 : i = 0 := by omega
      simp [natMaxUpTo, hi0]
  | succ n ih =>
      by_cases hin : i ≤ n
      · exact Nat.le_trans (ih hin) (Nat.le_max_left _ _)
      · have his : i = n + 1 := by omega
        rw [his]
        exact Nat.le_max_right (natMaxUpTo f n) (f (n + 1))

/-- Monotone finite envelope of the representative Cauchy modulus. -/
def repCauchyEnvelope {w : Nat → RegularSeq}
    (hc : CRealRepSequenceCauchyData w) (r : Nat) : Nat :=
  natMaxUpTo hc.cmod r

/-- The original Cauchy modulus is bounded by its finite envelope. -/
theorem cmod_le_repCauchyEnvelope
    {w : Nat → RegularSeq}
    (hc : CRealRepSequenceCauchyData w)
    {k r : Nat} (hkr : k ≤ r) :
    hc.cmod k ≤ repCauchyEnvelope hc r :=
  le_natMaxUpTo_self hc.cmod hkr

/-- If two indices are beyond an envelope covering gauge `k`, then the
representatives are close at gauge `k`. -/
theorem repCloseAtGauge_of_envelope_le
    {w : Nat → RegularSeq}
    (hc : CRealRepSequenceCauchyData w)
    {k r m n : Nat}
    (hkr : k ≤ r)
    (hm : repCauchyEnvelope hc r ≤ m)
    (hn : repCauchyEnvelope hc r ≤ n) :
    RepCloseAtGauge k (w m) (w n) :=
  hc.close_eventually k m n
    (Nat.le_trans (cmod_le_repCauchyEnvelope hc hkr) hm)
    (Nat.le_trans (cmod_le_repCauchyEnvelope hc hkr) hn)

/-- Envelope-selected representatives are Cauchy-close whenever both envelopes
cover the requested gauge. -/
theorem repCloseAtGauge_envelope_indices
    {w : Nat → RegularSeq}
    (hc : CRealRepSequenceCauchyData w)
    {k r s : Nat} (hkr : k ≤ r) (hks : k ≤ s) :
    RepCloseAtGauge k
      (w (repCauchyEnvelope hc r))
      (w (repCauchyEnvelope hc s)) :=
  hc.close_eventually k
    (repCauchyEnvelope hc r)
    (repCauchyEnvelope hc s)
    (cmod_le_repCauchyEnvelope hc hkr)
    (cmod_le_repCauchyEnvelope hc hks)

/-- Frontier after closing representative closeness calculus. -/
structure CRealQuotAfterRepCloseCalculusFrontier : Type where
  construct_diagonal_value : Prop
  prove_diagonal_regular : Prop
  prove_diagonal_tail_close : Prop
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterRepCloseCalculusFrontier :
    CRealQuotAfterRepCloseCalculusFrontier where
  construct_diagonal_value := True
  prove_diagonal_regular := True
  prove_diagonal_tail_close := True
  remove_global_rep_witness := True
  remove_decidable_order_fork := True

end BishopCReal

