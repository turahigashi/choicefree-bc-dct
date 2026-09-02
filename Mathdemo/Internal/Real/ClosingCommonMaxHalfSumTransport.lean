import Mathdemo.Internal.Real.HalfSumSampleStabilityCommonMax

set_option linter.style.longLine false

/-!
# G130: closing common-max half-sum transport

G129 transported the two half-sum samples to the common maximum with explicit
dyadic error budgets.  This file absorbs those budgets into one finer dyadic
strict gap and closes `CommonMaxMinHalfsumTransport`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Negation reverses the constructive non-strict scalar order. -/
theorem scalar_neg_le_neg
    {a b : Scalar}
    (h : Le a b) :
    Le (-b) (-a) := by
  intro hbad
  have t := COF.lt_add_left (a + b) hbad
  have t' : COF.lt b a := by
    simpa [show (a + b) + -a = b from by ring,
      show (a + b) + -b = a from by ring] using t
  exact h t'

/-- Lower-bound the transported strict gap after two one-sided additive
transport estimates. -/
theorem scalar_gap_lower_of_le_add
    {A A' B B' ex ey : Scalar}
    (hA : Le A (A' + ex))
    (hB : Le B' (B + ey)) :
    Le ((A - B) - (ex + ey)) (A' - B') := by
  have hA' : Le (A - ex) A' := by
    have hsub := BishopC.le_sub_right (c := ex) hA
    rwa [show A' + ex - ex = A' from by ring] at hsub
  have hB' : Le (-(B + ey)) (-B') :=
    scalar_neg_le_neg hB
  have hsum : Le ((A - ex) + (-(B + ey))) (A' + (-B')) :=
    BishopC.le_add hA' hB'
  rwa [show (A - ex) + (-(B + ey)) = (A - B) - (ex + ey) from by ring,
    show A' + (-B') = A' - B' from by ring] at hsum

/-- If an error budget can be added to a finer positive gauge while staying
below the previous gauge, a strict previous gap gives a strict budget-subtracted gap. -/
theorem scalar_strict_sub_budget_of_sum_le
    {e previous gap err : Scalar}
    (hsum : Le (e + err) previous)
    (hgap : COF.lt previous gap) :
    COF.lt e (gap - err) := by
  have hpre : COF.lt (e + err) gap :=
    scalar_lt_of_le_of_lt hsum hgap
  have hshift := COF.lt_add_left (-err) hpre
  rwa [show -err + (e + err) = e from by ring,
    show -err + gap = gap - err from by ring] at hshift

/-- Strict-gap transport across the two half-sum common-max error estimates. -/
theorem scalar_strict_gap_transport_of_le_add
    {A A' B B' ex ey : Scalar} {k : Nat}
    (hA : Le A (A' + ex))
    (hB : Le B' (B + ey))
    (herr : Le (ex + ey) (eps (k + 1)))
    (hstrict : COF.lt (eps k) (A - B)) :
    COF.lt (eps (k + 1)) (A' - B') := by
  have hsum0 :
      Le (eps (k + 1) + (ex + ey))
        (eps (k + 1) + eps (k + 1)) :=
    BishopC.le_add (BishopC.le_refl (eps (k + 1))) herr
  have hsum : Le (eps (k + 1) + (ex + ey)) (eps k) := by
    rwa [eps_succ_add_self k] at hsum0
  have hsub :
      COF.lt (eps (k + 1)) ((A - B) - (ex + ey)) :=
    scalar_strict_sub_budget_of_sum_le hsum hstrict
  exact BishopC.lt_of_lt_of_le hsub
    (scalar_gap_lower_of_le_add hA hB)

/-- The two explicit half-sum transport budgets are eventually absorbed by one
finer dyadic gauge. -/
theorem commonMax_halfsum_error_budget
    (Fx Fy : Nat -> Nat)
    (hFx : forall n : Nat, n <= Fx n)
    (hFy : forall n : Nat, n <= Fy n)
    {k n : Nat}
    (hkn : k + 3 <= n) :
    Le
      ((eps (Fx n) + eps (Fx n)) +
        (eps (Fy n) + eps (Fy n)))
      (eps (k + 1)) := by
  have hx : Le (eps (Fx n)) (eps (k + 3)) :=
    eps_sample_le_of_late Fx hFx hkn
  have hy : Le (eps (Fy n)) (eps (k + 3)) :=
    eps_sample_le_of_late Fy hFy hkn
  have hxx0 :
      Le (eps (Fx n) + eps (Fx n))
        (eps (k + 3) + eps (k + 3)) :=
    BishopC.le_add hx hx
  have hyy0 :
      Le (eps (Fy n) + eps (Fy n))
        (eps (k + 3) + eps (k + 3)) :=
    BishopC.le_add hy hy
  have hxx : Le (eps (Fx n) + eps (Fx n)) (eps (k + 2)) := by
    rwa [eps_succ_add_self (k + 2)] at hxx0
  have hyy : Le (eps (Fy n) + eps (Fy n)) (eps (k + 2)) := by
    rwa [eps_succ_add_self (k + 2)] at hyy0
  have hsum0 :
      Le
        ((eps (Fx n) + eps (Fx n)) +
          (eps (Fy n) + eps (Fy n)))
        (eps (k + 2) + eps (k + 2)) :=
    BishopC.le_add hxx hyy
  rwa [eps_succ_add_self (k + 1)] at hsum0

/-- The constructive common-max transport theorem for the two-sample half-sum
strict statement. -/
theorem commonMaxMinHalfsumTransport_closed
    (x y c : RegularSeq) :
    CommonMaxMinHalfsumTransport x y c := by
  intro Fx Fy hFx hFy htwo
  rcases htwo with ⟨k, N, hN⟩
  refine ⟨k + 1, N + (k + 3), ?_⟩
  intro n hn
  have hNn : N <= n := Nat.le_trans (Nat.le_add_right N (k + 3)) hn
  have hkn : k + 3 <= n := Nat.le_trans (Nat.le_add_left (k + 3) N) hn
  have hstrict := hN n hNn
  have hA :=
    minHalfsumSample_left_to_commonMax_add_budget x c Fx Fy n
  have hB :=
    minHalfsumSample_commonMax_to_right_add_budget y c Fx Fy n
  have herr :=
    commonMax_halfsum_error_budget Fx Fy hFx hFy hkn
  exact scalar_strict_gap_transport_of_le_add hA hB herr hstrict

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}




end BishopRegularSeqTheorem118





end BishopCReal
