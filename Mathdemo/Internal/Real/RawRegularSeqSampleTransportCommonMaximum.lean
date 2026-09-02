import Mathdemo.Internal.Real.NamingCommonMaxHalfSumSample

set_option linter.style.longLine false

/-!
# G128: raw RegularSeq sample transport to the common maximum

G127 named the scalar half-sum sample.  The next constructive ingredient is
the raw regularity estimate needed when a sample index is replaced by the
common maximum `max (Fx n) (Fy n)`.

This file closes that raw transport for any `RegularSeq`.  The remaining work
is to lift these component estimates through the named half-sum minimum and
then through the strict-gap arithmetic.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Transport a raw sample from the left input index to the common maximum.
The budget is the original left sample gauge. -/
theorem regularSeq_sample_close_to_commonMax_left_budget
    (x : RegularSeq) (Fx Fy : Nat -> Nat) (n : Nat) :
    Le
      (COF.abs
        (x.val (Fx n + 1) -
          x.val (commonMaxSample Fx Fy n + 1)))
      (eps (Fx n)) := by
  have hbase :
      Le
        (COF.abs
          (x.val (Fx n + 1) -
            x.val (commonMaxSample Fx Fy n + 1)))
        (eps (Fx n + 1) + eps (commonMaxSample Fx Fy n + 1)) :=
    regularSeq_sample_close x (Fx n) (commonMaxSample Fx Fy n)
  have hJ :
      Fx n + 1 <= commonMaxSample Fx Fy n + 1 :=
    Nat.succ_le_succ (le_commonMaxSample_left Fx Fy n)
  have hright :
      Le (eps (commonMaxSample Fx Fy n + 1)) (eps (Fx n + 1)) :=
    eps_le_of_le hJ
  have hsum :
      Le
        (eps (Fx n + 1) + eps (commonMaxSample Fx Fy n + 1))
        (eps (Fx n + 1) + eps (Fx n + 1)) :=
    BishopC.le_add (BishopC.le_refl (eps (Fx n + 1))) hright
  have hbudget :
      Le
        (eps (Fx n + 1) + eps (commonMaxSample Fx Fy n + 1))
        (eps (Fx n)) := by
    rwa [eps_succ_add_self (Fx n)] at hsum
  exact BishopC.le_trans hbase hbudget

/-- Transport a raw sample from the right input index to the common maximum.
The budget is the original right sample gauge. -/
theorem regularSeq_sample_close_to_commonMax_right_budget
    (x : RegularSeq) (Fx Fy : Nat -> Nat) (n : Nat) :
    Le
      (COF.abs
        (x.val (Fy n + 1) -
          x.val (commonMaxSample Fx Fy n + 1)))
      (eps (Fy n)) := by
  have hbase :
      Le
        (COF.abs
          (x.val (Fy n + 1) -
            x.val (commonMaxSample Fx Fy n + 1)))
        (eps (Fy n + 1) + eps (commonMaxSample Fx Fy n + 1)) :=
    regularSeq_sample_close x (Fy n) (commonMaxSample Fx Fy n)
  have hJ :
      Fy n + 1 <= commonMaxSample Fx Fy n + 1 :=
    Nat.succ_le_succ (le_commonMaxSample_right Fx Fy n)
  have hright :
      Le (eps (commonMaxSample Fx Fy n + 1)) (eps (Fy n + 1)) :=
    eps_le_of_le hJ
  have hsum :
      Le
        (eps (Fy n + 1) + eps (commonMaxSample Fx Fy n + 1))
        (eps (Fy n + 1) + eps (Fy n + 1)) :=
    BishopC.le_add (BishopC.le_refl (eps (Fy n + 1))) hright
  have hbudget :
      Le
        (eps (Fy n + 1) + eps (commonMaxSample Fx Fy n + 1))
        (eps (Fy n)) := by
    rwa [eps_succ_add_self (Fy n)] at hsum
  exact BishopC.le_trans hbase hbudget

/-- Cofinality weakens the sampled dyadic gauge back to any earlier tail
gauge. -/
theorem eps_sample_le_of_late
    (F : Nat -> Nat)
    (hF : forall n : Nat, n <= F n)
    {k n : Nat}
    (hkn : k <= n) :
    Le (eps (F n)) (eps k) :=
  eps_le_of_le (Nat.le_trans hkn (hF n))



namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}



end BishopRegularSeqTheorem118





end BishopCReal
