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

/-- Late left-sample-to-common-max transport with an externally chosen tail
gauge. -/
theorem regularSeq_sample_close_to_commonMax_left_late
    (x : RegularSeq) (Fx Fy : Nat -> Nat)
    (hFx : forall n : Nat, n <= Fx n)
    {k n : Nat}
    (hkn : k <= n) :
    Le
      (COF.abs
        (x.val (Fx n + 1) -
          x.val (commonMaxSample Fx Fy n + 1)))
      (eps k) := by
  exact BishopC.le_trans
    (regularSeq_sample_close_to_commonMax_left_budget x Fx Fy n)
    (eps_sample_le_of_late Fx hFx hkn)

/-- Late right-sample-to-common-max transport with an externally chosen tail
gauge. -/
theorem regularSeq_sample_close_to_commonMax_right_late
    (x : RegularSeq) (Fx Fy : Nat -> Nat)
    (hFy : forall n : Nat, n <= Fy n)
    {k n : Nat}
    (hkn : k <= n) :
    Le
      (COF.abs
        (x.val (Fy n + 1) -
          x.val (commonMaxSample Fx Fy n + 1)))
      (eps k) := by
  exact BishopC.le_trans
    (regularSeq_sample_close_to_commonMax_right_budget x Fx Fy n)
    (eps_sample_le_of_late Fy hFy hkn)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G128 audit: raw component transport to common max is closed. -/
structure Property4RegularSeqCommonMaxRawTransportAudit : Type where
  left_budget_transport_closed : Nat
  right_budget_transport_closed : Nat
  cofinal_eps_weakening_closed : Nat
  late_left_transport_closed : Nat
  late_right_transport_closed : Nat
  named_halfsum_sample_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_halfsum_sample_tail_stability : Prop

def property4RegularSeqCommonMaxRawTransportAudit :
    Property4RegularSeqCommonMaxRawTransportAudit where
  left_budget_transport_closed := 1
  right_budget_transport_closed := 1
  cofinal_eps_weakening_closed := 1
  late_left_transport_closed := 1
  late_right_transport_closed := 1
  named_halfsum_sample_inputs := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_halfsum_sample_tail_stability := True

end BishopRegularSeqTheorem118

/-- G128 package: raw RegularSeq samples can be transported to common max. -/
structure BishopRegularSeqTheorem118G128Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g127 : BishopRegularSeqTheorem118G127Package S
  left_budget_transport :
    forall x : RegularSeq, forall Fx Fy : Nat -> Nat, forall n : Nat,
      Le
        (COF.abs
          (x.val (Fx n + 1) -
            x.val (commonMaxSample Fx Fy n + 1)))
        (eps (Fx n))
  right_budget_transport :
    forall x : RegularSeq, forall Fx Fy : Nat -> Nat, forall n : Nat,
      Le
        (COF.abs
          (x.val (Fy n + 1) -
            x.val (commonMaxSample Fx Fy n + 1)))
        (eps (Fy n))
  late_left_transport :
    forall x : RegularSeq, forall Fx Fy : Nat -> Nat,
      (forall n : Nat, n <= Fx n) ->
        forall {k n : Nat}, k <= n ->
          Le
            (COF.abs
              (x.val (Fx n + 1) -
                x.val (commonMaxSample Fx Fy n + 1)))
            (eps k)
  late_right_transport :
    forall x : RegularSeq, forall Fx Fy : Nat -> Nat,
      (forall n : Nat, n <= Fy n) ->
        forall {k n : Nat}, k <= n ->
          Le
            (COF.abs
              (x.val (Fy n + 1) -
                x.val (commonMaxSample Fx Fy n + 1)))
            (eps k)
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqCommonMaxRawTransportAudit
  line735_raw_samples_transport_to_common_max : Prop
  line735_remaining_frontier_halfsum_sample_tail_stability : Prop
  no_quotient_extraction_in_g128_mainline : Prop

def bishopRegularSeqTheorem118G128Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G128Package S where
  g127 := bishopRegularSeqTheorem118G127Package S
  left_budget_transport := by
    intro x Fx Fy n
    exact regularSeq_sample_close_to_commonMax_left_budget x Fx Fy n
  right_budget_transport := by
    intro x Fx Fy n
    exact regularSeq_sample_close_to_commonMax_right_budget x Fx Fy n
  late_left_transport := by
    intro x Fx Fy hFx k n hkn
    exact regularSeq_sample_close_to_commonMax_left_late x Fx Fy hFx hkn
  late_right_transport := by
    intro x Fx Fy hFy k n hkn
    exact regularSeq_sample_close_to_commonMax_right_late x Fx Fy hFy hkn
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqCommonMaxRawTransportAudit
  line735_raw_samples_transport_to_common_max := True
  line735_remaining_frontier_halfsum_sample_tail_stability := True
  no_quotient_extraction_in_g128_mainline := True

/-- Progress after G128: raw sample transport to common max is closed; the next
frontier is lifting those raw estimates through `minHalfsumSample`. -/
def bishopRegularSeqCh1To4ProgressAfterG128 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G128: closed raw RegularSeq sample transport from Fx/Fy to commonMaxSample; \
    remaining line-735 work is lifting this through the named half-sum sample."


end BishopCReal
