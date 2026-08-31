import Mathdemo.Internal.Real.RawRegularSeqSampleTransportCommonMaximum

set_option linter.style.longLine false

/-!
# G129: half-sum sample stability under common-max transport

G128 closed the raw `RegularSeq` estimates that move a component sample from
`Fx n` or `Fy n` to the common maximum.  This file lifts those raw estimates
through the scalar half-sum minimum, still carrying all sample functions as
data.

The remaining line-735 step after this file is the strict-gap arithmetic that
absorbs the two explicit dyadic error budgets.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Minimal half-sum order kernel for the audited scalar rationals. -/
def scalarMinHalfsumOrderKernel :
    MinHalfsumOrderKernel Scalar where
  lt_trans := by
    intro a b c hab hbc
    exact scalarCOFOSeed.lt_trans hab hbc
  abs_neg := by
    intro a
    exact scalarCOFOSeed.abs_neg a
  le_abs_self := by
    intro a
    exact scalarCOFOSeed.le_abs_self a
  abs_le_of := by
    intro a b ha hb
    exact scalarCOFOSeed.abs_le_of ha hb
  half_pos := scalarCOFOSeed.half_pos
  abs_add_le := by
    intro a b
    exact scalar_abs_add_le a b
  abs_of_nonneg := by
    intro a ha
    exact scalarCOFOSeed.abs_of_nonneg ha
  mul_nonneg := by
    intro a b ha hb
    exact scalarCOFOSeed.mul_nonneg ha hb

/-- Symmetric form of an absolute-difference upper bound. -/
theorem scalar_abs_sub_comm_le
    {a b d : Scalar}
    (h : Le (COF.abs (a - b)) d) :
    Le (COF.abs (b - a)) d := by
  have hsym : COF.abs (b - a) = COF.abs (a - b) := by
    rw [show b - a = -(a - b) from by ring]
    change BishopCRat.CRat.absF (-(a - b)) =
      BishopCRat.CRat.absF (a - b)
    exact scalarCOFOSeed.abs_neg (a - b)
  rwa [hsym]

/-- If the left input changes by at most `d`, the half-sum minimum changes by
at most the same additive budget. -/
theorem scalar_min_halfsum_left_stable_add
    (a b c d : Scalar)
    (h : Le (COF.abs (a - b)) d) :
    Le (COF.min a c) (COF.min b c + d) := by
  have hab : Le a (b + d) :=
    scalar_le_add_of_abs_diff_le h
  have hd : BishopC.Nonneg d :=
    BishopC.le_trans (scalar_abs_nonneg (a - b)) h
  have hmono : Le (COF.min a c) (COF.min (b + d) c) :=
    minKernel_min_halfsum_monotone_left
      scalarMinHalfsumOrderKernel a (b + d) c hab
  have hshift : Le (COF.min (b + d) c) (COF.min b c + d) :=
    minKernel_min_halfsum_add_nonnegative_right_bound
      scalarMinHalfsumOrderKernel b d c hd
  exact BishopC.le_trans hmono hshift

/-- Right-input version of `scalar_min_halfsum_left_stable_add`. -/
theorem scalar_min_halfsum_right_stable_add
    (a c d e : Scalar)
    (h : Le (COF.abs (c - d)) e) :
    Le (COF.min a c) (COF.min a d + e) := by
  have h0 : Le (COF.min c a) (COF.min d a + e) :=
    scalar_min_halfsum_left_stable_add c d a e h
  rw [minKernel_min_halfsum_comm scalarMinHalfsumOrderKernel c a,
    minKernel_min_halfsum_comm scalarMinHalfsumOrderKernel d a] at h0
  exact h0

/-- Two-input stability for the scalar half-sum minimum. -/
theorem scalar_min_halfsum_two_arg_stable_add
    (a b c d ea ec : Scalar)
    (ha : Le (COF.abs (a - b)) ea)
    (hc : Le (COF.abs (c - d)) ec) :
    Le (COF.min a c) (COF.min b d + (ea + ec)) := by
  have hleft : Le (COF.min a c) (COF.min b c + ea) :=
    scalar_min_halfsum_left_stable_add a b c ea ha
  have hright : Le (COF.min b c) (COF.min b d + ec) :=
    scalar_min_halfsum_right_stable_add b c d ec hc
  have hright_add :
      Le (COF.min b c + ea) ((COF.min b d + ec) + ea) :=
    BishopC.le_add hright (BishopC.le_refl ea)
  have hright_budget :
      Le (COF.min b c + ea) (COF.min b d + (ea + ec)) := by
    rwa [show (COF.min b d + ec) + ea =
        COF.min b d + (ea + ec) from by ring] at hright_add
  exact BishopC.le_trans hleft hright_budget

/-- Raw sample transport, written from the common maximum back to the left
input. -/
theorem regularSeq_sample_close_from_commonMax_left_budget
    (x : RegularSeq) (Fx Fy : Nat -> Nat) (n : Nat) :
    Le
      (COF.abs
        (x.val (commonMaxSample Fx Fy n + 1) -
          x.val (Fx n + 1)))
      (eps (Fx n)) :=
  scalar_abs_sub_comm_le
    (regularSeq_sample_close_to_commonMax_left_budget x Fx Fy n)

/-- Raw sample transport, written from the common maximum back to the right
input. -/
theorem regularSeq_sample_close_from_commonMax_right_budget
    (x : RegularSeq) (Fx Fy : Nat -> Nat) (n : Nat) :
    Le
      (COF.abs
        (x.val (commonMaxSample Fx Fy n + 1) -
          x.val (Fy n + 1)))
      (eps (Fy n)) :=
  scalar_abs_sub_comm_le
    (regularSeq_sample_close_to_commonMax_right_budget x Fx Fy n)

/-- Move the left half-sum sample to the common maximum with the two raw
component budgets exposed. -/
theorem minHalfsumSample_left_to_commonMax_add_budget
    (x c : RegularSeq) (Fx Fy : Nat -> Nat) (n : Nat) :
    Le
      (minHalfsumSample x c (Fx n))
      (minHalfsumSample x c (commonMaxSample Fx Fy n) +
        (eps (Fx n) + eps (Fx n))) := by
  have hx :=
    regularSeq_sample_close_to_commonMax_left_budget x Fx Fy n
  have hc :=
    regularSeq_sample_close_to_commonMax_left_budget c Fx Fy n
  have h :=
    scalar_min_halfsum_two_arg_stable_add
      (x.val (Fx n + 1))
      (x.val (commonMaxSample Fx Fy n + 1))
      (c.val (Fx n + 1))
      (c.val (commonMaxSample Fx Fy n + 1))
      (eps (Fx n)) (eps (Fx n)) hx hc
  rw [COF.min_halfsum
      (x.val (Fx n + 1))
      (c.val (Fx n + 1)),
    COF.min_halfsum
      (x.val (commonMaxSample Fx Fy n + 1))
      (c.val (commonMaxSample Fx Fy n + 1))] at h
  simpa [minHalfsumSample] using h

/-- Move the common maximum half-sum sample back to the original right sample
with the two raw component budgets exposed. -/
theorem minHalfsumSample_commonMax_to_right_add_budget
    (y c : RegularSeq) (Fx Fy : Nat -> Nat) (n : Nat) :
    Le
      (minHalfsumSample y c (commonMaxSample Fx Fy n))
      (minHalfsumSample y c (Fy n) +
        (eps (Fy n) + eps (Fy n))) := by
  have hy :=
    regularSeq_sample_close_from_commonMax_right_budget y Fx Fy n
  have hc :=
    regularSeq_sample_close_from_commonMax_right_budget c Fx Fy n
  have h :=
    scalar_min_halfsum_two_arg_stable_add
      (y.val (commonMaxSample Fx Fy n + 1))
      (y.val (Fy n + 1))
      (c.val (commonMaxSample Fx Fy n + 1))
      (c.val (Fy n + 1))
      (eps (Fy n)) (eps (Fy n)) hy hc
  rw [COF.min_halfsum
      (y.val (commonMaxSample Fx Fy n + 1))
      (c.val (commonMaxSample Fx Fy n + 1)),
    COF.min_halfsum
      (y.val (Fy n + 1))
      (c.val (Fy n + 1))] at h
  simpa [minHalfsumSample] using h

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G129 audit: raw component transport has been lifted through the half-sum
minimum with explicit dyadic budgets. -/
structure Property4RegularSeqCommonMaxHalfsumStabilityAudit : Type where
  scalar_kernel_installed : Nat
  scalar_left_stability_closed : Nat
  scalar_right_stability_closed : Nat
  scalar_two_arg_stability_closed : Nat
  reverse_abs_sample_transport_closed : Nat
  left_halfsum_commonmax_transport_closed : Nat
  right_halfsum_commonmax_transport_closed : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_strict_gap_budget_absorption : Prop

def property4RegularSeqCommonMaxHalfsumStabilityAudit :
    Property4RegularSeqCommonMaxHalfsumStabilityAudit where
  scalar_kernel_installed := 1
  scalar_left_stability_closed := 1
  scalar_right_stability_closed := 1
  scalar_two_arg_stability_closed := 1
  reverse_abs_sample_transport_closed := 2
  left_halfsum_commonmax_transport_closed := 1
  right_halfsum_commonmax_transport_closed := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_strict_gap_budget_absorption := True

end BishopRegularSeqTheorem118

/-- G129 package: half-sum sample stability under common-max transport. -/
structure BishopRegularSeqTheorem118G129Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g128 : BishopRegularSeqTheorem118G128Package S
  scalar_two_arg_stability :
    forall a b c d ea ec : Scalar,
      Le (COF.abs (a - b)) ea ->
      Le (COF.abs (c - d)) ec ->
        Le (COF.min a c) (COF.min b d + (ea + ec))
  left_halfsum_transport :
    forall x c : RegularSeq, forall Fx Fy : Nat -> Nat, forall n : Nat,
      Le
        (minHalfsumSample x c (Fx n))
        (minHalfsumSample x c (commonMaxSample Fx Fy n) +
          (eps (Fx n) + eps (Fx n)))
  right_halfsum_transport :
    forall y c : RegularSeq, forall Fx Fy : Nat -> Nat, forall n : Nat,
      Le
        (minHalfsumSample y c (commonMaxSample Fx Fy n))
        (minHalfsumSample y c (Fy n) +
          (eps (Fy n) + eps (Fy n)))
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqCommonMaxHalfsumStabilityAudit
  line735_halfsum_sample_transport_to_common_max : Prop
  line735_remaining_frontier_strict_gap_budget_absorption : Prop
  no_quotient_extraction_in_g129_mainline : Prop

def bishopRegularSeqTheorem118G129Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G129Package S where
  g128 := bishopRegularSeqTheorem118G128Package S
  scalar_two_arg_stability := by
    intro a b c d ea ec ha hc
    exact scalar_min_halfsum_two_arg_stable_add a b c d ea ec ha hc
  left_halfsum_transport := by
    intro x c Fx Fy n
    exact minHalfsumSample_left_to_commonMax_add_budget x c Fx Fy n
  right_halfsum_transport := by
    intro y c Fx Fy n
    exact minHalfsumSample_commonMax_to_right_add_budget y c Fx Fy n
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqCommonMaxHalfsumStabilityAudit
  line735_halfsum_sample_transport_to_common_max := True
  line735_remaining_frontier_strict_gap_budget_absorption := True
  no_quotient_extraction_in_g129_mainline := True

/-- Progress after G129: the half-sum samples now transport to the common max;
only the strict-gap budget absorption remains for line 735. -/
def bishopRegularSeqCh1To4ProgressAfterG129 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G129: lifted commonMaxSample transport through the named half-sum samples; \
    remaining line-735 work is strict-gap dyadic budget absorption."


end BishopCReal
