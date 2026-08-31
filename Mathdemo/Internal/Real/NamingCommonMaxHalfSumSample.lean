import Mathdemo.Internal.Real.FixingAlignmentSampleCommonMaximum

set_option linter.style.longLine false

/-!
# G127: naming the common-max half-sum sample values

G126 fixed the remaining line-735 alignment sample to the computable common
maximum `fun n => max (Fx n) (Fy n)`.

This file prepares the actual regularity transport by naming the scalar
half-sum sample value and exposing the exact folds for the two-sample and
same-sample strictness statements.  No representative is extracted from a
quotient and no positivity witness is selected from a proposition.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Scalar half-sum expression for `min z c` at the raw sample `j`.  The
definition uses `j + 1`, matching the existing `subSeq`-based strictness
interfaces. -/
def minHalfsumSample (z c : RegularSeq) (j : Nat) : Scalar :=
  (COF.half : Scalar) *
    (z.val (j + 1) + c.val (j + 1) -
      COF.abs (z.val (j + 1) - c.val (j + 1)))

/-- Exact fold for the two-sample strictness statement. -/
theorem twoSampleMinHalfsumLeftStrict_iff_named
    (x y c : RegularSeq) (Fx Fy : Nat -> Nat) :
    TwoSampleMinHalfsumLeftStrict x y c Fx Fy ↔
      ∃ k N : Nat,
        ∀ n : Nat, N <= n ->
          COF.lt (eps k)
            (minHalfsumSample x c (Fx n) -
              minHalfsumSample y c (Fy n)) := by
  rfl

/-- Exact fold for the same-sample strictness statement. -/
theorem sameSampleMinHalfsumLeftStrict_iff_named
    (x y c : RegularSeq) (F : Nat -> Nat) :
    SameSampleMinHalfsumLeftStrict x y c F ↔
      ∃ k N : Nat,
        ∀ n : Nat, N <= n ->
          COF.lt (eps k)
            (minHalfsumSample x c (F n) -
              minHalfsumSample y c (F n)) := by
  rfl

/-- Exact value expansion of `minSeqWith`, folded through
`minHalfsumSample`. -/
theorem minSeqWith_val_eq_minHalfsumSample
    (A : ScalarMulArchimedeanData)
    (x c : RegularSeq) (n : Nat) :
    (minSeqWith A x c).val n =
      minHalfsumSample x c (minSeqWithSampleIndex A x c n + 1) := by
  rw [minSeqWith_val_eq_halfsum_sample A x c n]
  rfl

/-- Left input sample is contained in the common maximum. -/
theorem le_commonMaxSample_left
    (Fx Fy : Nat -> Nat) (n : Nat) :
    Fx n <= commonMaxSample Fx Fy n := by
  exact Nat.le_max_left (Fx n) (Fy n)

/-- Right input sample is contained in the common maximum. -/
theorem le_commonMaxSample_right
    (Fx Fy : Nat -> Nat) (n : Nat) :
    Fy n <= commonMaxSample Fx Fy n := by
  exact Nat.le_max_right (Fx n) (Fy n)

/-- Raw regularity estimate between two samples of a regular representative.
The later common-max proof will combine this with dyadic budget weakening. -/
theorem regularSeq_sample_close
    (x : RegularSeq) (i j : Nat) :
    Le (COF.abs (x.val (i + 1) - x.val (j + 1)))
      (eps (i + 1) + eps (j + 1)) := by
  exact x.regular (i + 1) (j + 1)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G127 audit: the scalar sample values are now named and the common maximum's
left/right containment facts are exposed. -/
structure Property4RegularSeqCommonMaxNamedSampleAudit : Type where
  named_halfsum_sample_defs : Nat
  two_sample_named_folds : Nat
  same_sample_named_folds : Nat
  minSeqWith_named_value_expansion : Nat
  common_max_left_right_bounds : Nat
  raw_regular_sample_close_inputs : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_named_sample_tail_stability : Prop

def property4RegularSeqCommonMaxNamedSampleAudit :
    Property4RegularSeqCommonMaxNamedSampleAudit where
  named_halfsum_sample_defs := 1
  two_sample_named_folds := 1
  same_sample_named_folds := 1
  minSeqWith_named_value_expansion := 1
  common_max_left_right_bounds := 2
  raw_regular_sample_close_inputs := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_named_sample_tail_stability := True

end BishopRegularSeqTheorem118

/-- G127 package: named half-sum samples for the common-max transport proof. -/
structure BishopRegularSeqTheorem118G127Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g126 : BishopRegularSeqTheorem118G126Package S
  two_sample_named :
    forall x y c : RegularSeq, forall Fx Fy : Nat -> Nat,
      TwoSampleMinHalfsumLeftStrict x y c Fx Fy ↔
        ∃ k N : Nat,
          ∀ n : Nat, N <= n ->
            COF.lt (eps k)
              (minHalfsumSample x c (Fx n) -
                minHalfsumSample y c (Fy n))
  same_sample_named :
    forall x y c : RegularSeq, forall F : Nat -> Nat,
      SameSampleMinHalfsumLeftStrict x y c F ↔
        ∃ k N : Nat,
          ∀ n : Nat, N <= n ->
            COF.lt (eps k)
              (minHalfsumSample x c (F n) -
                minHalfsumSample y c (F n))
  minSeqWith_named_value :
    forall x c : RegularSeq, forall n : Nat,
      (minSeqWith Arch x c).val n =
        minHalfsumSample x c (minSeqWithSampleIndex Arch x c n + 1)
  common_max_left :
    forall Fx Fy : Nat -> Nat, forall n : Nat,
      Fx n <= commonMaxSample Fx Fy n
  common_max_right :
    forall Fx Fy : Nat -> Nat, forall n : Nat,
      Fy n <= commonMaxSample Fx Fy n
  regular_sample_close :
    forall x : RegularSeq, forall i j : Nat,
      Le (COF.abs (x.val (i + 1) - x.val (j + 1)))
        (eps (i + 1) + eps (j + 1))
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqCommonMaxNamedSampleAudit
  line735_sample_values_are_named : Prop
  line735_remaining_frontier_named_sample_tail_stability : Prop
  no_quotient_extraction_in_g127_mainline : Prop

def bishopRegularSeqTheorem118G127Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G127Package S where
  g126 := bishopRegularSeqTheorem118G126Package S
  two_sample_named := by
    intro x y c Fx Fy
    exact twoSampleMinHalfsumLeftStrict_iff_named x y c Fx Fy
  same_sample_named := by
    intro x y c F
    exact sameSampleMinHalfsumLeftStrict_iff_named x y c F
  minSeqWith_named_value := by
    intro x c n
    exact minSeqWith_val_eq_minHalfsumSample Arch x c n
  common_max_left := by
    intro Fx Fy n
    exact le_commonMaxSample_left Fx Fy n
  common_max_right := by
    intro Fx Fy n
    exact le_commonMaxSample_right Fx Fy n
  regular_sample_close := by
    intro x i j
    exact regularSeq_sample_close x i j
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqCommonMaxNamedSampleAudit
  line735_sample_values_are_named := True
  line735_remaining_frontier_named_sample_tail_stability := True
  no_quotient_extraction_in_g127_mainline := True

/-- Progress after G127: still 99%; the sample values and common-max bounds are
named, leaving tail-stability of the named sample as the next frontier. -/
def bishopRegularSeqCh1To4ProgressAfterG127 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G127: named the scalar half-sum sample and exposed commonMaxSample left/right \
    bounds; remaining line-735 work is named-sample tail-stability."


end BishopCReal
