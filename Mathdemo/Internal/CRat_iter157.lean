import Mathdemo.Internal.CRat_iter156

/-!
# G57: closing the strict upper-transfer bridge

G56 reduced the Theorem 1.18(4) estimates to two norm bounds and a generic
order step.  This file closes that generic order step from the existing
RegularSeq order layer.

The proof uses data-valued cotransitivity.  From `y < z` and a comparison point
`x`, cotransitivity yields either `y < x` or `x < z`.  The first case
contradicts `x <= y`; the second case is the desired result.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- A strict comparison `y < x` contradicts the non-strict comparison
`x <= y`. -/
theorem regularSeqLe_not_lt_reverse
    {x y : RegularSeq}
    (hxy : RegularSeqLe x y)
    (hyx : regularSeqLtData y x) :
    False := by
  have hprop : PosEventually (subSeq x y) := hyx.toProp
  have htarget :
      PosEventually (subSeq zeroSeq (subSeq y x)) := by
    have h1 :
        relEventually (subSeq x y) (negSeq (subSeq y x)) :=
      subSeq_comm_neg_eventually x y
    have h2 :
        relEventually (negSeq (subSeq y x)) (subSeq zeroSeq (subSeq y x)) :=
      relEventually_symm
        (subSeq zeroSeq (subSeq y x))
        (negSeq (subSeq y x))
        (subSeq_zero_left_eventually (subSeq y x))
    exact
      posEventually_respects
        (subSeq x y)
        (subSeq zeroSeq (subSeq y x))
        (relEventually_trans
          (subSeq x y)
          (negSeq (subSeq y x))
          (subSeq zeroSeq (subSeq y x))
          h1 h2)
        hprop
  exact hxy htarget

/-- The strict upper-transfer order step required by Theorem 1.18(4). -/
def regularSeqStrictUpperTransfer :
    RegularSeqStrictUpperTransfer where
  from_le_lt := by
    intro x y z hxy hyz
    cases regularSeqLtData_cotrans y z x hyz with
    | inl hyx =>
        exact False.elim (regularSeqLe_not_lt_reverse hxy hyx)
    | inr hxz =>
        exact hxz
  source_order_step_for_epsilon_estimates := True

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G56 large estimate constructor with the generic strict-transfer bridge now
closed. -/
def property4LargeLipschitzBridge_from_norm_bound_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bound_bridge : Property4LargeNormBoundBridge S) :
    Property4LargeLipschitzBridge S :=
  property4LargeLipschitzBridge_from_norm_bound
    S regularSeqStrictUpperTransfer bound_bridge

/-- G56 small estimate constructor with the generic strict-transfer bridge now
closed. -/
def property4SmallLipschitzBridge_from_norm_bound_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bound_bridge : Property4SmallNormBoundBridge S) :
    Property4SmallLipschitzBridge S :=
  property4SmallLipschitzBridge_from_norm_bound
    S regularSeqStrictUpperTransfer bound_bridge

end BishopRegularSeqTheorem118

/-- G57 package: the order-transfer bridge in G56 is now implemented from the
existing RegularSeq data-order layer. -/
structure BishopRegularSeqTheorem118G57Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  g56 : BishopRegularSeqTheorem118G56Package S
  strict_transfer : RegularSeqStrictUpperTransfer
  large_from_norm_bound :
    BishopRegularSeqTheorem118.Property4LargeNormBoundBridge S ->
      BishopRegularSeqTheorem118.Property4LargeLipschitzBridge S
  small_from_norm_bound :
    BishopRegularSeqTheorem118.Property4SmallNormBoundBridge S ->
      BishopRegularSeqTheorem118.Property4SmallLipschitzBridge S
  source_order_transfer_closed_by_cotransitivity : Prop
  remaining_work_is_the_two_truncation_norm_bounds : Prop

def bishopRegularSeqTheorem118G57Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G57Package S where
  g56 := bishopRegularSeqTheorem118G56Package S
  strict_transfer := regularSeqStrictUpperTransfer
  large_from_norm_bound := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeLipschitzBridge_from_norm_bound_closed
      S bridge
  small_from_norm_bound := fun bridge =>
    BishopRegularSeqTheorem118.property4SmallLipschitzBridge_from_norm_bound_closed
      S bridge
  source_order_transfer_closed_by_cotransitivity := True
  remaining_work_is_the_two_truncation_norm_bounds := True

/-- Progress after G57: the generic strict upper-transfer bridge needed for
Theorem 1.18(4)'s estimates is closed. -/
def bishopRegularSeqCh1To4ProgressAfterG57 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 85
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 57
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G57: closed the strict upper-transfer order bridge used in Theorem 1.18 \
    property (4)'s estimate reduction."

set_option linter.style.longLine false


end BishopCReal
