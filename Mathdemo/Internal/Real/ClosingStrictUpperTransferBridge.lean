import Mathdemo.Internal.Real.Theorem1184EstimateBridges

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



end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
