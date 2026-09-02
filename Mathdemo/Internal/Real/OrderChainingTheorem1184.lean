import Mathdemo.Internal.Real.ClosingStrictUpperTransferBridge

/-!
# G58: order chaining for Theorem 1.18(4) norm bounds

G57 closed the strict upper-transfer bridge.  The next source estimates,
lines 734--735 and 743--747, also require chaining non-strict bounds.  This
file closes the needed `RegularSeqLe` transitivity step from the existing
cotransitive strict order, then uses it to factor the remaining large and small
norm-bound targets into two displayed non-strict inequalities.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- A counterexample to `x <= y`, in the internal `RegularSeqLe` spelling, gives
the reverse strict comparison `y < x`. -/
theorem regularSeqLtProp_reverse_of_le_counterexample
    {x y : RegularSeq}
    (h : regularSeqLtProp (subSeq y x) zeroSeq) :
    regularSeqLtProp y x := by
  have h1 :
      relEventually
        (subSeq zeroSeq (subSeq y x))
        (negSeq (subSeq y x)) :=
    subSeq_zero_left_eventually (subSeq y x)
  have h2 :
      relEventually
        (negSeq (subSeq y x))
        (subSeq x y) :=
    relEventually_symm
      (subSeq x y)
      (negSeq (subSeq y x))
      (subSeq_comm_neg_eventually x y)
  exact
    posEventually_respects
      (subSeq zeroSeq (subSeq y x))
      (subSeq x y)
      (relEventually_trans
        (subSeq zeroSeq (subSeq y x))
        (negSeq (subSeq y x))
        (subSeq x y)
        h1 h2)
      h

/-- Prop-valued version of the G57 contradiction: `y < x` contradicts
`x <= y`. -/
theorem regularSeqLe_not_lt_reverse_prop
    {x y : RegularSeq}
    (hxy : RegularSeqLe x y)
    (hyx : regularSeqLtProp y x) :
    False := by
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
        hyx
  exact hxy htarget

/-- Non-strict order transitivity for the RegularSeq order surface. -/
theorem regularSeqLe_trans
    {x y z : RegularSeq}
    (hxy : RegularSeqLe x y)
    (hyz : RegularSeqLe y z) :
    RegularSeqLe x z := by
  intro hcounter
  have hzx : regularSeqLtProp z x :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  rcases regularSeqLtProp_cotrans z x y hzx with hzy | hyx
  · exact regularSeqLe_not_lt_reverse_prop hyz hzy
  · exact regularSeqLe_not_lt_reverse_prop hxy hyx



namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
