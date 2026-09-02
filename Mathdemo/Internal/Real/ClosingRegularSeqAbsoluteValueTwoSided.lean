import Mathdemo.Internal.Real.ClosingMonotonicityAddingCommonRightTerm

set_option linter.style.longLine false

/-!
# G95: closing the RegularSeq absolute-value two-sided bridge

The G94 layer still carried the order bridge

`x <= y` and `-x <= y` imply `|x| <= y`.

This file closes that bridge by converting the RegularSeq non-strict order to
the already closed quotient `absQuot_le_of` theorem and transporting the result
back to the RegularSeq order surface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The counterexample form of `RegularSeqLe x y` is eventually equal to the
quotient strict-order representative `x-y`. -/
theorem regularSeqLe_counter_eventually_lt_rep
    (x y : RegularSeq) :
    relEventually
      (subSeq x y)
      (subSeq zeroSeq (subSeq y x)) := by
  have hxy_to_neg :
      relEventually
        (subSeq x y)
        (negSeq (subSeq y x)) :=
    subSeq_comm_neg_eventually x y
  have hneg_to_zero :
      relEventually
        (negSeq (subSeq y x))
        (subSeq zeroSeq (subSeq y x)) :=
    relEventually_symm
      (subSeq zeroSeq (subSeq y x))
      (negSeq (subSeq y x))
      (subSeq_zero_left_eventually (subSeq y x))
  exact
    relEventually_trans
      (subSeq x y)
      (negSeq (subSeq y x))
      (subSeq zeroSeq (subSeq y x))
      hxy_to_neg
      hneg_to_zero

/-- `RegularSeqLe x y` forbids the quotient strict inequality `y < x`. -/
theorem not_ltQuot_of_regularSeqLe
    (x y : RegularSeq)
    (hxy : RegularSeqLe x y) :
    ¬ ltQuot (mkQuot y) (mkQuot x) := by
  intro hlt
  have hpos : PosEventually (subSeq x y) := by
    change PosEventually (subSeq x y) at hlt
    exact hlt
  have hcounter :
      PosEventually (subSeq zeroSeq (subSeq y x)) :=
    posEventually_respects
      (subSeq x y)
      (subSeq zeroSeq (subSeq y x))
      (regularSeqLe_counter_eventually_lt_rep x y)
      hpos
  exact hxy hcounter

/-- A quotient-level negation of `y < x` gives the RegularSeq order `x <= y`. -/
theorem regularSeqLe_of_not_ltQuot
    (x y : RegularSeq)
    (hnot : ¬ ltQuot (mkQuot y) (mkQuot x)) :
    RegularSeqLe x y := by
  intro hcounter
  have hpos :
      PosEventually (subSeq x y) :=
    posEventually_respects
      (subSeq zeroSeq (subSeq y x))
      (subSeq x y)
      (relEventually_symm
        (subSeq x y)
        (subSeq zeroSeq (subSeq y x))
        (regularSeqLe_counter_eventually_lt_rep x y))
      hcounter
  apply hnot
  change PosEventually (subSeq x y)
  exact hpos

/-- Closed RegularSeq order bridge:
if `x <= y` and `-x <= y`, then `|x| <= y`. -/
theorem regularSeq_abs_le_of_two_sided
    (x y : RegularSeq)
    (hxy : RegularSeqLe x y)
    (hnxy : RegularSeqLe (negSeq x) y) :
    RegularSeqLe (absSeq x) y := by
  have hyx :
      ¬ ltQuot (mkQuot y) (mkQuot x) :=
    not_ltQuot_of_regularSeqLe x y hxy
  have hynx :
      ¬ ltQuot (mkQuot y) (negQuot (mkQuot x)) := by
    change ¬ ltQuot (mkQuot y) (mkQuot (negSeq x))
    exact not_ltQuot_of_regularSeqLe (negSeq x) y hnxy
  have hyabs :
      ¬ ltQuot (mkQuot y) (absQuot (mkQuot x)) :=
    absQuot_le_of hyx hynx
  apply regularSeqLe_of_not_ltQuot (absSeq x) y
  change ¬ ltQuot (mkQuot y) (absQuot (mkQuot x))
  exact hyabs


namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
