import Mathdemo.Internal.Real.ClosingLeftMonotonicitySubtraction

set_option linter.style.longLine false

/-!
# G91: closing the base-to-absolute bound

G90 left the small line-743 absolute-tail chain with the primitive order input

`b <= |b|`.

This file closes that input from the existing representative theorem
`not_posEventually_sub_self_abs`, transporting only the spelling difference
between `RegularSeqLe b (absSeq b)` and the direct strict-counterexample form.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Representative-level order bound `b <= |b|` in the `RegularSeqLe` surface. -/
theorem base_le_abs_base_regularSeqLe
    (b : RegularSeq) :
    RegularSeqLe b (absSeq b) := by
  intro hcounter
  have hzero_to_neg :
      relEventually
        (subSeq zeroSeq (subSeq (absSeq b) b))
        (negSeq (subSeq (absSeq b) b)) :=
    subSeq_zero_left_eventually (subSeq (absSeq b) b)
  have hneg_to_self_abs :
      relEventually
        (negSeq (subSeq (absSeq b) b))
        (subSeq b (absSeq b)) :=
    relEventually_symm
      (subSeq b (absSeq b))
      (negSeq (subSeq (absSeq b) b))
      (subSeq_comm_neg_eventually b (absSeq b))
  have htarget :
      PosEventually (subSeq b (absSeq b)) :=
    posEventually_respects
      (subSeq zeroSeq (subSeq (absSeq b) b))
      (subSeq b (absSeq b))
      (relEventually_trans
        (subSeq zeroSeq (subSeq (absSeq b) b))
        (negSeq (subSeq (absSeq b) b))
        (subSeq b (absSeq b))
        hzero_to_neg
        hneg_to_self_abs)
      hcounter
  exact not_posEventually_sub_self_abs b htarget

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
