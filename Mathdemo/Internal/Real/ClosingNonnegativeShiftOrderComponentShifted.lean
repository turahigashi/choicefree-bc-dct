import Mathdemo.Internal.Real.RemovingPositiveInverseTotalizationMinLaw
set_option linter.style.longLine false

/-!
# G113: closing the nonnegative shift-order component of shifted min

G112 decomposed the line-743 shifted-min law into three RegularSeq/data
components.  This file closes the middle component

`0 <= d -> c - d <= c`

directly on the `RegularSeq` representation surface.  The proof uses only
existing `relEventually` algebra laws and nonnegativity transport; no quotient
representative extraction or `Prop`-to-data selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Cancelling a represented difference on the right:
`c - (c - d) = d` over the implementation equality. -/
theorem subSeq_right_sub_cancel_eventually
    (c d : RegularSeq) :
    relEventually (subSeq c (subSeq c d)) d := by
  have hcomm :
      relEventually
        (subSeq c (subSeq c d))
        (negSeq (subSeq (subSeq c d) c)) :=
    subSeq_comm_neg_eventually c (subSeq c d)
  have hleft :
      relEventually
        (subSeq c d)
        (addSeq c (negSeq d)) :=
    subSeq_eq_add_neg_eventually c d
  have hinner0 :
      relEventually
        (subSeq (subSeq c d) c)
        (subSeq (addSeq c (negSeq d)) c) :=
    subSeq_respects_eventually
      (subSeq c d) (addSeq c (negSeq d))
      c c
      hleft
      (relEventually_refl c)
  have hinner1 :
      relEventually
        (subSeq (addSeq c (negSeq d)) c)
        (negSeq d) :=
    subSeq_add_left_cancel_eventually c (negSeq d)
  have hinner :
      relEventually
        (subSeq (subSeq c d) c)
        (negSeq d) :=
    relEventually_trans
      (subSeq (subSeq c d) c)
      (subSeq (addSeq c (negSeq d)) c)
      (negSeq d)
      hinner0
      hinner1
  have hneg :
      relEventually
        (negSeq (subSeq (subSeq c d) c))
        (negSeq (negSeq d)) :=
    negSeq_respects_eventually
      (subSeq (subSeq c d) c)
      (negSeq d)
      hinner
  have hdn :
      relEventually (negSeq (negSeq d)) d :=
    negSeq_negSeq_eventually d
  exact
    relEventually_trans
      (subSeq c (subSeq c d))
      (negSeq (subSeq (subSeq c d) c))
      d
      hcomm
      (relEventually_trans
        (negSeq (subSeq (subSeq c d) c))
        (negSeq (negSeq d))
        d
        hneg
        hdn)

/-- If the shift is nonnegative, subtracting it from the right lowers the
left endpoint: `0 <= d -> c - d <= c`. -/
theorem regularSeqLe_sub_right_self_of_nonneg
    (c d : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) :
    RegularSeqLe (subSeq c d) c := by
  have hd_nonneg : RegularSeqNonneg d :=
    regularSeqNonneg_of_eventual
      (relEventually_symm
        (subSeq d zeroSeq)
        d
        (subSeq_zero_right_eventually d))
      hd
  exact
    regularSeqNonneg_of_eventual
      (subSeq_right_sub_cancel_eventually c d)
      hd_nonneg

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
