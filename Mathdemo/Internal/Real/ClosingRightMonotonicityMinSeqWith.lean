import Mathdemo.Internal.Real.ClosingNonnegativeShiftOrderComponentShifted

set_option linter.style.longLine false

/-!
# G114: closing right monotonicity of `minSeqWith`

G113 left line 743 with two RegularSeq/data inputs: the translation step and
right monotonicity of `minSeqWith`.  This file closes the right monotonicity
input from:

* representative commutativity of `minSeqWith`;
* the existing left monotonicity input for line 735;
* existing `RegularSeqLe` transport across `relEventually`.

This keeps the route on the data-carrying `RegularSeq` surface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Absolute value ignores representative negation over eventual equality. -/
theorem absSeq_negSeq_eventually
    (x : RegularSeq) :
    relEventually (absSeq (negSeq x)) (absSeq x) := by
  apply rel_to_relEventually
  change relVal (absVal (negVal x.val)) (absVal x.val)
  exact abs_neg_raw x

/-- The half-sum representative minimum is commutative over eventual equality. -/
theorem minSeqWith_comm_eventually
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually (minSeqWith A x y) (minSeqWith A y x) := by
  unfold minSeqWith
  have hsum :
      relEventually (addSeq x y) (addSeq y x) :=
    addSeq_comm_eventually x y
  have hsub_to_neg :
      relEventually
        (subSeq x y)
        (negSeq (subSeq y x)) :=
    subSeq_comm_neg_eventually x y
  have habs0 :
      relEventually
        (absSeq (subSeq x y))
        (absSeq (negSeq (subSeq y x))) :=
    absSeq_respects_eventually
      (subSeq x y)
      (negSeq (subSeq y x))
      hsub_to_neg
  have habs1 :
      relEventually
        (absSeq (negSeq (subSeq y x)))
        (absSeq (subSeq y x)) :=
    absSeq_negSeq_eventually (subSeq y x)
  have habs :
      relEventually
        (absSeq (subSeq x y))
        (absSeq (subSeq y x)) :=
    relEventually_trans
      (absSeq (subSeq x y))
      (absSeq (negSeq (subSeq y x)))
      (absSeq (subSeq y x))
      habs0
      habs1
  have hbody :
      relEventually
        (subSeq (addSeq x y) (absSeq (subSeq x y)))
        (subSeq (addSeq y x) (absSeq (subSeq y x))) :=
    subSeq_respects_eventually
      (addSeq x y) (addSeq y x)
      (absSeq (subSeq x y)) (absSeq (subSeq y x))
      hsum
      habs
  exact
    mulSeqConcrete_respects_eventually A
      halfSeq halfSeq
      (subSeq (addSeq x y) (absSeq (subSeq x y)))
      (subSeq (addSeq y x) (absSeq (subSeq y x)))
      (relEventually_refl halfSeq)
      hbody

/-- Right monotonicity of `minSeqWith` follows from left monotonicity plus
commutativity, all over the RegularSeq order surface. -/
theorem minSeqWith_monotone_right_regularSeqLe_from_left
    (A : ScalarMulArchimedeanData)
    (left_mono :
      forall x y c : RegularSeq,
        RegularSeqLe x y ->
          RegularSeqLe (minSeqWith A x c) (minSeqWith A y c))
    (x a b : RegularSeq)
    (hab : RegularSeqLe a b) :
    RegularSeqLe (minSeqWith A x a) (minSeqWith A x b) := by
  have hleft :
      RegularSeqLe (minSeqWith A a x) (minSeqWith A b x) :=
    left_mono a b x hab
  have hx_left :
      relEventually (minSeqWith A x a) (minSeqWith A a x) :=
    minSeqWith_comm_eventually A x a
  have hx_right :
      relEventually (minSeqWith A b x) (minSeqWith A x b) :=
    minSeqWith_comm_eventually A b x
  exact
    regularSeqLe_of_right_eventual
      hx_right
      (regularSeqLe_of_left_eventual hx_left hleft)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
