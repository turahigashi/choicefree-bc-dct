import Mathdemo.Internal.Real.ClosingCommonMaxHalfSumTransport
set_option linter.style.longLine false

/-!
# G147: closing the half absolute-value term law

G146 reduced half recovery to the local termwise identity
`|u| ~ 2 * |(1/2)u|`.  This file extracts the representative-level
absolute-value multiplication theorem already used by the quotient layer and
uses it, together with half arithmetic, to close that term law.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24HalfTermLaw


/-- Representative-level absolute value distributes over concrete
multiplication.  This is the non-quotient content used inside
`abs_mulQuotConcreteWith`. -/
theorem abs_mulSeqConcrete_eventually
    (Arch : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually
      (absSeq (mulSeqConcreteWith Arch x y))
      (mulSeqConcreteWith Arch (absSeq x) (absSeq y)) := by
  set K : Nat := mulBoundWith Arch x y with hKdef
  set L : Nat := mulBoundWith Arch (absSeq x) (absSeq y) with hLdef
  set C : Nat := Nat.max K L with hCdef
  have hKleC : K <= C := by
    rw [hCdef]
    exact Nat.le_max_left K L
  have hLleC : L <= C := by
    rw [hCdef]
    exact Nat.le_max_right K L
  have hxK : standardBoundWith Arch x <= K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_left Arch x y
  have hyK : standardBoundWith Arch y <= K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_right Arch x y
  have haxL : standardBoundWith Arch (absSeq x) <= L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_left Arch (absSeq x) (absSeq y)
  have hayL : standardBoundWith Arch (absSeq y) <= L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_right Arch (absSeq x) (absSeq y)
  have hxC : standardBoundWith Arch x <= C := Nat.le_trans hxK hKleC
  have hyC : standardBoundWith Arch y <= C := Nat.le_trans hyK hKleC
  have haxC : standardBoundWith Arch (absSeq x) <= C := Nat.le_trans haxL hLleC
  have hayC : standardBoundWith Arch (absSeq y) <= C := Nat.le_trans hayL hLleC
  have hleft : relEventually (mulSeqConcreteWith Arch x y)
      (mulSeqAtBoundWith Arch C x y hxC hyC) :=
    mulSeqConcrete_to_common_bound_eventually_with Arch x y hxC hyC
  have hleft_abs :
      relEventually
        (absSeq (mulSeqConcreteWith Arch x y))
        (absSeq (mulSeqAtBoundWith Arch C x y hxC hyC)) :=
    absSeq_respects_eventually
      (mulSeqConcreteWith Arch x y)
      (mulSeqAtBoundWith Arch C x y hxC hyC)
      hleft
  have hmid :
      relEventually
        (absSeq (mulSeqAtBoundWith Arch C x y hxC hyC))
        (mulSeqAtBoundWith Arch C (absSeq x) (absSeq y) haxC hayC) :=
    abs_mul_common_bound_eventually_with Arch x y hxC hyC haxC hayC
  have hright :
      relEventually
        (mulSeqAtBoundWith Arch C (absSeq x) (absSeq y) haxC hayC)
        (mulSeqConcreteWith Arch (absSeq x) (absSeq y)) :=
    mulSeqCommon_to_concrete_bound_eventually_with
      Arch (absSeq x) (absSeq y) haxC hayC
  exact
    relEventually_trans
      (absSeq (mulSeqConcreteWith Arch x y))
      (absSeq (mulSeqAtBoundWith Arch C x y hxC hyC))
      (mulSeqConcreteWith Arch (absSeq x) (absSeq y))
      hleft_abs
      (relEventually_trans
        (absSeq (mulSeqAtBoundWith Arch C x y hxC hyC))
        (mulSeqAtBoundWith Arch C (absSeq x) (absSeq y) haxC hayC)
        (mulSeqConcreteWith Arch (absSeq x) (absSeq y))
        hmid
        hright)










end Prop24HalfTermLaw
end BishopRegularSeqChapter2





end BishopCReal
