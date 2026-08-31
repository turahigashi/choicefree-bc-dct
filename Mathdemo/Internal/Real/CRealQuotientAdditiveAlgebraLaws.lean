import Mathdemo.Internal.Real.CRealConcreteQuotientMultiplicationNegation

/-!
# CReal quotient additive algebra laws

This file lifts the already-audited raw additive and subtraction algebra laws
to the eventual-equality quotient.  These laws are a required scaffold for the
later `CommRing` packaging and for stating distributivity in ordinary
quotient-level algebraic form.
-/

namespace BishopCReal

open BishopC
open BishopCRat

theorem addQuot_zero_right_mk (x : RegularSeq) :
    addQuot (mkQuot x) zeroQuot = mkQuot x := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal x.val zeroVal) x.val
  exact add_zero_raw x

theorem addQuot_zero_left_mk (x : RegularSeq) :
    addQuot zeroQuot (mkQuot x) = mkQuot x := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal zeroVal x.val) x.val
  exact zero_add_raw x

theorem addQuot_comm_mk (x y : RegularSeq) :
    addQuot (mkQuot x) (mkQuot y) = addQuot (mkQuot y) (mkQuot x) := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal x.val y.val) (addVal y.val x.val)
  exact add_comm_raw x y

theorem addQuot_assoc_mk (x y z : RegularSeq) :
    addQuot (addQuot (mkQuot x) (mkQuot y)) (mkQuot z) =
      addQuot (mkQuot x) (addQuot (mkQuot y) (mkQuot z)) := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal (addVal x.val y.val) z.val)
    (addVal x.val (addVal y.val z.val))
  exact add_assoc_raw x y z

theorem addQuot_neg_left_mk (x : RegularSeq) :
    addQuot (negQuot (mkQuot x)) (mkQuot x) = zeroQuot := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal (negVal x.val) x.val) zeroVal
  exact neg_add_cancel_raw x

theorem addQuot_neg_right_mk (x : RegularSeq) :
    addQuot (mkQuot x) (negQuot (mkQuot x)) = zeroQuot := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal x.val (negVal x.val)) zeroVal
  exact add_neg_cancel_raw x

theorem addQuot_zero_right (x : CRealQuot) :
    addQuot x zeroQuot = x := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact addQuot_zero_right_mk x'

theorem addQuot_zero_left (x : CRealQuot) :
    addQuot zeroQuot x = x := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact addQuot_zero_left_mk x'

theorem addQuot_comm (x y : CRealQuot) :
    addQuot x y = addQuot y x := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  exact addQuot_comm_mk x' y'

theorem addQuot_assoc (x y z : CRealQuot) :
    addQuot (addQuot x y) z = addQuot x (addQuot y z) := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  refine Quotient.inductionOn z ?_
  intro z'
  exact addQuot_assoc_mk x' y' z'

theorem addQuot_neg_left (x : CRealQuot) :
    addQuot (negQuot x) x = zeroQuot := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact addQuot_neg_left_mk x'

theorem addQuot_neg_right (x : CRealQuot) :
    addQuot x (negQuot x) = zeroQuot := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact addQuot_neg_right_mk x'

theorem subQuot_zero_right_mk (x : RegularSeq) :
    subQuot (mkQuot x) zeroQuot = mkQuot x := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (subVal x.val zeroVal) x.val
  exact sub_zero_raw x

theorem subQuot_zero_left_mk (x : RegularSeq) :
    subQuot zeroQuot (mkQuot x) = negQuot (mkQuot x) := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (subVal zeroVal x.val) (negVal x.val)
  exact zero_sub_raw x

theorem subQuot_eq_add_neg_mk (x y : RegularSeq) :
    subQuot (mkQuot x) (mkQuot y) = addQuot (mkQuot x) (negQuot (mkQuot y)) := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (subVal x.val y.val) (addVal x.val (negVal y.val))
  exact sub_eq_add_neg_raw x y

theorem subQuot_comm_neg_mk (x y : RegularSeq) :
    subQuot (mkQuot x) (mkQuot y) = negQuot (subQuot (mkQuot y) (mkQuot x)) := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (subVal x.val y.val) (negVal (subVal y.val x.val))
  exact sub_comm_neg_raw x y

theorem subQuot_zero_right (x : CRealQuot) :
    subQuot x zeroQuot = x := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact subQuot_zero_right_mk x'

theorem subQuot_zero_left (x : CRealQuot) :
    subQuot zeroQuot x = negQuot x := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact subQuot_zero_left_mk x'

theorem subQuot_self (x : CRealQuot) :
    subQuot x x = zeroQuot := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact subQuot_self_mk x'

theorem subQuot_eq_add_neg (x y : CRealQuot) :
    subQuot x y = addQuot x (negQuot y) := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  exact subQuot_eq_add_neg_mk x' y'

theorem subQuot_comm_neg (x y : CRealQuot) :
    subQuot x y = negQuot (subQuot y x) := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  exact subQuot_comm_neg_mk x' y'

/-- Audited quotient additive algebra seed. -/
structure CRealQuotAdditiveAlgebraSeed : Type where
  add_zero_right : ∀ x : CRealQuot, addQuot x zeroQuot = x
  add_zero_left : ∀ x : CRealQuot, addQuot zeroQuot x = x
  add_comm : ∀ x y : CRealQuot, addQuot x y = addQuot y x
  add_assoc : ∀ x y z : CRealQuot,
    addQuot (addQuot x y) z = addQuot x (addQuot y z)
  add_neg_left : ∀ x : CRealQuot, addQuot (negQuot x) x = zeroQuot
  add_neg_right : ∀ x : CRealQuot, addQuot x (negQuot x) = zeroQuot
  sub_zero_right : ∀ x : CRealQuot, subQuot x zeroQuot = x
  sub_zero_left : ∀ x : CRealQuot, subQuot zeroQuot x = negQuot x
  sub_self : ∀ x : CRealQuot, subQuot x x = zeroQuot
  sub_eq_add_neg : ∀ x y : CRealQuot, subQuot x y = addQuot x (negQuot y)
  sub_comm_neg : ∀ x y : CRealQuot, subQuot x y = negQuot (subQuot y x)

def cRealQuotAdditiveAlgebraSeed : CRealQuotAdditiveAlgebraSeed where
  add_zero_right := addQuot_zero_right
  add_zero_left := addQuot_zero_left
  add_comm := addQuot_comm
  add_assoc := addQuot_assoc
  add_neg_left := addQuot_neg_left
  add_neg_right := addQuot_neg_right
  sub_zero_right := subQuot_zero_right
  sub_zero_left := subQuot_zero_left
  sub_self := subQuot_self
  sub_eq_add_neg := subQuot_eq_add_neg
  sub_comm_neg := subQuot_comm_neg

end BishopCReal

