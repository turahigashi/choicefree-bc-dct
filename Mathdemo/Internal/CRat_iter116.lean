import Mathdemo.Internal.CRat_iter115

/-!
# Algebra law layer for the RegularSeq data-interface

`CRat_iter115` made the setoid layer explicit.  This file packages the already
closed representative-level algebra laws as `relEventually` laws over the
Bishop-style `RegularSeq` carrier.

The point is still not to create a Lean `CommRing RegularSeq`: structural
equality is the wrong equality for Bishop reals.  Instead, these are algebra
laws over the implementation setoid `relEventually`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Right additive identity over the implementation setoid. -/
theorem addSeq_zero_right_eventually (x : RegularSeq) :
    relEventually (addSeq x zeroSeq) x := by
  apply rel_to_relEventually
  change relVal (addVal x.val zeroVal) x.val
  exact add_zero_raw x

/-- Left additive identity over the implementation setoid. -/
theorem addSeq_zero_left_eventually (x : RegularSeq) :
    relEventually (addSeq zeroSeq x) x := by
  apply rel_to_relEventually
  change relVal (addVal zeroVal x.val) x.val
  exact zero_add_raw x

/-- Additive commutativity over the implementation setoid. -/
theorem addSeq_comm_eventually (x y : RegularSeq) :
    relEventually (addSeq x y) (addSeq y x) := by
  apply rel_to_relEventually
  change relVal (addVal x.val y.val) (addVal y.val x.val)
  exact add_comm_raw x y

/-- Additive associativity over the implementation setoid. -/
theorem addSeq_assoc_eventually
    (x y z : RegularSeq) :
    relEventually (addSeq (addSeq x y) z) (addSeq x (addSeq y z)) := by
  apply rel_to_relEventually
  change relVal
    (addVal (addVal x.val y.val) z.val)
    (addVal x.val (addVal y.val z.val))
  exact add_assoc_raw x y z

/-- Left additive inverse over the implementation setoid. -/
theorem addSeq_neg_left_eventually (x : RegularSeq) :
    relEventually (addSeq (negSeq x) x) zeroSeq := by
  apply rel_to_relEventually
  change relVal (addVal (negVal x.val) x.val) zeroVal
  exact neg_add_cancel_raw x

/-- Right additive inverse over the implementation setoid. -/
theorem addSeq_neg_right_eventually (x : RegularSeq) :
    relEventually (addSeq x (negSeq x)) zeroSeq := by
  apply rel_to_relEventually
  change relVal (addVal x.val (negVal x.val)) zeroVal
  exact add_neg_cancel_raw x

/-- Right subtraction identity over the implementation setoid. -/
theorem subSeq_zero_right_eventually (x : RegularSeq) :
    relEventually (subSeq x zeroSeq) x := by
  apply rel_to_relEventually
  change relVal (subVal x.val zeroVal) x.val
  exact sub_zero_raw x

/-- Left zero subtraction over the implementation setoid. -/
theorem subSeq_zero_left_eventually (x : RegularSeq) :
    relEventually (subSeq zeroSeq x) (negSeq x) := by
  apply rel_to_relEventually
  change relVal (subVal zeroVal x.val) (negVal x.val)
  exact zero_sub_raw x

/-- Self-subtraction over the implementation setoid. -/
theorem subSeq_self_eventually_law (x : RegularSeq) :
    relEventually (subSeq x x) zeroSeq := by
  apply rel_to_relEventually
  change relVal (subVal x.val x.val) zeroVal
  exact sub_self_raw x

/-- Subtraction agrees with addition of the negative over the implementation
setoid. -/
theorem subSeq_eq_add_neg_eventually (x y : RegularSeq) :
    relEventually (subSeq x y) (addSeq x (negSeq y)) := by
  apply rel_to_relEventually
  change relVal (subVal x.val y.val) (addVal x.val (negVal y.val))
  exact sub_eq_add_neg_raw x y

/-- Reversing subtraction agrees with negation over the implementation setoid. -/
theorem subSeq_comm_neg_eventually (x y : RegularSeq) :
    relEventually (subSeq x y) (negSeq (subSeq y x)) := by
  apply rel_to_relEventually
  change relVal (subVal x.val y.val) (negVal (subVal y.val x.val))
  exact sub_comm_neg_raw x y

/-- Left multiplication by zero over the implementation setoid. -/
theorem mulSeqConcrete_zero_left_eventually
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relEventually (mulSeqConcreteWith A zeroSeq x) zeroSeq := by
  apply rel_to_relEventually
  change relVal (boundedMulValWith A zeroSeq x) zeroVal
  exact bounded_mul_zero_left_raw_with A x

/-- Right multiplication by zero over the implementation setoid. -/
theorem mulSeqConcrete_zero_right_eventually
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relEventually (mulSeqConcreteWith A x zeroSeq) zeroSeq := by
  apply rel_to_relEventually
  change relVal (boundedMulValWith A x zeroSeq) zeroVal
  exact bounded_mul_zero_right_raw_with A x

/-- Left multiplication by one over the implementation setoid. -/
theorem mulSeqConcrete_one_left_eventually
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relEventually (mulSeqConcreteWith A oneSeq x) x := by
  apply rel_to_relEventually
  change relVal (boundedMulValWith A oneSeq x) x.val
  exact bounded_mul_one_left_raw_with A x

/-- Right multiplication by one over the implementation setoid. -/
theorem mulSeqConcrete_one_right_eventually
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relEventually (mulSeqConcreteWith A x oneSeq) x := by
  apply rel_to_relEventually
  change relVal (boundedMulValWith A x oneSeq) x.val
  exact bounded_mul_one_right_raw_with A x

/-- Multiplicative commutativity over the implementation setoid. -/
theorem mulSeqConcrete_comm_eventually
    (A : ScalarMulArchimedeanData) (x y : RegularSeq) :
    relEventually (mulSeqConcreteWith A x y) (mulSeqConcreteWith A y x) := by
  apply rel_to_relEventually
  change relVal (boundedMulValWith A x y) (boundedMulValWith A y x)
  exact bounded_mul_comm_raw_with A x y

/-- Multiplicative associativity over the implementation setoid. -/
theorem mulSeqConcrete_assoc_eventually
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A (mulSeqConcreteWith A x y) z)
      (mulSeqConcreteWith A x (mulSeqConcreteWith A y z)) :=
  boundedMul_assoc_eventually_with A x y z

/-- Left distributivity over the implementation setoid. -/
theorem mulSeqConcrete_left_distrib_eventually
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A x (addSeq y z))
      (addSeq (mulSeqConcreteWith A x y) (mulSeqConcreteWith A x z)) :=
  boundedMul_left_distrib_eventually_with A x y z

/-- Right distributivity over the implementation setoid. -/
theorem mulSeqConcrete_right_distrib_eventually
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A (addSeq x y) z)
      (addSeq (mulSeqConcreteWith A x z) (mulSeqConcreteWith A y z)) :=
  boundedMul_right_distrib_eventually_with A x y z

/-- RegularSeq algebra laws stated over `relEventually`. -/
structure CRealRegularSeqAlgebraLawLayer
    (A : ScalarMulArchimedeanData) : Type 1 where
  setoidLayer : CRealRegularSeqSetoidLawLayer A
  add_zero_right :
    ∀ x : RegularSeq, relEventually (addSeq x zeroSeq) x
  add_zero_left :
    ∀ x : RegularSeq, relEventually (addSeq zeroSeq x) x
  add_comm :
    ∀ x y : RegularSeq, relEventually (addSeq x y) (addSeq y x)
  add_assoc :
    ∀ x y z : RegularSeq,
      relEventually (addSeq (addSeq x y) z) (addSeq x (addSeq y z))
  add_neg_left :
    ∀ x : RegularSeq, relEventually (addSeq (negSeq x) x) zeroSeq
  add_neg_right :
    ∀ x : RegularSeq, relEventually (addSeq x (negSeq x)) zeroSeq
  sub_zero_right :
    ∀ x : RegularSeq, relEventually (subSeq x zeroSeq) x
  sub_zero_left :
    ∀ x : RegularSeq, relEventually (subSeq zeroSeq x) (negSeq x)
  sub_self :
    ∀ x : RegularSeq, relEventually (subSeq x x) zeroSeq
  sub_eq_add_neg :
    ∀ x y : RegularSeq,
      relEventually (subSeq x y) (addSeq x (negSeq y))
  sub_comm_neg :
    ∀ x y : RegularSeq,
      relEventually (subSeq x y) (negSeq (subSeq y x))
  mul_zero_left :
    ∀ x : RegularSeq,
      relEventually (mulSeqConcreteWith A zeroSeq x) zeroSeq
  mul_zero_right :
    ∀ x : RegularSeq,
      relEventually (mulSeqConcreteWith A x zeroSeq) zeroSeq
  mul_one_left :
    ∀ x : RegularSeq,
      relEventually (mulSeqConcreteWith A oneSeq x) x
  mul_one_right :
    ∀ x : RegularSeq,
      relEventually (mulSeqConcreteWith A x oneSeq) x
  mul_comm :
    ∀ x y : RegularSeq,
      relEventually (mulSeqConcreteWith A x y) (mulSeqConcreteWith A y x)
  mul_assoc :
    ∀ x y z : RegularSeq,
      relEventually
        (mulSeqConcreteWith A (mulSeqConcreteWith A x y) z)
        (mulSeqConcreteWith A x (mulSeqConcreteWith A y z))
  left_distrib :
    ∀ x y z : RegularSeq,
      relEventually
        (mulSeqConcreteWith A x (addSeq y z))
        (addSeq (mulSeqConcreteWith A x y) (mulSeqConcreteWith A x z))
  right_distrib :
    ∀ x y z : RegularSeq,
      relEventually
        (mulSeqConcreteWith A (addSeq x y) z)
        (addSeq (mulSeqConcreteWith A x z) (mulSeqConcreteWith A y z))

def cRealRegularSeqAlgebraLawLayer
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqAlgebraLawLayer A where
  setoidLayer := cRealRegularSeqSetoidLawLayer A
  add_zero_right := addSeq_zero_right_eventually
  add_zero_left := addSeq_zero_left_eventually
  add_comm := addSeq_comm_eventually
  add_assoc := addSeq_assoc_eventually
  add_neg_left := addSeq_neg_left_eventually
  add_neg_right := addSeq_neg_right_eventually
  sub_zero_right := subSeq_zero_right_eventually
  sub_zero_left := subSeq_zero_left_eventually
  sub_self := subSeq_self_eventually_law
  sub_eq_add_neg := subSeq_eq_add_neg_eventually
  sub_comm_neg := subSeq_comm_neg_eventually
  mul_zero_left := mulSeqConcrete_zero_left_eventually A
  mul_zero_right := mulSeqConcrete_zero_right_eventually A
  mul_one_left := mulSeqConcrete_one_left_eventually A
  mul_one_right := mulSeqConcrete_one_right_eventually A
  mul_comm := mulSeqConcrete_comm_eventually A
  mul_assoc := mulSeqConcrete_assoc_eventually A
  left_distrib := mulSeqConcrete_left_distrib_eventually A
  right_distrib := mulSeqConcrete_right_distrib_eventually A

/-- Extended package after adding the algebra law layer to the RegularSeq
data-interface route. -/
structure CRealRegularSeqDataCOFOCAlgebraPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  setoidPackage : CRealRegularSeqDataCOFOCSetoidPackage A
  algebraLaws : CRealRegularSeqAlgebraLawLayer A
  additive_group_laws_over_eventual_equality : Prop
  multiplicative_comm_semiring_laws_over_eventual_equality : Prop
  distributivity_over_eventual_equality : Prop
  structural_equality_commring_not_claimed : Prop

def cRealRegularSeqDataCOFOCAlgebraPackage
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqDataCOFOCAlgebraPackage A where
  setoidPackage := cRealRegularSeqDataCOFOCSetoidPackage A
  algebraLaws := cRealRegularSeqAlgebraLawLayer A
  additive_group_laws_over_eventual_equality := True
  multiplicative_comm_semiring_laws_over_eventual_equality := True
  distributivity_over_eventual_equality := True
  structural_equality_commring_not_claimed := True

/-- Roadmap checkpoint after RegularSeq algebra laws have been repackaged. -/
structure CRealAfterRegularSeqAlgebraLawLayerFrontier : Type where
  regularseq_algebra_laws_available : Prop
  laws_are_over_eventual_equality_not_structural_equality : Prop
  order_and_archimedean_law_thickening_remains : Prop
  quotient_adapter_remains_separate : Prop

def cRealAfterRegularSeqAlgebraLawLayerFrontier :
    CRealAfterRegularSeqAlgebraLawLayerFrontier where
  regularseq_algebra_laws_available := True
  laws_are_over_eventual_equality_not_structural_equality := True
  order_and_archimedean_law_thickening_remains := True
  quotient_adapter_remains_separate := True

end BishopCReal

set_option linter.style.longLine false

