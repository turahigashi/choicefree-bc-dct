import Mathdemo.Internal.CRat_iter41

/-!
# CReal quotient closed algebra package

The previous files closed the additive quotient laws and the multiplication
frontier, including associativity and distributivity.  This file does not add a
new estimate; it fixes the public packaging layer that the final COFO/COFOC
assembly can consume.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Audited package of the quotient-level algebra that is already closed for
the concrete CReal construction, relative to the explicit scalar
multiplicative Archimedean datum used by multiplication. -/
structure CRealQuotClosedAlgebraSeed
    (A : ScalarMulArchimedeanData) : Type where
  eventualSetoid : CRealEventualSetoidSeed
  eventualAdditive : CRealEventualAdditiveSeed
  quotientAdditiveOps : CRealQuotAdditiveOpsSeed
  quotientAdditiveLaws : CRealQuotAdditiveAlgebraSeed
  quotientPositive : CRealQuotPositiveSeed
  quotientOrderSanity : CRealQuotOrderSanitySeed
  quotientOrderAdd : CRealQuotOrderAddSeed
  quotientOrderCotrans : CRealQuotOrderCotransSeed
  mulBound : CRealMulBoundSeed
  mulRegularity : CRealMulRegularitySeed
  mulClosure : CRealMulClosureSeed
  mulOps : CRealQuotMulConcreteSeed A
  mulNeg : CRealQuotMulNegConcreteSeed A
  mulCommonBoundTransport : CRealCommonBoundMulTransportSeed A
  mulDistrib : CRealQuotMulDistribConcreteSeed A
  mulRingLaws : CRealQuotMulRingLawData (cRealMulCompletionObligationsWith A)
  mulFinalFrontier : CRealMulFinalFrontier
  add_zero_left : ∀ x : CRealQuot, addQuot zeroQuot x = x
  add_zero_right : ∀ x : CRealQuot, addQuot x zeroQuot = x
  add_comm : ∀ x y : CRealQuot, addQuot x y = addQuot y x
  add_assoc : ∀ x y z : CRealQuot,
    addQuot (addQuot x y) z = addQuot x (addQuot y z)
  add_neg_left : ∀ x : CRealQuot, addQuot (negQuot x) x = zeroQuot
  add_neg_right : ∀ x : CRealQuot, addQuot x (negQuot x) = zeroQuot
  sub_eq_add_neg : ∀ x y : CRealQuot, subQuot x y = addQuot x (negQuot y)
  mul_zero_left : ∀ x : CRealQuot, mulQuotConcreteWith A zeroQuot x = zeroQuot
  mul_zero_right : ∀ x : CRealQuot, mulQuotConcreteWith A x zeroQuot = zeroQuot
  mul_one_left : ∀ x : CRealQuot, mulQuotConcreteWith A oneQuot x = x
  mul_one_right : ∀ x : CRealQuot, mulQuotConcreteWith A x oneQuot = x
  mul_comm : ∀ x y : CRealQuot,
    mulQuotConcreteWith A x y = mulQuotConcreteWith A y x
  mul_assoc : ∀ x y z : CRealQuot,
    mulQuotConcreteWith A (mulQuotConcreteWith A x y) z =
      mulQuotConcreteWith A x (mulQuotConcreteWith A y z)
  mul_neg_left : ∀ x y : CRealQuot,
    mulQuotConcreteWith A (negQuot x) y = negQuot (mulQuotConcreteWith A x y)
  mul_neg_right : ∀ x y : CRealQuot,
    mulQuotConcreteWith A x (negQuot y) = negQuot (mulQuotConcreteWith A x y)
  left_distrib : ∀ x y z : CRealQuot,
    mulQuotConcreteWith A x (addQuot y z) =
      addQuot (mulQuotConcreteWith A x y) (mulQuotConcreteWith A x z)
  right_distrib : ∀ x y z : CRealQuot,
    mulQuotConcreteWith A (addQuot x y) z =
      addQuot (mulQuotConcreteWith A x z) (mulQuotConcreteWith A y z)
  lt_irrefl : ∀ x : CRealQuot, ¬ ltQuot x x
  lt_cotrans : ∀ {a b : CRealQuot}, ltQuot a b → ∀ c : CRealQuot,
    ltQuot a c ∨ ltQuot c b
  lt_add_left : ∀ c a b : CRealQuot,
    ltQuot a b → ltQuot (addQuot c a) (addQuot c b)
  apart_of_lt : ∀ {x y : CRealQuot}, ltQuot x y → apartQuot x y
  apart_symm : ∀ {x y : CRealQuot}, apartQuot x y → apartQuot y x

def cRealQuotClosedAlgebraSeedWith
    (A : ScalarMulArchimedeanData) : CRealQuotClosedAlgebraSeed A where
  eventualSetoid := cRealEventualSetoidSeed
  eventualAdditive := cRealEventualAdditiveSeed
  quotientAdditiveOps := cRealQuotAdditiveOpsSeed
  quotientAdditiveLaws := cRealQuotAdditiveAlgebraSeed
  quotientPositive := cRealQuotPositiveSeed
  quotientOrderSanity := cRealQuotOrderSanitySeed
  quotientOrderAdd := cRealQuotOrderAddSeed
  quotientOrderCotrans := cRealQuotOrderCotransSeed
  mulBound := cRealMulBoundSeedWith A
  mulRegularity := cRealMulRegularitySeed
  mulClosure := cRealMulClosureSeedWith A
  mulOps := cRealQuotMulConcreteSeedWith A
  mulNeg := cRealQuotMulNegConcreteSeedWith A
  mulCommonBoundTransport := cRealCommonBoundMulTransportSeedWith A
  mulDistrib := cRealQuotMulDistribConcreteSeed A
  mulRingLaws := cRealQuotMulRingLawDataConcreteWith A
  mulFinalFrontier := cRealMulFinalFrontierConcreteWith A
  add_zero_left := addQuot_zero_left
  add_zero_right := addQuot_zero_right
  add_comm := addQuot_comm
  add_assoc := addQuot_assoc
  add_neg_left := addQuot_neg_left
  add_neg_right := addQuot_neg_right
  sub_eq_add_neg := subQuot_eq_add_neg
  mul_zero_left := mulQuotConcrete_zero_left A
  mul_zero_right := mulQuotConcrete_zero_right A
  mul_one_left := mulQuotConcrete_one_left A
  mul_one_right := mulQuotConcrete_one_right A
  mul_comm := mulQuotConcrete_comm A
  mul_assoc := mulQuotConcrete_assoc A
  mul_neg_left := mulQuotConcrete_neg_left A
  mul_neg_right := mulQuotConcrete_neg_right A
  left_distrib := mulQuotConcrete_left_distrib A
  right_distrib := mulQuotConcrete_right_distrib A
  lt_irrefl := ltQuot_irrefl
  lt_cotrans := fun {a b} h c => ltQuot_cotrans a b c h
  lt_add_left := ltQuot_add_left
  apart_of_lt := fun h => apartQuot_of_lt h
  apart_symm := fun h => apartQuot_symm h

/-- The remaining final-goal work after the closed quotient algebra package.
These are the genuinely non-algebraic COFO/COFOC obligations that must still be
discharged before emitting an actual `COFOC CReal` instance. -/
structure CRealCOFOCRemainingFrontier : Type where
  quotient_cof_instance : Prop
  quotient_cofo_order_laws : Prop
  quotient_archimedean : Prop
  quotient_inverse_for_positive : Prop
  quotient_cauchy_completeness : Prop

/-- Honest roadmap marker: after `cRealQuotClosedAlgebraSeedWith`, the algebraic
frontier is closed, while the order/Archimedean/inverse/completeness frontier
remains. -/
def cRealCOFOCRemainingFrontierMarker : CRealCOFOCRemainingFrontier where
  quotient_cof_instance := True
  quotient_cofo_order_laws := True
  quotient_archimedean := True
  quotient_inverse_for_positive := True
  quotient_cauchy_completeness := True

end BishopCReal

