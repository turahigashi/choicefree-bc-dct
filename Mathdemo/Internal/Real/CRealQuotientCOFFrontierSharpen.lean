import Mathdemo.Internal.Real.ConditionalCRealQuotientCOFRecord

set_option linter.unusedVariables false

/-!
# CReal quotient COF frontier sharpen

`ConditionalCRealQuotientCOFRecord` exposes two remaining inputs before the conditional quotient
`COF` package can become unconditional:

* representative extraction for quotient elements;
* conversion from the current Prop-valued quotient order to the data-valued
  quotient order.

An attempted direct closure of the first item by
`Quotient.inductionOn : (x : CRealQuot) → CRealQuotRepWitness x` is rejected by
Lean as an invalid motive: this would eliminate a quotient into a Type-valued
dependent witness carrying an equality to a chosen representative.  Thus this
file records the sharpened frontier without pretending that representative
extraction has been closed.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Exact shape of the rejected tempting path.  This is intentionally only a
type alias: a choice-free inhabitant is not provided. -/
abbrev CRealQuotRepWitnessByQuotInductionAttempt : Type :=
  ∀ x : CRealQuot, CRealQuotRepWitness x

/-- Exact shape of the Prop-to-data strict-order bridge still needed by the
conditional `COF` package. -/
abbrev CRealQuotPropLTToDataLTObligation : Type :=
  ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b

/-- The conditional quotient `COF` package after `ConditionalCRealQuotientCOFRecord`: all algebraic
and Prop-order fields are closed, but the two Type-valued extraction bridges
remain explicit inputs. -/
structure CRealQuotCOFExtractionFrontier : Type 1 where
  repWitness : Type
  propLTToDataLT : Type
  conditionalCOF : ∀
    (A : ScalarMulArchimedeanData)
    (rep : CRealQuotRepWitnessByQuotInductionAttempt)
    (ltDataOf : CRealQuotPropLTToDataLTObligation),
    BishopC.COF CRealQuot
  conditionalPackage : ∀
    (A : ScalarMulArchimedeanData)
    (rep : CRealQuotRepWitnessByQuotInductionAttempt)
    (ltDataOf : CRealQuotPropLTToDataLTObligation),
    CRealQuotConditionalCOFPackage A

def cRealQuotCOFExtractionFrontier : CRealQuotCOFExtractionFrontier where
  repWitness := CRealQuotRepWitnessByQuotInductionAttempt
  propLTToDataLT := CRealQuotPropLTToDataLTObligation
  conditionalCOF := fun A rep ltDataOf =>
    cRealQuotCOFConditionalWith A rep ltDataOf
  conditionalPackage := fun A rep ltDataOf =>
    cRealQuotConditionalCOFPackageWith A rep ltDataOf

/-- Remaining work after the extraction-frontier sharpening.  The quotient
path cannot claim an unconditional `COF CRealQuot` until these extraction
bridges are replaced by a representation-carrying design or are otherwise
constructively supplied. -/
structure CRealQuotAfterExtractionSharpeningFrontier : Type where
  representative_extraction : Prop
  prop_lt_to_data_lt : Prop
  representation_carrying_alternative : Prop
  cofo_order_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotAfterExtractionSharpeningFrontier :
    CRealQuotAfterExtractionSharpeningFrontier where
  representative_extraction := True
  prop_lt_to_data_lt := True
  representation_carrying_alternative := True
  cofo_order_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

