import Mathdemo.Internal.CRat_iter112

/-!
# Bishop-source hint audit for the remaining CReal quotient assumptions

For this compatibility audit, Bishop-Bridges (1985) and Bishop (1967) serve as
conceptual guardrails rather than as a claim of line-by-line correspondence to
a single primary text:

* a real number is presented as a regular sequence, not as an opaque quotient
  class from which a representative should later be selected;
* the rational approximation operation from a real to its `n`-th approximation
  is not a function on quotient classes;
* positivity is not just a Prop attached to a sequence: a positive real carries
  an index/witness;
* reciprocal construction consumes nonzero/positive-apartness data.

This file does not add a new live `BishopC.COFOC CRealQuot`.  It classifies the
three remaining inputs in the current quotient route and records the
source-guided next fork: either keep the previous quotient interface and explicitly
provide its selectors, or refactor the final scalar interface around
representation/data-carrying reals.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Local source-alignment observations relevant to the final `CReal` route.

These are deliberately recorded as audit flags, not as proof obligations about
the historical text.  They guide which Lean assumptions should be treated as
mathematical content and which are artifacts of the current quotient encoding. -/
structure CRealBishopSourceHintAudit : Type where
  real_is_regular_sequence : Prop
  equality_is_bishop_relation_not_structure_equality : Prop
  rational_approximation_is_not_quotient_function : Prop
  positive_real_carries_witness_data : Prop
  strict_order_is_positive_difference : Prop
  reciprocal_consumes_nonzero_or_positive_data : Prop
  quotient_representative_extraction_is_not_source_shape : Prop

def cRealBishopSourceHintAudit : CRealBishopSourceHintAudit where
  real_is_regular_sequence := True
  equality_is_bishop_relation_not_structure_equality := True
  rational_approximation_is_not_quotient_function := True
  positive_real_carries_witness_data := True
  strict_order_is_positive_difference := True
  reciprocal_consumes_nonzero_or_positive_data := True
  quotient_representative_extraction_is_not_source_shape := True

/-- Remaining representative extraction problem in the opaque quotient route. -/
abbrev CRealQuotGlobalRepProblem : Type :=
  ∀ x : CRealQuot, CRealQuotRepWitness x

/-- Remaining Prop-to-data positivity selector in the quotient order route. -/
abbrev CRealQuotPosEventuallyProblem : Type :=
  CRealPosEventuallySelector

/-- Remaining total inverse selector demanded by the previous `COFO.inv` field. -/
abbrev CRealQuotTotalInverseProblem
    (A : ScalarMulArchimedeanData) : Type :=
  CRealQuotPositiveInverseTotalizationData A

/-- Exact classifier for the three remaining assumptions after
`CRat_iter112`.

The two output maps make the split explicit:

* `faithfulPackageFrom` reaches the data-carrying scalar package without a
  total inverse selector;
* `oldLiveCOFOCFrom` reaches the previous live `BishopC.COFOC` interface only after
  the total inverse problem is also supplied. -/
structure CRealQuotRemainingAssumptionClassifier
    (A : ScalarMulArchimedeanData) : Type 1 where
  sourceHints : CRealBishopSourceHintAudit
  globalRepProblem : Type
  posEventuallyProblem : Type
  totalInverseProblem : Type
  faithfulPackageFrom :
    globalRepProblem → posEventuallyProblem →
      CRealQuotFaithfulScalarPackage A
  oldLiveCOFOCFrom :
    globalRepProblem → posEventuallyProblem → totalInverseProblem →
      BishopC.COFOC CRealQuot
  globalRep_is_opaque_quotient_representative_extraction : Prop
  posEventually_is_prop_to_data_witness_selection : Prop
  totalInverse_is_old_total_inv_interface_pressure : Prop
  source_guided_resolution_is_representation_data_interface : Prop

def cRealQuotRemainingAssumptionClassifier
    (A : ScalarMulArchimedeanData) :
    CRealQuotRemainingAssumptionClassifier A where
  sourceHints := cRealBishopSourceHintAudit
  globalRepProblem := CRealQuotGlobalRepProblem
  posEventuallyProblem := CRealQuotPosEventuallyProblem
  totalInverseProblem := CRealQuotTotalInverseProblem A
  faithfulPackageFrom := fun rep sel =>
    cRealQuotFaithfulScalarPackageWith A rep sel
  oldLiveCOFOCFrom := fun rep sel tot =>
    cRealQuotFaithfulScalarPackage_to_liveCOFOC_with_totalization
      A (cRealQuotFaithfulScalarPackageWith A rep sel) tot
  globalRep_is_opaque_quotient_representative_extraction := True
  posEventually_is_prop_to_data_witness_selection := True
  totalInverse_is_old_total_inv_interface_pressure := True
  source_guided_resolution_is_representation_data_interface := True

/-- Source-guided refactor target for the next stage.

This is not yet a replacement implementation.  It records the carrier/interface
shape that removes the `globalRep` problem by construction: work over
`RegularSeq` with Bishop equality and Type-valued positive evidence, and use
the quotient only as an optional presentation bridge. -/
structure CRealRegularSeqRefactorContract : Type 1 where
  carrier : Type
  carrier_is_regular_seq : carrier = RegularSeq
  eqRel : RegularSeq → RegularSeq → Prop
  eqRel_is_existing : eqRel = rel
  positiveData : RegularSeq → Type
  positiveData_is_existing : positiveData = PosEventuallyData
  quotient_is_bridge_not_primary_carrier : Prop
  no_global_rep_extraction_required : Prop
  positive_inverse_should_be_data_indexed : Prop
  old_total_inverse_field_should_be_adapter_only : Prop

def cRealRegularSeqRefactorContract :
    CRealRegularSeqRefactorContract where
  carrier := RegularSeq
  carrier_is_regular_seq := rfl
  eqRel := rel
  eqRel_is_existing := rfl
  positiveData := PosEventuallyData
  positiveData_is_existing := rfl
  quotient_is_bridge_not_primary_carrier := True
  no_global_rep_extraction_required := True
  positive_inverse_should_be_data_indexed := True
  old_total_inverse_field_should_be_adapter_only := True

/-- G6 checkpoint: the remaining assumptions are now classified rather than
being treated as a single opaque "missing COFOC" block. -/
structure CRealQuotAfterSourceHintAssumptionAuditFrontier : Type where
  g6_remaining_assumptions_classified : Prop
  faithful_data_package_already_available : Prop
  old_live_cofoc_needs_total_inverse_adapter : Prop
  quotient_route_needs_global_rep_adapter : Prop
  positivity_route_needs_prop_to_data_adapter : Prop
  next_g7_choose_old_cofoc_adapter_or_regularseq_data_interface : Prop

def cRealQuotAfterSourceHintAssumptionAuditFrontier :
    CRealQuotAfterSourceHintAssumptionAuditFrontier where
  g6_remaining_assumptions_classified := True
  faithful_data_package_already_available := True
  old_live_cofoc_needs_total_inverse_adapter := True
  quotient_route_needs_global_rep_adapter := True
  positivity_route_needs_prop_to_data_adapter := True
  next_g7_choose_old_cofoc_adapter_or_regularseq_data_interface := True

end BishopCReal

set_option linter.style.longLine false
