import Mathdemo.Internal.Real.Property4ReductionNoInverseMin

set_option linter.style.longLine false

/-!
# G103: selector-exact no-inverse min-law bridge

G102 routed property (4) through no-inverse min-law transport, but still took
the no-inverse transport law bundle as a field.  This file generates that
bundle from the exact remaining inputs:

* a G96 scalar-min bridge;
* a global quotient representative selector;
* a `PosEventually` selector.

Thus positive-inverse totalization is no longer merely absent from the proof
body; it is absent from the data interface for this min-law route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Exact data needed to generate the G102 no-inverse min-law bridge. -/
structure Property4NoInverseMinLawSelectorExactData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g96_bridge :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S
  global_rep_selector :
    ∀ x : CRealQuot, CRealQuotRepWitness x
  pos_eventually_selector :
    CRealPosEventuallySelector
  source_line735_and_line743_generated_from_exact_selector_pair : Prop
  source_positive_inverse_totalization_removed_from_selector_exact_route : Prop

/-- Generate the G97 minSeq quotient-transport laws from the exact selector
pair and the already closed G96 scalar-min kernel. -/
def noInverseMinSeqTransportCoreLaws_from_selectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawSelectorExactData S) :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch :=
  minSeqQuotientTransportCoreLaws_from_noInverseTotalization
    Arch
    data.g96_bridge.scalar_min_kernel_closed_core_laws
    data.global_rep_selector
    data.pos_eventually_selector

/-- Generate the G102 no-inverse unified bridge from exactly the two remaining
selector inputs. -/
def noInverseMinSeqQuotientTransportBridge_from_selectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (data : Property4NoInverseMinLawSelectorExactData S) :
    Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge S where
  no_inverse_minseq_transport_laws :=
    noInverseMinSeqTransportCoreLaws_from_selectorExact S data
  g96_bridge := data.g96_bridge
  source_line735_min_transport_no_inverse_totalization :=
    data.source_line735_and_line743_generated_from_exact_selector_pair
  source_line743_shifted_min_transport_no_inverse_totalization :=
    data.source_line735_and_line743_generated_from_exact_selector_pair
  remaining_global_rep_selector_frontier := True
  remaining_pos_eventually_selector_frontier := True

/-- Property-(4) reduction data whose min-law part is obtained from the exact
selector pair, rather than from a pre-supplied transport law bundle. -/
structure Property4ReductionDataFromSelectorExactNoInverseMinLawBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g96_data :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r
  global_rep_selector :
    ∀ x : CRealQuot, CRealQuotRepWitness x
  pos_eventually_selector :
    CRealPosEventuallySelector
  source_property4_min_laws_generated_from_exact_selector_pair : Prop
  source_no_positive_inverse_totalization_input_for_min_laws : Prop

/-- Extract the selector-exact bridge data from the property-(4) reduction
record. -/
def selectorExactData_from_reductionData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r) :
    Property4NoInverseMinLawSelectorExactData S where
  g96_bridge := data.g96_data.scalar_min_kernel_bridge
  global_rep_selector := data.global_rep_selector
  pos_eventually_selector := data.pos_eventually_selector
  source_line735_and_line743_generated_from_exact_selector_pair :=
    data.source_property4_min_laws_generated_from_exact_selector_pair
  source_positive_inverse_totalization_removed_from_selector_exact_route :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

/-- Convert the selector-exact reduction data into the G102 no-inverse
reduction layer. -/
def property4NoInverseTotalizationData_from_selectorExact
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r) :
    Property4ReductionDataFromNoInverseTotalizationBridge S r where
  g96_data := data.g96_data
  no_inverse_bridge :=
    noInverseMinSeqQuotientTransportBridge_from_selectorExact
      S
      (selectorExactData_from_reductionData S r data)
  source_property4_reduction_uses_no_inverse_totalization_for_min_laws :=
    data.source_no_positive_inverse_totalization_input_for_min_laws

/-- Theorem 1.18 property (4), with the min-law part obtained from the exact
remaining selector pair and with no positive-inverse totalization input. -/
def property4_from_selector_exact_no_inverse_min_laws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromSelectorExactNoInverseMinLawBridge S r) :
    Property4Conclusion S r :=
  property4_from_no_inverse_totalization_min_laws
    S r
    (property4NoInverseTotalizationData_from_selectorExact S r data)

end BishopRegularSeqTheorem118

/-- G103 package. -/
structure BishopRegularSeqTheorem118G103Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g102_package_available : Prop
  selector_exact_data : Type 4
  selector_exact_bridge :
    selector_exact_data ->
      BishopRegularSeqTheorem118.Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge
        S
  selector_exact_reduction_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_selector_exact_no_inverse :
    forall r : BishopRegularSeqIntegrableRep S,
      selector_exact_reduction_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  remaining_selector_count_for_min_laws : Nat
  source_frontier_exactly_global_rep_and_pos_eventually : Prop
  positive_inverse_totalization_not_part_of_min_frontier : Prop

def bishopRegularSeqTheorem118G103Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G103Package S where
  g102_package_available := True
  selector_exact_data :=
    BishopRegularSeqTheorem118.Property4NoInverseMinLawSelectorExactData S
  selector_exact_bridge := fun data =>
    BishopRegularSeqTheorem118.noInverseMinSeqQuotientTransportBridge_from_selectorExact
      S data
  selector_exact_reduction_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromSelectorExactNoInverseMinLawBridge
      S
  property4_from_selector_exact_no_inverse := fun r data =>
    BishopRegularSeqTheorem118.property4_from_selector_exact_no_inverse_min_laws
      S r data
  remaining_selector_count_for_min_laws := 2
  source_frontier_exactly_global_rep_and_pos_eventually := True
  positive_inverse_totalization_not_part_of_min_frontier := True

/-- Progress after G103: the min-law data interface now exposes exactly the
two remaining selector inputs. -/
def bishopRegularSeqCh1To4ProgressAfterG103 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G103: generated the G102 no-inverse min-law bridge from exactly the \
    global quotient representative selector plus the PosEventually selector."


end BishopCReal
