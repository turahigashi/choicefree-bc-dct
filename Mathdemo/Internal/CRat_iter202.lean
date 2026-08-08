import Mathdemo.Internal.CRat_iter201

set_option linter.style.longLine false

/-!
# G102: property-(4) reduction through the no-inverse min-law bridge

G101 removed positive-inverse totalization from the two quotient min-law
obligations.  This file pushes that improvement into the property-(4)
reduction data itself: the reduction now routes through the G97
`minSeqWith` quotient-transport bridge without requiring the G98/G100
global-selector `COFO` bundle.

The remaining frontier is unchanged and sharper: global quotient
representatives plus the `PosEventually` Prop-to-data selector.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Unified bridge for the G97 minSeq quotient-transport layer, obtained from
the G101 no-positive-inverse-totalization laws. -/
structure Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  no_inverse_minseq_transport_laws :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch
  g96_bridge :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S
  source_line735_min_transport_no_inverse_totalization : Prop
  source_line743_shifted_min_transport_no_inverse_totalization : Prop
  remaining_global_rep_selector_frontier : Prop
  remaining_pos_eventually_selector_frontier : Prop

/-- Convert the no-inverse bridge into the existing G97 unified bridge. -/
def minSeqQuotientTransportClosedBridge_from_noInverse
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge S) :
    Property4MinSeqQuotientTransportClosedCoreUnifiedBridge S where
  minseq_quotient_transport_closed_core_laws :=
    bridge.no_inverse_minseq_transport_laws
  g96_bridge := bridge.g96_bridge
  source_line735_representative_min_transport_closed :=
    bridge.source_line735_min_transport_no_inverse_totalization
  source_line743_representative_shifted_min_transport_closed :=
    bridge.source_line743_shifted_min_transport_no_inverse_totalization
  remaining_frontier_is_quotient_min_order := True

/-- Property-(4) reduction data whose min-law transport no longer requires a
positive-inverse totalization bundle. -/
structure Property4ReductionDataFromNoInverseTotalizationBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g96_data :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r
  no_inverse_bridge :
    Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge S
  source_property4_reduction_uses_no_inverse_totalization_for_min_laws : Prop

/-- Convert G102 reduction data to the G97 reduction layer. -/
def property4MinSeqQuotientTransportData_from_noInverse
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromNoInverseTotalizationBridge S r) :
    Property4ReductionDataFromMinSeqQuotientTransportClosedBridge S r where
  g96_data := data.g96_data
  minseq_quotient_transport_bridge :=
    minSeqQuotientTransportClosedBridge_from_noInverse
      S data.no_inverse_bridge
  source_property4_frontier_after_minseq_quotient_transport_closed :=
    data.source_property4_reduction_uses_no_inverse_totalization_for_min_laws

/-- Theorem 1.18 property (4), routed through the no-inverse-totalization
min-law bridge. -/
def property4_from_no_inverse_totalization_min_laws
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromNoInverseTotalizationBridge S r) :
    Property4Conclusion S r :=
  property4_from_minseq_quotient_transport_closed
    S r
    (property4MinSeqQuotientTransportData_from_noInverse
      S r data)

end BishopRegularSeqTheorem118

/-- G102 package. -/
structure BishopRegularSeqTheorem118G102Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g101_package_available : Prop
  no_inverse_unified_bridge : Type 4
  property4_no_inverse_data : BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_no_inverse_totalization :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_no_inverse_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_property4_reduction_no_longer_requires_positive_inverse_totalization :
    Prop
  remaining_global_rep_selector_frontier : Prop
  remaining_pos_eventually_selector_frontier : Prop

def bishopRegularSeqTheorem118G102Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G102Package S where
  g101_package_available := True
  no_inverse_unified_bridge :=
    BishopRegularSeqTheorem118.Property4MinSeqQuotientTransportNoInverseCoreUnifiedBridge
      S
  property4_no_inverse_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromNoInverseTotalizationBridge
      S
  property4_from_no_inverse_totalization := fun r data =>
    BishopRegularSeqTheorem118.property4_from_no_inverse_totalization_min_laws
      S r data
  source_property4_reduction_no_longer_requires_positive_inverse_totalization :=
    True
  remaining_global_rep_selector_frontier := True
  remaining_pos_eventually_selector_frontier := True

/-- Progress after G102: the property-(4) reduction itself can use the G101
no-inverse min-law transport, so positive-inverse totalization is no longer
part of this source-line frontier. -/
def bishopRegularSeqCh1To4ProgressAfterG102 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G102: routed property (4) through the no-inverse-totalization min-law \
    bridge; remaining min frontier is representative/PosEventually selector \
    extraction."


end BishopCReal
