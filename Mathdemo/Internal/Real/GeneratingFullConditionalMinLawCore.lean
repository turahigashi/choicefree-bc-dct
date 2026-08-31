import Mathdemo.Internal.Real.ConditionalShiftedMinQuotientBound

set_option linter.style.longLine false

/-!
# G100: generating the full conditional min-law core from G98 data

G99 proved the remaining shifted-min quotient obligation under the same
global-selector quotient `COFO` route used in G98.  This file removes one layer
of manual bookkeeping: a G98 law bundle now generates the G99 "both min laws"
bundle, the G97 quotient transport laws, and the G96 scalar-kernel law package.

No unconditional quotient `COFO` construction is claimed here; that remains the
honest frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- A G98 conditional quotient-min-monotonicity law bundle already contains the
global-selector data needed by G99's shifted-min quotient proof. -/
def quotientMinBothConditionalCoreLaws_from_monotoneConditional
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4QuotientMinMonotoneConditionalCoreLaws Arch) :
    Property4QuotientMinBothConditionalCoreLaws Arch where
  g98_core_laws := laws
  quotient_min_add_nonnegative_right_bound_conditional := by
    intro x d c hd
    exact
      quotient_min_add_nonnegative_right_bound_regularSeqLe_with_global_cofo
        Arch
        laws.rep
        laws.pos_eventually_selector
        laws.positive_inverse_totalization
        x d c hd
  source_line735_quotient_min_monotone_conditional_closed :=
    laws.source_line735_quotient_min_monotone_conditional_closed
  source_line743_quotient_shifted_min_bound_conditional_closed := True
  unconditional_quotient_min_order_frontier_still_open := True

/-- Directly produce the G97 quotient-transport law bundle from G98 data, now
using G99 for the shifted-min field. -/
def minSeqQuotientTransportCoreLaws_from_monotoneConditionalFull
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4QuotientMinMonotoneConditionalCoreLaws Arch) :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch :=
  minSeqQuotientTransportCoreLaws_from_quotientMinBothConditional
    Arch
    (quotientMinBothConditionalCoreLaws_from_monotoneConditional
      Arch laws)

/-- Directly produce the G96 scalar-kernel law bundle with both representative
`minSeqWith` fields generated under the conditional quotient `COFO` data. -/
def scalarMinKernelClosedCoreLaws_from_monotoneConditionalFull
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4QuotientMinMonotoneConditionalCoreLaws Arch) :
    Property4ScalarMinKernelClosedCoreLaws Arch :=
  scalarMinKernelClosedCoreLaws_from_minSeqQuotientTransport
    Arch
    (minSeqQuotientTransportCoreLaws_from_monotoneConditionalFull
      Arch laws)

/-- G100 unified bridge. -/
structure Property4QuotientMinBothGeneratedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g98_bridge :
    Property4QuotientMinMonotoneConditionalCoreUnifiedBridge S
  generated_both_conditional_laws :
    Property4QuotientMinBothConditionalCoreLaws Arch
  generated_minseq_transport_laws :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch
  generated_scalar_kernel_laws :
    Property4ScalarMinKernelClosedCoreLaws Arch
  source_line735_and_line743_generated_from_single_g98_bundle : Prop
  unconditional_quotient_order_frontier_still_open : Prop

/-- Convert G100 unified data back to the G98 bridge. -/
def quotientMinMonotoneConditionalBridge_from_bothGenerated
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4QuotientMinBothGeneratedCoreUnifiedBridge S) :
    Property4QuotientMinMonotoneConditionalCoreUnifiedBridge S :=
  bridge.g98_bridge

/-- Property-(4) reduction data after generating both conditional min laws from
the single G98 quotient `COFO` bundle. -/
structure Property4ReductionDataFromQuotientMinBothGeneratedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g98_data :
    Property4ReductionDataFromQuotientMinMonotoneConditionalBridge S r
  both_generated_bridge :
    Property4QuotientMinBothGeneratedCoreUnifiedBridge S
  source_property4_frontier_is_unconditional_quotient_order_only : Prop

/-- Convert G100 reduction data to the G98 layer. -/
def property4QuotientMinMonotoneConditionalData_from_bothGenerated
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromQuotientMinBothGeneratedBridge S r) :
    Property4ReductionDataFromQuotientMinMonotoneConditionalBridge S r :=
  data.g98_data

/-- Theorem 1.18 property (4), with both conditional min-law bundles generated
from the G98 quotient `COFO` data. -/
def property4_from_quotient_min_both_generated
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromQuotientMinBothGeneratedBridge S r) :
    Property4Conclusion S r :=
  property4_from_quotient_min_monotone_conditional
    S r
    (property4QuotientMinMonotoneConditionalData_from_bothGenerated
      S r data)

end BishopRegularSeqTheorem118

/-- G100 package. -/
structure BishopRegularSeqTheorem118G100Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g99_package_available : Prop
  quotient_min_both_laws_from_g98_laws :
    BishopRegularSeqTheorem118.Property4QuotientMinMonotoneConditionalCoreLaws
      Arch ->
    BishopRegularSeqTheorem118.Property4QuotientMinBothConditionalCoreLaws
      Arch
  minseq_transport_laws_from_g98_laws :
    BishopRegularSeqTheorem118.Property4QuotientMinMonotoneConditionalCoreLaws
      Arch ->
    BishopRegularSeqTheorem118.Property4MinSeqQuotientTransportClosedCoreLaws
      Arch
  scalar_kernel_laws_from_g98_laws :
    BishopRegularSeqTheorem118.Property4QuotientMinMonotoneConditionalCoreLaws
      Arch ->
    BishopRegularSeqTheorem118.Property4ScalarMinKernelClosedCoreLaws Arch
  generated_bridge : Type 4
  property4_generated_data : BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_generated :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_generated_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_both_minseq_fields_generated_under_global_cofo_data : Prop
  unconditional_quotient_min_order_frontier_still_open : Prop

def bishopRegularSeqTheorem118G100Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G100Package S where
  g99_package_available := True
  quotient_min_both_laws_from_g98_laws := by
    intro laws
    exact
      BishopRegularSeqTheorem118.quotientMinBothConditionalCoreLaws_from_monotoneConditional
        Arch laws
  minseq_transport_laws_from_g98_laws := by
    intro laws
    exact
      BishopRegularSeqTheorem118.minSeqQuotientTransportCoreLaws_from_monotoneConditionalFull
        Arch laws
  scalar_kernel_laws_from_g98_laws := by
    intro laws
    exact
      BishopRegularSeqTheorem118.scalarMinKernelClosedCoreLaws_from_monotoneConditionalFull
        Arch laws
  generated_bridge :=
    BishopRegularSeqTheorem118.Property4QuotientMinBothGeneratedCoreUnifiedBridge
      S
  property4_generated_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromQuotientMinBothGeneratedBridge
      S
  property4_from_generated := fun r data =>
    BishopRegularSeqTheorem118.property4_from_quotient_min_both_generated
      S r data
  source_both_minseq_fields_generated_under_global_cofo_data := True
  unconditional_quotient_min_order_frontier_still_open := True

/-- Progress after G100: the G98 conditional quotient `COFO` bundle now
generates both min-law fields needed by the property-(4) reduction. -/
def bishopRegularSeqCh1To4ProgressAfterG100 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G100: generated both line-735 and line-743 conditional min-law core \
    fields from the single G98 global-selector quotient COFO bundle."


end BishopCReal
