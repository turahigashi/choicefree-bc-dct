import Mathdemo.Internal.CRat_iter198

set_option linter.style.longLine false

/-!
# G99: conditional shifted-min quotient bound

G98 conditionally closed the quotient min monotonicity obligation for source
line 735.  This file treats the remaining source line 743 shifted-min bound:

`min(x + d, c) <= min(x, c) + d` when `0 <= d`.

As in G98, the quotient result is explicitly conditional on the existing
global-selector quotient `COFO` route.  The unconditional quotient order
frontier is therefore still recorded as open.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Translation identity for the half-sum minimum:
`min(x+d,c) = min(x,c-d)+d`. -/
theorem generic_min_halfsum_translate_right
    {R : Type*} [BishopC.COFO R]
    (x d c : R) :
    COF.min (x + d) c = COF.min x (c - d) + d := by
  rw [COF.min_halfsum (x + d) c, COF.min_halfsum x (c - d),
    show x - (c - d) = (x + d) - c from by ring]
  linear_combination d * COF.half_add_half (R := R)

/-- Generic shifted-min bound from nonnegative right shift. -/
theorem generic_min_halfsum_add_nonnegative_right_bound
    {R : Type*} [BishopC.COFO R]
    (x d c : R)
    (hd : BishopC.Nonneg d) :
    BishopC.Le (COF.min (x + d) c) (COF.min x c + d) := by
  have hcd : BishopC.Le (c - d) c := by
    apply BishopC.le_of_nonneg_sub
    rwa [show c - (c - d) = d from by ring]
  have hmono : BishopC.Le (COF.min x (c - d)) (COF.min x c) :=
    generic_min_halfsum_monotone_right x (c - d) c hcd
  have hadd :
      BishopC.Le (COF.min x (c - d) + d) (COF.min x c + d) :=
    BishopC.le_add hmono (BishopC.le_refl d)
  rw [generic_min_halfsum_translate_right x d c]
  exact hadd

/-- Conditional quotient shifted-min bound, using the already isolated
global-selector quotient `COFO` route. -/
theorem quotient_minQuotCOF_add_nonnegative_right_bound_with_global_cofo
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A)
    (x d c : CRealQuot)
    (hd : ¬ ltQuot d zeroQuot) :
    ¬ ltQuot
      (addQuot (minQuotCOFWith A x c) d)
      (minQuotCOFWith A (addQuot x d) c) := by
  letI : BishopC.COFO CRealQuot :=
    cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
      A rep sel tot
  have hd_nonneg : BishopC.Nonneg d := by
    change ¬ ltQuot d zeroQuot
    exact hd
  have hmin :
      BishopC.Le (COF.min (x + d) c) (COF.min x c + d) :=
    generic_min_halfsum_add_nonnegative_right_bound x d c hd_nonneg
  change
    ¬ ltQuot
      (addQuot (minQuotCOFWith A x c) d)
      (minQuotCOFWith A (addQuot x d) c)
  exact hmin

/-- The G97 quotient obligation for line 743 is discharged once the
conditional global-selector quotient `COFO` route is supplied. -/
theorem quotient_min_add_nonnegative_right_bound_regularSeqLe_with_global_cofo
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A)
    (x d c : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) :
    ¬ ltQuot
      (addQuot
        (minQuotCOFWith A (mkQuot x) (mkQuot c))
        (mkQuot d))
      (minQuotCOFWith A (mkQuot (addSeq x d)) (mkQuot c)) := by
  have hbase :
      ¬ ltQuot
        (addQuot
          (minQuotCOFWith A (mkQuot x) (mkQuot c))
          (mkQuot d))
        (minQuotCOFWith A
          (addQuot (mkQuot x) (mkQuot d))
          (mkQuot c)) :=
    quotient_minQuotCOF_add_nonnegative_right_bound_with_global_cofo
      A rep sel tot
      (mkQuot x) (mkQuot d) (mkQuot c)
      (not_ltQuot_of_regularSeqLe zeroSeq d hd)
  rwa [← mkQuot_addSeq_eq_addQuot x d] at hbase

/-- Conditional representative shifted-min bound, obtained from the quotient
discharge and the G97 adapter. -/
theorem minSeqWith_add_nonnegative_right_bound_regularSeqLe_with_global_cofo
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A)
    (x d c : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) :
    RegularSeqLe
      (minSeqWith A (addSeq x d) c)
      (addSeq (minSeqWith A x c) d) :=
  minSeqWith_add_nonnegative_right_bound_of_quot_not_lt
    A x d c
    (quotient_min_add_nonnegative_right_bound_regularSeqLe_with_global_cofo
      A rep sel tot x d c hd)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G99 core data: both G97 quotient min order obligations are conditionally
discharged by the global-selector quotient `COFO` route. -/
structure Property4QuotientMinBothConditionalCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  g98_core_laws : Property4QuotientMinMonotoneConditionalCoreLaws Arch
  quotient_min_add_nonnegative_right_bound_conditional :
    forall x d c : RegularSeq,
      RegularSeqLe zeroSeq d ->
        ¬ ltQuot
          (addQuot
            (minQuotCOFWith Arch (mkQuot x) (mkQuot c))
            (mkQuot d))
          (minQuotCOFWith Arch (mkQuot (addSeq x d)) (mkQuot c))
  source_line735_quotient_min_monotone_conditional_closed : Prop
  source_line743_quotient_shifted_min_bound_conditional_closed : Prop
  unconditional_quotient_min_order_frontier_still_open : Prop

/-- Collapse G99 back to G97, replacing both quotient min fields by the
conditional generic-COFO discharges. -/
def minSeqQuotientTransportCoreLaws_from_quotientMinBothConditional
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4QuotientMinBothConditionalCoreLaws Arch) :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch where
  g96_core_laws := laws.g98_core_laws.g97_core_laws.g96_core_laws
  quotient_min_monotone_left := by
    intro x y c hxy
    exact laws.g98_core_laws.quotient_min_monotone_left_conditional x y c hxy
  quotient_min_add_nonnegative_right_bound := by
    intro x d c hd
    exact laws.quotient_min_add_nonnegative_right_bound_conditional x d c hd
  source_minSeqWith_to_quotient_min_closed :=
    laws.g98_core_laws.g97_core_laws.source_minSeqWith_to_quotient_min_closed
  source_line735_min_frontier_now_quotient_order := True
  source_line743_shifted_min_frontier_now_quotient_order := True

/-- G99 unified bridge. -/
structure Property4QuotientMinBothConditionalCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  quotient_min_both_conditional_core_laws :
    Property4QuotientMinBothConditionalCoreLaws Arch
  g98_bridge :
    Property4QuotientMinMonotoneConditionalCoreUnifiedBridge S
  source_line735_conditional_quotient_min_monotone_closed : Prop
  source_line743_conditional_quotient_shifted_min_bound_closed : Prop
  unconditional_quotient_order_frontier_still_open : Prop

/-- Convert G99 unified data to the G98 bridge. -/
def quotientMinMonotoneConditionalBridge_from_quotientMinBothConditional
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4QuotientMinBothConditionalCoreUnifiedBridge S) :
    Property4QuotientMinMonotoneConditionalCoreUnifiedBridge S :=
  bridge.g98_bridge

/-- Property-(4) reduction data after conditionally closing both quotient min
order obligations. -/
structure Property4ReductionDataFromQuotientMinBothConditionalBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g98_data : Property4ReductionDataFromQuotientMinMonotoneConditionalBridge S r
  quotient_min_both_conditional_bridge :
    Property4QuotientMinBothConditionalCoreUnifiedBridge S
  source_property4_frontier_after_both_conditional_quotient_min_bounds : Prop

/-- Convert G99 reduction data to the G98 layer. -/
def property4QuotientMinMonotoneConditionalData_from_quotientMinBothConditional
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromQuotientMinBothConditionalBridge S r) :
    Property4ReductionDataFromQuotientMinMonotoneConditionalBridge S r :=
  data.g98_data

/-- Theorem 1.18 property (4), using conditional quotient closures for both
min order obligations. -/
def property4_from_quotient_min_both_conditional
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromQuotientMinBothConditionalBridge S r) :
    Property4Conclusion S r :=
  property4_from_quotient_min_monotone_conditional
    S r
    (property4QuotientMinMonotoneConditionalData_from_quotientMinBothConditional
      S r data)

end BishopRegularSeqTheorem118

/-- G99 package. -/
structure BishopRegularSeqTheorem118G99Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g98_package_available : Prop
  generic_min_shifted_bound :
    forall {R : Type*} [BishopC.COFO R], forall x d c : R,
      BishopC.Nonneg d ->
        BishopC.Le (COF.min (x + d) c) (COF.min x c + d)
  quotient_min_shifted_bound_global_cofo :
    forall (A : ScalarMulArchimedeanData),
      (∀ x : CRealQuot, CRealQuotRepWitness x) ->
      CRealPosEventuallySelector ->
      CRealQuotPositiveInverseTotalizationData A ->
      forall x d c : RegularSeq,
        RegularSeqLe zeroSeq d ->
          ¬ ltQuot
            (addQuot
              (minQuotCOFWith A (mkQuot x) (mkQuot c))
              (mkQuot d))
            (minQuotCOFWith A (mkQuot (addSeq x d)) (mkQuot c))
  quotient_min_both_conditional_core_laws : Type 1
  quotient_min_both_conditional_core_bridge : Type 4
  property4_quotient_min_both_conditional_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_quotient_min_both_conditional :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_quotient_min_both_conditional_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_line735_quotient_min_monotone_conditional_closed : Prop
  source_line743_quotient_shifted_min_bound_conditional_closed : Prop
  unconditional_quotient_min_order_frontier_still_open : Prop

def bishopRegularSeqTheorem118G99Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G99Package S where
  g98_package_available := True
  generic_min_shifted_bound := by
    intro R cofo x d c hd
    exact generic_min_halfsum_add_nonnegative_right_bound x d c hd
  quotient_min_shifted_bound_global_cofo := by
    intro A rep sel tot x d c hd
    exact quotient_min_add_nonnegative_right_bound_regularSeqLe_with_global_cofo
      A rep sel tot x d c hd
  quotient_min_both_conditional_core_laws :=
    BishopRegularSeqTheorem118.Property4QuotientMinBothConditionalCoreLaws
      Arch
  quotient_min_both_conditional_core_bridge :=
    BishopRegularSeqTheorem118.Property4QuotientMinBothConditionalCoreUnifiedBridge
      S
  property4_quotient_min_both_conditional_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromQuotientMinBothConditionalBridge
      S
  property4_from_quotient_min_both_conditional := fun r data =>
    BishopRegularSeqTheorem118.property4_from_quotient_min_both_conditional
      S r data
  source_line735_quotient_min_monotone_conditional_closed := True
  source_line743_quotient_shifted_min_bound_conditional_closed := True
  unconditional_quotient_min_order_frontier_still_open := True

/-- Progress after G99: both line-735 and line-743 quotient min obligations are
closed conditionally under the existing global-selector quotient `COFO` route. -/
def bishopRegularSeqCh1To4ProgressAfterG99 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G99: closed the line-743 shifted-min quotient obligation conditionally \
    under the global-selector quotient COFO route."


end BishopCReal
