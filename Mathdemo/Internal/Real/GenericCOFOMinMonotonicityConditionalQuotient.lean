import Mathdemo.Internal.Real.TransportingMinSeqWithQuotientMinObligations

set_option linter.style.longLine false

/-!
# G98: generic COFO min monotonicity and conditional quotient discharge

G97 reduced the representative `minSeqWith` monotonicity law to a quotient
order obligation.  This file proves the source half-sum min monotonicity in
the generic `COFO` interface, then applies it to the existing conditional live
quotient `COFO` route.

The quotient result is explicitly conditional on the previously isolated
global representative selector, `PosEventually` selector, and positive-inverse
totalization data.  Thus it is not reported as an unconditional solution of
the quotient frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Generic half-sum proof that min is monotone in its second argument. -/
theorem generic_min_halfsum_monotone_right
    {R : Type*} [BishopC.COFO R]
    (s a b : R)
    (h : BishopC.Le a b) :
    BishopC.Le (COF.min s a) (COF.min s b) := by
  apply BishopC.le_of_nonneg_sub
  rw [COF.min_halfsum s a, COF.min_halfsum s b,
    show COF.half * (s + b - COF.abs (s - b)) -
        COF.half * (s + a - COF.abs (s - a)) =
      COF.half * ((b - a) - (COF.abs (s - b) - COF.abs (s - a)))
    from by ring]
  have hrt : BishopC.Le
      (COF.abs (s - b) - COF.abs (s - a))
      (b - a) := by
    have h1 : BishopC.Le
        (COF.abs (s - b) - COF.abs (s - a))
        (COF.abs ((s - b) - (s - a))) :=
      BishopC.le_trans
        (COFO.le_abs_self
          (COF.abs (s - b) - COF.abs (s - a)))
        (BishopC.abs_abs_sub_abs_le (s - b) (s - a))
    rwa [show (s - b) - (s - a) = -(b - a) from by ring,
      COFO.abs_neg,
      COFO.abs_of_nonneg (BishopC.nonneg_sub_of_le h)] at h1
  exact COFO.mul_nonneg
    (BishopC.le_of_lt COFO.half_pos)
    (BishopC.nonneg_sub_of_le hrt)

/-- Generic commutativity of min from the half-sum formula. -/
theorem generic_min_halfsum_comm
    {R : Type*} [BishopC.COFO R]
    (a b : R) :
    COF.min a b = COF.min b a := by
  rw [COF.min_halfsum a b, COF.min_halfsum b a,
    show b - a = -(a - b) from by ring,
    COFO.abs_neg]
  ring

/-- Generic half-sum proof that min is monotone in its first argument. -/
theorem generic_min_halfsum_monotone_left
    {R : Type*} [BishopC.COFO R]
    (a b c : R)
    (h : BishopC.Le a b) :
    BishopC.Le (COF.min a c) (COF.min b c) := by
  rw [generic_min_halfsum_comm a c, generic_min_halfsum_comm b c]
  exact generic_min_halfsum_monotone_right c a b h

/-- Conditional quotient min monotonicity in the first argument, using the
already isolated global-selector quotient `COFO` route. -/
theorem quotient_minQuotCOF_monotone_left_with_global_cofo
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A)
    (x y c : CRealQuot)
    (hxy : ¬ ltQuot y x) :
    ¬ ltQuot
      (minQuotCOFWith A y c)
      (minQuotCOFWith A x c) := by
  letI : BishopC.COFO CRealQuot :=
    cRealQuotCOFOWithGlobalRepPosEventuallySelectorTotalized
      A rep sel tot
  have hle : BishopC.Le x y := by
    change ¬ ltQuot y x
    exact hxy
  have hmin : BishopC.Le (COF.min x c) (COF.min y c) :=
    generic_min_halfsum_monotone_left x y c hle
  change BishopC.Le (COF.min x c) (COF.min y c)
  exact hmin

/-- The G97 quotient obligation for line 735 is discharged once the conditional
global-selector quotient `COFO` route is supplied. -/
theorem quotient_min_monotone_left_regularSeqLe_with_global_cofo
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A)
    (x y c : RegularSeq)
    (hxy : RegularSeqLe x y) :
    ¬ ltQuot
      (minQuotCOFWith A (mkQuot y) (mkQuot c))
      (minQuotCOFWith A (mkQuot x) (mkQuot c)) :=
  quotient_minQuotCOF_monotone_left_with_global_cofo
    A rep sel tot
    (mkQuot x) (mkQuot y) (mkQuot c)
    (not_ltQuot_of_regularSeqLe x y hxy)

/-- Conditional representative min monotonicity, obtained from the quotient
discharge and the G97 adapter. -/
theorem minSeqWith_monotone_left_regularSeqLe_with_global_cofo
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (tot : CRealQuotPositiveInverseTotalizationData A)
    (x y c : RegularSeq)
    (hxy : RegularSeqLe x y) :
    RegularSeqLe (minSeqWith A x c) (minSeqWith A y c) :=
  minSeqWith_monotone_left_of_quot_not_lt
    A x y c
    (quotient_min_monotone_left_regularSeqLe_with_global_cofo
      A rep sel tot x y c hxy)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G98 core data: the line-735 quotient min monotonicity obligation is
conditionally discharged by the global-selector quotient `COFO` route. -/
structure Property4QuotientMinMonotoneConditionalCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  g97_core_laws : Property4MinSeqQuotientTransportClosedCoreLaws Arch
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  pos_eventually_selector : CRealPosEventuallySelector
  positive_inverse_totalization :
    CRealQuotPositiveInverseTotalizationData Arch
  quotient_min_monotone_left_conditional :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        ¬ ltQuot
          (minQuotCOFWith Arch (mkQuot y) (mkQuot c))
          (minQuotCOFWith Arch (mkQuot x) (mkQuot c))
  source_line735_quotient_min_monotone_conditional_closed : Prop
  source_line743_shifted_min_bound_still_frontier : Prop

/-- Collapse G98 back to G97, replacing the line-735 quotient min monotonicity
field by the conditional generic-COFO discharge. -/
def minSeqQuotientTransportCoreLaws_from_quotientMinMonotoneConditional
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4QuotientMinMonotoneConditionalCoreLaws Arch) :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch where
  g96_core_laws := laws.g97_core_laws.g96_core_laws
  quotient_min_monotone_left := by
    intro x y c hxy
    exact laws.quotient_min_monotone_left_conditional x y c hxy
  quotient_min_add_nonnegative_right_bound :=
    laws.g97_core_laws.quotient_min_add_nonnegative_right_bound
  source_minSeqWith_to_quotient_min_closed :=
    laws.g97_core_laws.source_minSeqWith_to_quotient_min_closed
  source_line735_min_frontier_now_quotient_order := True
  source_line743_shifted_min_frontier_now_quotient_order :=
    laws.g97_core_laws.source_line743_shifted_min_frontier_now_quotient_order

/-- G98 unified bridge. -/
structure Property4QuotientMinMonotoneConditionalCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  quotient_min_monotone_conditional_core_laws :
    Property4QuotientMinMonotoneConditionalCoreLaws Arch
  g97_bridge :
    Property4MinSeqQuotientTransportClosedCoreUnifiedBridge S
  source_line735_conditional_quotient_min_monotone_closed : Prop
  remaining_frontier_line743_quotient_shifted_min_bound : Prop

/-- Convert G98 unified data to the G97 bridge. -/
def minSeqQuotientTransportCoreUnifiedBridge_from_quotientMinMonotoneConditional
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4QuotientMinMonotoneConditionalCoreUnifiedBridge S) :
    Property4MinSeqQuotientTransportClosedCoreUnifiedBridge S :=
  bridge.g97_bridge

/-- Property-(4) reduction data after the conditional line-735 quotient min
monotonicity closure. -/
structure Property4ReductionDataFromQuotientMinMonotoneConditionalBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g97_data :
    Property4ReductionDataFromMinSeqQuotientTransportClosedBridge S r
  quotient_min_monotone_conditional_bridge :
    Property4QuotientMinMonotoneConditionalCoreUnifiedBridge S
  source_property4_frontier_after_conditional_quotient_min_monotone : Prop

/-- Convert G98 reduction data to the G97 layer. -/
def property4MinSeqQuotientTransportData_from_quotientMinMonotoneConditional
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromQuotientMinMonotoneConditionalBridge S r) :
    Property4ReductionDataFromMinSeqQuotientTransportClosedBridge S r :=
  data.g97_data

/-- Theorem 1.18 property (4), using the conditional line-735 quotient min
monotonicity bridge and the still-explicit line-743 shifted-min frontier. -/
def property4_from_quotient_min_monotone_conditional
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromQuotientMinMonotoneConditionalBridge S r) :
    Property4Conclusion S r :=
  property4_from_minseq_quotient_transport_closed
    S r
    (property4MinSeqQuotientTransportData_from_quotientMinMonotoneConditional
      S r data)

end BishopRegularSeqTheorem118

/-- G98 package. -/
structure BishopRegularSeqTheorem118G98Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g97 : BishopRegularSeqTheorem118G97Package S
  generic_min_monotone_right :
    forall {R : Type*} [BishopC.COFO R], forall s a b : R,
      BishopC.Le a b -> BishopC.Le (COF.min s a) (COF.min s b)
  generic_min_monotone_left :
    forall {R : Type*} [BishopC.COFO R], forall a b c : R,
      BishopC.Le a b -> BishopC.Le (COF.min a c) (COF.min b c)
  quotient_min_monotone_left_global_cofo :
    forall (A : ScalarMulArchimedeanData),
      (∀ x : CRealQuot, CRealQuotRepWitness x) ->
      CRealPosEventuallySelector ->
      CRealQuotPositiveInverseTotalizationData A ->
      forall x y c : RegularSeq,
        RegularSeqLe x y ->
          ¬ ltQuot
            (minQuotCOFWith A (mkQuot y) (mkQuot c))
            (minQuotCOFWith A (mkQuot x) (mkQuot c))
  quotient_min_monotone_conditional_core_laws : Type 1
  quotient_min_monotone_conditional_core_bridge : Type 4
  property4_quotient_min_monotone_conditional_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_quotient_min_monotone_conditional :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_quotient_min_monotone_conditional_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_line735_quotient_min_monotone_conditional_closed : Prop
  remaining_frontier_line743_quotient_shifted_min_bound : Prop
  unconditional_quotient_min_order_frontier_still_open : Prop

def bishopRegularSeqTheorem118G98Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G98Package S where
  g97 := bishopRegularSeqTheorem118G97Package S
  generic_min_monotone_right := by
    intro R cofo s a b h
    exact generic_min_halfsum_monotone_right s a b h
  generic_min_monotone_left := by
    intro R cofo a b c h
    exact generic_min_halfsum_monotone_left a b c h
  quotient_min_monotone_left_global_cofo := by
    intro A rep sel tot x y c hxy
    exact quotient_min_monotone_left_regularSeqLe_with_global_cofo
      A rep sel tot x y c hxy
  quotient_min_monotone_conditional_core_laws :=
    BishopRegularSeqTheorem118.Property4QuotientMinMonotoneConditionalCoreLaws
      Arch
  quotient_min_monotone_conditional_core_bridge :=
    BishopRegularSeqTheorem118.Property4QuotientMinMonotoneConditionalCoreUnifiedBridge
      S
  property4_quotient_min_monotone_conditional_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromQuotientMinMonotoneConditionalBridge
      S
  property4_from_quotient_min_monotone_conditional := fun r data =>
    BishopRegularSeqTheorem118.property4_from_quotient_min_monotone_conditional
      S r data
  source_line735_quotient_min_monotone_conditional_closed := True
  remaining_frontier_line743_quotient_shifted_min_bound := True
  unconditional_quotient_min_order_frontier_still_open := True

/-- Progress after G98: generic COFO min monotonicity is closed, and the
line-735 quotient min monotonicity obligation is discharged conditionally by
the existing global-selector quotient `COFO` route. -/
def bishopRegularSeqCh1To4ProgressAfterG98 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 98
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G98: closed generic COFO min monotonicity and conditionally discharged \
    the line-735 quotient min monotonicity obligation."


end BishopCReal
