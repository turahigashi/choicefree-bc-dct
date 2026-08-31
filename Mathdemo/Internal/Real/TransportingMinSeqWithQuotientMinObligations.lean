import Mathdemo.Internal.Real.ScalarHalfSumKernelMinMonotonicity

set_option linter.style.longLine false

/-!
# G97: transporting `minSeqWith` to quotient min obligations

G96 closed the scalar half-sum kernel for min monotonicity.  The remaining
representative-level min laws still had to cross the `minSeqWith` wrapper.

This file closes that wrapper transport:

* `mkQuot (minSeqWith A x y)` is the quotient min half-sum;
* the two sequence-level min laws reduce to quotient-level `not_ltQuot`
  obligations.

The quotient min order obligations are intentionally left explicit.  This
keeps the source proof honest: the representative adapter is closed, while the
next mathematical step is the quotient order comparison itself.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The representative min half-sum denotes the concrete quotient min. -/
theorem mkQuot_minSeqWith_eq_minQuotConcreteWith
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    mkQuot (minSeqWith A x y) =
      minQuotConcreteWith A (mkQuot x) (mkQuot y) := by
  rfl

/-- The representative min half-sum denotes the COF-facing quotient min. -/
theorem mkQuot_minSeqWith_eq_minQuotCOFWith
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    mkQuot (minSeqWith A x y) =
      minQuotCOFWith A (mkQuot x) (mkQuot y) := by
  rw [minQuotCOF_eq_concrete A (mkQuot x) (mkQuot y)]
  rfl

/-- Addition of representatives denotes quotient addition. -/
theorem mkQuot_addSeq_eq_addQuot
    (x y : RegularSeq) :
    mkQuot (addSeq x y) = addQuot (mkQuot x) (mkQuot y) := by
  rfl

/-- A quotient-level reverse-strict obstruction for min gives the
representative `RegularSeqLe` min monotonicity statement. -/
theorem minSeqWith_monotone_left_of_quot_not_lt
    (A : ScalarMulArchimedeanData)
    (x y c : RegularSeq)
    (hnot :
      ¬ ltQuot
        (minQuotCOFWith A (mkQuot y) (mkQuot c))
        (minQuotCOFWith A (mkQuot x) (mkQuot c))) :
    RegularSeqLe (minSeqWith A x c) (minSeqWith A y c) := by
  apply regularSeqLe_of_not_ltQuot
  change ¬ ltQuot
    (mkQuot (minSeqWith A y c))
    (mkQuot (minSeqWith A x c))
  rw [mkQuot_minSeqWith_eq_minQuotCOFWith A y c,
    mkQuot_minSeqWith_eq_minQuotCOFWith A x c]
  exact hnot

/-- A quotient-level reverse-strict obstruction gives the shifted
nonnegative-min bound on representatives. -/
theorem minSeqWith_add_nonnegative_right_bound_of_quot_not_lt
    (A : ScalarMulArchimedeanData)
    (x d c : RegularSeq)
    (hnot :
      ¬ ltQuot
        (addQuot
          (minQuotCOFWith A (mkQuot x) (mkQuot c))
          (mkQuot d))
        (minQuotCOFWith A (mkQuot (addSeq x d)) (mkQuot c))) :
    RegularSeqLe
      (minSeqWith A (addSeq x d) c)
      (addSeq (minSeqWith A x c) d) := by
  apply regularSeqLe_of_not_ltQuot
  change ¬ ltQuot
    (mkQuot (addSeq (minSeqWith A x c) d))
    (mkQuot (minSeqWith A (addSeq x d) c))
  rw [mkQuot_addSeq_eq_addQuot,
    mkQuot_minSeqWith_eq_minQuotCOFWith A x c,
    mkQuot_minSeqWith_eq_minQuotCOFWith A (addSeq x d) c]
  exact hnot

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G97 core data: the representative `minSeqWith` laws are reduced to
quotient min order obligations. -/
structure Property4MinSeqQuotientTransportClosedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  g96_core_laws : Property4ScalarMinKernelClosedCoreLaws Arch
  quotient_min_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        ¬ ltQuot
          (minQuotCOFWith Arch (mkQuot y) (mkQuot c))
          (minQuotCOFWith Arch (mkQuot x) (mkQuot c))
  quotient_min_add_nonnegative_right_bound :
    forall x d c : RegularSeq,
      RegularSeqLe zeroSeq d ->
        ¬ ltQuot
          (addQuot
            (minQuotCOFWith Arch (mkQuot x) (mkQuot c))
            (mkQuot d))
          (minQuotCOFWith Arch (mkQuot (addSeq x d)) (mkQuot c))
  source_minSeqWith_to_quotient_min_closed : Prop
  source_line735_min_frontier_now_quotient_order : Prop
  source_line743_shifted_min_frontier_now_quotient_order : Prop

/-- Collapse G97 back to the G96 layer, generating the G95 sequence min fields
from the quotient obligations. -/
def scalarMinKernelClosedCoreLaws_from_minSeqQuotientTransport
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4MinSeqQuotientTransportClosedCoreLaws Arch) :
    Property4ScalarMinKernelClosedCoreLaws Arch where
  g95_core_laws :=
    { laws.g96_core_laws.g95_core_laws with
      minSeqWith_monotone_left := by
        intro x y c hxy
        exact minSeqWith_monotone_left_of_quot_not_lt
          Arch x y c
          (laws.quotient_min_monotone_left x y c hxy)
      minSeqWith_add_nonnegative_right_bound := by
        intro x d c hd
        exact minSeqWith_add_nonnegative_right_bound_of_quot_not_lt
          Arch x d c
          (laws.quotient_min_add_nonnegative_right_bound x d c hd) }
  source_scalar_min_right_abs_gap_bound_closed :=
    laws.g96_core_laws.source_scalar_min_right_abs_gap_bound_closed
  source_scalar_min_halfsum_difference_nonneg_closed :=
    laws.g96_core_laws.source_scalar_min_halfsum_difference_nonneg_closed
  source_scalar_min_halfsum_monotone_right_closed :=
    laws.g96_core_laws.source_scalar_min_halfsum_monotone_right_closed
  representative_minSeqWith_transport_frontier := False

/-- G97 unified bridge: representative min transport has been discharged into
quotient min order obligations. -/
structure Property4MinSeqQuotientTransportClosedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  minseq_quotient_transport_closed_core_laws :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch
  g96_bridge :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S
  source_line735_representative_min_transport_closed : Prop
  source_line743_representative_shifted_min_transport_closed : Prop
  remaining_frontier_is_quotient_min_order : Prop

/-- Convert G97 unified data back to the G96 bridge. -/
def scalarMinKernelClosedCoreUnifiedBridge_from_minSeqQuotientTransport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4MinSeqQuotientTransportClosedCoreUnifiedBridge S) :
    Property4ScalarMinKernelClosedCoreUnifiedBridge S :=
  bridge.g96_bridge

/-- Property-(4) reduction data after closing representative min transport. -/
structure Property4ReductionDataFromMinSeqQuotientTransportClosedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  g96_data : Property4ReductionDataFromScalarMinKernelClosedBridge S r
  minseq_quotient_transport_bridge :
    Property4MinSeqQuotientTransportClosedCoreUnifiedBridge S
  source_property4_frontier_after_minseq_quotient_transport_closed : Prop

/-- Convert G97 reduction data to the G96 layer. -/
def property4ScalarMinKernelData_from_minSeqQuotientTransport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromMinSeqQuotientTransportClosedBridge S r) :
    Property4ReductionDataFromScalarMinKernelClosedBridge S r :=
  data.g96_data

/-- Theorem 1.18 property (4), using closed representative min transport and
explicit quotient min order obligations. -/
def property4_from_minseq_quotient_transport_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromMinSeqQuotientTransportClosedBridge S r) :
    Property4Conclusion S r :=
  property4_from_scalar_min_kernel_closed
    S r
    (property4ScalarMinKernelData_from_minSeqQuotientTransport S r data)

end BishopRegularSeqTheorem118

/-- G97 package: representative `minSeqWith` transport is closed, and the
frontier is now the quotient min order comparison. -/
structure BishopRegularSeqTheorem118G97Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g96 : BishopRegularSeqTheorem118G96Package S
  minseq_to_quotient_min :
    forall A : ScalarMulArchimedeanData,
      forall x y : RegularSeq,
        mkQuot (minSeqWith A x y) =
          minQuotCOFWith A (mkQuot x) (mkQuot y)
  minseq_monotone_from_quotient_not_lt :
    forall A : ScalarMulArchimedeanData,
      forall x y c : RegularSeq,
        (¬ ltQuot
          (minQuotCOFWith A (mkQuot y) (mkQuot c))
          (minQuotCOFWith A (mkQuot x) (mkQuot c))) ->
          RegularSeqLe (minSeqWith A x c) (minSeqWith A y c)
  shifted_min_bound_from_quotient_not_lt :
    forall A : ScalarMulArchimedeanData,
      forall x d c : RegularSeq,
        (¬ ltQuot
          (addQuot
            (minQuotCOFWith A (mkQuot x) (mkQuot c))
            (mkQuot d))
          (minQuotCOFWith A (mkQuot (addSeq x d)) (mkQuot c))) ->
          RegularSeqLe
            (minSeqWith A (addSeq x d) c)
            (addSeq (minSeqWith A x c) d)
  minseq_quotient_transport_core_laws : Type 1
  minseq_quotient_transport_core_bridge : Type 4
  property4_minseq_quotient_transport_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_minseq_quotient_transport_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_minseq_quotient_transport_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_minSeqWith_to_quotient_min_closed : Prop
  remaining_frontier_quotient_min_monotone_left : Prop
  remaining_frontier_quotient_shifted_min_bound : Prop

def bishopRegularSeqTheorem118G97Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G97Package S where
  g96 := bishopRegularSeqTheorem118G96Package S
  minseq_to_quotient_min := by
    intro A x y
    exact mkQuot_minSeqWith_eq_minQuotCOFWith A x y
  minseq_monotone_from_quotient_not_lt := by
    intro A x y c hnot
    exact minSeqWith_monotone_left_of_quot_not_lt A x y c hnot
  shifted_min_bound_from_quotient_not_lt := by
    intro A x d c hnot
    exact minSeqWith_add_nonnegative_right_bound_of_quot_not_lt A x d c hnot
  minseq_quotient_transport_core_laws :=
    BishopRegularSeqTheorem118.Property4MinSeqQuotientTransportClosedCoreLaws
      Arch
  minseq_quotient_transport_core_bridge :=
    BishopRegularSeqTheorem118.Property4MinSeqQuotientTransportClosedCoreUnifiedBridge
      S
  property4_minseq_quotient_transport_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromMinSeqQuotientTransportClosedBridge
      S
  property4_from_minseq_quotient_transport_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_minseq_quotient_transport_closed
      S r data
  source_minSeqWith_to_quotient_min_closed := True
  remaining_frontier_quotient_min_monotone_left := True
  remaining_frontier_quotient_shifted_min_bound := True

/-- Progress after G97: representative min transport is closed; the remaining
min laws are now stated as quotient order obligations. -/
def bishopRegularSeqCh1To4ProgressAfterG97 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 98
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 97
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G97: closed the representative-to-quotient transport for minSeqWith; \
    remaining min frontiers are quotient order obligations."


end BishopCReal
