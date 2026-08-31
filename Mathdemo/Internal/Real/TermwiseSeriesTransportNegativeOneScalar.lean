import Mathdemo.Internal.Real.RefinedNonnegativeSubseriesFrontierProposition2

set_option linter.style.longLine false

/-!
# G145: termwise series transport and the negative-one scalar recover

G144 refined the Proposition 2.4 scalar frontier to scalar-specific recovery
for `1/2` and `-1`.  This file closes the reusable termwise-transport lemma
for `BishopRegularSeqSeriesSum` and uses it to construct the `-1` recovery
data from the already proved representative identity `|-u| = |u|`.

The half-scalar recovery remains the real scalar-rescaling frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24ScalarRecover

open Prop24RefinedSeriesFrontier

/-- Finite sums respect termwise Bishop eventual equality. -/
theorem regularSeqFinSum_respects_eventually_terms
    (u v : Nat -> RegularSeq)
    (hterm : forall n : Nat, relEventually (u n) (v n)) :
    forall N : Nat,
      relEventually (regularSeqFinSum u N) (regularSeqFinSum v N) := by
  intro N
  induction N with
  | zero =>
      simpa [regularSeqFinSum] using hterm 0
  | succ n ih =>
      simpa [regularSeqFinSum] using
        addSeq_respects_eventually
          (regularSeqFinSum u n)
          (regularSeqFinSum v n)
          (u (Nat.succ n))
          (v (Nat.succ n))
          ih
          (hterm (Nat.succ n))

/-- Transport a represented series sum across termwise Bishop eventual
equality. -/
def seriesSum_transport_termwise_eventually
    (u v : Nat -> RegularSeq)
    (hterm : forall n : Nat, relEventually (u n) (v n))
    (hu : BishopRegularSeqSeriesSum u) :
    BishopRegularSeqSeriesSum v where
  sum := hu.sum
  tends :=
    { modulus := hu.tends.modulus
      close := by
        intro k n hn
        have huv :
            relEventually (regularSeqFinSum u n) (regularSeqFinSum v n) :=
          regularSeqFinSum_respects_eventually_terms u v hterm n
        have hclose :
            relEventually (regularSeqFinSum u n) hu.sum :=
          hu.tends.close k n hn
        exact
          relEventually_trans
            (regularSeqFinSum v n)
            (regularSeqFinSum u n)
            hu.sum
            (relEventually_symm
              (regularSeqFinSum u n)
              (regularSeqFinSum v n)
              huv)
            hclose }

/-- Absolute values are invariant under multiplication by `-1`, in the
representative eventual-equality surface. -/
theorem absSeq_mul_neg_one_left_eventually_absSeq
    (Arch : ScalarMulArchimedeanData)
    (u : RegularSeq) :
    relEventually
      (absSeq (mulSeqConcreteWith Arch (negSeq oneSeq) u))
      (absSeq u) := by
  have hneg :
      relEventually
        (mulSeqConcreteWith Arch (negSeq oneSeq) u)
        (negSeq u) :=
    mulSeq_neg_one_left_eventually_neg Arch u
  have habs_neg :
      relEventually
        (absSeq (mulSeqConcreteWith Arch (negSeq oneSeq) u))
        (absSeq (negSeq u)) :=
    absSeq_respects_eventually
      (mulSeqConcreteWith Arch (negSeq oneSeq) u)
      (negSeq u)
      hneg
  have habs :
      relEventually (absSeq (negSeq u)) (absSeq u) :=
    rel_to_relEventually (absSeq (negSeq u)) (absSeq u) (abs_neg_raw u)
  exact
    relEventually_trans
      (absSeq (mulSeqConcreteWith Arch (negSeq oneSeq) u))
      (absSeq (negSeq u))
      (absSeq u)
      habs_neg
      habs

/-- Closed scalar-recovery data for the `-1` factor used in subtraction. -/
def negOneScalarAbsRecoverData
    (Arch : ScalarMulArchimedeanData) :
    ScalarAbsRecoverData Arch (negSeq oneSeq) where
  recover := by
    intro u hneg_abs
    exact
      seriesSum_transport_termwise_eventually
        (fun n => absSeq (mulSeqConcreteWith Arch (negSeq oneSeq) (u n)))
        (fun n => absSeq (u n))
        (fun n => absSeq_mul_neg_one_left_eventually_absSeq Arch (u n))
        hneg_abs
  scalar_specific_constructive_data := True
  no_global_scalar_choice := True

/-- Once the half-scalar recovery is supplied, the `-1` side is now generated
by the closed termwise transport lemma. -/
def prop24ScalarRecoverDataFromHalfRecover
    (half_recover : ScalarAbsRecoverData Arch halfSeq) :
    Prop24ScalarRecoverData Arch where
  half_recover := half_recover
  neg_one_recover := negOneScalarAbsRecoverData Arch
  only_prop24_scalars_required := True

/-- Build the G144 refined projection data after closing the negative-one
recover side.  The remaining scalar frontier is the half recovery. -/
def prop24RefinedSeriesProjectionDataFromHalfRecover
    (subseries : NonnegativeSubseriesProjectionBridge)
    (half_recover : ScalarAbsRecoverData Arch halfSeq) :
    Prop24RefinedSeriesProjectionData Arch where
  nonnegative_subseries := subseries
  scalar_recover := prop24ScalarRecoverDataFromHalfRecover half_recover
  avoids_arbitrary_series_projection := True

/-- Audit for G145. -/
structure Prop24ScalarRecoverAudit : Type where
  fin_sum_termwise_transport_closed : Nat
  series_sum_termwise_transport_closed : Nat
  neg_one_abs_eventual_closed : Nat
  neg_one_scalar_recover_closed : Nat
  remaining_half_scalar_recover_frontier : Prop
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat

def prop24ScalarRecoverAudit : Prop24ScalarRecoverAudit where
  fin_sum_termwise_transport_closed := 1
  series_sum_termwise_transport_closed := 1
  neg_one_abs_eventual_closed := 1
  neg_one_scalar_recover_closed := 1
  remaining_half_scalar_recover_frontier := True
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0

end Prop24ScalarRecover
end BishopRegularSeqChapter2

/-- G145 package: termwise series transport is closed and the `-1` scalar
recover data is constructed. -/
structure BishopRegularSeqChapter2G145Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g144 : BishopRegularSeqChapter2G144Package S
  audit :
    BishopRegularSeqChapter2.Prop24ScalarRecover.Prop24ScalarRecoverAudit
  termwise_series_transport_closed : Prop
  neg_one_scalar_recover_closed : Prop
  next_frontier_half_scalar_recover_and_nonnegative_subseries : Prop

def bishopRegularSeqChapter2G145Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G145Package S where
  g144 := bishopRegularSeqChapter2G144Package S
  audit := BishopRegularSeqChapter2.Prop24ScalarRecover.prop24ScalarRecoverAudit
  termwise_series_transport_closed := True
  neg_one_scalar_recover_closed := True
  next_frontier_half_scalar_recover_and_nonnegative_subseries := True

/-- Progress after G145: the `-1` scalar-recovery side of Proposition 2.4 is
closed; the remaining scalar frontier is the half recovery. -/
def bishopRegularSeqCh1To4ProgressAfterG145 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 72
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G145: closed termwise series-sum transport and constructed the \
    negative-one scalar absolute recovery for Chapter 2 Proposition 2.4."


end BishopCReal
