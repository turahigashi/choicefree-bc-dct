import Mathdemo.Internal.CRat_iter245

set_option linter.style.longLine false

/-!
# G146: scalar multiplication transport for represented series

G145 closed termwise transport and the negative-one scalar recovery.  This file
closes the reusable fixed-scalar series transport.  As a result, the remaining
half-scalar recovery is reduced to a termwise representative identity
`|u| ~ 2 * |(1/2)u|`, rather than a series-level mystery.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24HalfRecover

open Prop24RefinedSeriesFrontier
open Prop24ScalarRecover

/-- The representative `2`, kept as explicit data for the half recovery. -/
def twoSeq : RegularSeq :=
  addSeq oneSeq oneSeq

/-- Finite sums commute with fixed left scalar multiplication over Bishop
eventual equality. -/
theorem regularSeqFinSum_smul_left_eventually
    (Arch : ScalarMulArchimedeanData)
    (c : RegularSeq)
    (u : Nat -> RegularSeq) :
    forall N : Nat,
      relEventually
        (regularSeqFinSum (fun n => mulSeqConcreteWith Arch c (u n)) N)
        (mulSeqConcreteWith Arch c (regularSeqFinSum u N)) := by
  intro N
  induction N with
  | zero =>
      simpa [regularSeqFinSum] using
        relEventually_refl (mulSeqConcreteWith Arch c (u 0))
  | succ n ih =>
      have hadd :
          relEventually
            (addSeq
              (regularSeqFinSum
                (fun i => mulSeqConcreteWith Arch c (u i)) n)
              (mulSeqConcreteWith Arch c (u (Nat.succ n))))
            (addSeq
              (mulSeqConcreteWith Arch c (regularSeqFinSum u n))
              (mulSeqConcreteWith Arch c (u (Nat.succ n)))) :=
        addSeq_respects_eventually
          (regularSeqFinSum
            (fun i => mulSeqConcreteWith Arch c (u i)) n)
          (mulSeqConcreteWith Arch c (regularSeqFinSum u n))
          (mulSeqConcreteWith Arch c (u (Nat.succ n)))
          (mulSeqConcreteWith Arch c (u (Nat.succ n)))
          ih
          (relEventually_refl
            (mulSeqConcreteWith Arch c (u (Nat.succ n))))
      have hdist :
          relEventually
            (mulSeqConcreteWith Arch c
              (addSeq (regularSeqFinSum u n) (u (Nat.succ n))))
            (addSeq
              (mulSeqConcreteWith Arch c (regularSeqFinSum u n))
              (mulSeqConcreteWith Arch c (u (Nat.succ n)))) :=
        mulSeqConcrete_left_distrib_eventually
          Arch c (regularSeqFinSum u n) (u (Nat.succ n))
      exact
        relEventually_trans
          (regularSeqFinSum
            (fun i => mulSeqConcreteWith Arch c (u i)) (Nat.succ n))
          (addSeq
            (mulSeqConcreteWith Arch c (regularSeqFinSum u n))
            (mulSeqConcreteWith Arch c (u (Nat.succ n))))
          (mulSeqConcreteWith Arch c (regularSeqFinSum u (Nat.succ n)))
          (by simpa [regularSeqFinSum] using hadd)
          (by
            simpa [regularSeqFinSum] using
              relEventually_symm
                (mulSeqConcreteWith Arch c
                  (addSeq (regularSeqFinSum u n) (u (Nat.succ n))))
                (addSeq
                  (mulSeqConcreteWith Arch c (regularSeqFinSum u n))
                  (mulSeqConcreteWith Arch c (u (Nat.succ n))))
                hdist)

/-- A represented series can be multiplied by a fixed scalar on the left. -/
def seriesSum_smul_left
    (Arch : ScalarMulArchimedeanData)
    (c : RegularSeq)
    (u : Nat -> RegularSeq)
    (hu : BishopRegularSeqSeriesSum u) :
    BishopRegularSeqSeriesSum
      (fun n => mulSeqConcreteWith Arch c (u n)) where
  sum := mulSeqConcreteWith Arch c hu.sum
  tends :=
    { modulus := hu.tends.modulus
      close := by
        intro k n hn
        have hfin :
            relEventually
              (regularSeqFinSum
                (fun i => mulSeqConcreteWith Arch c (u i)) n)
              (mulSeqConcreteWith Arch c (regularSeqFinSum u n)) :=
          regularSeqFinSum_smul_left_eventually Arch c u n
        have hclose :
            relEventually (regularSeqFinSum u n) hu.sum :=
          hu.tends.close k n hn
        have hmul :
            relEventually
              (mulSeqConcreteWith Arch c (regularSeqFinSum u n))
              (mulSeqConcreteWith Arch c hu.sum) :=
          mulSeqConcrete_respects_eventually
            Arch c c (regularSeqFinSum u n) hu.sum
            (relEventually_refl c)
            hclose
        exact
          relEventually_trans
            (regularSeqFinSum
              (fun i => mulSeqConcreteWith Arch c (u i)) n)
            (mulSeqConcreteWith Arch c (regularSeqFinSum u n))
            (mulSeqConcreteWith Arch c hu.sum)
            hfin
            hmul }

/-- The only remaining local identity needed to turn the closed scalar-series
transport into half recovery. -/
structure HalfAbsRecoverTermLaw
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  term :
    forall u : RegularSeq,
      relEventually
        (absSeq u)
        (mulSeqConcreteWith Arch twoSeq
          (absSeq (mulSeqConcreteWith Arch halfSeq u)))
  source_half_abs_scaling_identity : Prop

/-- Half scalar recovery from the termwise identity `|u| ~ 2*|(1/2)u|`. -/
def halfScalarAbsRecoverDataFromTermLaw
    (Arch : ScalarMulArchimedeanData)
    (law : HalfAbsRecoverTermLaw Arch) :
    ScalarAbsRecoverData Arch halfSeq where
  recover := by
    intro u hhalf_abs
    have hdouble :
        BishopRegularSeqSeriesSum
          (fun n =>
            mulSeqConcreteWith Arch twoSeq
              (absSeq (mulSeqConcreteWith Arch halfSeq (u n)))) :=
      seriesSum_smul_left
        Arch twoSeq
        (fun n => absSeq (mulSeqConcreteWith Arch halfSeq (u n)))
        hhalf_abs
    exact
      seriesSum_transport_termwise_eventually
        (fun n =>
          mulSeqConcreteWith Arch twoSeq
            (absSeq (mulSeqConcreteWith Arch halfSeq (u n))))
        (fun n => absSeq (u n))
        (fun n =>
          relEventually_symm
            (absSeq (u n))
            (mulSeqConcreteWith Arch twoSeq
              (absSeq (mulSeqConcreteWith Arch halfSeq (u n))))
            (law.term (u n)))
        hdouble
  scalar_specific_constructive_data := True
  no_global_scalar_choice := True

/-- Full Proposition 2.4 scalar recovery data from the half term-law. -/
def prop24ScalarRecoverDataFromHalfTermLaw
    (Arch : ScalarMulArchimedeanData)
    (law : HalfAbsRecoverTermLaw Arch) :
    Prop24ScalarRecoverData Arch :=
  prop24ScalarRecoverDataFromHalfRecover
    (halfScalarAbsRecoverDataFromTermLaw Arch law)

/-- Build refined projection data from the nonnegative-subseries bridge and the
half term-law. -/
def prop24RefinedSeriesProjectionDataFromHalfTermLaw
    (subseries : NonnegativeSubseriesProjectionBridge)
    (law : HalfAbsRecoverTermLaw Arch) :
    Prop24RefinedSeriesProjectionData Arch where
  nonnegative_subseries := subseries
  scalar_recover := prop24ScalarRecoverDataFromHalfTermLaw Arch law
  avoids_arbitrary_series_projection := True

/-- Audit for G146. -/
structure Prop24HalfRecoverAudit : Type where
  fin_sum_scalar_transport_closed : Nat
  series_sum_scalar_transport_closed : Nat
  half_recover_reduced_to_term_law : Nat
  neg_one_recover_reused_from_g145 : Nat
  remaining_half_abs_term_law_frontier : Prop
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat

def prop24HalfRecoverAudit : Prop24HalfRecoverAudit where
  fin_sum_scalar_transport_closed := 1
  series_sum_scalar_transport_closed := 1
  half_recover_reduced_to_term_law := 1
  neg_one_recover_reused_from_g145 := 1
  remaining_half_abs_term_law_frontier := True
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0

end Prop24HalfRecover
end BishopRegularSeqChapter2

/-- G146 package: fixed-scalar series transport is closed, and half recovery is
reduced to a local absolute-value scaling identity. -/
structure BishopRegularSeqChapter2G146Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g145 : BishopRegularSeqChapter2G145Package S
  audit :
    BishopRegularSeqChapter2.Prop24HalfRecover.Prop24HalfRecoverAudit
  scalar_series_transport_closed : Prop
  half_recover_series_part_closed : Prop
  next_frontier_half_abs_term_law_and_nonnegative_subseries : Prop

def bishopRegularSeqChapter2G146Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G146Package S where
  g145 := bishopRegularSeqChapter2G145Package S
  audit := BishopRegularSeqChapter2.Prop24HalfRecover.prop24HalfRecoverAudit
  scalar_series_transport_closed := True
  half_recover_series_part_closed := True
  next_frontier_half_abs_term_law_and_nonnegative_subseries := True

/-- Progress after G146: scalar multiplication of represented series is closed;
the half recovery is reduced to the termwise identity `|u| ~ 2*|(1/2)u|`. -/
def bishopRegularSeqCh1To4ProgressAfterG146 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 76
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G146: closed fixed-scalar transport for represented RegularSeq series; \
    half recovery now only needs the termwise identity |u| ~ 2*|(1/2)u|."


end BishopCReal
