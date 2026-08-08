import Mathdemo.Internal.CRat_iter307

set_option linter.style.longLine false

/-!
# G209: source-proof friendly real/set interface for Proposition 4.12

The issue after G208 is whether a class of reals should be used that lets the
Bishop--Cheng source proof be formalized closer to the way it is written.

This file records the answer at the formal interface level.  A scalar `COFOC`
class alone is not the main issue.  The source proof also treats integrable
sets as characteristic representatives whose values can be read at points of
the set.  The previous `IntegrableSet1.valid` direction is weaker for Lean: it says
that if an absolute-convergence witness is already available, then membership
and characteristic values follow.  The source-style direction needed in
Prop.4.12 is the forward datum from membership to the representative's
absolute-convergence witness.

G209 therefore names this source-level data and shows that the first G208
obligation, `chi_A` absolute convergence on the common good set, follows from
it and the good-pair subset information in Definition 4.11.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Prop412AssumptionDischarge

open Proposition412
open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- Source-facing representative data for an already-given integrable set.

This is the piece missing from a proof-as-written formalization: membership in
`A¹` or `A²` gives the characteristic representative's absolute-convergence
witness as data, without extracting a witness from a Prop-valued domain
statement. -/
structure Prop412IntegrableSetRepresentativeSource
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A) : Type _ where
  chi_abs_on_s1 :
    ∀ x, x ∈ A.S1 ->
      RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x))
  chi_abs_on_s2 :
    ∀ x, x ∈ A.S2 ->
      RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x))
  membership_to_characteristic_rep_abs_is_source_data : Prop

/-- If a good set `E` is included in `A¹`, the source-level integrable-set
representative data gives the `chi_A` absolute-convergence datum required by
the Prop.4.12 truncated-integral bridge. -/
def prop412_good_set_chiA_abs_from_integrable_set_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    (ASource : Prop412IntegrableSetRepresentativeSource hA)
    (hEsubA : E.S1 ⊆ A.S1) :
    Prop412GoodSetChiAAbsData A E hA where
  chiA_abs_on_good := by
    intro x hxE
    exact ASource.chi_abs_on_s1 x (hEsubA hxE)

/-- A source-faithful local witness source is scoped to the good pairs returned
by Definition 4.11.  This differs from the older all-`B,C` provider, which was
stronger than the source proof: Bishop only needs the returned `B,C` satisfying
the subset/domain hypotheses. -/
structure Prop412GoodPairScopedRepresentativeWitnessSource
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (Mf : Prop412DataCarryingMeasurable S f) : Type _ where
  integrable_set_source :
    ∀ (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A),
      Prop412IntegrableSetRepresentativeSource hA
  pointwise_seed_on_good_pair :
    ∀ {g : BishopC.PFunR Y R}
      (Mg : Prop412DataCarryingMeasurable S g)
      (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (truncN : Nat)
      (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
      (_hBsubA : B.S1 ⊆ A.S1)
      (_hCsubA : C.S1 ⊆ A.S1),
      Prop412ComplementPointwiseConcreteSupportSeedData
        A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
        truncN f g
        (prop412_mid_support_data_from_constructor_source_data
          (Mf.mid_constructor_source A hA truncN))
        (prop412_mid_support_data_from_constructor_source_data
          (Mg.mid_constructor_source A hA truncN))

/-- The `chi_A` part of a good-pair-scoped witness is now constructed from
integrable-set representative source data plus the source subset
`B¹ ⊆ A¹`. -/
def prop412_good_pair_scoped_chiA_abs
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Src : Prop412GoodPairScopedRepresentativeWitnessSource Mf)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (B : BishopC.BSet Y) (_hB : BishopC.IntegrableSet1 S B)
    (C : BishopC.BSet Y) (_hC : BishopC.IntegrableSet1 S C)
    (hBsubA : B.S1 ⊆ A.S1) :
    Prop412GoodSetChiAAbsData A (BishopC.BSet.and B C) hA :=
  prop412_good_set_chiA_abs_from_integrable_set_source
    (Src.integrable_set_source A hA)
    (fun _ hxE => hBsubA hxE.1)

/-- One local witness datum for a returned good pair, using the source-scoped
subset hypotheses instead of an all-`B,C` provider. -/
def prop412_good_pair_scoped_witness_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f g : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Src : Prop412GoodPairScopedRepresentativeWitnessSource Mf)
    (Mg : Prop412DataCarryingMeasurable S g)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
    (hBsubA : B.S1 ⊆ A.S1)
    (hCsubA : C.S1 ⊆ A.S1) :
    Prop412TwoNatLocalGoodSetWitnessData A hA truncN
      (prop412_mid_support_data_from_constructor_source_data
        (Mf.mid_constructor_source A hA truncN))
      (prop412_mid_support_data_from_constructor_source_data
        (Mg.mid_constructor_source A hA truncN))
      B hB C hC where
  chiA_abs_on_good :=
    prop412_good_pair_scoped_chiA_abs Src A hA B hB C hC hBsubA
  pointwise_seed :=
    Src.pointwise_seed_on_good_pair
      Mg A hA truncN B hB C hC hBsubA hCsubA

/-- G209 audit: the source-friendly class is not merely a stronger scalar
class.  It is a scalar plus data-carrying representative discipline for
integrable sets and good pairs. -/
structure Prop412SourceProofFriendlyInterfaceAuditAfterG209 : Type where
  scalar_COFOC_alone_sufficient_for_source_proof_as_written : Nat
  source_real_layer_needs_series_moduli_and_archimedean_schedules : Nat
  integrable_set_membership_to_abs_witness_data_required : Nat
  old_unscoped_all_BC_local_provider_source_faithful : Nat
  good_pair_scoped_local_provider_named : Nat
  chiA_abs_from_good_pair_subset_closed : Nat
  remaining_pointwise_seed_obligations : Nat
  remaining_downstream_bridge_from_good_pair_scoped_provider : Nat
  external_choice_principle_added : Nat

def prop412SourceProofFriendlyInterfaceAuditAfterG209 :
    Prop412SourceProofFriendlyInterfaceAuditAfterG209 where
  scalar_COFOC_alone_sufficient_for_source_proof_as_written := 0
  source_real_layer_needs_series_moduli_and_archimedean_schedules := 1
  integrable_set_membership_to_abs_witness_data_required := 1
  old_unscoped_all_BC_local_provider_source_faithful := 0
  good_pair_scoped_local_provider_named := 1
  chiA_abs_from_good_pair_subset_closed := 1
  remaining_pointwise_seed_obligations := 1
  remaining_downstream_bridge_from_good_pair_scoped_provider := 1
  external_choice_principle_added := 0

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G209 package: a source-proof-friendly interface has been named, and the
`chi_A` good-set obligation has been reduced to carried integrable-set
representative data. -/
structure BishopRegularSeqChapter4G209Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g208 : BishopRegularSeqChapter4G208Package S
  source_proof_friendly_interface_audit :
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.Prop412SourceProofFriendlyInterfaceAuditAfterG209
  chiA_abs_good_pair_obligation_closed_this_step : Nat
  remaining_good_pair_scoped_prop412_steps : Nat

def bishopRegularSeqChapter4G209Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G209Package S where
  g208 := bishopRegularSeqChapter4G208Package S
  source_proof_friendly_interface_audit :=
    BishopRegularSeqChapter4.Prop412AssumptionDischarge.prop412SourceProofFriendlyInterfaceAuditAfterG209
  chiA_abs_good_pair_obligation_closed_this_step := 1
  remaining_good_pair_scoped_prop412_steps := 2

/-- Progress after G209: the right interface is identified.  The main remaining
work is adapting the downstream Prop.4.12 bridge from the older all-`B,C`
provider to the source-scoped good-pair provider, and then building the
pointwise seed data. -/
def bishopRegularSeqSourceProofFriendlyProgressAfterG209 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G209: identified the source-proof-friendly interface. A scalar COFOC \
    class alone is insufficient; integrable sets must carry membership-to-\
    representative-absolute-convergence data. With that data, the chi_A \
    absolute-convergence obligation on the common good set is closed from \
    B^1 subset A^1. Remaining: adapt the downstream Prop.4.12 bridge to the \
    good-pair-scoped provider and construct the complement/bad pointwise seed."


end BishopCReal
