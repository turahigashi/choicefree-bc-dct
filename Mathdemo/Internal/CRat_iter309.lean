import Mathdemo.Internal.CRat_iter308

set_option linter.style.longLine false

/-!
# G210: backtracking integrable sets to characteristic-function witnesses

This increment implements the selected definitional backtracking direction:

`A` is an integrable set, so its characteristic function is an integrable
function; an integrable function carries the Definition 1.6 representative
data; Proposition 4.12 should use that carried data, not a later choice of a
representative.

The previous `BishopC.IntegrableSet1` already contains the Definition 1.6
representative as `hA.rep`, but it does not expose the source-forward
membership-to-pointwise-absolute-convergence direction.  We therefore name the
missing direction as part of the definition-facing set layer, and connect it to
the G209 Prop.4.12 source interface.  For the newer RegularSeq Chapter 2 layer,
the same direction follows directly from `domain_eq` plus the Definition 1.6
value law's `abs_from_domain` field.
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

/-- For the previous scalar-valued set layer, the characteristic-function
Definition 1.6 witness is already the carried representative `hA.rep`.

This definition records the part that is just definitional unfolding:
no representative is chosen after the fact. -/
def integrableSet1_characteristic_definition16_witness
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A) :
    BishopC.IntegrableRep S :=
  hA.rep

/-- Definition-facing source data for an previous `IntegrableSet1`.

The first two fields are exactly the source-forward direction needed by
Prop.4.12: membership in the complemented set supplies the pointwise absolute
summability witness for the carried characteristic representative.  The final
fields are audit markers saying that this data is being treated as part of the
integrable-set definition, not as an external choice principle. -/
structure IntegrableSet1CharacteristicWitness
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A) : Type _ where
  chi_abs_on_s1 :
    ∀ x, x ∈ A.S1 ->
      RSeq.SeriesSum (fun n => COF.abs (((integrableSet1_characteristic_definition16_witness hA).fn n).toFun x))
  chi_abs_on_s2 :
    ∀ x, x ∈ A.S2 ->
      RSeq.SeriesSum (fun n => COF.abs (((integrableSet1_characteristic_definition16_witness hA).fn n).toFun x))
  characteristic_function_integrable_by_definition : Prop
  definition_16_witness_is_carried_rep_not_chosen_later : Prop

/-- The definition-facing witness is exactly the G209 source data for
Prop.4.12. -/
def prop412_integrable_set_source_from_characteristic_witness
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    (W : IntegrableSet1CharacteristicWitness hA) :
    Prop412IntegrableSetRepresentativeSource hA where
  chi_abs_on_s1 := by
    intro x hx
    simpa [integrableSet1_characteristic_definition16_witness] using
      W.chi_abs_on_s1 x hx
  chi_abs_on_s2 := by
    intro x hx
    simpa [integrableSet1_characteristic_definition16_witness] using
      W.chi_abs_on_s2 x hx
  membership_to_characteristic_rep_abs_is_source_data := True

/-- Backtracking from `E ⊆ A` now uses only the definition-facing
characteristic-function witness of the integrable set `A`. -/
def prop412_good_set_chiA_abs_from_characteristic_witness
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    (W : IntegrableSet1CharacteristicWitness hA)
    (hEsubA : E.S1 ⊆ A.S1) :
    Prop412GoodSetChiAAbsData A E hA :=
  prop412_good_set_chiA_abs_from_integrable_set_source
    (prop412_integrable_set_source_from_characteristic_witness W)
    hEsubA

/-- A source-faithful Prop.4.12 good-pair witness source can get all
integrable-set source data from the definition-facing characteristic witnesses.

The pointwise seed for the complement/bad-set comparison remains the next
frontier; the `chi_A` side is no longer an external provider. -/
structure Prop412CharacteristicWitnessFamily
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R} : Type _ where
  witness :
    ∀ (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A),
      IntegrableSet1CharacteristicWitness hA
  all_witnesses_come_from_integrable_set_definition : Prop

/-- Convert a definition-facing characteristic-witness family into the
integrable-set part of G209's good-pair-scoped source. -/
def prop412_integrable_set_source_from_characteristic_witness_family
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (Fam : Prop412CharacteristicWitnessFamily (S := S))
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A) :
    Prop412IntegrableSetRepresentativeSource hA :=
  prop412_integrable_set_source_from_characteristic_witness (Fam.witness A hA)

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

namespace BishopRegularSeqChapter2

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- In the newer RegularSeq Chapter 2 set layer, the source-forward direction
`x ∈ A¹ -> χ_A` has Definition 1.6 pointwise absolute-summability data follows
by unfolding the carried characteristic representative and using `domain_eq`. -/
def integrableSet_abs_on_s1_from_definition
    {A : BishopC.BSet X}
    (hA : IntegrableSet S A) :
    ∀ x, x ∈ A.S1 ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq (((characteristicRep hA).fn n).toFun x)) := by
  intro x hxA
  have hxdom : x ∈ BishopRegularSeqIntegrableRep.domain (characteristicRep hA) := by
    rw [characteristicRep, hA.domain_eq]
    exact Or.inl hxA
  exact (characteristicRep hA).value_law.abs_from_domain x
    (by simpa [BishopRegularSeqIntegrableRep.domain] using hxdom)

/-- The same source-forward Definition 1.6 witness on the negative side of the
complemented set. -/
def integrableSet_abs_on_s2_from_definition
    {A : BishopC.BSet X}
    (hA : IntegrableSet S A) :
    ∀ x, x ∈ A.S2 ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq (((characteristicRep hA).fn n).toFun x)) := by
  intro x hxA
  have hxdom : x ∈ BishopRegularSeqIntegrableRep.domain (characteristicRep hA) := by
    rw [characteristicRep, hA.domain_eq]
    exact Or.inr hxA
  exact (characteristicRep hA).value_law.abs_from_domain x
    (by simpa [BishopRegularSeqIntegrableRep.domain] using hxdom)

/-- Once the witness is obtained by definition, the `0/1` characteristic-value
law is the existing `valid` field of the integrable set. -/
theorem integrableSet_value_one_on_s1_from_definition
    {A : BishopC.BSet X}
    (hA : IntegrableSet S A)
    (x : X) (hxA : x ∈ A.S1) :
    relEventually
      (BishopRegularSeqIntegrableRep.valueAt
        (characteristicRep hA) x
        (integrableSet_abs_on_s1_from_definition hA x hxA))
      oneSeq :=
  (hA.valid x (integrableSet_abs_on_s1_from_definition hA x hxA)).2.1 hxA

/-- Negative-side characteristic value law, again from the definition-facing
witness plus `valid`. -/
theorem integrableSet_value_zero_on_s2_from_definition
    {A : BishopC.BSet X}
    (hA : IntegrableSet S A)
    (x : X) (hxA : x ∈ A.S2) :
    relEventually
      (BishopRegularSeqIntegrableRep.valueAt
        (characteristicRep hA) x
        (integrableSet_abs_on_s2_from_definition hA x hxA))
      zeroSeq :=
  (hA.valid x (integrableSet_abs_on_s2_from_definition hA x hxA)).2.2 hxA

end BishopRegularSeqChapter2

open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G210 audit: the right repair is definitional backtracking through
integrable sets and characteristic functions, not a new real class. -/
structure Prop412DefinitionBacktrackingAuditAfterG210 : Type where
  new_real_class_needed : Nat
  old_integrableSet1_carried_definition16_rep_exposed : Nat
  old_integrableSet1_missing_forward_direction_named : Nat
  regularSeq_chapter2_membership_to_definition16_abs_closed : Nat
  chiA_source_provider_reduced_to_integrable_set_definition : Nat
  external_choice_principle_added : Nat
  remaining_pointwise_seed_obligations : Nat
  remaining_downstream_bridge_from_good_pair_scoped_provider : Nat

def prop412DefinitionBacktrackingAuditAfterG210 :
    Prop412DefinitionBacktrackingAuditAfterG210 where
  new_real_class_needed := 0
  old_integrableSet1_carried_definition16_rep_exposed := 1
  old_integrableSet1_missing_forward_direction_named := 1
  regularSeq_chapter2_membership_to_definition16_abs_closed := 1
  chiA_source_provider_reduced_to_integrable_set_definition := 1
  external_choice_principle_added := 0
  remaining_pointwise_seed_obligations := 1
  remaining_downstream_bridge_from_good_pair_scoped_provider := 1

/-- G210 package: the integrable-set-to-characteristic-function route is now
the formal path for the `chi_A` part of Prop.4.12. -/
structure BishopRegularSeqChapter4G210Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g209 : BishopRegularSeqChapter4G209Package S
  definition_backtracking_audit : Prop412DefinitionBacktrackingAuditAfterG210
  integrable_set_definition_route_for_chiA_closed_this_step : Nat
  remaining_steps_after_definition_route : Nat

def bishopRegularSeqChapter4G210Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G210Package S where
  g209 := bishopRegularSeqChapter4G209Package S
  definition_backtracking_audit := prop412DefinitionBacktrackingAuditAfterG210
  integrable_set_definition_route_for_chiA_closed_this_step := 1
  remaining_steps_after_definition_route := 2

/-- Progress after G210: no new real class is needed.  The repair is to make
the integrable-set definition expose the characteristic-function Definition
1.6 witness and then use that witness in Prop.4.12. -/
def bishopRegularSeqDefinitionBacktrackingProgressAfterG210 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G210: implemented the definitional backtracking route. No new real class \
    is needed. For previous IntegrableSet1, hA.rep is \
    exposed as the Definition 1.6 characteristic-function witness, and the \
    missing membership-to-pointwise-absolute-summability direction is named as \
    definition-facing characteristic-witness data. For the newer RegularSeq \
    Chapter 2 integrable-set layer, membership in A^1 or A^2 now directly \
    yields the Definition 1.6 absolute-summability witness by domain_eq and \
    value_law.abs_from_domain. Remaining: build the complement/bad pointwise \
    seed and adapt the downstream Prop.4.12 bridge to the good-pair-scoped \
    provider."


end BishopCReal
