import Mathdemo.Internal.CRat_iter314

set_option linter.style.longLine false

/-!
# G216: Bishop/Bridges located supremum data for Chapter 4.5

Bishop-Bridges (1985) Chapter 2, Definition 4.2 defines a supremum not merely by
order-theoretic least-upper-bound minimality, but by upper-boundedness plus
points of the set arbitrarily close from below.  The previous Chapter 4 frontier
`RangeSupremum` kept only the order-theoretic Prop layer.

This increment adds the Bishop-facing data structure.  The direction used in
the constructive development is:

`LocatedRangeSupremum -> RangeSupremum`

and not the reverse.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

/-- If every dyadic lower cut `a - 2^-k` is strictly below `b`, then
constructively `a <= b`.

This is the order lemma needed to project Bishop's located supremum definition
to the older order-theoretic `RangeSupremum` wrapper. -/
theorem le_of_forall_sub_halfPow_lt
    {R : Type*} [COFO R] {a b : R}
    (h : forall k : Nat, COF.lt (a - COF.halfPow (R := R) k) b) :
    BishopC.Le a b := by
  intro hba
  have hpos : COF.lt 0 (a - b) := by
    have t := BishopC.neg_pos_of_neg (BishopC.sub_neg_of_lt hba)
    rwa [show -(b - a) = a - b from by ring] at t
  obtain ⟨k, hk⟩ := COFO.archimedean_pos (a - b) hpos
  have hb_lower : COF.lt b (a - COF.halfPow (R := R) k) := by
    have t := COF.lt_add_left (b - COF.halfPow (R := R) k) hk
    rwa [show (b - COF.halfPow (R := R) k) + COF.halfPow (R := R) k = b from by ring,
      show (b - COF.halfPow (R := R) k) + (a - b) =
        a - COF.halfPow (R := R) k from by ring] at t
  exact COF.lt_irrefl b (COFO.lt_trans hb_lower (h k))

/-- Bishop/Bridges-style supremum of a range: an upper bound together with
actual range points arbitrarily close from below.  The `approx` field is the
dyadic version of Definition 4.2's `forall eps > 0` clause. -/
structure LocatedRangeSupremum
    {R : Type*} [COFO R] {T : Type*}
    (φ : T -> R) (c : R) : Type _ where
  upper : forall s : T, BishopC.Le (φ s) c
  approx : forall k : Nat,
    { s : T // COF.lt (c - COF.halfPow (R := R) k) (φ s) }

/-- Bishop/Bridges-style infimum of a range, included because Definition 4.2
introduces the dual notion in the same data-carrying form. -/
structure LocatedRangeInfimum
    {R : Type*} [COFO R] {T : Type*}
    (φ : T -> R) (c : R) : Type _ where
  lower : forall s : T, BishopC.Le c (φ s)
  approx : forall k : Nat,
    { s : T // COF.lt (φ s) (c + COF.halfPow (R := R) k) }

/-- Located supremum data projects to the previous order-theoretic wrapper.
The reverse direction is intentionally not provided: it is not constructively
valid in general. -/
theorem locatedRangeSupremum_to_rangeSupremum
    {R : Type*} [COFOC R] {T : Type*}
    {φ : T -> R} {c : R}
    (h : LocatedRangeSupremum φ c) :
    RangeSupremum φ c := by
  constructor
  · exact h.upper
  · intro b hb
    apply le_of_forall_sub_halfPow_lt
    intro k
    exact BishopC.lt_of_lt_of_le (h.approx k).property (hb (h.approx k).val)

/-- Data-carrying version of Lemma 4.5's directed domination hypothesis:
the dominating state `s3` is carried as data rather than hidden behind a Prop
existential. -/
structure Lemma45SourceHypothesisData
    {R : Type*} [COFOC R] {T : Type*}
    (φ ψ : T -> R) : Type _ where
  directed_domination :
    forall s1 s2 : T,
      { s3 : T //
        (BishopC.Le 0 (φ s3 - φ s1) ∧ BishopC.Le (φ s3 - φ s1) (ψ s3 - ψ s1)) ∧
        (BishopC.Le 0 (φ s3 - φ s2) ∧ BishopC.Le (φ s3 - φ s2) (ψ s3 - ψ s2)) }

/-- The data version still implies the previous Prop statement; this is a one-way
forgetful projection. -/
theorem lemma45SourceHypothesisData_to_prop
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R}
    (h : Lemma45SourceHypothesisData φ ψ) :
    Lemma45SourceHypothesis φ ψ := by
  refine ⟨?_⟩
  intro s1 s2
  exact ⟨(h.directed_domination s1 s2).val,
    (h.directed_domination s1 s2).property⟩

/-- Corrected Lemma 4.5 target shape: the input and output suprema are located
suprema.  This replaces the previous thin `RangeSupremum` target as the constructive
main route. -/
def lemma45_located_transfer_target
    {R : Type*} [COFOC R] {T : Type*} (φ ψ : T -> R) : Type _ :=
  Lemma45SourceHypothesisData φ ψ ->
    (Sigma fun cψ : R => LocatedRangeSupremum ψ cψ) ->
      Sigma fun cφ : R => LocatedRangeSupremum φ cφ

/-- Audit for the supremum repair. -/
structure LocatedSupremumRepairAuditAfterG216 : Type where
  bishop_bridges_supremum_definition_used : Nat
  located_supremum_data_added : Nat
  old_rangeSupremum_kept_as_forgetful_wrapper : Nat
  reverse_rangeSupremum_to_locatedSupremum_provided : Nat
  prop_to_data_selector_inputs_added : Nat
  classical_choice_inputs_added : Nat
  remaining_located_sup_seed_obligations : Nat

def locatedSupremumRepairAuditAfterG216 :
    LocatedSupremumRepairAuditAfterG216 where
  bishop_bridges_supremum_definition_used := 1
  located_supremum_data_added := 1
  old_rangeSupremum_kept_as_forgetful_wrapper := 1
  reverse_rangeSupremum_to_locatedSupremum_provided := 0
  prop_to_data_selector_inputs_added := 0
  classical_choice_inputs_added := 0
  remaining_located_sup_seed_obligations := 0

/-- G216 package: Chapter 4.5's supremum interface now has the Bishop-facing
located/data-carrying shape needed before closing 4.5--4.10. -/
structure Chapter4G216LocatedSupremumPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g215 : BishopRegularSeqChapter4G215Package S
  audit : LocatedSupremumRepairAuditAfterG216
  located_supremum_interface_closed_this_step : Nat
  remaining_source_completion_steps_for_4_5_to_4_10 : Nat

def chapter4G216LocatedSupremumPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G216LocatedSupremumPackage S where
  g215 := bishopRegularSeqChapter4G215Package S
  audit := locatedSupremumRepairAuditAfterG216
  located_supremum_interface_closed_this_step := 1
  remaining_source_completion_steps_for_4_5_to_4_10 := 4

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G216.  This reopens the source-complete Chapter 4 route
honestly: Prop.4.12's no-seed route remains closed, while the textbook-order
4.5--4.10 route now has the correct located supremum interface. -/
def bishopRegularSeqChapter4LocatedSupremumProgressAfterG216 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 74
  total_final_goal_percent := 94
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G216: repaired the Chapter 4.5 supremum interface using Bishop/Bridges \
    located supremum data: upper bound plus dyadic near-maximizers. The previous \
    RangeSupremum is now only a forgetful wrapper target; no reverse selector \
    or choice principle was added. Countdown for source-complete 4.5-4.10: 4."


end BishopCReal
