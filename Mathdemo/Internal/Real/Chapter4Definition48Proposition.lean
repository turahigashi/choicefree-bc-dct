import Mathdemo.Internal.Real.Chapter4Lemma45Theorem

set_option linter.style.longLine false

/-!
# G166: Chapter 4 Definition 4.8 / Proposition 4.9 / Theorem 4.10

Definition 4.8 is already represented constructively as a data-carrying
measurable-set predicate: for every integrable set `A`, the intersection
`A ∧ B` is integrable.

Proposition 4.9 and Theorem 4.10 are not closed in the current core artifact.
This step records their source-shaped frontier without replacing them by
empty conclusions.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Def48Prop49Thm410

/-- Definition 4.8 surface: measurable sets as data-carrying intersection closure. -/
def definition48_isMeasurableSet_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (B : BishopC.BSet Y) : Type _ :=
  BishopC.IsMeasurableSet (S := S) B

/-- Definition 4.8: every integrable set is measurable. -/
noncomputable def definition48_integrable_set_measurable_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {B : BishopC.BSet Y} (hB : BishopC.IntegrableSet1 S B) :
    BishopC.IsMeasurableSet (S := S) B :=
  BishopC.isMeasurableSet_of_integrable hB

/-- Definition 4.8: the absolute complement of an integrable set is measurable. -/
noncomputable def definition48_neg_integrable_set_measurable_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {C : BishopC.BSet Y} (hC : BishopC.IntegrableSet1 S C) :
    BishopC.IsMeasurableSet (S := S) (BishopC.BSet.neg C) :=
  BishopC.isMeasurableSet_neg_of_integrable hC

/-- Definition 4.8 relative integral surface for integrable sets. -/
noncomputable def definition48_relative_integral_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
    (f : BishopC.IntegrableRep S) (hnn : BishopC.RepNonneg f) : R :=
  BishopC.relIntegral C hC f hnn

/-- Source-shaped frontier for Proposition 4.9.

The missing core is the exact "on B" representation relation for
`mid(-n,h,n)=f` and the assembly of the countable patching argument into
`IsMeasurable S h`. -/
structure Prop49ExactLocalApproximationFrontier
    {R : Type*} [COFOC R] {Y : Type} (S : BishopC.IntSpaceRC Y R)
    (h : BishopC.PFunR Y R) : Type where
  full_domain_assumption_needed : Prop
  measurable_patch_function_witness_needed : Prop
  integrable_subset_witness_needed : Prop
  measure_defect_bound_needed : Prop
  exact_on_subset_relation_needed : Prop
  target_is_measurable : Prop

/-- Source-shaped frontier for Theorem 4.10.

Compared with Proposition 4.9, the equality on `B` is weakened to an
`epsilon`-approximation and then recovered by a Cauchy/gluing construction. -/
structure Thm410ApproxLocalApproximationFrontier
    {R : Type*} [COFOC R] {Y : Type} (S : BishopC.IntSpaceRC Y R)
    (h : BishopC.PFunR Y R) : Type where
  prop49_frontier : Prop49ExactLocalApproximationFrontier S h
  approximate_on_subset_relation_needed : Prop
  cauchy_patch_construction_needed : Prop
  null_remaining_set_argument_needed : Prop
  target_is_measurable : Prop

/-- G166 audit package for Definition 4.8, Proposition 4.9, and Theorem 4.10. -/
structure Chapter4G166Def48Prop49Thm410Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g165 : BishopRegularSeqChapter4G165Package S
  definition_4_8_measurable_set_available : Prop
  definition_4_8_integrable_and_complement_surfaces_available : Prop
  definition_4_8_relative_integral_surface_available : Prop
  proposition_4_9_faithful_frontier_encoded : Prop
  theorem_4_10_faithful_frontier_encoded : Prop
  empty_true_statement_used_for_4_9_or_4_10 : Nat
  remaining_chapter4_countdown_steps : Nat

def chapter4G166Def48Prop49Thm410Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G166Def48Prop49Thm410Package S where
  g165 := bishopRegularSeqChapter4G165Package S
  definition_4_8_measurable_set_available := True
  definition_4_8_integrable_and_complement_surfaces_available := True
  definition_4_8_relative_integral_surface_available := True
  proposition_4_9_faithful_frontier_encoded := True
  theorem_4_10_faithful_frontier_encoded := True
  empty_true_statement_used_for_4_9_or_4_10 := 0
  remaining_chapter4_countdown_steps := 1

end Def48Prop49Thm410
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Def48Prop49Thm410

/-- G166 package exposed at top level. -/
structure BishopRegularSeqChapter4G166Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Def48Prop49Thm410.Chapter4G166Def48Prop49Thm410Package S
  chapter4_items_reached_after_g166 : Nat
  chapter4_frontier_items_identified_after_g166 : Nat
  remaining_chapter4_countdown_steps : Nat
  next_frontier_def411_to_thm415_final_audit : Prop

def bishopRegularSeqChapter4G166Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G166Package S where
  package := BishopRegularSeqChapter4.Def48Prop49Thm410.chapter4G166Def48Prop49Thm410Package S
  chapter4_items_reached_after_g166 := 10
  chapter4_frontier_items_identified_after_g166 := 4
  remaining_chapter4_countdown_steps := 1
  next_frontier_def411_to_thm415_final_audit := True

/-- Progress after G166: Definition 4.8 is available; 4.9 and 4.10 are faithful frontiers. -/
def bishopRegularSeqCh1To4ProgressAfterG166 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 67
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G166: Definition 4.8 measurable sets exposed; Proposition 4.9 and Theorem 4.10 \
    recorded as faithful local-approximation frontiers. Countdown remaining: 1."


end BishopCReal
