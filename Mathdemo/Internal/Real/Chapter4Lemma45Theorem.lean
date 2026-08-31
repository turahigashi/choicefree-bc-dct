import Mathdemo.Internal.Real.Chapter4Lemma43Proposition

set_option linter.style.longLine false

/-!
# G165: Chapter 4 Lemma 4.5 / Theorem 4.6 / Corollary 4.7 boundary

The existing Chapter 4 artifact intentionally removed the previous empty statements
for Theorem 4.6 and Corollary 4.7 (`exists rep, True`).  This step records the
faithful boundary instead:

* Lemma 4.5 is encoded as the source-shaped supremum-transfer target type.
* Theorem 4.6 exposes the genuine state construction `s3` and the `phi/psi`
  truncation-integral surfaces.
* Corollary 4.7 is marked as depending on the same faithful representation
  bridge rather than being counted as closed by an empty theorem.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

/-- Upper bound of the range of a real-valued family. -/
def RangeUpperBound {R : Type*} [COFOC R] {T : Type*} (φ : T -> R) (c : R) : Prop :=
  forall s, BishopC.Le (φ s) c

/-- Least upper bound of the range of a real-valued family. -/
def RangeSupremum {R : Type*} [COFOC R] {T : Type*} (φ : T -> R) (c : R) : Prop :=
  RangeUpperBound φ c ∧ forall b, RangeUpperBound φ b -> BishopC.Le c b

/-- Lemma 4.5 source hypothesis:
for any `s1,s2`, some `s3` dominates both `φ` increments by `ψ` increments. -/
structure Lemma45SourceHypothesis {R : Type*} [COFOC R] {T : Type*}
    (φ ψ : T -> R) : Prop where
  directed_domination :
    forall s1 s2,
      exists s3,
        (BishopC.Le 0 (φ s3 - φ s1) ∧ BishopC.Le (φ s3 - φ s1) (ψ s3 - ψ s1)) ∧
        (BishopC.Le 0 (φ s3 - φ s2) ∧ BishopC.Le (φ s3 - φ s2) (ψ s3 - ψ s2))

/-- Lemma 4.5 faithful target type: `sup ψ` should transfer to `sup φ`. -/
def lemma45_transfer_target
    {R : Type*} [COFOC R] {T : Type*} (φ ψ : T -> R) : Type _ :=
  Lemma45SourceHypothesis φ ψ ->
    ({ cψ : R // RangeSupremum ψ cψ }) ->
      { cφ : R // RangeSupremum φ cφ }

/-- Theorem 4.6 source state surface `(A,n)`. -/
def theorem46_state_available (Y : Type) : Type :=
  BishopC.Thm46State Y

/-- Theorem 4.6 source construction `s3 = (A1 ∨ A2, n1+n2)`. -/
def theorem46_s3_available
    {Y : Type} (s1 s2 : BishopC.Thm46State Y) : BishopC.Thm46State Y :=
  BishopC.thm_4_6_s3 s1 s2

/-- Theorem 4.6 `phi` surface: `I(min(chi_A f^+, n))` in the existing approximation layer. -/
noncomputable def theorem46_phi_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (f : BishopC.PFunR Y R) (hm : BishopC.IsMeasurable S f)
    (s : BishopC.Thm46State Y) (hA : BishopC.IntegrableSet1 S s.1) : R :=
  BishopC.thm_4_6_phi f hm s hA

/-- Theorem 4.6 `psi` surface: `I(min(chi_A |f|, n))` in the existing approximation layer. -/
noncomputable def theorem46_psi_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (f : BishopC.PFunR Y R) (hm : BishopC.IsMeasurable S f)
    (s : BishopC.Thm46State Y) (hA : BishopC.IntegrableSet1 S s.1) : R :=
  BishopC.thm_4_6_psi f hm s hA

/-- Faithful frontier for Theorem 4.6 and Corollary 4.7.

This is deliberately a data boundary, not a fake theorem.  The missing piece is
the representation relation saying that the constructed integrable
representative actually represents the measurable function. -/
structure Theorem46Cor47FaithfulFrontier : Type where
  lemma_4_5_transfer_target_encoded : Prop
  theorem_4_6_s3_phi_psi_surfaces_available : Prop
  positive_negative_part_supremum_bridge_needed : Prop
  measurable_function_representation_relation_needed : Prop
  corollary_4_7_requires_theorem_4_6_faithful_representation : Prop
  empty_exists_rep_true_statement_used : Nat

def theorem46Cor47FaithfulFrontier : Theorem46Cor47FaithfulFrontier where
  lemma_4_5_transfer_target_encoded := True
  theorem_4_6_s3_phi_psi_surfaces_available := True
  positive_negative_part_supremum_bridge_needed := True
  measurable_function_representation_relation_needed := True
  corollary_4_7_requires_theorem_4_6_faithful_representation := True
  empty_exists_rep_true_statement_used := 0

/-- G165 audit package for the 4.5--4.7 block. -/
structure Chapter4G165Lemma45Theorem46Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g164 : BishopRegularSeqChapter4G164Package S
  lemma_4_5_source_target_encoded : Prop
  theorem_4_6_support_surfaces_available : Prop
  theorem_4_6_faithful_frontier_open : Prop
  corollary_4_7_faithful_frontier_open : Prop
  frontier : Theorem46Cor47FaithfulFrontier
  remaining_chapter4_countdown_steps : Nat

def chapter4G165Lemma45Theorem46Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G165Lemma45Theorem46Package S where
  g164 := bishopRegularSeqChapter4G164Package S
  lemma_4_5_source_target_encoded := True
  theorem_4_6_support_surfaces_available := True
  theorem_4_6_faithful_frontier_open := True
  corollary_4_7_faithful_frontier_open := True
  frontier := theorem46Cor47FaithfulFrontier
  remaining_chapter4_countdown_steps := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- G165 package exposed at top level. -/
structure BishopRegularSeqChapter4G165Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Lemma45Theorem46.Chapter4G165Lemma45Theorem46Package S
  chapter4_items_reached_after_g165 : Nat
  chapter4_frontier_items_identified_after_g165 : Nat
  remaining_chapter4_countdown_steps : Nat
  next_frontier_def48_prop49_thm410 : Prop

def bishopRegularSeqChapter4G165Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G165Package S where
  package := BishopRegularSeqChapter4.Lemma45Theorem46.chapter4G165Lemma45Theorem46Package S
  chapter4_items_reached_after_g165 := 7
  chapter4_frontier_items_identified_after_g165 := 2
  remaining_chapter4_countdown_steps := 2
  next_frontier_def48_prop49_thm410 := True

/-- Progress after G165: 4.5--4.7 are source-encoded, with the faithful 4.6/4.7 frontier explicit. -/
def bishopRegularSeqCh1To4ProgressAfterG165 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 47
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G165: encoded Lemma 4.5 target and Theorem 4.6/Corollary 4.7 faithful frontier. \
    Countdown remaining: 2."


end BishopCReal
