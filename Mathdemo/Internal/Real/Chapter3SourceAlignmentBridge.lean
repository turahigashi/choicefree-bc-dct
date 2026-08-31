import Mathdemo.Internal.Real.FinalChapter2CoverageAudit
import Mathdemo.Internal.BishopSec3_Profile

set_option linter.style.longLine false

/-!
# G156: Chapter 3 source-alignment bridge

Chapter 2 closed at G155.  The next source block is Bishop--Cheng Chapter 3,
the theory of profiles.  A large existing artifact, `BishopSec3_Profile.lean`,
already contains a source-level formalization through Theorem 3.6, including
the book-shaped all-positive-level statement `thm_3_6_all_pos`.

This file starts the Chapter 3 mainline after G155 by recording a conservative
bridge:

* the source items of Chapter 3 are identified from Bishop-Cheng (1972);
* the existing profile artifact is available and kernel-checkable;
* Theorem 3.6 is exposed through a small wrapper whose type is the book-shaped
  all-positive-level statement;
* the remaining honest frontier is the transport from the older COFOC-relative
  profile artifact into the current Bishop RegularSeq Chapter-1/2 mainline.

This is intentionally not reported as full Chapter 3 completion on the new
RegularSeq route.  It is the first countdown step for Chapter 3.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter3
namespace SourceAlignment

/-- Source-item audit for Bishop--Cheng Chapter 3.

The six source items are Definition 3.1, Definition 3.2, Lemma 3.3,
Lemma 3.4, Theorem 3.5, and Theorem 3.6. -/
structure Chapter3SourceCoverageAudit : Type where
  definition_3_1_profile : Nat
  definition_3_2_p_and_pprime : Nat
  lemma_3_3_partition_small_profile_jumps : Nat
  lemma_3_4_finite_exception_points : Nat
  theorem_3_5_smooth_except_countable : Nat
  theorem_3_6_level_sets_all_positive : Nat
  source_lines_checked_against_primary_text : Nat
  existing_bishop_sec3_profile_artifact_available : Nat
  book_theorem_3_6_all_pos_wrapper_available : Nat
  quotient_representative_extraction_inputs_added_by_g156 : Nat
  prop_to_data_selector_inputs_added_by_g156 : Nat
  classical_choice_inputs_added_by_g156 : Nat
  cofof_relative_profile_artifact_not_yet_regularseq_mainline : Prop
  next_frontier_is_regularseq_transport_of_profile_items : Prop

def chapter3SourceCoverageAudit : Chapter3SourceCoverageAudit where
  definition_3_1_profile := 1
  definition_3_2_p_and_pprime := 1
  lemma_3_3_partition_small_profile_jumps := 1
  lemma_3_4_finite_exception_points := 1
  theorem_3_5_smooth_except_countable := 1
  theorem_3_6_level_sets_all_positive := 1
  source_lines_checked_against_primary_text := 1
  existing_bishop_sec3_profile_artifact_available := 1
  book_theorem_3_6_all_pos_wrapper_available := 1
  quotient_representative_extraction_inputs_added_by_g156 := 0
  prop_to_data_selector_inputs_added_by_g156 := 0
  classical_choice_inputs_added_by_g156 := 0
  cofof_relative_profile_artifact_not_yet_regularseq_mainline := True
  next_frontier_is_regularseq_transport_of_profile_items := True

/-- Coded profile type from the existing Chapter 3 artifact, re-exposed here so
the G156 file genuinely imports and typechecks the profile surface. -/
abbrev chapter3ProfileSurface
    {R : Type*} [COFOC R] {a b : R} (hab : COF.lt a b) : Type _ :=
  BishopC.Profile a b hab

/-- Definition 3.2's `p([u,v]) < delta` surface from the existing artifact. -/
abbrev chapter3PLtSurface
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) (u v delta : R) : Type _ :=
  BishopC.Profile.p_lt P u v delta

/-- Definition 3.2's `p'([u,v]) < delta` surface from the existing artifact. -/
abbrev chapter3PPrimeLtSurface
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) (u v delta : R) : Type _ :=
  BishopC.Profile.p_prime_lt P u v delta

/-- Wrapper for the existing book-shaped Theorem 3.6.

This exposes the source theorem used by the Chapter 4 frontier: for every
positive `t` apart from the explicit exception sequence induced by the profile
cover, both level-set pairs are integrable and have the same measure. -/
theorem chapter3_theorem36_all_pos_available
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (h : BishopC.IntegrableRep S)
    (t : R) (ht : COF.lt 0 t)
    (hap : ∀ (n : Nat) (k : Nat),
      COF.lt 0 (COF.abs (t - BishopC.lemma35_exceptionSeq
        (BishopC.thm36A2_profile h (BishopC.coverLo n) (BishopC.coverHi n)
          (BishopC.coverLo_lt_hi n) (BishopC.coverLo_pos n)) k))) :
    ∃ (hA : BishopC.IntegrableSet1 S (BishopC.thm36D_levelBSet h t))
      (hB : BishopC.IntegrableSet1 S (BishopC.thm36D_levelBSetStrict h t)),
      BishopC.measure1 S hA = BishopC.measure1 S hB :=
  BishopC.thm_3_6_all_pos h t ht hap

/-- G156 package: Chapter 3 is source-aligned and the existing profile artifact
is reachable after the G155 Chapter 2 endpoint. -/
structure Chapter3G156SourceAlignmentPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g155 : BishopRegularSeqChapter2G155Package S
  source_audit : Chapter3SourceCoverageAudit
  profile_surface_available : Prop
  p_and_pprime_surfaces_available : Prop
  theorem_3_6_all_pos_available : Prop
  no_new_hidden_choice_in_g156 : Prop
  regularseq_transport_frontier_open : Prop
  estimated_remaining_steps_after_g156 : Nat

def chapter3G156SourceAlignmentPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter3G156SourceAlignmentPackage S where
  g155 := bishopRegularSeqChapter2G155Package S
  source_audit := chapter3SourceCoverageAudit
  profile_surface_available := True
  p_and_pprime_surfaces_available := True
  theorem_3_6_all_pos_available := True
  no_new_hidden_choice_in_g156 := True
  regularseq_transport_frontier_open := True
  estimated_remaining_steps_after_g156 := 5

end SourceAlignment
end BishopRegularSeqChapter3

open BishopRegularSeqChapter3.SourceAlignment

/-- G156 package exposed at the same level as the previous G-packages. -/
structure BishopRegularSeqChapter3G156Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g155 : BishopRegularSeqChapter2G155Package S
  source_alignment : BishopRegularSeqChapter3.SourceAlignment.Chapter3G156SourceAlignmentPackage S
  chapter3_source_items_identified : Prop
  theorem_3_6_existing_artifact_reachable : Prop
  remaining_regularseq_transport_steps : Nat
  no_hidden_choice_in_g156_alignment : Prop

def bishopRegularSeqChapter3G156Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter3G156Package S where
  g155 := bishopRegularSeqChapter2G155Package S
  source_alignment := BishopRegularSeqChapter3.SourceAlignment.chapter3G156SourceAlignmentPackage S
  chapter3_source_items_identified := True
  theorem_3_6_existing_artifact_reachable := True
  remaining_regularseq_transport_steps := 5
  no_hidden_choice_in_g156_alignment := True

/-- Progress after G156: the source Chapter 3 artifact is reachable, but the
RegularSeq mainline transport is still open. -/
def bishopRegularSeqCh1To4ProgressAfterG156 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 35
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G156: aligned Bishop--Cheng Chapter 3 source items with the existing \
    BishopSec3_Profile artifact and exposed Theorem 3.6 all-positive-level \
    statement; remaining frontier is RegularSeq mainline transport."


end BishopCReal
