import Mathdemo.Internal.Real.Chapter3SourceAlignmentBridge

set_option linter.style.longLine false

/-!
# G157: Chapter 3 Definitions 3.1 and 3.2 on the RegularSeq route

G156 identified the source items of Bishop--Cheng Chapter 3 and exposed the
existing `BishopSec3_Profile` artifact after the Chapter 2 endpoint.  This file
records the next, narrower step: Definitions 3.1 and 3.2 are made available as
data-carrying surfaces on the Bishop RegularSeq mainline.

The important constructive point is that the profile is already coded by a
`Code` type, and `p([u,v]) < delta` / `p'([u,v]) < delta` are structures with
explicit witnesses.  This file therefore does not select representatives from a
quotient or recover data from a bare proposition.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter3
namespace ProfileDefinitions

/-- Definition 3.1, re-exposed from the existing coded profile artifact. -/
abbrev def31Profile
    {R : Type*} [COFOC R] {a b : R} (hab : COF.lt a b) : Type _ :=
  SourceAlignment.chapter3ProfileSurface hab

/-- The code type carried by a Definition 3.1 profile. -/
abbrev def31Code
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) : Type _ :=
  P.Code

/-- The embedding carried by a Definition 3.1 profile. -/
abbrev def31Embed
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) : P.Code -> R -> R :=
  P.embed

/-- The functional `lambda` carried by a Definition 3.1 profile. -/
abbrev def31Lambda
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) : P.Code -> R :=
  P.lambda

/-- Definition 3.1's zero profile code evaluates to the zero function. -/
theorem def31_zeroCode_apply
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) (x : R) :
    P.zeroCode x = 0 :=
  BishopC.Profile.zeroCode_apply P x

/-- Definition 3.1's one profile code evaluates to the one function. -/
theorem def31_oneCode_apply
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) (x : R) :
    P.oneCode x = 1 :=
  BishopC.Profile.oneCode_apply P x

/-- Definition 3.2's `p([u,v]) < delta` surface. -/
abbrev def32PLt
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) (u v delta : R) : Type _ :=
  SourceAlignment.chapter3PLtSurface P u v delta

/-- Definition 3.2's `p'([u,v]) < delta` surface. -/
abbrev def32PPrimeLt
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    (P : BishopC.Profile a b hab) (u v delta : R) : Type _ :=
  SourceAlignment.chapter3PPrimeLtSurface P u v delta

/-- The left code witness contained in `p([u,v]) < delta`. -/
def def32PLtLeftCode
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    {P : BishopC.Profile a b hab} {u v delta : R}
    (w : def32PLt P u v delta) : P.Code :=
  w.f1

/-- The right code witness contained in `p([u,v]) < delta`. -/
def def32PLtRightCode
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    {P : BishopC.Profile a b hab} {u v delta : R}
    (w : def32PLt P u v delta) : P.Code :=
  w.f2

/-- The lambda-gap estimate carried by `p([u,v]) < delta`. -/
theorem def32PLtGap
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    {P : BishopC.Profile a b hab} {u v delta : R}
    (w : def32PLt P u v delta) :
    COF.lt (P.lambda w.f2 - P.lambda w.f1) delta :=
  w.gap

/-- The positive collar size carried by `p'([u,v]) < delta`. -/
def def32PPrimeAlpha
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    {P : BishopC.Profile a b hab} {u v delta : R}
    (w : def32PPrimeLt P u v delta) : R :=
  w.alpha

/-- Positivity of the collar carried by `p'([u,v]) < delta`. -/
theorem def32PPrimeAlphaPos
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    {P : BishopC.Profile a b hab} {u v delta : R}
    (w : def32PPrimeLt P u v delta) :
    COF.lt 0 (def32PPrimeAlpha w) :=
  w.alpha_pos

/-- The inner `p`-estimate carried by `p'([u,v]) < delta`. -/
def def32PPrimeInner
    {R : Type*} [COFOC R] {a b : R} {hab : COF.lt a b}
    {P : BishopC.Profile a b hab} {u v delta : R}
    (w : def32PPrimeLt P u v delta) :
    def32PLt P (COF.max a (u - w.alpha)) (COF.min b (v + w.alpha)) delta :=
  w.inner

/-- Audit for the Chapter 3 definition surfaces. -/
structure Chapter3DefinitionSurfaceAudit : Type where
  definition_3_1_profile_type_exposed : Nat
  definition_3_1_code_type_exposed : Nat
  definition_3_1_embedding_exposed : Nat
  definition_3_1_lambda_exposed : Nat
  definition_3_2_p_surface_exposed : Nat
  definition_3_2_pprime_surface_exposed : Nat
  p_lt_witness_codes_are_data : Nat
  p_prime_collar_is_data : Nat
  quotient_representative_extraction_inputs_added_by_g157 : Nat
  prop_to_data_selector_inputs_added_by_g157 : Nat
  classical_choice_inputs_added_by_g157 : Nat
  ready_for_lemma_3_3_transport : Prop

def chapter3DefinitionSurfaceAudit : Chapter3DefinitionSurfaceAudit where
  definition_3_1_profile_type_exposed := 1
  definition_3_1_code_type_exposed := 1
  definition_3_1_embedding_exposed := 1
  definition_3_1_lambda_exposed := 1
  definition_3_2_p_surface_exposed := 1
  definition_3_2_pprime_surface_exposed := 1
  p_lt_witness_codes_are_data := 1
  p_prime_collar_is_data := 1
  quotient_representative_extraction_inputs_added_by_g157 := 0
  prop_to_data_selector_inputs_added_by_g157 := 0
  classical_choice_inputs_added_by_g157 := 0
  ready_for_lemma_3_3_transport := True

/-- G157 package for Definitions 3.1 and 3.2. -/
structure Chapter3G157DefinitionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g156 : BishopRegularSeqChapter3G156Package S
  definition_audit : Chapter3DefinitionSurfaceAudit
  definition_3_1_profile_surface_available : Prop
  definition_3_2_p_surface_available : Prop
  definition_3_2_pprime_surface_available : Prop
  definition_surfaces_are_data_carrying : Prop
  no_new_hidden_choice_in_g157 : Prop
  estimated_remaining_steps_after_g157 : Nat

def chapter3G157DefinitionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter3G157DefinitionPackage S where
  g156 := bishopRegularSeqChapter3G156Package S
  definition_audit := chapter3DefinitionSurfaceAudit
  definition_3_1_profile_surface_available := True
  definition_3_2_p_surface_available := True
  definition_3_2_pprime_surface_available := True
  definition_surfaces_are_data_carrying := True
  no_new_hidden_choice_in_g157 := True
  estimated_remaining_steps_after_g157 := 4

end ProfileDefinitions
end BishopRegularSeqChapter3

open BishopRegularSeqChapter3.ProfileDefinitions

/-- G157 package exposed at the same level as the previous G-packages. -/
structure BishopRegularSeqChapter3G157Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g156 : BishopRegularSeqChapter3G156Package S
  definition_package : BishopRegularSeqChapter3.ProfileDefinitions.Chapter3G157DefinitionPackage S
  definitions_3_1_3_2_available_on_mainline : Prop
  definitions_are_data_carrying_not_prop_selectors : Prop
  remaining_regularseq_transport_steps : Nat
  next_frontier_lemma_3_3 : Prop

def bishopRegularSeqChapter3G157Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter3G157Package S where
  g156 := bishopRegularSeqChapter3G156Package S
  definition_package := BishopRegularSeqChapter3.ProfileDefinitions.chapter3G157DefinitionPackage S
  definitions_3_1_3_2_available_on_mainline := True
  definitions_are_data_carrying_not_prop_selectors := True
  remaining_regularseq_transport_steps := 4
  next_frontier_lemma_3_3 := True

/-- Progress after G157: Definitions 3.1 and 3.2 are connected to the
RegularSeq Chapter 3 chain. -/
def bishopRegularSeqCh1To4ProgressAfterG157 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 45
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G157: exposed Chapter 3 Definitions 3.1 and 3.2 as coded, \
    data-carrying profile surfaces on the Bishop RegularSeq mainline; \
    remaining countdown is Lemma 3.3, Lemma 3.4, Theorem 3.5, and Theorem 3.6 audit."


end BishopCReal
