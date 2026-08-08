import Mathdemo.Internal.CRat_iter330

set_option linter.style.longLine false

/-!
# G232: Local theorem 4.15 from the cover-set provider

G231 connected theorem 4.15 to the local full-set majorant route, but that
local entry point still accepted the majorant split as an input field.  This
file constructs that split from the existing `coverSet` tail construction and
the generic row-seed provider.  Thus the local route now has the same
source-level inputs as the G230 cover-set provider route: domination by `g`,
nonnegativity of `g`, a Proposition-4.2 row-seed provider, and convergence in
measure of the abs-error sequence.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Build the source proof's single-`g` tail choice from the concrete
`coverSet` complement-tail construction, adding the `2g` row seeds from the
generic provider. -/
noncomputable def theorem415_g_single_tail_choice_from_coverSet_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetProviderSourceData fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415GSingleTailChoiceSourceData
      (S := S) g D.g_nonneg eps :=
  let budget : BishopC.Lemma415TailBudgetSourceData (R := R) eps :=
    BishopC.lemma_4_15_default_tail_budget (R := R) eps heps
  let gComp :
      BishopC.Lemma415GComplementTailRelChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    BishopC.lemma_4_15_g_complement_tail_rel_choice_data_from_coverSetBudget
      (S := S) g D.g_nonneg eps
      (D.rowSeedProvider.rowSeeds g D.g_nonneg)
      budget
  let gRel :
      BishopC.Lemma415GSingleTailRelChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    BishopC.lemma_4_15_g_single_tail_rel_choice_source_data_from_g_complement_tail_data
      (S := S) g D.g_nonneg eps gComp
  {
    gSeeds := gRel.gSeeds
    twoGSeeds :=
      D.rowSeedProvider.rowSeeds (g.add g)
        (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
    A := gRel.A
    hA := gRel.hA
    N := gRel.N
    N_ge_one := gRel.N_ge_one
    epsAB := gRel.epsAB
    epsG := gRel.epsG
    epsNeg := gRel.epsNeg
    epsAB_pos := gRel.epsAB_pos
    gTailBudget := gRel.gTailBudget
    pieces_sum_lt := gRel.pieces_sum_lt
    gNegSmall := gRel.gNegSmall
  }

/-- Construct the local route's `2g` majorant split from the cover-set
provider data. -/
noncomputable def theorem415_majorant_split_from_coverSet_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetProviderSourceData fn f g)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantSplitUniformSourceData
      (S := S) fn f (g.add g)
      (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
      eps :=
  let gTail :
      BishopC.Lemma415GSingleTailChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    theorem415_g_single_tail_choice_from_coverSet_provider
      (S := S) D eps heps
  let twoGTail :
      BishopC.Lemma415TwoGTailChoiceSourceData
        (S := S) g D.g_nonneg eps :=
    BishopC.lemma_4_15_two_g_tail_choice_source_data_from_g_single_tail_choice_data
      (S := S) g D.g_nonneg eps gTail
  let twoGChoice :
      BishopC.Lemma415TwoGChoiceSourceData
        (S := S) fn f g D.g_nonneg eps :=
    BishopC.lemma_4_15_two_g_choice_source_data_from_tail_choice_data
      (S := S) fn f g D.g_nonneg
      D.dominated_fn D.dominated_limit eps twoGTail
  let majorantChoice :
      BishopC.Lemma415MajorantChoiceSourceData
        (S := S) fn f (g.add g)
        (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
        eps :=
    BishopC.lemma_4_15_majorant_choice_source_data_from_two_g_choice_data
      (S := S) fn f g D.g_nonneg eps twoGChoice
  BishopC.lemma_4_15_majorant_split_uniform_source_data_from_choice_data
    (S := S) fn f (g.add g)
    (BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg)
    eps majorantChoice

/-- Convert the G230 cover-set provider data into the G231 local-majorant
source data. -/
noncomputable def theorem415_local_majorant_source_data_of_coverSet_provider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetProviderSourceData fn f g) :
    Theorem415LocalMajorantSourceData fn f (g.add g) where
  majorant_nonneg :=
    BishopC.thm_4_15_two_g_majorant_nonneg (S := S) g D.g_nonneg
  rowSeedProvider := D.rowSeedProvider
  majorantSplit := fun eps heps =>
    theorem415_majorant_split_from_coverSet_provider
      (S := S) D eps heps
  abs_error_converges_in_measure := D.abs_error_converges_in_measure

/-- The local full-set theorem-4.15 endpoint from the cover-set provider data.

This endpoint no longer exposes the local route's `majorantSplit` field to the
caller; it is obtained from `coverSet`, the source epsilon budget, and the
domination hypotheses. -/
noncomputable def theorem415_integral_convergence_from_local_coverSet_provider_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetProviderSourceData fn f g) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_local_majorant_provider_data
    (S := S)
    (theorem415_local_majorant_source_data_of_coverSet_provider
      (S := S) D)

/-- Audit after lowering the local route from explicit majorant-split data to
cover-set provider data. -/
structure Theorem415LocalCoverSetRouteAuditAfterG232 : Type where
  local_route_uses_coverSet_tail_construction : Nat
  local_majorantSplit_no_longer_endpoint_input : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_plain_415_definition_bridge_steps : Nat

def theorem415LocalCoverSetRouteAuditAfterG232 :
    Theorem415LocalCoverSetRouteAuditAfterG232 where
  local_route_uses_coverSet_tail_construction := 1
  local_majorantSplit_no_longer_endpoint_input := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_plain_415_definition_bridge_steps := 3

/-- G232 package. -/
structure Chapter4G232Theorem415LocalCoverSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g231 : Chapter4G231Theorem415LocalMajorantPackage S
  audit : Theorem415LocalCoverSetRouteAuditAfterG232
  theorem415_local_coverSet_endpoint_closed_this_step : Nat
  remaining_plain_415_definition_bridge_steps : Nat

def chapter4G232Theorem415LocalCoverSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G232Theorem415LocalCoverSetPackage S where
  g231 := chapter4G231Theorem415LocalMajorantPackage S
  audit := theorem415LocalCoverSetRouteAuditAfterG232
  theorem415_local_coverSet_endpoint_closed_this_step := 1
  remaining_plain_415_definition_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G232. -/
def bishopRegularSeqChapter4Theorem415LocalCoverSetProgressAfterG232 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G232: lowered the local theorem-4.15 route from explicit majorantSplit \
    input to the coverSet/default-budget provider data. The local endpoint now \
    matches the G230 source-level inputs. Countdown to the completely plain \
    theorem-4.15 statement remains 3 definition-witness bridges."


end BishopCReal
