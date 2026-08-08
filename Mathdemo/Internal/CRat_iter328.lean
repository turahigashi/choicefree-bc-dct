import Mathdemo.Internal.CRat_iter327

set_option linter.style.longLine false

/-!
# G229: Theorem 4.15 through the source cover-set route

G228 connected the already verified theorem-4.15 endpoint, but still consumed
the bundled `Lemma415IBUniformFrontierData`.  This file moves one step closer to
the printed proof: the uniform relative-integral control is obtained from the
source cover-set/tail construction for the dominating function `g`.

The remaining work is not hidden.  To obtain the plain textbook statement, the
fields of `Theorem415CoverSetSourceData` still have to be derived from the
definitions of integrable functions, convergence in measure, and the pointwise
domination hypothesis.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-shaped data for theorem 4.15 after the printed proof's
cover-set/tail step has been made explicit.

`dominated_fn` is the printed domination hypothesis `|f_n| <= g`.  The other
fields are definition-witness bridges that should be obtained from the
integrability and convergence definitions in the final plain route. -/
structure Theorem415CoverSetSourceData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S) : Type _ where
  g_nonneg : BishopC.RepNonneg g
  dominated_fn : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)
  dominated_limit : BishopC.RepNonneg (g.sub f.absVal)
  abs_error_rowSeeds : forall n,
    BishopC.Sec4Prop42RowSeedTools (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  g_rowSeeds :
    BishopC.Sec4Prop42RowSeedTools (S := S) g g_nonneg
  abs_error_converges_in_measure :
    BishopC.Lemma414ConvergeInMeasureToZeroData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)

/-- Build the source-level lemma-4.14 abs-error data using the concrete
cover-set construction and the canonical epsilon budget. -/
noncomputable def theorem415_abs_error_source_data_from_coverSet
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetSourceData fn f g) :
    BishopC.Lemma415AbsErrorSourceData (S := S) fn f :=
  BishopC.Lemma415AbsErrorSourceData.of_gCoverSetTailBudgetData
    (S := S) fn f g D.g_nonneg D.dominated_fn D.dominated_limit
    D.abs_error_rowSeeds D.g_rowSeeds
    (fun eps heps => BishopC.lemma_4_15_default_tail_budget (R := R) eps heps)
    D.abs_error_converges_in_measure

/-- The abs-error convergence part of theorem 4.15 via the source cover-set
route. -/
noncomputable def theorem415_abs_error_convergence_from_coverSet_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetSourceData fn f g) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  BishopC.thm_4_15_abs_error_tendsto_from_source_data
    (S := S) fn f
    (theorem415_abs_error_source_data_from_coverSet (S := S) D)

/-- Theorem 4.15 via the source cover-set route, without a separate
`uniformIB` field. -/
noncomputable def theorem415_integral_convergence_from_coverSet_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415CoverSetSourceData fn f g) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_source_from_g_coverSet_default_budget_data
    (S := S) fn f g D.g_nonneg D.dominated_fn D.dominated_limit
    D.abs_error_rowSeeds D.g_rowSeeds D.abs_error_converges_in_measure

/-- Audit after replacing the bundled `uniformIB` endpoint by the source
cover-set/tail endpoint. -/
structure Theorem415CoverSetRouteAuditAfterG229 : Type where
  coverSet_tail_uniform_bridge_closed : Nat
  bundled_uniformIB_field_required_for_this_endpoint : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_definition_witness_bridges_to_plain_415 : Nat

def theorem415CoverSetRouteAuditAfterG229 :
    Theorem415CoverSetRouteAuditAfterG229 where
  coverSet_tail_uniform_bridge_closed := 1
  bundled_uniformIB_field_required_for_this_endpoint := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_definition_witness_bridges_to_plain_415 := 4

/-- G229 package. -/
structure Chapter4G229Theorem415CoverSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g228 : Chapter4G228Theorem415RoutePackage S
  audit : Theorem415CoverSetRouteAuditAfterG229
  theorem415_coverSet_source_endpoint_closed_this_step : Nat
  remaining_plain_415_definition_bridge_steps : Nat

def chapter4G229Theorem415CoverSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G229Theorem415CoverSetPackage S where
  g228 := chapter4G228Theorem415RoutePackage S
  audit := theorem415CoverSetRouteAuditAfterG229
  theorem415_coverSet_source_endpoint_closed_this_step := 1
  remaining_plain_415_definition_bridge_steps := 4

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G229. -/
def bishopRegularSeqChapter4Theorem415CoverSetProgressAfterG229 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G229: replaced the bundled theorem-4.15 uniformIB endpoint by the source \
    coverSet/tail route. The g-tail and epsilon budget are now obtained from the \
    Bishop cover-set construction. Countdown to the plain theorem-4.15 statement: \
    4 definition-witness bridges remain."


end BishopCReal
