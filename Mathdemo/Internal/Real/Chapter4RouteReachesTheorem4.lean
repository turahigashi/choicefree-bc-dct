import Mathdemo.Internal.Real.FinalChapter4RouteProposition4
import Mathdemo.Internal.Sec4.DominatedConvergence415SourceComplete

set_option linter.style.longLine false

/-!
# G228: Chapter 4 route reaches Theorem 4.15

G227 completed the route up to Proposition 4.12.  The existing
`Sec4_dominated_convergence_415_source_complete...` development already contains
the source-complete Theorem 4.15 endpoint once the theorem's uniform `I_B`
frontier is supplied.

This file connects that endpoint to the current Bishop-real Chapter 4 progress
ledger.  It does not hide the remaining plain-DCT obligation: deriving the
uniform `I_B` data from the domination hypothesis and the convergence data is
still the final theorem-4.15 bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- The source-complete Theorem 4.15 data currently needed by the verified
endpoint.

`nonIB` contains the non-relative-integral work: the absolute-error sequence,
its PFunR convergence to zero, and its representative data.  `uniformIB` is the
remaining source-shaped uniform relative-integral control. -/
structure Theorem415SourceCompleteData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S) : Type _ where
  nonIB : BishopC.Lemma415AbsErrorNonIBData (S := S) fn f
  uniformIB : BishopC.Lemma415IBUniformFrontierData (S := S) fn f g nonIB

/-- Theorem 4.15 endpoint: from the source-complete data, the integrals of
`f_n` converge to the integral of `f`. -/
noncomputable def theorem415_integral_convergence_from_source_complete_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415SourceCompleteData fn f g) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_convergence_except_measurableSetIB
    (S := S) fn f g D.nonIB D.uniformIB

/-- The abs-error form of Theorem 4.15, also obtained from the same data. -/
noncomputable def theorem415_abs_error_convergence_from_source_complete_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f g : BishopC.IntegrableRep S}
    (D : Theorem415SourceCompleteData fn f g) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  BishopC.thm_4_15_dominated_convergence_except_generalIB
    (S := S) fn f g D.nonIB D.uniformIB

/-- Audit after connecting the verified Theorem 4.15 endpoint. -/
structure Theorem415RouteAuditAfterG228 : Type where
  theorem415_endpoint_from_source_complete_data_closed : Nat
  abs_error_endpoint_closed : Nat
  integral_endpoint_closed : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_plain_dct_bridge_uniformIB_from_domination : Nat

def theorem415RouteAuditAfterG228 :
    Theorem415RouteAuditAfterG228 where
  theorem415_endpoint_from_source_complete_data_closed := 1
  abs_error_endpoint_closed := 1
  integral_endpoint_closed := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_plain_dct_bridge_uniformIB_from_domination := 1

/-- G228 package. -/
structure Chapter4G228Theorem415RoutePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g227 : Chapter4To412Final.Chapter4G227UpTo412FinalPackage S
  audit : Theorem415RouteAuditAfterG228
  theorem415_source_endpoint_closed_this_step : Nat
  remaining_plain_dct_bridge_steps : Nat

def chapter4G228Theorem415RoutePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G228Theorem415RoutePackage S where
  g227 := Chapter4To412Final.chapter4G227UpTo412FinalPackage S
  audit := theorem415RouteAuditAfterG228
  theorem415_source_endpoint_closed_this_step := 1
  remaining_plain_dct_bridge_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G228. -/
def bishopRegularSeqChapter4Theorem415RouteProgressAfterG228 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G228: connected the existing source-complete Theorem 4.15 endpoint to the \
    current Bishop-real Chapter 4 route. From explicit non-IB abs-error data and \
    uniform IB source data, both I(|f_n-f|)->0 and I(f_n)->I(f) are obtained. \
    Remaining plain-DCT bridge: derive the uniform IB data from domination by g \
    and convergence data, without adding a selector or choice principle."


end BishopCReal
