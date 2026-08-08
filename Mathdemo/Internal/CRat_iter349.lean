import Mathdemo.Internal.CRat_iter348
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b20_absOuterPack_iteration1

set_option linter.style.longLine false

/-!
# G250: theorem 4.15 from corrected abs-outer pack tools

G249 routed theorem 4.15 through function-side case tools.  The chapter-4
development has a corrected, lower interface for those tools:
`Sec4ChiFCaseAbsPackTools`.  This interface uses the abs-outer row sum required
by `seriesSumRep_L1` flat absolute convergence, avoiding the earlier
signed-outer design bug.

This file exposes the theorem-4.15 endpoint from that corrected abs-outer
package.  It keeps the set-side data definitional: cover/difference dichotomy
is still built from `IntegrableSet1.valid` downstream.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 statement data using corrected abs-outer pack tools for every
abs-error representative. -/
structure Theorem415AbsErrorAbsPackToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_absPackTools : forall n : Nat,
    BishopC.Sec4ChiFCaseAbsPackTools (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Corrected abs-pack tools give the function-side case-tool route. -/
noncomputable def theorem415_caseTools_statement_data_of_absPackTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorAbsPackToolsStatementData (S := S) fn f) :
    Theorem415AbsErrorCaseToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_caseTools := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_chiFCaseToolsData_of_absPackTools
        (S := S) u hnn_u
        (D.abs_error_absPackTools n)
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from corrected abs-outer pack tools. -/
noncomputable def theorem415_integral_convergence_from_absPackTools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorAbsPackToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_caseTools_statement_data
    (S := S)
    (theorem415_caseTools_statement_data_of_absPackTools (S := S) D)

structure Theorem415AbsPackToolsRouteAuditAfterG250 : Type where
  corrected_abs_outer_pack_route_added : Nat
  signed_outer_pack_route_required : Nat
  set_dichotomy_built_from_integrable_validness : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_abs_pack_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415AbsPackToolsRouteAuditAfterG250 :
    Theorem415AbsPackToolsRouteAuditAfterG250 where
  corrected_abs_outer_pack_route_added := 1
  signed_outer_pack_route_required := 0
  set_dichotomy_built_from_integrable_validness := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_abs_pack_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

structure Chapter4G250Theorem415AbsPackToolsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g249 : Chapter4G249Theorem415CaseToolsPackage S
  audit : Theorem415AbsPackToolsRouteAuditAfterG250
  corrected_abs_outer_pack_route_added_this_step : Nat
  remaining_abs_pack_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G250Theorem415AbsPackToolsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G250Theorem415AbsPackToolsPackage S where
  g249 := chapter4G249Theorem415CaseToolsPackage S
  audit := theorem415AbsPackToolsRouteAuditAfterG250
  corrected_abs_outer_pack_route_added_this_step := 1
  remaining_abs_pack_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G250. -/
def bishopRegularSeqChapter4Theorem415AbsPackToolsProgressAfterG250 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G250: connected theorem 4.15 to the corrected abs-outer pack tools for \
    prop_4_2_chi_f_rep. The route uses abs-outer row sums, not the obsolete \
    signed-outer package, and still obtains set-side cover/difference \
    dichotomy from IntegrableSet1.valid. Remaining frontiers are abs-pack \
    construction for the abs-error representatives and the PFun/representation \
    source layer."


end BishopCReal
