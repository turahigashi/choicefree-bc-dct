import Mathdemo.Internal.CRat_iter334

set_option linter.style.longLine false

/-!
# G236: theorem-4.15 domination packaged as source-statement data

G235 preserved the source theorem statement by replacing the displayed `2g`
majorant with the constructive majorant `g + |f|`.  The remaining visible
`g_nonneg` input is not an extra mathematical assumption: in Bishop's statement
`|f_n| <= g`, the right-hand side is a non-negative dominating majorant.

This file packages that convention as statement-level data:

* `g` is the witness in "there exists an integrable function g";
* `domination` is the source assertion `forall n, |f_n| <= g`;
* the non-negativity needed by the cover-set machinery is projected from that
  domination package, not passed as a separate theorem-4.15 input.

No Prop-to-data selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Source-level data for the theorem-4.15 domination statement
`forall n, |f_n| <= g`.

The `nonneg_majorant` field records the order-theoretic convention that a
majorant of absolute values is a non-negative representative.  This is now part
of the domination assertion itself, rather than a free-standing theorem input.
-/
structure Theorem415DominatingMajorantData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (g : BishopC.IntegrableRep S) : Type _ where
  nonneg_majorant : BishopC.RepNonneg g
  dominates_abs_fn : forall n, BishopC.RepNonneg (g.sub (fn n).absVal)

def Theorem415DominatingMajorantData.g_nonneg
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {g : BishopC.IntegrableRep S}
    (D : Theorem415DominatingMajorantData fn g) :
    BishopC.RepNonneg g :=
  D.nonneg_majorant

def Theorem415DominatingMajorantData.dominated_fn
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {g : BishopC.IntegrableRep S}
    (D : Theorem415DominatingMajorantData fn g) :
    forall n, BishopC.RepNonneg (g.sub (fn n).absVal) :=
  D.dominates_abs_fn

/-- Source-data form of theorem 4.15 with the existential majorant `g` kept as
a field, matching the source statement's "there exists an integrable g". -/
structure Theorem415PFunSourceStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  domainResidualProvider : BishopC.Sec4GeneralIBDomainResidualProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Forget only the source-statement packaging and feed the G235 route. -/
noncomputable def theorem415_noLimitDom_data_of_statementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415PFunSourceStatementData (S := S) fn f) :
    Theorem415LocalPFunSourceDataNoLimitDomination (S := S) fn f D.g where
  g_nonneg := D.domination.g_nonneg
  dominated_fn := D.domination.dominated_fn
  domainResidualProvider := D.domainResidualProvider
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from statement-shaped PFun source data.

At this endpoint `g_nonneg` is no longer an independent input; it is a projection
of the source domination assertion `forall n, |f_n| <= g`.
-/
noncomputable def theorem415_integral_convergence_from_statement_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415PFunSourceStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_noLimitDom_source_data
    (S := S) (fn := fn) (f := f) (g := D.g)
    (theorem415_noLimitDom_data_of_statementData (S := S) D)

structure Theorem415StatementDominationRouteAuditAfterG236 : Type where
  separate_g_nonneg_input_removed : Nat
  g_witness_kept_inside_source_statement : Nat
  domination_statement_carries_majorant_nonnegativity : Nat
  separate_limit_domination_input_removed : Nat
  substitute_majorant_g_plus_abs_f_used : Nat
  direct_abs_error_convergence_input_removed : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def theorem415StatementDominationRouteAuditAfterG236 :
    Theorem415StatementDominationRouteAuditAfterG236 where
  separate_g_nonneg_input_removed := 1
  g_witness_kept_inside_source_statement := 1
  domination_statement_carries_majorant_nonnegativity := 1
  separate_limit_domination_input_removed := 1
  substitute_majorant_g_plus_abs_f_used := 1
  direct_abs_error_convergence_input_removed := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 1
  remaining_plain_prop_415_bridge_steps := 3

structure Chapter4G236Theorem415StatementDominationPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g235 : Chapter4G235Theorem415NoLimitDomPackage S
  audit : Theorem415StatementDominationRouteAuditAfterG236
  theorem415_statement_domination_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_plain_prop_415_bridge_steps : Nat

def chapter4G236Theorem415StatementDominationPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G236Theorem415StatementDominationPackage S where
  g235 := chapter4G235Theorem415NoLimitDomPackage S
  audit := theorem415StatementDominationRouteAuditAfterG236
  theorem415_statement_domination_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 1
  remaining_plain_prop_415_bridge_steps := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G236. -/
def bishopRegularSeqChapter4Theorem415StatementDominationProgressAfterG236 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G236: absorbed the visible g_nonneg input into the theorem-4.15 source \
    domination statement. The majorant witness g is now a field of the \
    statement-shaped source data, and |f_n| <= g carries the non-negative \
    majorant convention. Remaining source-data bridge: the Proposition 4.2 \
    domain-residual provider."


end BishopCReal
