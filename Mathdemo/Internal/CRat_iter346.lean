import Mathdemo.Internal.CRat_iter345
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2a_chiData_iteration1

set_option linter.style.longLine false

/-!
# G247: theorem 4.15 from canonical cover facts

G246 made the theorem-4.15 endpoint consume only local full-set value bridges
for the abs-error sequence.  This file traces that local bridge one definition
layer lower: the public bridge input can now be replaced by the concrete
canonical-cover facts, or by the still lower `χ` telescope data already used
in the chapter-4 `I_B` construction.

The direction is deliberately one-way:

* canonical cover/χ data -> value bridge -> local bridge -> theorem 4.15;
* no attempt is made to recover cover data from a propositional value bridge.

This preserves the Bishop-style discipline: carry the witnesses that the
construction actually uses, and do not extract them from bare membership or
fullness propositions.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 statement data where the abs-error local bridge is supplied
by canonical cover facts. -/
structure Theorem415AbsErrorCoverFactsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_coverFacts : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverFacts (S := S) B hB
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

/-- Cover facts produce the local-bridge statement data used in G246. -/
noncomputable def theorem415_localBridge_statement_data_of_coverFacts
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorCoverFactsStatementData (S := S) fn f) :
    Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_local_bridge := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_genIBLocalValueBridge_of_valueBridge
        (S := S) B hB u hnn_u
        (BishopC.sec4_genIBValueBridge_of_coverFacts
          (S := S) B hB u hnn_u
          (D.abs_error_coverFacts n B hB))
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Abs-error convergence from canonical cover facts. -/
noncomputable def theorem415_abs_error_tendsto_from_coverFacts_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorCoverFactsStatementData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  theorem415_abs_error_tendsto_from_localBridge_statement_data
    (S := S)
    (theorem415_localBridge_statement_data_of_coverFacts (S := S) D)

/-- Theorem 4.15 from canonical cover facts for the abs-error sequence. -/
noncomputable def theorem415_integral_convergence_from_coverFacts_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorCoverFactsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_localBridge_statement_data
    (S := S)
    (theorem415_localBridge_statement_data_of_coverFacts (S := S) D)

/-- Theorem-4.15 statement data where the canonical cover facts are themselves
supplied by the lower `χ` telescope data. -/
structure Theorem415AbsErrorChiDataStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_chiData : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverChiData (S := S) B hB
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

/-- Lower `χ` telescope data produces canonical cover-facts statement data. -/
noncomputable def theorem415_coverFacts_statement_data_of_chiData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorChiDataStatementData (S := S) fn f) :
    Theorem415AbsErrorCoverFactsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_coverFacts := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_canonicalCoverFacts_of_chiData
        (S := S) B hB u hnn_u
        (D.abs_error_chiData n B hB)
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Lower `χ` telescope data produces the local-bridge statement data used in
G246. -/
noncomputable def theorem415_localBridge_statement_data_of_chiData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorChiDataStatementData (S := S) fn f) :
    Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f :=
  theorem415_localBridge_statement_data_of_coverFacts
    (S := S)
    (theorem415_coverFacts_statement_data_of_chiData (S := S) D)

/-- Abs-error convergence from the lower `χ` telescope data. -/
noncomputable def theorem415_abs_error_tendsto_from_chiData_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorChiDataStatementData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  theorem415_abs_error_tendsto_from_coverFacts_statement_data
    (S := S)
    (theorem415_coverFacts_statement_data_of_chiData (S := S) D)

/-- Theorem 4.15 from lower `χ` telescope data for the abs-error sequence. -/
noncomputable def theorem415_integral_convergence_from_chiData_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorChiDataStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_coverFacts_statement_data
    (S := S)
    (theorem415_coverFacts_statement_data_of_chiData (S := S) D)

structure Theorem415CoverFactsRouteAuditAfterG247 : Type where
  global_source_s2_provider_required : Nat
  characteristic_domain_provider_required : Nat
  local_full_set_bridge_public_input_required : Nat
  canonical_cover_facts_route_added : Nat
  chi_telescope_data_route_added : Nat
  global_value_bridge_compatibility_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_chi_fact_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415CoverFactsRouteAuditAfterG247 :
    Theorem415CoverFactsRouteAuditAfterG247 where
  global_source_s2_provider_required := 0
  characteristic_domain_provider_required := 0
  local_full_set_bridge_public_input_required := 0
  canonical_cover_facts_route_added := 1
  chi_telescope_data_route_added := 1
  global_value_bridge_compatibility_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_chi_fact_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

structure Chapter4G247Theorem415CoverFactsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g246 : Chapter4G246Theorem415LocalBridgePackage S
  audit : Theorem415CoverFactsRouteAuditAfterG247
  local_bridge_public_input_removed_this_step : Nat
  remaining_chi_fact_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G247Theorem415CoverFactsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G247Theorem415CoverFactsPackage S where
  g246 := chapter4G246Theorem415LocalBridgePackage S
  audit := theorem415CoverFactsRouteAuditAfterG247
  local_bridge_public_input_removed_this_step := 1
  remaining_chi_fact_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G247. -/
def bishopRegularSeqChapter4Theorem415CoverFactsProgressAfterG247 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G247: traced the theorem-4.15 local full-set bridge one layer lower. \
    Canonical cover facts, and below them χ telescope data, now feed the \
    local-bridge theorem-4.15 route. The route still avoids the previous global \
    membership-to-witness provider and records the remaining work as the \
    concrete construction of those χ/cover facts from the definitions, plus \
    the PFun/representation source layer."


end BishopCReal
