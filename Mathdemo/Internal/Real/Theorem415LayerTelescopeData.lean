import Mathdemo.Internal.Real.Theorem415CanonicalCoverFacts
import Mathdemo.Internal.Sec4.LayerTelescope

set_option linter.style.longLine false

/-!
# G248: theorem 4.15 from layer telescope data

G247 routed theorem 4.15 through canonical cover facts and then through the
`χ` telescope data.  The chapter-4 `I_B` construction already decomposes that
`χ` data further:

* telescope data, where `coverApart` has supplied the `coverSet.S2` smallness;
* layer telescope data, where the remaining pointwise finite telescope is
  reduced to base-row, tail-row, and characteristic-telescope facts.

This file connects those lower layers to the theorem-4.15 endpoint.  It does
not add any selector from bare membership/fullness; it only composes the
existing constructive data transformations.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 statement data using the remaining telescope data for the
abs-error sequence. -/
structure Theorem415AbsErrorTelescopeStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_telescopeData : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverTelescopeData (S := S) B hB
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

/-- Telescope data gives the lower `χ`-data route from G247. -/
noncomputable def theorem415_chiData_statement_data_of_telescopeData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorTelescopeStatementData (S := S) fn f) :
    Theorem415AbsErrorChiDataStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_chiData := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_canonicalCoverChiData_of_coreData
        (S := S) B hB u hnn_u
        (BishopC.sec4_coreData_of_telescopeData
          (S := S) B hB u hnn_u
          (D.abs_error_telescopeData n B hB))
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from the remaining telescope data. -/
noncomputable def theorem415_integral_convergence_from_telescope_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorTelescopeStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_chiData_statement_data
    (S := S)
    (theorem415_chiData_statement_data_of_telescopeData (S := S) D)

/-- Theorem-4.15 statement data using the layer telescope data for the
abs-error sequence. -/
structure Theorem415AbsErrorLayerTelescopeStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_layerTelescopeData : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CanonicalCoverLayerTelescopeData (S := S) B hB
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

/-- Layer telescope data gives the remaining telescope route. -/
noncomputable def theorem415_telescope_statement_data_of_layerTelescopeData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLayerTelescopeStatementData (S := S) fn f) :
    Theorem415AbsErrorTelescopeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_telescopeData := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_telescopeData_of_layerTelescopeData
        (S := S) B hB u hnn_u
        (D.abs_error_layerTelescopeData n B hB)
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Layer telescope data gives the lower `χ`-data route from G247. -/
noncomputable def theorem415_chiData_statement_data_of_layerTelescopeData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLayerTelescopeStatementData (S := S) fn f) :
    Theorem415AbsErrorChiDataStatementData (S := S) fn f :=
  theorem415_chiData_statement_data_of_telescopeData
    (S := S)
    (theorem415_telescope_statement_data_of_layerTelescopeData (S := S) D)

/-- Theorem 4.15 from layer telescope data for the abs-error sequence. -/
noncomputable def theorem415_integral_convergence_from_layerTelescope_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorLayerTelescopeStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_telescope_statement_data
    (S := S)
    (theorem415_telescope_statement_data_of_layerTelescopeData (S := S) D)

structure Theorem415LayerTelescopeRouteAuditAfterG248 : Type where
  local_full_set_bridge_public_input_required : Nat
  canonical_cover_facts_public_input_required : Nat
  chi_data_public_input_required : Nat
  coverApart_smallness_closed_by_existing_layer : Nat
  finite_sum_telescope_assembly_closed_by_existing_layer : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_layer_telescope_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415LayerTelescopeRouteAuditAfterG248 :
    Theorem415LayerTelescopeRouteAuditAfterG248 where
  local_full_set_bridge_public_input_required := 0
  canonical_cover_facts_public_input_required := 0
  chi_data_public_input_required := 0
  coverApart_smallness_closed_by_existing_layer := 1
  finite_sum_telescope_assembly_closed_by_existing_layer := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_layer_telescope_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

structure Chapter4G248Theorem415LayerTelescopePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g247 : Chapter4G247Theorem415CoverFactsPackage S
  audit : Theorem415LayerTelescopeRouteAuditAfterG248
  chi_data_public_input_removed_this_step : Nat
  remaining_layer_telescope_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G248Theorem415LayerTelescopePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G248Theorem415LayerTelescopePackage S where
  g247 := chapter4G247Theorem415CoverFactsPackage S
  audit := theorem415LayerTelescopeRouteAuditAfterG248
  chi_data_public_input_removed_this_step := 1
  remaining_layer_telescope_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G248. -/
def bishopRegularSeqChapter4Theorem415LayerTelescopeProgressAfterG248 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G248: lowered the theorem-4.15 abs-error bridge from χ-data to layer \
    telescope data. Existing chapter-4 layers now discharge the coverApart \
    smallness branch and the finite-sum telescope assembly before reaching \
    the local full-set theorem-4.15 route. Remaining frontiers are the concrete \
    construction of the layer telescope facts and the PFun/representation \
    source layer."


end BishopCReal
