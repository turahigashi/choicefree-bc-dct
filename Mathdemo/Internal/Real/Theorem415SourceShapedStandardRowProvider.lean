import Mathdemo.Internal.Real.Theorem415CorrectedAbsOuter
import Mathdemo.Internal.Sec4.S2StandardOuterProvider

set_option linter.style.longLine false

/-!
# G251: theorem 4.15 from the source-shaped standard-row provider

G250 exposed theorem 4.15 from corrected abs-outer pack tools for the
abs-error representatives.  This file moves that input one definition layer
upstream: the pack tools are supplied by the source-shaped standard-row
provider of `b2b31`.

This is still not a proof of the provider itself.  It records the correct
remaining frontier:

* a generic row-to-flat bridge for `seriesSumRep_L1`;
* the characteristic-domain witness for `χ_A`;
* corrected abs-outer convergence for the standard Proposition 4.2 rows on
  both `A.S1` and `A.S2`.

No witness is extracted from a Prop-valued existence proof.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 statement data from the source-shaped standard-row provider.

Compared with `Theorem415AbsErrorAbsPackToolsStatementData`, this no longer
asks for an abs-pack tool separately for each error representative. -/
structure Theorem415SourceS2StandardOuterProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  source_s2_standard_outer_provider :
    BishopC.Sec4GeneralIBSourceS2StandardOuterProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- The source-shaped standard-row provider supplies the corrected abs-pack
tools needed by G250. -/
noncomputable def theorem415_absPackTools_statement_data_of_sourceS2StandardOuterProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceS2StandardOuterProviderStatementData (S := S) fn f) :
    Theorem415AbsErrorAbsPackToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_absPackTools := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.Sec4GeneralIBSourceS2StandardOuterProvider.absPackTools
        (S := S) D.source_s2_standard_outer_provider u hnn_u
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from the source-shaped standard-row provider. -/
noncomputable def theorem415_integral_convergence_from_sourceS2StandardOuterProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceS2StandardOuterProviderStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_absPackTools_statement_data
    (S := S)
    (theorem415_absPackTools_statement_data_of_sourceS2StandardOuterProvider
      (S := S) D)

structure Theorem415SourceS2StandardOuterProviderRouteAuditAfterG251 : Type where
  per_abs_error_abs_pack_tools_required : Nat
  source_s2_standard_outer_provider_route_added : Nat
  arbitrary_s2_abs_pack_provider_required : Nat
  characteristic_domain_witness_exposed : Nat
  standard_prop42_rows_on_s2_exposed : Nat
  row_to_flat_bridge_required : Nat
  standard_outer_s1_required : Nat
  standard_outer_s2_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_standard_outer_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415SourceS2StandardOuterProviderRouteAuditAfterG251 :
    Theorem415SourceS2StandardOuterProviderRouteAuditAfterG251 where
  per_abs_error_abs_pack_tools_required := 0
  source_s2_standard_outer_provider_route_added := 1
  arbitrary_s2_abs_pack_provider_required := 0
  characteristic_domain_witness_exposed := 1
  standard_prop42_rows_on_s2_exposed := 1
  row_to_flat_bridge_required := 1
  standard_outer_s1_required := 1
  standard_outer_s2_required := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_standard_outer_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

structure Chapter4G251Theorem415SourceS2StandardOuterProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g250 : Chapter4G250Theorem415AbsPackToolsPackage S
  audit : Theorem415SourceS2StandardOuterProviderRouteAuditAfterG251
  per_abs_error_abs_pack_tools_required : Nat
  source_s2_standard_outer_provider_route_added_this_step : Nat
  remaining_standard_outer_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G251Theorem415SourceS2StandardOuterProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G251Theorem415SourceS2StandardOuterProviderPackage S where
  g250 := chapter4G250Theorem415AbsPackToolsPackage S
  audit := theorem415SourceS2StandardOuterProviderRouteAuditAfterG251
  per_abs_error_abs_pack_tools_required := 0
  source_s2_standard_outer_provider_route_added_this_step := 1
  remaining_standard_outer_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G251. -/
def bishopRegularSeqChapter4Theorem415SourceS2StandardOuterProviderProgressAfterG251 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G251: replaced the per-abs-error abs-pack input for theorem 4.15 by the \
    source-shaped standard-row provider. The remaining I_B construction is now \
    localized to row-to-flat for seriesSumRep_L1, characteristic-domain data, \
    and corrected standard-row abs-outer convergence on S1 and S2; PFun \
    representation faithfulness remains separate."


end BishopCReal
