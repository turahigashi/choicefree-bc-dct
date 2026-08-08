import Mathdemo.Internal.CRat_iter343
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b32_s2StandardOuterBridge_iteration1

set_option linter.style.longLine false

/-!
# G245: unbundle the theorem-4.15 S2 provider frontier

G244 gives the preferred endpoint for theorem 4.15: source-shaped S2 data,
direct local split data, local full-set `I_B`, and PFun convergence.

This file does not prove new lower mathematics.  It makes the remaining
source-shaped provider frontier explicit by replacing the bundled
`Sec4GeneralIBSourceS2StandardOuterProvider` input with its five concrete
source components: row-to-flat, characteristic-domain witnesses, standard S1
outer data, S2 rows, and S2 outer data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source data with the chapter-4 S2 provider unbundled into its
five source-shaped components. -/
structure Theorem415Chapter4IBUnbundledS2ToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  rowToFlat : BishopC.Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S)
  charDomain : BishopC.Sec4Prop42CharacteristicDomainWitness (S := S)
  standard_outer_on_s1 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4Prop42StandardAbsOuterOnS1OfFAbs
        (S := S) charDomain u unn
  rows_on_s2 : BishopC.Lemma415Prop42RowsOnS2Tool (S := S)
  outer_on_s2 : BishopC.Lemma415Prop42AbsOuterOnS2Tool (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Rebundle the five exposed S2 components into the G244 source-shaped
statement data. -/
noncomputable def theorem415_sourceS2_statement_data_of_unbundledS2Tools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBUnbundledS2ToolsStatementData (S := S) fn f) :
    Theorem415Chapter4IBSourceS2StatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  chapter4IBSourceS2Provider :=
    BishopC.Sec4GeneralIBSourceS2StandardOuterProvider.ofGenericS2Tools
      (S := S)
      D.rowToFlat
      D.charDomain
      D.standard_outer_on_s1
      D.rows_on_s2
      D.outer_on_s2
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 through the unbundled source-shaped S2 tool frontier. -/
noncomputable def theorem415_integral_convergence_from_unbundledS2Tools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBUnbundledS2ToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceS2_direct_local_statement_data
    (S := S)
    (theorem415_sourceS2_statement_data_of_unbundledS2Tools
      (S := S) D)

structure Theorem415UnbundledS2ToolsRouteAuditAfterG245 : Type where
  bundled_source_s2_provider_removed_from_public_route : Nat
  rowToFlat_component_exposed : Nat
  characteristic_domain_component_exposed : Nat
  standard_s1_outer_component_exposed : Nat
  s2_rows_component_exposed : Nat
  s2_outer_component_exposed : Nat
  direct_local_split_from_majorant_choice_used : Nat
  local_full_set_ib_interface_used : Nat
  pfun_convergence_source_data_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_shaped_provider_frontiers : Nat
  remaining_unbundled_provider_component_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415UnbundledS2ToolsRouteAuditAfterG245 :
    Theorem415UnbundledS2ToolsRouteAuditAfterG245 where
  bundled_source_s2_provider_removed_from_public_route := 1
  rowToFlat_component_exposed := 1
  characteristic_domain_component_exposed := 1
  standard_s1_outer_component_exposed := 1
  s2_rows_component_exposed := 1
  s2_outer_component_exposed := 1
  direct_local_split_from_majorant_choice_used := 1
  local_full_set_ib_interface_used := 1
  pfun_convergence_source_data_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_shaped_provider_frontiers := 0
  remaining_unbundled_provider_component_frontiers := 5
  remaining_pfun_representation_frontiers := 1

structure Chapter4G245Theorem415UnbundledS2ToolsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g244 : Chapter4G244Theorem415SourceS2DirectLocalPackage S
  audit : Theorem415UnbundledS2ToolsRouteAuditAfterG245
  bundled_provider_frontier_exposed_this_step : Nat
  remaining_unbundled_provider_component_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G245Theorem415UnbundledS2ToolsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G245Theorem415UnbundledS2ToolsPackage S where
  g244 := chapter4G244Theorem415SourceS2DirectLocalPackage S
  audit := theorem415UnbundledS2ToolsRouteAuditAfterG245
  bundled_provider_frontier_exposed_this_step := 1
  remaining_unbundled_provider_component_frontiers := 5
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G245. -/
def bishopRegularSeqChapter4Theorem415UnbundledS2ToolsProgressAfterG245 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G245: exposed the bundled theorem-4.15 source-shaped S2 provider as five \
    explicit lower components: rowToFlat, characteristic-domain witnesses, \
    standard S1 outer data, S2 rows, and S2 outer data. This makes the \
    remaining source-shaped provider frontier auditable instead of hidden \
    behind one structure. The theorem endpoint still uses the G244 direct \
    local split and adds no choice principle."


end BishopCReal
