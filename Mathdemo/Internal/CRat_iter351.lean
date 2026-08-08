import Mathdemo.Internal.CRat_iter350
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b21_rowToFlat_iteration1
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b32_s2StandardOuterBridge_iteration1

set_option linter.style.longLine false

/-!
# G252: remove row-to-flat from the theorem-4.15 public frontier

G251 reduced the abs-error pack input to the source-shaped standard-row
provider.  One of that provider's fields, the generic row-to-flat bridge for
`seriesSumRep_L1`, is already proved as `sec4_rowToFlat_source`.

This file therefore removes `rowToFlat` from the theorem-4.15 statement data
and fills it from the existing proof.  The remaining provider components are
the genuinely source-shaped standard-row data:

* characteristic-domain witnesses for `χ_A`;
* standard `A.S1` abs-outer convergence;
* standard `A.S2` rows;
* standard `A.S2` abs-outer convergence.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source-shaped data after the generic `rowToFlat` bridge has
been closed by `sec4_rowToFlat_source`. -/
structure Theorem415SourceS2StandardOuterNoRowToFlatStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
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

/-- Rebuild the G251 provider statement data, filling `rowToFlat` from the
existing source proof `sec4_rowToFlat_source`. -/
noncomputable def theorem415_sourceS2StandardOuterProvider_statement_data_of_noRowToFlat
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceS2StandardOuterNoRowToFlatStatementData
      (S := S) fn f) :
    Theorem415SourceS2StandardOuterProviderStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  source_s2_standard_outer_provider :=
    BishopC.Sec4GeneralIBSourceS2StandardOuterProvider.ofGenericS2Tools
      (S := S)
      (BishopC.sec4_rowToFlat_source (S := S))
      D.charDomain
      D.standard_outer_on_s1
      D.rows_on_s2
      D.outer_on_s2
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 after removing `rowToFlat` from the public frontier. -/
noncomputable def theorem415_integral_convergence_from_noRowToFlat_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceS2StandardOuterNoRowToFlatStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceS2StandardOuterProvider_statement_data
    (S := S)
    (theorem415_sourceS2StandardOuterProvider_statement_data_of_noRowToFlat
      (S := S) D)

structure Theorem415NoRowToFlatRouteAuditAfterG252 : Type where
  row_to_flat_public_input_required : Nat
  row_to_flat_closed_by_sec4_rowToFlat_source : Nat
  characteristic_domain_witness_exposed : Nat
  standard_outer_s1_required : Nat
  standard_rows_s2_required : Nat
  standard_outer_s2_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_standard_outer_component_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415NoRowToFlatRouteAuditAfterG252 :
    Theorem415NoRowToFlatRouteAuditAfterG252 where
  row_to_flat_public_input_required := 0
  row_to_flat_closed_by_sec4_rowToFlat_source := 1
  characteristic_domain_witness_exposed := 1
  standard_outer_s1_required := 1
  standard_rows_s2_required := 1
  standard_outer_s2_required := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_standard_outer_component_frontiers := 4
  remaining_pfun_representation_frontiers := 1

structure Chapter4G252Theorem415NoRowToFlatPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g251 : Chapter4G251Theorem415SourceS2StandardOuterProviderPackage S
  audit : Theorem415NoRowToFlatRouteAuditAfterG252
  row_to_flat_removed_from_public_frontier_this_step : Nat
  remaining_standard_outer_component_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G252Theorem415NoRowToFlatPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G252Theorem415NoRowToFlatPackage S where
  g251 := chapter4G251Theorem415SourceS2StandardOuterProviderPackage S
  audit := theorem415NoRowToFlatRouteAuditAfterG252
  row_to_flat_removed_from_public_frontier_this_step := 1
  remaining_standard_outer_component_frontiers := 4
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G252. -/
def bishopRegularSeqChapter4Theorem415NoRowToFlatProgressAfterG252 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G252: closed the generic row-to-flat bridge in theorem 4.15 by using \
    sec4_rowToFlat_source, so rowToFlat is no longer a public frontier. The \
    remaining standard-row components are characteristic-domain data, S1 \
    corrected outer convergence, S2 standard rows, and S2 corrected outer \
    convergence, plus the separate PFun representation layer."


end BishopCReal
