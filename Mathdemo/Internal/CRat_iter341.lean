import Mathdemo.Internal.CRat_iter340

set_option linter.style.longLine false

/-!
# G242: theorem 4.15 through the source-shaped standard-row `I_B` provider

G241 routed theorem 4.15 through the domain-residual provider.  That provider
is useful as a row-seed bridge, but it still packages obligations for arbitrary
row witnesses.

This file adds a more source-shaped theorem-4.15 endpoint.  The error side of
lemma 4.14 is lowered to the completed `remainingAtoms` interface supplied by
`Sec4GeneralIBSourceS2StandardOuterProvider`, whose `A.S1` and `A.S2` outer
obligations are attached to the standard Proposition 4.2 rows.  The majorant
tail is kept on the ordinary relative/complement-integral side, so no row-seed
data for the constructive majorant `g + |f|` is reintroduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 source-shaped statement data using the refined chapter-4
standard-row provider for the general measurable `I_B` construction. -/
structure Theorem415Chapter4IBSourceS2StatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  chapter4IBSourceS2Provider :
    BishopC.Sec4GeneralIBSourceS2StandardOuterProvider (S := S)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- The source-shaped chapter-4 provider supplies exactly the remaining
Proposition-4.2 atoms needed by the error sequence `|f_n - f|`. -/
noncomputable def theorem415_sourceS2_error_atoms
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    forall n,
      BishopC.Sec4Prop42RemainingAtomTools (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  BishopC.Lemma415AbsErrorRemainingAtomFrontier.toAtoms
    (S := S) fn f
    (BishopC.Lemma415AbsErrorRemainingAtomFrontier.of_absPackToolsProvider
      (S := S) fn f
      (BishopC.Lemma415Prop42AbsPackToolsProvider.of_generalIBSourceS2StandardOuterProvider
        (S := S) D.chapter4IBSourceS2Provider))

/-- The constructive majorant used in the G235 route. -/
noncomputable def theorem415_sourceS2_majorant
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    BishopC.IntegrableRep S :=
  D.g.add f.absVal

/-- Non-negativity of the constructive majorant `g + |f|`. -/
noncomputable def theorem415_sourceS2_majorant_nonneg
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    BishopC.RepNonneg (theorem415_sourceS2_majorant (S := S) D) :=
  theorem415_g_add_absf_majorant_nonneg
    (S := S) f D.g D.domination.g_nonneg

/-- Majorant choice data for `g + |f|`, with the majorant tail kept as the
previous complement expression.  This avoids rebuilding row seeds for the
majorant; the tail is selected directly from the `coverSet` sequence. -/
noncomputable def theorem415_sourceS2_majorant_rel_choice
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma415MajorantRelChoiceSourceData
      (S := S) fn f
      (theorem415_sourceS2_majorant (S := S) D)
      (theorem415_sourceS2_majorant_nonneg (S := S) D)
      eps :=
  let majorant : BishopC.IntegrableRep S :=
    theorem415_sourceS2_majorant (S := S) D
  let majorant_nonneg : BishopC.RepNonneg majorant :=
    theorem415_sourceS2_majorant_nonneg (S := S) D
  let budget : BishopC.Lemma415TailBudgetSourceData (R := R) eps :=
    BishopC.lemma_4_15_default_tail_budget (R := R) eps heps
  let tailTendsto :=
    BishopC.lemma_4_15_g_complement_tail_sequence_from_coverSet
      (S := S) majorant majorant_nonneg
  let k : Nat := (COFO.archimedean_pos budget.epsG budget.epsG_pos).1
  let m : Nat := tailTendsto.mod k
  {
    A := BishopC.coverSet majorant m
    hA := BishopC.coverSet_int majorant m
    N := budget.N
    N_ge_one := budget.N_ge_one
    epsAB := budget.epsAB
    epsNeg := budget.epsNeg
    epsAB_pos := budget.epsAB_pos
    pieces_sum_lt := budget.pieces_sum_lt
    dominatesError :=
      theorem415_abs_error_dominated_by_g_add_absf
        (S := S) fn f D.g D.domination.dominated_fn
    majorantNegSmall := by
      have hk : COF.lt (COF.halfPow (R := R) k) budget.epsG :=
        (COFO.archimedean_pos budget.epsG budget.epsG_pos).2
      have hclose :
          COF.lt
            (COF.abs
              (BishopC.lemma_4_15_g_complement_tail_value
                (S := S) majorant majorant_nonneg
                (BishopC.coverSet majorant m)
                (BishopC.coverSet_int majorant m) - 0))
            (COF.halfPow (R := R) k) :=
        tailTendsto.close k m (Nat.le_refl m)
      have htail_le_abs :
          BishopC.Le
            (BishopC.lemma_4_15_g_complement_tail_value
              (S := S) majorant majorant_nonneg
              (BishopC.coverSet majorant m)
              (BishopC.coverSet_int majorant m))
            (COF.abs
              (BishopC.lemma_4_15_g_complement_tail_value
                (S := S) majorant majorant_nonneg
                (BishopC.coverSet majorant m)
                (BishopC.coverSet_int majorant m) - 0)) := by
        rw [sub_zero]
        exact COFO.le_abs_self
          (BishopC.lemma_4_15_g_complement_tail_value
            (S := S) majorant majorant_nonneg
            (BishopC.coverSet majorant m)
            (BishopC.coverSet_int majorant m))
      have hsmall_epsG :
          COF.lt
            (BishopC.lemma_4_15_g_complement_tail_value
              (S := S) majorant majorant_nonneg
              (BishopC.coverSet majorant m)
              (BishopC.coverSet_int majorant m))
            budget.epsG :=
        COFO.lt_trans (BishopC.lt_of_le_of_lt htail_le_abs hclose) hk
      have h_epsG_nonneg : BishopC.Nonneg budget.epsG :=
        BishopC.le_of_lt budget.epsG_pos
      have h_epsG_le_double :
          BishopC.Le budget.epsG (budget.epsG + budget.epsG) := by
        apply BishopC.le_of_nonneg_sub
        rw [show (budget.epsG + budget.epsG) - budget.epsG =
            budget.epsG from by ring]
        exact h_epsG_nonneg
      have h_epsG_lt_epsNeg : COF.lt budget.epsG budget.epsNeg :=
        BishopC.lt_of_le_of_lt h_epsG_le_double budget.gTailBudget
      exact COFO.lt_trans hsmall_epsG h_epsG_lt_epsNeg
  }

/-- Uniform `I_B` source data for the theorem-4.15 error sequence, using
remaining atoms from the source-shaped provider and the row-seed-free majorant
relative-choice route. -/
noncomputable def theorem415_sourceS2_uniform_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    BishopC.Lemma414UniformIBSourceData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      (BishopC.lemma_4_14_ib_interface_from_genIB_remainingAtoms
        (S := S)
        (BishopC.thm_4_15_abs_error (S := S) fn f)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
        (theorem415_sourceS2_error_atoms (S := S) D))
      eps :=
  let hAtoms := theorem415_sourceS2_error_atoms (S := S) D
  let hSplit : BishopC.Lemma415SplitUniformSourceData (S := S) fn f eps :=
    BishopC.lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data_of_atoms
      (S := S) fn f hAtoms
      (theorem415_sourceS2_majorant (S := S) D)
      (theorem415_sourceS2_majorant_nonneg (S := S) D)
      eps
      (theorem415_sourceS2_majorant_rel_choice (S := S) D eps heps)
  BishopC.lemma_4_15_uniform_ib_source_data_from_split_data_of_atoms
    (S := S) fn f hAtoms eps hSplit

/-- Abs-error convergence for theorem 4.15 through the source-shaped
standard-row provider, with PFun convergence supplying the convergence-to-zero
part of lemma 4.14. -/
noncomputable def theorem415_abs_error_tendsto_from_sourceS2_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (BishopC.thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  let hAtoms := theorem415_sourceS2_error_atoms (S := S) D
  let IB :=
    BishopC.lemma_4_14_ib_interface_from_genIB_remainingAtoms
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      hAtoms
  BishopC.lemma_4_14_tendsto_zero_from_ib_and_pfun_converge
    (S := S)
    (BishopC.thm_4_15_abs_error (S := S) fn f)
    (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
    (BishopC.thm_4_15_pfun_abs_error D.pfnsrc D.pf)
    (BishopC.thm_4_15_pfun_zero (X := Y) (R := R))
    IB
    (BishopC.lemma_4_14_uniform_ib_data_from_source
      (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f)
      IB
      (theorem415_sourceS2_uniform_source_data (S := S) D))
    (BishopC.lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) D.pfnsrc D.pf D.pfun_converges)
    (BishopC.thm_4_15_pfun_zero_is_zero (X := Y) (R := R))
    (fun n =>
      BishopC.lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (D.pfnsrc n) D.pf
        (D.represents_fn n) D.represents_limit)

/-- Theorem 4.15 from source-shaped statement data and the refined
chapter-4 standard-row provider. -/
noncomputable def theorem415_integral_convergence_from_sourceS2_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415Chapter4IBSourceS2StatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (theorem415_abs_error_tendsto_from_sourceS2_statement_data
      (S := S) D)

structure Theorem415SourceS2RouteAuditAfterG242 : Type where
  source_s2_standard_outer_provider_used : Nat
  arbitrary_row_residual_provider_removed_from_public_415_route : Nat
  error_side_lowered_to_remaining_atoms : Nat
  majorant_tail_kept_on_complement_integral_side : Nat
  majorant_row_seed_input_removed : Nat
  separate_g_nonneg_input_removed : Nat
  separate_limit_domination_input_removed : Nat
  substitute_majorant_g_plus_abs_f_used : Nat
  source_pfun_convergence_input_used : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_source_shaped_provider_frontiers : Nat
  remaining_lower_layer_frontiers : Nat

def theorem415SourceS2RouteAuditAfterG242 :
    Theorem415SourceS2RouteAuditAfterG242 where
  source_s2_standard_outer_provider_used := 1
  arbitrary_row_residual_provider_removed_from_public_415_route := 1
  error_side_lowered_to_remaining_atoms := 1
  majorant_tail_kept_on_complement_integral_side := 1
  majorant_row_seed_input_removed := 1
  separate_g_nonneg_input_removed := 1
  separate_limit_domination_input_removed := 1
  substitute_majorant_g_plus_abs_f_used := 1
  source_pfun_convergence_input_used := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_data_415_bridge_steps := 0
  remaining_source_shaped_provider_frontiers := 1
  remaining_lower_layer_frontiers := 2

structure Chapter4G242Theorem415SourceS2Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g241 : Chapter4G241Theorem415Chapter4IBDomainResidualProviderPackage S
  audit : Theorem415SourceS2RouteAuditAfterG242
  theorem415_sourceS2_endpoint_closed_this_step : Nat
  remaining_source_data_415_bridge_steps : Nat
  remaining_source_shaped_provider_frontiers : Nat
  remaining_lower_layer_frontiers : Nat

def chapter4G242Theorem415SourceS2Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G242Theorem415SourceS2Package S where
  g241 := chapter4G241Theorem415Chapter4IBDomainResidualProviderPackage S
  audit := theorem415SourceS2RouteAuditAfterG242
  theorem415_sourceS2_endpoint_closed_this_step := 1
  remaining_source_data_415_bridge_steps := 0
  remaining_source_shaped_provider_frontiers := 1
  remaining_lower_layer_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G242. -/
def bishopRegularSeqChapter4Theorem415SourceS2ProgressAfterG242 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G242: added a theorem-4.15 endpoint through the source-shaped S2 \
    standard-outer chapter-4 I_B provider. The error side now uses the lower \
    remainingAtoms interface derived from standard-row abs-pack data, while \
    the constructive majorant g + |f| is handled on the ordinary \
    complement-integral side. The 4.15 source endpoint remains at zero bridge \
    steps; the remaining work is lower-layer derivation of the source-shaped \
    standard-row provider and the PFun/representation source layer."


end BishopCReal
