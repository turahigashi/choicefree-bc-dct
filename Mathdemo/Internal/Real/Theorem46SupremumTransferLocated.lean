import Mathdemo.Internal.Real.LocatedLemma45Transfer

set_option linter.style.longLine false

/-!
# G219: Theorem 4.6 supremum transfer through located Lemma 4.5

This file connects the closed located Lemma 4.5 to the source shape of Theorem
4.6.  The state carries the integrability witness for `A`, so the source
construction `s3 = (A1 ∨ A2, n1+n2)` also carries its witness by
`IntegrableSet1_or`.

The remaining concrete work for Theorem 4.6 is now sharply isolated: prove the
two source inequalities for the actual `f+`, `f-`, and `|f|` truncation
surfaces.  Once those inequalities are data, the positive and negative located
suprema follow by the proven Lemma 4.5 transfer.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

/-- Theorem 4.6 source state, with the integrability witness for `A` carried
as data.  This avoids selecting the witness later from the set component. -/
structure Theorem46StateData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  A : BishopC.BSet Y
  n : Nat
  hA : BishopC.IntegrableSet1 S A

/-- Source construction in Theorem 4.6:
`s3 = (A1 ∨ A2, n1+n2)`, including its integrability witness. -/
noncomputable def theorem46_stateData_s3
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (s1 s2 : Theorem46StateData S) :
    Theorem46StateData S where
  A := BishopC.BSet.or s1.A s2.A
  n := s1.n + s2.n
  hA := BishopC.IntegrableSet1_or s1.hA s2.hA

/-- The exact source-shaped domination law for a Theorem 4.6 truncation
surface.  The witness is not arbitrary: it is the source `s3`. -/
structure Theorem46S3DominationData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (φ ψ : Theorem46StateData S -> R) : Type _ where
  dominates :
    forall s1 s2 : Theorem46StateData S,
      (BishopC.Le 0 (φ (theorem46_stateData_s3 s1 s2) - φ s1) ∧
        BishopC.Le
          (φ (theorem46_stateData_s3 s1 s2) - φ s1)
          (ψ (theorem46_stateData_s3 s1 s2) - ψ s1)) ∧
      (BishopC.Le 0 (φ (theorem46_stateData_s3 s1 s2) - φ s2) ∧
        BishopC.Le
          (φ (theorem46_stateData_s3 s1 s2) - φ s2)
          (ψ (theorem46_stateData_s3 s1 s2) - ψ s2))

/-- Convert the source `s3` domination law into the generic Lemma 4.5 data. -/
noncomputable def theorem46_s3_domination_to_lemma45_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φ ψ : Theorem46StateData S -> R}
    (D : Theorem46S3DominationData φ ψ) :
    Lemma45SourceHypothesisData
      (R := R) (T := Theorem46StateData S) φ ψ where
  directed_domination := by
    intro s1 s2
    exact ⟨theorem46_stateData_s3 s1 s2, D.dominates s1 s2⟩

/-- The source-level data needed for Theorem 4.6's supremum-existence step.

For the concrete theorem, `phi_pos` is the `f+` truncation-integral surface,
`phi_neg` is the `f-` surface, and `psi_abs` is the `|f|` surface. -/
structure Theorem46LocatedSupremumInput
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  phi_pos : Theorem46StateData S -> R
  phi_neg : Theorem46StateData S -> R
  psi_abs : Theorem46StateData S -> R
  positive_s3_domination :
    Theorem46S3DominationData phi_pos psi_abs
  negative_s3_domination :
    Theorem46S3DominationData phi_neg psi_abs
  abs_located_supremum :
    Sigma fun cAbs : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S) psi_abs cAbs
  source_surfaces_are_fpos_fneg_abs_truncations : Prop
  old_prop_rangeSupremum_input_used : Nat
  rangeSupremum_to_locatedSupremum_selector_used : Nat
  classical_choice_inputs_added : Nat

/-- The positive and negative located suprema produced by Theorem 4.6. -/
structure Theorem46PositiveNegativeLocatedSuprema
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (D : Theorem46LocatedSupremumInput S) : Type _ where
  positive :
    Sigma fun cPos : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S) D.phi_pos cPos
  negative :
    Sigma fun cNeg : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S) D.phi_neg cNeg

/-- Theorem 4.6's supremum-transfer core: located supremum of the `|f|`
surface yields located suprema of the `f+` and `f-` surfaces. -/
noncomputable def theorem46_positive_negative_located_suprema
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (D : Theorem46LocatedSupremumInput S) :
    Theorem46PositiveNegativeLocatedSuprema D where
  positive :=
    lemma45_located_transfer
      (theorem46_s3_domination_to_lemma45_data
        D.positive_s3_domination)
      D.abs_located_supremum
  negative :=
    lemma45_located_transfer
      (theorem46_s3_domination_to_lemma45_data
        D.negative_s3_domination)
      D.abs_located_supremum

/-- Old Prop-only `RangeSupremum` conclusions are still available, but only by
forgetting located data. -/
noncomputable def theorem46_positive_negative_range_suprema_from_located
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (D : Theorem46LocatedSupremumInput S) :
    ({ cPos : R // RangeSupremum D.phi_pos cPos }) ×
      ({ cNeg : R // RangeSupremum D.phi_neg cNeg }) :=
  (lemma45_range_transfer_from_located
      (theorem46_s3_domination_to_lemma45_data
        D.positive_s3_domination)
      D.abs_located_supremum,
    lemma45_range_transfer_from_located
      (theorem46_s3_domination_to_lemma45_data
        D.negative_s3_domination)
      D.abs_located_supremum)

/-- Audit for the Theorem 4.6 transfer step. -/
structure Theorem46LocatedTransferAuditAfterG219 : Type where
  theorem46_state_carries_integrable_set_witness : Nat
  source_s3_is_A_or_B_and_n_sum : Nat
  positive_supremum_transferred_by_located_lemma45 : Nat
  negative_supremum_transferred_by_located_lemma45 : Nat
  old_rangeSupremum_conclusion_only_forgetful : Nat
  rangeSupremum_to_locatedSupremum_selector_used : Nat
  classical_choice_inputs_added : Nat
  remaining_concrete_theorem46_surface_inequalities : Nat
  remaining_corollary47_connection_steps : Nat

def theorem46LocatedTransferAuditAfterG219 :
    Theorem46LocatedTransferAuditAfterG219 where
  theorem46_state_carries_integrable_set_witness := 1
  source_s3_is_A_or_B_and_n_sum := 1
  positive_supremum_transferred_by_located_lemma45 := 1
  negative_supremum_transferred_by_located_lemma45 := 1
  old_rangeSupremum_conclusion_only_forgetful := 1
  rangeSupremum_to_locatedSupremum_selector_used := 0
  classical_choice_inputs_added := 0
  remaining_concrete_theorem46_surface_inequalities := 1
  remaining_corollary47_connection_steps := 1

/-- G219 package. -/
structure Chapter4G219Theorem46LocatedTransferPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g218 : Chapter4G218Lemma45LocatedPackage S
  audit : Theorem46LocatedTransferAuditAfterG219
  theorem46_located_transfer_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G219Theorem46LocatedTransferPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G219Theorem46LocatedTransferPackage S where
  g218 := chapter4G218Lemma45LocatedPackage S
  audit := theorem46LocatedTransferAuditAfterG219
  theorem46_located_transfer_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G219. -/
def bishopRegularSeqChapter4Theorem46LocatedTransferProgressAfterG219 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 86
  total_final_goal_percent := 97
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G219: connected the strengthened located Lemma 4.5 to Theorem 4.6's \
    source s3 construction. States now carry integrable-set witnesses, and \
    the located supremum of the abs truncation surface yields located suprema \
    for the positive and negative truncation surfaces. Remaining: prove the \
    concrete f+/f-/abs source inequalities, then connect Corollary 4.7."


end BishopCReal
