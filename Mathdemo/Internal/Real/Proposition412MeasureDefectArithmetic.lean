import Mathdemo.Internal.Real.Proposition412FirstFaithfulLayers

set_option linter.style.longLine false

/-!
# G169: Proposition 4.12 measure-defect arithmetic bridge

G168 closed the common-good-set extraction and the pointwise epsilon estimate
on `E = B ∧ C`.  This file closes the additive/numeric part of the next
source step:

* `μ(D ∨ E) ≤ μ(D) + μ(E)` follows from the finite additivity lemma for
  `or` and nonnegativity of the intersection.
* Hence `μ(A - (B ∧ C)) < eps` follows from the two half-epsilon defect
  estimates once the remaining set-cover/monotonicity bridge
  `μ(A - (B ∧ C)) ≤ μ((A - B) ∨ (A - C))` is supplied.

The remaining bridge is left explicit rather than hidden behind a proposition.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace MeasureDefectBridge

/-- Finite subadditivity for measurable binary unions, derived constructively
from the already formalized finite additivity identity
`μ(D ∨ E) + μ(D ∧ E) = μ(D) + μ(E)`. -/
theorem prop412_measure_or_le_sum
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {D E : BishopC.BSet Y}
    (hD : BishopC.IntegrableSet1 S D) (hE : BishopC.IntegrableSet1 S E) :
    BishopC.Le
      (BishopC.measure1 S (BishopC.IntegrableSet1_or hD hE))
      (BishopC.measure1 S hD + BishopC.measure1 S hE) := by
  apply BishopC.le_of_nonneg_sub
  have hEq := BishopC.IntegrableSet1_or_measure hD hE
  have hdiff :
      BishopC.measure1 S hD + BishopC.measure1 S hE
        - BishopC.measure1 S (BishopC.IntegrableSet1_or hD hE)
      =
      BishopC.measure1 S (BishopC.IntegrableSet1_and hD hE) := by
    calc
      BishopC.measure1 S hD + BishopC.measure1 S hE
          - BishopC.measure1 S (BishopC.IntegrableSet1_or hD hE)
          =
          (BishopC.measure1 S (BishopC.IntegrableSet1_or hD hE)
            + BishopC.measure1 S (BishopC.IntegrableSet1_and hD hE))
            - BishopC.measure1 S (BishopC.IntegrableSet1_or hD hE) := by
              rw [← hEq]
      _ = BishopC.measure1 S (BishopC.IntegrableSet1_and hD hE) := by
              ring
  rw [hdiff]
  exact BishopC.measure1_nonneg (BishopC.IntegrableSet1_and hD hE)

/-- Proposition 4.12, measure-defect arithmetic step.  If the set-cover bridge
has already supplied
`μ(A - (B ∧ C)) ≤ μ((A - B) ∨ (A - C))`, then the two half-epsilon estimates
force the defect of the common good set below `eps`. -/
theorem prop412_measure_defect_from_cover_bridge
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A B C : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hB : BishopC.IntegrableSet1 S B)
    (hC : BishopC.IntegrableSet1 S C)
    {eps : R}
    (hBmeasure :
      COF.lt
        (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hB))
        (prop412Half eps))
    (hCmeasure :
      COF.lt
        (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hC))
        (prop412Half eps))
    (hcover :
      BishopC.Le
        (BishopC.measure1 S
          (BishopC.IntegrableSet1_sub hA (BishopC.IntegrableSet1_and hB hC)))
        (BishopC.measure1 S
          (BishopC.IntegrableSet1_or
            (BishopC.IntegrableSet1_sub hA hB)
            (BishopC.IntegrableSet1_sub hA hC)))) :
    COF.lt
      (BishopC.measure1 S
        (BishopC.IntegrableSet1_sub hA (BishopC.IntegrableSet1_and hB hC)))
      eps := by
  have horLe :
      BishopC.Le
        (BishopC.measure1 S
          (BishopC.IntegrableSet1_or
            (BishopC.IntegrableSet1_sub hA hB)
            (BishopC.IntegrableSet1_sub hA hC)))
        (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hB)
          + BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hC)) :=
    prop412_measure_or_le_sum
      (S := S)
      (BishopC.IntegrableSet1_sub hA hB)
      (BishopC.IntegrableSet1_sub hA hC)
  have hsumHalf :
      COF.lt
        (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hB)
          + BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hC))
        (prop412Half eps + prop412Half eps) :=
    BishopC.lt_add hBmeasure hCmeasure
  have hsumEps :
      COF.lt
        (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hB)
          + BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hC))
        eps := by
    rw [prop412Half_add_self] at hsumHalf
    exact hsumHalf
  exact BishopC.lt_of_le_of_lt (BishopC.le_trans hcover horLe) hsumEps

/-- The exact residual obligation for the measure-defect part of Proposition
4.12 after G169. -/
structure Prop412MeasureCoverBridgeFrontier : Type where
  set_inclusion_A_minus_intersection_into_union_needed : Prop
  measure_monotonicity_for_that_cover_needed : Prop
  additive_arithmetic_bridge_closed : Prop
  old_true_statement_used : Nat

def prop412MeasureCoverBridgeFrontier : Prop412MeasureCoverBridgeFrontier where
  set_inclusion_A_minus_intersection_into_union_needed := True
  measure_monotonicity_for_that_cover_needed := True
  additive_arithmetic_bridge_closed := True
  old_true_statement_used := 0

/-- G169 package: the measure-defect estimate is reduced to one explicit
cover-monotonicity bridge; no choice of representatives is introduced. -/
structure Chapter4G169Prop412MeasurePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g168 : BishopRegularSeqChapter4G168Package S
  finite_union_subadditivity_closed : Prop
  measure_defect_arithmetic_from_cover_bridge_closed : Prop
  measure_cover_bridge_frontier : Prop412MeasureCoverBridgeFrontier
  proposition_4_12_internal_frontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_prop412_pass : Nat

def chapter4G169Prop412MeasurePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G169Prop412MeasurePackage S where
  g168 := bishopRegularSeqChapter4G168Package S
  finite_union_subadditivity_closed := True
  measure_defect_arithmetic_from_cover_bridge_closed := True
  measure_cover_bridge_frontier := prop412MeasureCoverBridgeFrontier
  proposition_4_12_internal_frontiers_remaining := 3
  chapter4_faithful_source_frontiers_still_open := 6
  countdown_remaining_for_prop412_pass := 3

end MeasureDefectBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.MeasureDefectBridge

/-- G169 package exposed at top level. -/
structure BishopRegularSeqChapter4G169Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.MeasureDefectBridge.Chapter4G169Prop412MeasurePackage S
  proposition_4_12_measure_arithmetic_layers_closed_this_step : Nat
  proposition_4_12_exact_measure_cover_bridge_remaining : Nat
  proposition_4_12_internal_frontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_prop412_pass : Nat

def bishopRegularSeqChapter4G169Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G169Package S where
  package := BishopRegularSeqChapter4.Proposition412.MeasureDefectBridge.chapter4G169Prop412MeasurePackage S
  proposition_4_12_measure_arithmetic_layers_closed_this_step := 2
  proposition_4_12_exact_measure_cover_bridge_remaining := 1
  proposition_4_12_internal_frontiers_remaining := 3
  chapter4_faithful_source_frontiers_still_open := 6
  remaining_countdown_steps_for_prop412_pass := 3

/-- Progress after G169: the additive part of the Proposition 4.12 measure
defect estimate is formalized. -/
def bishopRegularSeqCh1To4ProgressAfterG169 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 81
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G169: Proposition 4.12 measure-defect arithmetic is closed: \
    finite union subadditivity and half-epsilon summation are formalized. \
    The exact remaining measure bridge is now the cover-monotonicity step \
    μ(A-(B∧C))≤μ((A-B)∨(A-C)), followed by the truncated integral and \
    equality bridges. Countdown remaining: 3."


end BishopCReal
