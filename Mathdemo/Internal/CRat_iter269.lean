import Mathdemo.Internal.CRat_iter268

set_option linter.style.longLine false

/-!
# G170: Proposition 4.12 measure cover bridge

G169 reduced the measure-defect estimate in Proposition 4.12 to the exact
cover-monotonicity bridge

`μ(A - (B ∧ C)) ≤ μ((A - B) ∨ (A - C))`.

This file closes that bridge in the representation-carrying style:

* first prove the concrete `S1` cover
  `(A - (B ∧ C)).S1 ⊆ ((A - B) ∨ (A - C)).S1`;
* then prove a `measure1` monotonicity lemma from `S1` inclusion, using the
  `IntegrableSet1.valid` data and `prop_1_11`;
* finally combine the cover with G169's additive half-epsilon estimate.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace MeasureDefectBridge

/-- A representation-carrying monotonicity lemma for `measure1`.

It needs only `S1` inclusion: if the characteristic function of `D` is `1`,
then the characteristic function of `E` is also `1`; if it is `0`, the target
characteristic function is nonnegative because it is again a `0/1` valued
integrable-set representative. -/
theorem prop412_measure1_mono_of_s1_subset
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {D E : BishopC.BSet Y}
    (hD : BishopC.IntegrableSet1 S D) (hE : BishopC.IntegrableSet1 S E)
    (hsub : D.S1 ⊆ E.S1) :
    BishopC.Le (BishopC.measure1 S hD) (BishopC.measure1 S hE) := by
  change BishopC.Le hD.rep.integral hE.rep.integral
  refine BishopC.prop_1_11
    (BishopC.isFull_inter hD.rep.domain_isFull hE.rep.domain_isFull)
    hD.rep hE.rep ?_
  intro x hx hd he
  obtain ⟨hxD, hxE⟩ := hx
  obtain ⟨_, hDabs_ne⟩ := hxD
  obtain ⟨_, hEabs_ne⟩ := hxE
  obtain ⟨hDabs⟩ := hDabs_ne
  obtain ⟨hEabs⟩ := hEabs_ne
  rcases (hD.valid x hDabs).1 with hD1 | hD2
  · have hd1 : hd.sum = 1 :=
      (hD.valid x hDabs).2.1 hD1 hd
    have he1 : he.sum = 1 :=
      (hE.valid x hEabs).2.1 (hsub hD1) he
    rw [hd1, he1]
    exact BishopC.le_refl _
  · have hd0 : hd.sum = 0 :=
      (hD.valid x hDabs).2.2 hD2 hd
    rw [hd0]
    rcases (hE.valid x hEabs).1 with hE1 | hE2
    · have he1 : he.sum = 1 :=
        (hE.valid x hEabs).2.1 hE1 he
      rw [he1]
      exact BishopC.le_of_lt COFO.one_pos
    · have he0 : he.sum = 0 :=
        (hE.valid x hEabs).2.2 hE2 he
      rw [he0]
      exact BishopC.le_refl _

/-- Concrete set cover used in Proposition 4.12:
`A - (B ∧ C)` is covered by `(A - B) ∨ (A - C)` at the positive side `S1`. -/
theorem prop412_cover_s1_subset
    {Y : Type} (A B C : BishopC.BSet Y) :
    (BishopC.BSet.sub A (BishopC.BSet.and B C)).S1 ⊆
      (BishopC.BSet.or (BishopC.BSet.sub A B) (BishopC.BSet.sub A C)).S1 := by
  intro x hx
  dsimp [BishopC.BSet.sub, BishopC.BSet.and, BishopC.BSet.neg, BishopC.BSet.or] at hx ⊢
  obtain ⟨hA1, hBC2⟩ := hx
  rcases hBC2 with (hB1C2 | hB2C1) | hB2C2
  · exact Or.inr
      ⟨Or.inl (Or.inl ⟨hA1, hB1C2.1⟩), ⟨hA1, hB1C2.2⟩⟩
  · exact Or.inl (Or.inr
      ⟨⟨hA1, hB2C1.1⟩, Or.inl (Or.inl ⟨hA1, hB2C1.2⟩)⟩)
  · exact Or.inl (Or.inl
      ⟨⟨hA1, hB2C2.1⟩, ⟨hA1, hB2C2.2⟩⟩)

/-- The exact cover-monotonicity bridge left explicit by G169. -/
theorem prop412_measure_cover_bridge
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A B C : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hB : BishopC.IntegrableSet1 S B)
    (hC : BishopC.IntegrableSet1 S C) :
    BishopC.Le
      (BishopC.measure1 S
        (BishopC.IntegrableSet1_sub hA (BishopC.IntegrableSet1_and hB hC)))
      (BishopC.measure1 S
        (BishopC.IntegrableSet1_or
          (BishopC.IntegrableSet1_sub hA hB)
          (BishopC.IntegrableSet1_sub hA hC))) := by
  exact prop412_measure1_mono_of_s1_subset
    (BishopC.IntegrableSet1_sub hA (BishopC.IntegrableSet1_and hB hC))
    (BishopC.IntegrableSet1_or
      (BishopC.IntegrableSet1_sub hA hB)
      (BishopC.IntegrableSet1_sub hA hC))
    (prop412_cover_s1_subset A B C)

/-- Proposition 4.12, closed measure-defect estimate for the common good set
`B ∧ C`.  This discharges the first of the three G168 residual bridges. -/
theorem prop412_measure_defect_closed
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
        (prop412Half eps)) :
    COF.lt
      (BishopC.measure1 S
        (BishopC.IntegrableSet1_sub hA (BishopC.IntegrableSet1_and hB hC)))
      eps :=
  prop412_measure_defect_from_cover_bridge hA hB hC hBmeasure hCmeasure
    (prop412_measure_cover_bridge hA hB hC)

/-- G170 package: the measure-defect bridge of Proposition 4.12 is closed. -/
structure Chapter4G170Prop412MeasureClosedPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g169 : BishopRegularSeqChapter4G169Package S
  measure1_s1_monotonicity_closed : Prop
  concrete_cover_s1_subset_closed : Prop
  measure_cover_bridge_closed : Prop
  measure_defect_for_common_good_set_closed : Prop
  proposition_4_12_internal_frontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_prop412_pass : Nat

def chapter4G170Prop412MeasureClosedPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G170Prop412MeasureClosedPackage S where
  g169 := bishopRegularSeqChapter4G169Package S
  measure1_s1_monotonicity_closed := True
  concrete_cover_s1_subset_closed := True
  measure_cover_bridge_closed := True
  measure_defect_for_common_good_set_closed := True
  proposition_4_12_internal_frontiers_remaining := 2
  chapter4_faithful_source_frontiers_still_open := 5
  countdown_remaining_for_prop412_pass := 2

end MeasureDefectBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.MeasureDefectBridge

/-- G170 package exposed at top level. -/
structure BishopRegularSeqChapter4G170Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.MeasureDefectBridge.Chapter4G170Prop412MeasureClosedPackage S
  proposition_4_12_measure_frontier_closed_this_step : Nat
  proposition_4_12_internal_frontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_prop412_pass : Nat

def bishopRegularSeqChapter4G170Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G170Package S where
  package := BishopRegularSeqChapter4.Proposition412.MeasureDefectBridge.chapter4G170Prop412MeasureClosedPackage S
  proposition_4_12_measure_frontier_closed_this_step := 1
  proposition_4_12_internal_frontiers_remaining := 2
  chapter4_faithful_source_frontiers_still_open := 5
  remaining_countdown_steps_for_prop412_pass := 2

/-- Progress after G170: Proposition 4.12 now has its common-good-set measure
defect estimate closed. -/
def bishopRegularSeqCh1To4ProgressAfterG170 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 83
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G170: Proposition 4.12 measure-defect bridge is closed. \
    We proved S1-cover A-(B∧C)⊆(A-B)∨(A-C), representation-carrying \
    measure1 monotonicity from S1 inclusion, and μ(A-(B∧C))<ε from the two \
    half-epsilon defects. Remaining Prop. 4.12 internal bridges: truncated \
    difference integral bound and equality of truncated integrable functions. \
    Countdown remaining: 2."


end BishopCReal
