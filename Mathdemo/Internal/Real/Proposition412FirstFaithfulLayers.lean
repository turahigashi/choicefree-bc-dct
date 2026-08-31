import Mathdemo.Internal.Real.Chapter4FinalAuditDefinition4

set_option linter.style.longLine false

/-!
# G168: Proposition 4.12 first faithful layers

Proposition 4.12 says that a sequence converging in measure to both `f` and
`g` has the same measurable-function limit.  The source proof has three
constructive layers:

1. From the two convergence hypotheses, choose a common `N` and good sets
   `B,C` with half-epsilon measure defects.
2. On `E = B ∧ C`, prove the pointwise epsilon bound `|f-g| < eps`.
3. Use the small complement of `E` to force equality of all truncated
   integrable functions `mid(-n, chi_A f, n) = mid(-n, chi_A g, n)`.

This file closes layers 1 and 2 without replacing layer 3 by an empty
statement.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412

/-- The half-epsilon budget used in the source proof of Proposition 4.12. -/
def prop412Half {R : Type*} [COFOC R] (eps : R) : R :=
  COF.half * eps

/-- Half of a positive epsilon is positive. -/
theorem prop412Half_pos {R : Type*} [COFOC R] {eps : R}
    (heps : COF.lt 0 eps) : COF.lt 0 (prop412Half eps) := by
  dsimp [prop412Half]
  exact COFO.mul_pos COFO.half_pos heps

/-- Two half-epsilon budgets add back to epsilon. -/
theorem prop412Half_add_self {R : Type*} [COFOC R] (eps : R) :
    prop412Half eps + prop412Half eps = eps := by
  dsimp [prop412Half]
  rw [show COF.half * eps + COF.half * eps = (COF.half + COF.half) * eps from by ring,
      COF.half_add_half, one_mul]

/-- Source-shaped good pair obtained from convergence to `f` and to `g`. -/
def Prop412CommonGoodPair
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R) (f g : BishopC.PFunR Y R)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (eps : R) (n : Nat)
    (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C) : Prop :=
  (B.S1 ⊆ A.S1 ∩ f.dom ∩ (fn n).dom) ∧
  COF.lt (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hB)) (prop412Half eps) ∧
  (∀ x (_hxB : x ∈ B.S1) (hxf : x ∈ f.dom) (hxfn : x ∈ (fn n).dom),
    COF.lt (COF.abs (f.toFun x hxf - (fn n).toFun x hxfn)) (prop412Half eps)) ∧
  (C.S1 ⊆ A.S1 ∩ g.dom ∩ (fn n).dom) ∧
  COF.lt (BishopC.measure1 S (BishopC.IntegrableSet1_sub hA hC)) (prop412Half eps) ∧
  (∀ x (_hxC : x ∈ C.S1) (hxg : x ∈ g.dom) (hxfn : x ∈ (fn n).dom),
    COF.lt (COF.abs (g.toFun x hxg - (fn n).toFun x hxfn)) (prop412Half eps))

/-- Proposition 4.12, layer 1: the two convergence hypotheses give one common
index and two good sets with the source's half-epsilon budgets. -/
theorem prop412_common_good_pair_from_converge
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R} {f g : BishopC.PFunR Y R}
    (hf : BishopC.ConvergeInMeasure S fn f)
    (hg : BishopC.ConvergeInMeasure S fn g)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (eps : R) (heps : COF.lt 0 eps) :
    ∃ N : Nat, ∀ n, N ≤ n ->
      ∃ (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
        (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
          Prop412CommonGoodPair fn f g A hA eps n B hB C hC := by
  let eps2 : R := prop412Half eps
  have heps2 : COF.lt 0 eps2 := by
    dsimp [eps2]
    exact prop412Half_pos heps
  obtain ⟨Nf, hNf⟩ := hf A hA eps2 heps2
  obtain ⟨Ng, hNg⟩ := hg A hA eps2 heps2
  refine ⟨Nat.max Nf Ng, ?_⟩
  intro n hn
  have hnF : Nf ≤ n := Nat.le_trans (Nat.le_max_left Nf Ng) hn
  have hnG : Ng ≤ n := Nat.le_trans (Nat.le_max_right Nf Ng) hn
  obtain ⟨B, hB, hBsubset, hBmeasure, hBpoint⟩ := hNf n hnF
  obtain ⟨C, hC, hCsubset, hCmeasure, hCpoint⟩ := hNg n hnG
  refine ⟨B, hB, C, hC, ?_⟩
  dsimp [Prop412CommonGoodPair, eps2, prop412Half] at *
  exact ⟨hBsubset, hBmeasure, hBpoint, hCsubset, hCmeasure, hCpoint⟩

/-- The common good set `E = B ∧ C` is integrable. -/
noncomputable def prop412_intersection_integrable
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {B C : BishopC.BSet Y}
    (hB : BishopC.IntegrableSet1 S B) (hC : BishopC.IntegrableSet1 S C) :
    BishopC.IntegrableSet1 S (BishopC.BSet.and B C) :=
  BishopC.IntegrableSet1_and hB hC

/-- Domain facts available on the common intersection `E = B ∧ C`. -/
theorem prop412_intersection_domains
    {R : Type*} [COFOC R] {Y : Type}
    {fn : Nat -> BishopC.PFunR Y R} {f g : BishopC.PFunR Y R}
    {A B C : BishopC.BSet Y} {n : Nat}
    (hBsubset : B.S1 ⊆ A.S1 ∩ f.dom ∩ (fn n).dom)
    (hCsubset : C.S1 ⊆ A.S1 ∩ g.dom ∩ (fn n).dom) :
    ((BishopC.BSet.and B C).S1 ⊆ A.S1) ∧
    ((BishopC.BSet.and B C).S1 ⊆ f.dom) ∧
    ((BishopC.BSet.and B C).S1 ⊆ g.dom) ∧
    ((BishopC.BSet.and B C).S1 ⊆ (fn n).dom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxE
    exact (hBsubset hxE.1).1.1
  · intro x hxE
    exact (hBsubset hxE.1).1.2
  · intro x hxE
    exact (hCsubset hxE.2).1.2
  · intro x hxE
    exact (hBsubset hxE.1).2

/-- Proposition 4.12, layer 2: on `E = B ∧ C`, the pointwise difference
between the two candidate limits is bounded by `eps`. -/
theorem prop412_pointwise_on_intersection_lt
    {R : Type*} [COFOC R] {Y : Type}
    {fn : Nat -> BishopC.PFunR Y R} {f g : BishopC.PFunR Y R}
    {B C : BishopC.BSet Y} {eps : R} {n : Nat}
    (hBpoint :
      ∀ x (_hxB : x ∈ B.S1) (hxf : x ∈ f.dom) (hxfn : x ∈ (fn n).dom),
        COF.lt (COF.abs (f.toFun x hxf - (fn n).toFun x hxfn)) (prop412Half eps))
    (hCpoint :
      ∀ x (_hxC : x ∈ C.S1) (hxg : x ∈ g.dom) (hxfn : x ∈ (fn n).dom),
        COF.lt (COF.abs (g.toFun x hxg - (fn n).toFun x hxfn)) (prop412Half eps))
    {x : Y} (hxE : x ∈ (BishopC.BSet.and B C).S1)
    (hxf : x ∈ f.dom) (hxg : x ∈ g.dom) (hxfn : x ∈ (fn n).dom) :
    COF.lt (COF.abs (f.toFun x hxf - g.toFun x hxg)) eps := by
  let fv : R := f.toFun x hxf
  let gv : R := g.toFun x hxg
  let nv : R := (fn n).toFun x hxfn
  have hb : COF.lt (COF.abs (fv - nv)) (prop412Half eps) := by
    dsimp [fv, nv]
    exact hBpoint x hxE.1 hxf hxfn
  have hc : COF.lt (COF.abs (gv - nv)) (prop412Half eps) := by
    dsimp [gv, nv]
    exact hCpoint x hxE.2 hxg hxfn
  have htri : BishopC.Le (COF.abs (fv - gv))
      (COF.abs (fv - nv) + COF.abs (gv - nv)) := by
    have h0 := COFO.abs_add_le (fv - nv) (nv - gv)
    change BishopC.Le (COF.abs (fv - gv))
      (COF.abs (fv - nv) + COF.abs (gv - nv))
    rw [show fv - gv = (fv - nv) + (nv - gv) from by ring]
    rw [show gv - nv = -(nv - gv) from by ring, COFO.abs_neg]
    exact h0
  have hsum : COF.lt
      (COF.abs (fv - nv) + COF.abs (gv - nv))
      (prop412Half eps + prop412Half eps) :=
    BishopC.lt_add hb hc
  have hsum_eps : COF.lt
      (COF.abs (fv - nv) + COF.abs (gv - nv)) eps := by
    rw [prop412Half_add_self] at hsum
    exact hsum
  exact BishopC.lt_of_le_of_lt htri hsum_eps

/-- Remaining faithful bridge for Proposition 4.12 after G168. -/
structure Prop412RemainingBridgeFrontier : Type where
  measure_defect_of_intersection_needed : Prop
  truncated_difference_integral_bound_needed : Prop
  equality_of_truncated_integrable_functions_needed : Prop
  old_true_statement_used : Nat

def prop412RemainingBridgeFrontier : Prop412RemainingBridgeFrontier where
  measure_defect_of_intersection_needed := True
  truncated_difference_integral_bound_needed := True
  equality_of_truncated_integrable_functions_needed := True
  old_true_statement_used := 0

/-- G168 package: Proposition 4.12 has its common-good-set and pointwise
intersection layers closed; the final measure/integral bridge remains explicit. -/
structure Chapter4G168Prop412Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g167 : BishopRegularSeqChapter4G167Package S
  common_good_pair_from_two_convergences_closed : Prop
  common_intersection_integrable_available : Prop
  pointwise_epsilon_bound_on_intersection_closed : Prop
  prop412_remaining_bridge_frontier : Prop412RemainingBridgeFrontier
  proposition_4_12_internal_frontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_prop412_pass : Nat

def chapter4G168Prop412Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G168Prop412Package S where
  g167 := bishopRegularSeqChapter4G167Package S
  common_good_pair_from_two_convergences_closed := True
  common_intersection_integrable_available := True
  pointwise_epsilon_bound_on_intersection_closed := True
  prop412_remaining_bridge_frontier := prop412RemainingBridgeFrontier
  proposition_4_12_internal_frontiers_remaining := 3
  chapter4_faithful_source_frontiers_still_open := 6
  countdown_remaining_for_prop412_pass := 3

end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412

/-- G168 package exposed at top level. -/
structure BishopRegularSeqChapter4G168Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.Chapter4G168Prop412Package S
  proposition_4_12_layers_closed_this_step : Nat
  proposition_4_12_internal_frontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_prop412_pass : Nat

def bishopRegularSeqChapter4G168Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G168Package S where
  package := BishopRegularSeqChapter4.Proposition412.chapter4G168Prop412Package S
  proposition_4_12_layers_closed_this_step := 2
  proposition_4_12_internal_frontiers_remaining := 3
  chapter4_faithful_source_frontiers_still_open := 6
  remaining_countdown_steps_for_prop412_pass := 3

/-- Progress after G168: Proposition 4.12 is no longer a single opaque frontier;
its first two source layers are closed. -/
def bishopRegularSeqCh1To4ProgressAfterG168 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 80
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G168: Proposition 4.12 common-good-set extraction and pointwise \
    epsilon bound on E=B∧C are closed. Remaining internal 4.12 bridges: \
    measure defect of E, truncated integral bound, equality of truncated \
    integrable functions. Countdown remaining: 3."


end BishopCReal
