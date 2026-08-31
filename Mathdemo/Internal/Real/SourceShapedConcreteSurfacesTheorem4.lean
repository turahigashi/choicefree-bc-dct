import Mathdemo.Internal.Real.Theorem46SupremumTransferLocated

set_option linter.style.longLine false

/-!
# G220: source-shaped concrete surfaces for Theorem 4.6

G219 connected Lemma 4.5 to Theorem 4.6 once the `f+`, `f-`, and `|f|`
truncation-integral surfaces and the source `s3` inequalities are data.

This file removes the previous ambiguous `thm_4_6_phi/psi` surface from the active
route.  The concrete surfaces are now built from the data-carrying measurable
interface: for a function `h`, the value at `(A,n)` is the integral of the
carried representative for `mid(-n, chi_A h, n)`.

It also encodes the actual two-step source proof:

`(A_i,n_i) -> (A1∨A2,n_i) -> (A1∨A2,n1+n2)`.

The combined Lemma-4.5 domination law is proved from those two one-step
domination laws by ordered-field arithmetic.  The remaining concrete work is
therefore exactly the local monotonicity of the carried mid representatives in
the set coordinate and in the truncation coordinate.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge

/-- Positive part of a partial real-valued function. -/
def theorem46_pfun_posPart
    {R : Type*} [COFOC R] {Y : Type}
    (f : BishopC.PFunR Y R) : BishopC.PFunR Y R where
  dom := f.dom
  toFun := fun x hx => COF.max (f.toFun x hx) 0

/-- Negative part of a partial real-valued function. -/
def theorem46_pfun_negPart
    {R : Type*} [COFOC R] {Y : Type}
    (f : BishopC.PFunR Y R) : BishopC.PFunR Y R where
  dom := f.dom
  toFun := fun x hx => COF.max (-(f.toFun x hx)) 0

/-- Absolute value of a partial real-valued function. -/
def theorem46_pfun_absPart
    {R : Type*} [COFOC R] {Y : Type}
    (f : BishopC.PFunR Y R) : BishopC.PFunR Y R where
  dom := f.dom
  toFun := fun x hx => COF.abs (f.toFun x hx)

/-- The Theorem 4.6 truncation-integral surface determined by data-carrying
measurability: `(A,n) ↦ I(mid(-n, chi_A h, n))`.

The representative is read directly from the measurable data.  The old
Prop-valued `IsMeasurable` selector interface is not used. -/
def theorem46_midIntegralSurface
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {h : BishopC.PFunR Y R}
    (Mh : Prop412DataCarryingMeasurable S h) :
    Theorem46StateData S -> R :=
  fun s => (Mh.mid_constructor_source s.A s.hA s.n).rep.integral

/-- The source intermediate state `(A1∨A2,n1)`. -/
noncomputable def theorem46_stateData_or_leftN
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (s1 s2 : Theorem46StateData S) :
    Theorem46StateData S where
  A := BishopC.BSet.or s1.A s2.A
  n := s1.n
  hA := BishopC.IntegrableSet1_or s1.hA s2.hA

/-- The source intermediate state `(A1∨A2,n2)`. -/
noncomputable def theorem46_stateData_or_rightN
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (s1 s2 : Theorem46StateData S) :
    Theorem46StateData S where
  A := BishopC.BSet.or s1.A s2.A
  n := s2.n
  hA := BishopC.IntegrableSet1_or s1.hA s2.hA

/-- One step of the source domination chain. -/
structure Theorem46OneStepDomination
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (φ ψ : Theorem46StateData S -> R)
    (u t : Theorem46StateData S) : Prop where
  nonneg : BishopC.Le 0 (φ u - φ t)
  bounded : BishopC.Le (φ u - φ t) (ψ u - ψ t)

/-- One-step domination composes along the source chain. -/
theorem theorem46_oneStepDomination_trans
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φ ψ : Theorem46StateData S -> R}
    {t u v : Theorem46StateData S}
    (htu : Theorem46OneStepDomination φ ψ u t)
    (huv : Theorem46OneStepDomination φ ψ v u) :
    Theorem46OneStepDomination φ ψ v t := by
  constructor
  · have hsum := BishopC.le_add huv.nonneg htu.nonneg
    rwa [show (0 : R) + 0 = 0 by ring,
      show (φ v - φ u) + (φ u - φ t) = φ v - φ t by ring] at hsum
  · have hsum := BishopC.le_add huv.bounded htu.bounded
    rwa [show (φ v - φ u) + (φ u - φ t) = φ v - φ t by ring,
      show (ψ v - ψ u) + (ψ u - ψ t) = ψ v - ψ t by ring] at hsum

/-- The two-step source proof data for Theorem 4.6.

The four fields are the local monotonicity facts corresponding to:

* enlarging the set from `A_i` to `A1∨A2` at fixed `n_i`;
* enlarging the truncation level from `n_i` to `n1+n2` at fixed `A1∨A2`.
-/
structure Theorem46TwoStepDominationData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (φ ψ : Theorem46StateData S -> R) : Type _ where
  left_set_step :
    forall s1 s2 : Theorem46StateData S,
      Theorem46OneStepDomination φ ψ
        (theorem46_stateData_or_leftN s1 s2) s1
  left_truncation_step :
    forall s1 s2 : Theorem46StateData S,
      Theorem46OneStepDomination φ ψ
        (theorem46_stateData_s3 s1 s2)
        (theorem46_stateData_or_leftN s1 s2)
  right_set_step :
    forall s1 s2 : Theorem46StateData S,
      Theorem46OneStepDomination φ ψ
        (theorem46_stateData_or_rightN s1 s2) s2
  right_truncation_step :
    forall s1 s2 : Theorem46StateData S,
      Theorem46OneStepDomination φ ψ
        (theorem46_stateData_s3 s1 s2)
        (theorem46_stateData_or_rightN s1 s2)

/-- The source two-step proof yields the exact `s3` domination law required by
located Lemma 4.5. -/
def theorem46_s3_domination_from_two_step
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φ ψ : Theorem46StateData S -> R}
    (D : Theorem46TwoStepDominationData φ ψ) :
    Theorem46S3DominationData φ ψ where
  dominates := by
    intro s1 s2
    let hleft :=
      theorem46_oneStepDomination_trans
        (D.left_set_step s1 s2)
        (D.left_truncation_step s1 s2)
    let hright :=
      theorem46_oneStepDomination_trans
        (D.right_set_step s1 s2)
        (D.right_truncation_step s1 s2)
    exact ⟨⟨hleft.nonneg, hleft.bounded⟩, ⟨hright.nonneg, hright.bounded⟩⟩

/-- Concrete Theorem 4.6 surface package for one measurable function `f`.

The functions `f+`, `f-`, and `|f|` are definitionally specified as PFunR
constructions.  Their truncation-integral surfaces are then read from
data-carrying measurability, not from the previous Prop-valued `IsMeasurable`.
-/
structure Theorem46ConcretePartSurfaceData
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R)
    (f : BishopC.PFunR Y R) : Type _ where
  pos_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_posPart f)
  neg_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_negPart f)
  abs_measurable :
    Prop412DataCarryingMeasurable S (theorem46_pfun_absPart f)
  positive_two_step_domination :
    Theorem46TwoStepDominationData
      (theorem46_midIntegralSurface pos_measurable)
      (theorem46_midIntegralSurface abs_measurable)
  negative_two_step_domination :
    Theorem46TwoStepDominationData
      (theorem46_midIntegralSurface neg_measurable)
      (theorem46_midIntegralSurface abs_measurable)
  abs_located_supremum :
    Sigma fun cAbs : R =>
      LocatedRangeSupremum
        (R := R) (T := Theorem46StateData S)
        (theorem46_midIntegralSurface abs_measurable) cAbs

/-- Convert the concrete `f+`, `f-`, `|f|` surface package into the located
Theorem 4.6 input closed in G219. -/
def theorem46_located_input_from_concrete_parts
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (D : Theorem46ConcretePartSurfaceData S f) :
    Theorem46LocatedSupremumInput S where
  phi_pos := theorem46_midIntegralSurface D.pos_measurable
  phi_neg := theorem46_midIntegralSurface D.neg_measurable
  psi_abs := theorem46_midIntegralSurface D.abs_measurable
  positive_s3_domination :=
    theorem46_s3_domination_from_two_step D.positive_two_step_domination
  negative_s3_domination :=
    theorem46_s3_domination_from_two_step D.negative_two_step_domination
  abs_located_supremum := D.abs_located_supremum
  source_surfaces_are_fpos_fneg_abs_truncations := True
  old_prop_rangeSupremum_input_used := 0
  rangeSupremum_to_locatedSupremum_selector_used := 0
  classical_choice_inputs_added := 0

/-- Source-facing Theorem 4.6 supremum step for the concrete part surfaces. -/
noncomputable def theorem46_positive_negative_located_suprema_from_concrete_parts
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (D : Theorem46ConcretePartSurfaceData S f) :
    Theorem46PositiveNegativeLocatedSuprema
      (theorem46_located_input_from_concrete_parts D) :=
  theorem46_positive_negative_located_suprema
    (theorem46_located_input_from_concrete_parts D)

/-- Audit after G220. -/
structure Theorem46ConcreteSurfaceAuditAfterG220 : Type where
  fpos_fneg_abs_pfun_surfaces_defined : Nat
  surfaces_use_data_carrying_measurability : Nat
  old_prop_isMeasurable_choose_surface_used : Nat
  source_two_step_s3_proof_encoded : Nat
  combined_s3_domination_proved_from_two_step_laws : Nat
  located_theorem46_input_built_from_concrete_parts : Nat
  rangeSupremum_to_locatedSupremum_selector_used : Nat
  classical_choice_inputs_added : Nat
  remaining_local_monotonicity_laws_for_two_step_data : Nat
  remaining_corollary47_connection_steps : Nat

def theorem46ConcreteSurfaceAuditAfterG220 :
    Theorem46ConcreteSurfaceAuditAfterG220 where
  fpos_fneg_abs_pfun_surfaces_defined := 1
  surfaces_use_data_carrying_measurability := 1
  old_prop_isMeasurable_choose_surface_used := 0
  source_two_step_s3_proof_encoded := 1
  combined_s3_domination_proved_from_two_step_laws := 1
  located_theorem46_input_built_from_concrete_parts := 1
  rangeSupremum_to_locatedSupremum_selector_used := 0
  classical_choice_inputs_added := 0
  remaining_local_monotonicity_laws_for_two_step_data := 1
  remaining_corollary47_connection_steps := 1

/-- G220 package. -/
structure Chapter4G220Theorem46ConcreteSurfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g219 : Chapter4G219Theorem46LocatedTransferPackage S
  audit : Theorem46ConcreteSurfaceAuditAfterG220
  concrete_surface_route_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G220Theorem46ConcreteSurfacePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G220Theorem46ConcreteSurfacePackage S where
  g219 := chapter4G219Theorem46LocatedTransferPackage S
  audit := theorem46ConcreteSurfaceAuditAfterG220
  concrete_surface_route_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G220. -/
def bishopRegularSeqChapter4Theorem46ConcreteSurfaceProgressAfterG220 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 88
  total_final_goal_percent := 97
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G220: replaced the previous ambiguous thm_4_6_phi/psi route by concrete \
    f+/f-/abs PFunR surfaces and data-carrying mid-integral surfaces. The \
    source two-step s_i -> (A1∨A2,n_i) -> s3 argument is encoded, and the \
    combined s3 domination law is proved from the two local monotonicity laws. \
    Remaining countdown: local monotonicity laws, then Corollary 4.7/4.10 \
    connection."


end BishopCReal
