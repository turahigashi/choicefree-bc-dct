import Mathdemo.Internal.Real.LiftingLocalPointwiseMidInequalitiesTheorem

set_option linter.style.longLine false

/-!
# G222: scalar ingredients for the Theorem 4.6 pointwise laws

G221 reduced the remaining Theorem 4.6 local domination obligation to
pointwise inequalities between carried mid representative values.

This file closes the scalar ingredients used by those pointwise inequalities:
nonnegativity of `f+`, `f-`, and `|f|`; the bounds `f+ ≤ |f|` and `f- ≤ |f|`;
and the behavior of `mid(-n,z,n)` on nonnegative arguments.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge

/-- Scalar value of the positive part is nonnegative. -/
theorem theorem46_scalar_posPart_nonneg
    {R : Type*} [COFOC R] (a : R) :
    BishopC.Nonneg (COF.max a 0) :=
  COFO.max_zero_nonneg a

/-- Scalar value of the negative part is nonnegative. -/
theorem theorem46_scalar_negPart_nonneg
    {R : Type*} [COFOC R] (a : R) :
    BishopC.Nonneg (COF.max (-a) 0) :=
  COFO.max_zero_nonneg (-a)

/-- Scalar value of the absolute part is nonnegative. -/
theorem theorem46_scalar_absPart_nonneg
    {R : Type*} [COFOC R] (a : R) :
    BishopC.Nonneg (COF.abs a) :=
  BishopC.abs_nonneg a

/-- Scalar positive part is bounded by absolute value. -/
theorem theorem46_scalar_posPart_le_abs
    {R : Type*} [COFOC R] (a : R) :
    BishopC.Le (COF.max a 0) (COF.abs a) :=
  COFO.max_le_abs a

/-- Scalar negative part is bounded by absolute value. -/
theorem theorem46_scalar_negPart_le_abs
    {R : Type*} [COFOC R] (a : R) :
    BishopC.Le (COF.max (-a) 0) (COF.abs a) := by
  have h := COFO.max_le_abs (-a)
  rwa [COFO.abs_neg] at h

/-- Multiplying by a nonnegative characteristic value preserves
`f+ ≤ |f|`. -/
theorem theorem46_chi_mul_posPart_le_chi_mul_abs
    {R : Type*} [COFOC R] {chi a : R}
    (hchi : BishopC.Nonneg chi) :
    BishopC.Le (chi * COF.max a 0) (chi * COF.abs a) :=
  BishopC.mul_le_mul_left (theorem46_scalar_posPart_le_abs a) hchi

/-- Multiplying by a nonnegative characteristic value preserves
`f- ≤ |f|`. -/
theorem theorem46_chi_mul_negPart_le_chi_mul_abs
    {R : Type*} [COFOC R] {chi a : R}
    (hchi : BishopC.Nonneg chi) :
    BishopC.Le (chi * COF.max (-a) 0) (chi * COF.abs a) :=
  BishopC.mul_le_mul_left (theorem46_scalar_negPart_le_abs a) hchi

/-- A nonnegative argument makes `mid(-n,z,n)` equal to `min(z,n)`. -/
theorem theorem46_scalarMid_nonneg_arg_eq_min
    {R : Type*} [COFOC R] (n : Nat) {z : R}
    (hz : BishopC.Nonneg z) :
    prop412ScalarMid n z = COF.min z (n : R) := by
  dsimp [prop412ScalarMid]
  have hn : BishopC.Nonneg (n : R) :=
    BishopC.lemma33_natCast_nonneg n
  have hmin_nonneg : BishopC.Nonneg (COF.min z (n : R)) :=
    BishopC.min_nonneg hz hn
  have hneg_le_zero : BishopC.Le (-(n : R)) 0 := by
    apply BishopC.le_of_nonneg_sub
    convert hn using 1
    ring
  have hneg_le_min : BishopC.Le (-(n : R)) (COF.min z (n : R)) :=
    BishopC.le_trans hneg_le_zero hmin_nonneg
  exact BishopC.cof_max_eq_left_of_le hneg_le_min

/-- On nonnegative arguments, increasing the truncation level increases
`mid(-n,z,n)`. -/
theorem theorem46_scalarMid_nonneg_trunc_mono
    {R : Type*} [COFOC R] {n m : Nat} {z : R}
    (hnm : n ≤ m) (hz : BishopC.Nonneg z) :
    BishopC.Le (prop412ScalarMid n z) (prop412ScalarMid m z) := by
  rw [theorem46_scalarMid_nonneg_arg_eq_min n hz,
    theorem46_scalarMid_nonneg_arg_eq_min m hz]
  exact BishopC.min_le_min_right z (n : R) (m : R)
    (BishopC.lemma33_natCast_mono hnm)

/-- On nonnegative arguments, `mid(-n,-,n)` is monotone in its value input. -/
theorem theorem46_scalarMid_nonneg_value_mono
    {R : Type*} [COFOC R] (n : Nat) {a b : R}
    (ha : BishopC.Nonneg a) (hb : BishopC.Nonneg b)
    (hab : BishopC.Le a b) :
    BishopC.Le (prop412ScalarMid n a) (prop412ScalarMid n b) := by
  rw [theorem46_scalarMid_nonneg_arg_eq_min n ha,
    theorem46_scalarMid_nonneg_arg_eq_min n hb,
    BishopC.COF_min_comm a (n : R),
    BishopC.COF_min_comm b (n : R)]
  exact BishopC.min_le_min_right (n : R) a b hab

/-- Characteristic-weighted positive part is nonnegative. -/
theorem theorem46_chi_mul_posPart_nonneg
    {R : Type*} [COFOC R] {chi a : R}
    (hchi : BishopC.Nonneg chi) :
    BishopC.Nonneg (chi * COF.max a 0) :=
  COFO.mul_nonneg hchi (theorem46_scalar_posPart_nonneg a)

/-- Characteristic-weighted negative part is nonnegative. -/
theorem theorem46_chi_mul_negPart_nonneg
    {R : Type*} [COFOC R] {chi a : R}
    (hchi : BishopC.Nonneg chi) :
    BishopC.Nonneg (chi * COF.max (-a) 0) :=
  COFO.mul_nonneg hchi (theorem46_scalar_negPart_nonneg a)

/-- Characteristic-weighted absolute part is nonnegative. -/
theorem theorem46_chi_mul_absPart_nonneg
    {R : Type*} [COFOC R] {chi a : R}
    (hchi : BishopC.Nonneg chi) :
    BishopC.Nonneg (chi * COF.abs a) :=
  COFO.mul_nonneg hchi (theorem46_scalar_absPart_nonneg a)

/-- The positive-part mid value is bounded by the absolute-part mid value. -/
theorem theorem46_scalarMid_chi_posPart_le_chi_abs
    {R : Type*} [COFOC R] (n : Nat) {chi a : R}
    (hchi : BishopC.Nonneg chi) :
    BishopC.Le
      (prop412ScalarMid n (chi * COF.max a 0))
      (prop412ScalarMid n (chi * COF.abs a)) := by
  exact theorem46_scalarMid_nonneg_value_mono n
    (theorem46_chi_mul_posPart_nonneg hchi)
    (theorem46_chi_mul_absPart_nonneg hchi)
    (theorem46_chi_mul_posPart_le_chi_mul_abs hchi)

/-- The negative-part mid value is bounded by the absolute-part mid value. -/
theorem theorem46_scalarMid_chi_negPart_le_chi_abs
    {R : Type*} [COFOC R] (n : Nat) {chi a : R}
    (hchi : BishopC.Nonneg chi) :
    BishopC.Le
      (prop412ScalarMid n (chi * COF.max (-a) 0))
      (prop412ScalarMid n (chi * COF.abs a)) := by
  exact theorem46_scalarMid_nonneg_value_mono n
    (theorem46_chi_mul_negPart_nonneg hchi)
    (theorem46_chi_mul_absPart_nonneg hchi)
    (theorem46_chi_mul_negPart_le_chi_mul_abs hchi)

/-- Audit after G222. -/
structure Theorem46ScalarPointwiseAuditAfterG222 : Type where
  fpos_fneg_abs_nonneg_scalar_closed : Nat
  fpos_fneg_bounded_by_abs_scalar_closed : Nat
  chi_weighted_part_bounds_closed : Nat
  scalar_mid_nonnegative_reduction_closed : Nat
  scalar_mid_truncation_mono_closed : Nat
  scalar_mid_part_to_abs_bound_closed : Nat
  classical_choice_inputs_added : Nat
  prop_to_data_selector_inputs_added : Nat
  remaining_characteristic_set_expansion_laws : Nat
  remaining_corollary47_connection_steps : Nat

def theorem46ScalarPointwiseAuditAfterG222 :
    Theorem46ScalarPointwiseAuditAfterG222 where
  fpos_fneg_abs_nonneg_scalar_closed := 1
  fpos_fneg_bounded_by_abs_scalar_closed := 1
  chi_weighted_part_bounds_closed := 1
  scalar_mid_nonnegative_reduction_closed := 1
  scalar_mid_truncation_mono_closed := 1
  scalar_mid_part_to_abs_bound_closed := 1
  classical_choice_inputs_added := 0
  prop_to_data_selector_inputs_added := 0
  remaining_characteristic_set_expansion_laws := 1
  remaining_corollary47_connection_steps := 1

/-- G222 package. -/
structure Chapter4G222Theorem46ScalarPointwisePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g221 : Chapter4G221Theorem46PointwiseLiftPackage S
  audit : Theorem46ScalarPointwiseAuditAfterG222
  scalar_pointwise_laws_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G222Theorem46ScalarPointwisePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G222Theorem46ScalarPointwisePackage S where
  g221 := chapter4G221Theorem46PointwiseLiftPackage S
  audit := theorem46ScalarPointwiseAuditAfterG222
  scalar_pointwise_laws_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G222. -/
def bishopRegularSeqChapter4Theorem46ScalarPointwiseProgressAfterG222 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 92
  total_final_goal_percent := 98
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G222: closed the scalar ingredients for Theorem 4.6 pointwise laws: \
    f+, f-, |f| nonnegativity; f+/f- bounded by |f|; chi-weighted bounds; \
    and mid monotonicity on nonnegative arguments. Remaining: characteristic \
    set-expansion laws, then Corollary 4.7/4.10."


end BishopCReal
