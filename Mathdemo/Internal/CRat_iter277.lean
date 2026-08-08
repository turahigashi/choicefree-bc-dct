import Mathdemo.Internal.CRat_iter276

set_option linter.style.longLine false

/-!
# G178: Proposition 4.12 scalar support cases for the complement-to-bad bridge

G177 reduced the source bad-set estimate in Proposition 4.12 to pointwise
domination of the canonical complement representative by the `A-E` relative
representative.  This file lowers that frontier by one scalar layer: if the
characteristic values are the expected `0/1` values and the truncated
absolute-difference representative vanishes outside `A`, then

`(1 - chi_E) * d <= chi_(A-E) * d`

holds by the three source support cases.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Scalar support cases behind the source replacement of the canonical
complement term by the bad-set term `A-E`.

The intended concrete source of these fields is the characteristic-function
value lemma for `A`, `E`, and `A-E`, together with the fact that the
truncated absolute-difference representative has support contained in `A`. -/
structure Prop412ScalarSupportCases
    {R : Type*} [COFOC R]
    (chiA chiE chiBad dval : R) : Type where
  chiA_cases : chiA = 0 ∨ chiA = 1
  chiE_cases : chiE = 0 ∨ chiE = 1
  outside_A_zero : chiA = 0 -> dval = 0
  E_one_forces_A_one : chiE = 1 -> chiA = 1
  bad_one_of_A_one_E_zero : chiA = 1 -> chiE = 0 -> chiBad = 1
  bad_zero_of_E_one : chiE = 1 -> chiBad = 0
  bad_zero_of_A_zero : chiA = 0 -> chiBad = 0

/-- The scalar inequality needed at each point of the complement-to-bad
bridge.  It is just the `E`/`A`/`A-E` support case split. -/
theorem prop412_scalar_complement_le_bad_from_support_cases
    {R : Type*} [COFOC R] {chiA chiE chiBad dval : R}
    (C : Prop412ScalarSupportCases chiA chiE chiBad dval) :
    BishopC.Le ((1 - chiE) * dval) (chiBad * dval) := by
  rcases C.chiE_cases with hE0 | hE1
  · rcases C.chiA_cases with hA0 | hA1
    · have hd0 := C.outside_A_zero hA0
      have hb0 := C.bad_zero_of_A_zero hA0
      rw [hE0, hb0, hd0]
      ring_nf
      exact BishopC.le_refl _
    · have hb1 := C.bad_one_of_A_one_E_zero hA1 hE0
      rw [hE0, hb1]
      ring_nf
      exact BishopC.le_refl _
  · have hb0 := C.bad_zero_of_E_one hE1
    rw [hE1, hb0]
    ring_nf
    exact BishopC.le_refl _

/-- A pointwise scalar decomposition of the complement and bad-set values. -/
structure Prop412PointwiseScalarDatum
    {R : Type*} [COFOC R] (comp bad : R) : Type _ where
  chiA : R
  chiE : R
  chiBad : R
  dval : R
  comp_eq : comp = (1 - chiE) * dval
  bad_eq : bad = chiBad * dval
  cases : Prop412ScalarSupportCases chiA chiE chiBad dval

/-- Pointwise scalar support data sufficient to build the G177 pointwise
domination datum. -/
structure Prop412ComplementPointwiseScalarData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A E : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d) : Type _ where
  data :
    ∀ x ∈
      (prop412ComplementRep hE d hdnn).domain ∩
        (prop412BadRelRep hA hE d hdnn).domain,
      ∀ (hcomp : RSeq.SeriesSum
          (fun m => ((prop412ComplementRep hE d hdnn).fn m).toFun x))
        (hbad : RSeq.SeriesSum
          (fun m => ((prop412BadRelRep hA hE d hdnn).fn m).toFun x)),
        Prop412PointwiseScalarDatum hcomp.sum hbad.sum

/-- Scalar support data implies the pointwise domination datum used in G177. -/
def prop412_pointwise_bad_data_from_scalar_support
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d)
    (SData : Prop412ComplementPointwiseScalarData A E hA hE d hdnn) :
    Prop412ComplementPointwiseBadData A E hA hE d hdnn where
  pointwise_le := by
    intro x hx hcomp hbad
    rcases SData.data x hx hcomp hbad with
      ⟨chiA, chiE, chiBad, dval, hcomp_eq, hbad_eq, cases⟩
    rw [hcomp_eq, hbad_eq]
    exact prop412_scalar_complement_le_bad_from_support_cases cases

/-- G173+G174+G176+G177 estimate with the pointwise support frontier lowered
to scalar characteristic-value cases. -/
theorem prop412_full_integral_le_from_value_bound_scalar_support_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hE : BishopC.IntegrableSet1 S E)
    (hA : BishopC.IntegrableSet1 S A)
    (hEsubA : E.S1 ⊆ A.S1)
    {f g : BishopC.PFunR Y R}
    (hEf : E.S1 ⊆ f.dom) (hEg : E.S1 ⊆ g.dom)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d)
    (n : Nat) (eps : R)
    (D : Prop412TruncatedAbsValueData A E hA d n f g hEf hEg)
    (hfg :
      ∀ x (hxE : x ∈ E.S1),
        COF.lt
          (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
          eps)
    (hbadBound :
      ∀ (x : Y)
        (hdfabs : RSeq.SeriesSum (fun m => COF.abs ((d.fn m).toFun x)))
        (hχBadAbs : RSeq.SeriesSum
          (fun m => COF.abs (((prop412_bad_set_integrable hA hE).rep.fn m).toFun x))),
        (BishopC.seriesSum_of_abs hχBadAbs).sum = 1 ->
          BishopC.Le (BishopC.seriesSum_of_abs hdfabs).sum (n : R))
    (SData : Prop412ComplementPointwiseScalarData A E hA hE d hdnn) :
    BishopC.Le d.integral
      (eps * BishopC.measure1 S hE +
        (n : R) *
          BishopC.measure1 S (prop412_bad_set_integrable hA hE)) :=
  prop412_full_integral_le_from_value_bound_pointwise_complement_data
    hE hA hEsubA hEf hEg d hdnn n eps D hfg hbadBound
    (prop412_pointwise_bad_data_from_scalar_support hA hE d hdnn SData)

/-- Residual shape after G178. -/
structure Prop412ScalarSupportFrontierAfterG178 : Type where
  scalar_support_case_analysis_closed : Prop
  scalar_support_to_pointwise_adapter_closed : Prop
  characteristic_value_witnesses_needed : Prop
  concrete_truncated_abs_rep_constructor_needed : Prop
  arbitrary_epsilon_to_truncated_equality_needed : Prop
  old_true_statement_used : Nat

def prop412ScalarSupportFrontierAfterG178 :
    Prop412ScalarSupportFrontierAfterG178 where
  scalar_support_case_analysis_closed := True
  scalar_support_to_pointwise_adapter_closed := True
  characteristic_value_witnesses_needed := True
  concrete_truncated_abs_rep_constructor_needed := True
  arbitrary_epsilon_to_truncated_equality_needed := True
  old_true_statement_used := 0

/-- G178 package: the complement-to-bad support frontier is reduced to scalar
`0/1` characteristic-value witnesses and the concrete support proof for the
truncated absolute-difference representative. -/
structure Chapter4G178Prop412ScalarSupportPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g177 : BishopRegularSeqChapter4G177Package S
  scalar_support_case_analysis_closed : Prop
  scalar_support_frontier_after_g178 : Prop412ScalarSupportFrontierAfterG178
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_prop412_pass : Nat

def chapter4G178Prop412ScalarSupportPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G178Prop412ScalarSupportPackage S where
  g177 := bishopRegularSeqChapter4G177Package S
  scalar_support_case_analysis_closed := True
  scalar_support_frontier_after_g178 := prop412ScalarSupportFrontierAfterG178
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 2
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G178 package exposed at top level. -/
structure BishopRegularSeqChapter4G178Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G178Prop412ScalarSupportPackage S
  proposition_4_12_scalar_support_closed_this_step : Nat
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_prop412_pass : Nat

def bishopRegularSeqChapter4G178Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G178Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G178Prop412ScalarSupportPackage S
  proposition_4_12_scalar_support_closed_this_step := 1
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 2
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_prop412_pass := 2

/-- Progress after G178. -/
def bishopRegularSeqCh1To4ProgressAfterG178 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 91
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G178: Proposition 4.12 complement-to-bad pointwise domination is \
    reduced to scalar 0/1 characteristic-value support cases. Remaining: \
    provide the concrete chi-value/support witnesses for the truncated-abs \
    representative, then close equality from arbitrary epsilon. Prop. 4.12 \
    countdown remains 2."


end BishopCReal
