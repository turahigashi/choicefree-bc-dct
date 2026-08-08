import Mathdemo.Internal.CRat_iter277

set_option linter.style.longLine false

/-!
# G179: Proposition 4.12 chi-membership data to scalar support cases

G178 reduced the complement-to-bad estimate in Proposition 4.12 to scalar
`0/1` support cases.  This file closes the set-theoretic part of that
frontier: once characteristic values are tied to `S1`/`S2` membership, the
cases for `A-E` follow directly from `BSet.sub A E = A ∧ -E` and the source
assumption `E.S1 ⊆ A.S1`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- If `x ∈ A` and `x ∈ -E`, then `x ∈ A-E`. -/
theorem prop412_bad_s1_of_A1_E2
    {Y : Type} {A E : BishopC.BSet Y} {x : Y}
    (hxA : x ∈ A.S1) (hxE : x ∈ E.S2) :
    x ∈ (prop412BadSet A E).S1 := by
  dsimp [prop412BadSet, BishopC.BSet.sub, BishopC.BSet.and, BishopC.BSet.neg]
  exact ⟨hxA, hxE⟩

/-- If `x ∈ A ∩ E`, then `x` is on the zero side of `A-E`. -/
theorem prop412_bad_s2_of_A1_E1
    {Y : Type} {A E : BishopC.BSet Y} {x : Y}
    (hxA : x ∈ A.S1) (hxE : x ∈ E.S1) :
    x ∈ (prop412BadSet A E).S2 := by
  dsimp [prop412BadSet, BishopC.BSet.sub, BishopC.BSet.and, BishopC.BSet.neg]
  exact Or.inl (Or.inl ⟨hxA, hxE⟩)

/-- If `x` is outside `A` and outside `E`, then it is on the zero side of
`A-E`. -/
theorem prop412_bad_s2_of_A2_E2
    {Y : Type} {A E : BishopC.BSet Y} {x : Y}
    (hxA : x ∈ A.S2) (hxE : x ∈ E.S2) :
    x ∈ (prop412BadSet A E).S2 := by
  dsimp [prop412BadSet, BishopC.BSet.sub, BishopC.BSet.and, BishopC.BSet.neg]
  exact Or.inl (Or.inr ⟨hxA, hxE⟩)

/-- If `x` is outside `A` but in `E`, then it is on the zero side of `A-E`. -/
theorem prop412_bad_s2_of_A2_E1
    {Y : Type} {A E : BishopC.BSet Y} {x : Y}
    (hxA : x ∈ A.S2) (hxE : x ∈ E.S1) :
    x ∈ (prop412BadSet A E).S2 := by
  dsimp [prop412BadSet, BishopC.BSet.sub, BishopC.BSet.and, BishopC.BSet.neg]
  exact Or.inr ⟨hxA, hxE⟩

/-- Characteristic values tied to the complemented-set membership data at one
point.  The next concrete representative step should fill these fields using
the existing `IntegrableSet1.valid`/`prop_4_2_chi_f_rep_value` witnesses. -/
structure Prop412ChiMembershipValueData
    {R : Type*} [COFOC R] {Y : Type}
    (A E : BishopC.BSet Y) (x : Y)
    (chiA chiE chiBad : R) : Type where
  chiA_cases : chiA = 0 ∨ chiA = 1
  chiE_cases : chiE = 0 ∨ chiE = 1
  chiA_one_mem_s1 : chiA = 1 -> x ∈ A.S1
  chiA_zero_mem_s2 : chiA = 0 -> x ∈ A.S2
  chiA_one_of_mem_s1 : x ∈ A.S1 -> chiA = 1
  chiE_one_mem_s1 : chiE = 1 -> x ∈ E.S1
  chiE_zero_mem_s2 : chiE = 0 -> x ∈ E.S2
  chiBad_one_of_mem_s1 : x ∈ (prop412BadSet A E).S1 -> chiBad = 1
  chiBad_zero_of_mem_s2 : x ∈ (prop412BadSet A E).S2 -> chiBad = 0

/-- The set-membership interpretation of characteristic values supplies all
scalar support cases required by G178. -/
def prop412_scalar_support_cases_from_chi_membership_data
    {R : Type*} [COFOC R] {Y : Type}
    {A E : BishopC.BSet Y} {x : Y}
    {chiA chiE chiBad dval : R}
    (hEsubA : E.S1 ⊆ A.S1)
    (M : Prop412ChiMembershipValueData A E x chiA chiE chiBad)
    (houtside : chiA = 0 -> dval = 0) :
    Prop412ScalarSupportCases chiA chiE chiBad dval where
  chiA_cases := M.chiA_cases
  chiE_cases := M.chiE_cases
  outside_A_zero := houtside
  E_one_forces_A_one := by
    intro hχE1
    exact M.chiA_one_of_mem_s1 (hEsubA (M.chiE_one_mem_s1 hχE1))
  bad_one_of_A_one_E_zero := by
    intro hχA1 hχE0
    exact M.chiBad_one_of_mem_s1
      (prop412_bad_s1_of_A1_E2
        (M.chiA_one_mem_s1 hχA1)
        (M.chiE_zero_mem_s2 hχE0))
  bad_zero_of_E_one := by
    intro hχE1
    have hxE1 : x ∈ E.S1 := M.chiE_one_mem_s1 hχE1
    exact M.chiBad_zero_of_mem_s2
      (prop412_bad_s2_of_A1_E1 (hEsubA hxE1) hxE1)
  bad_zero_of_A_zero := by
    intro hχA0
    have hxA2 : x ∈ A.S2 := M.chiA_zero_mem_s2 hχA0
    rcases M.chiE_cases with hχE0 | hχE1
    · exact M.chiBad_zero_of_mem_s2
        (prop412_bad_s2_of_A2_E2 hxA2 (M.chiE_zero_mem_s2 hχE0))
    · exact M.chiBad_zero_of_mem_s2
        (prop412_bad_s2_of_A2_E1 hxA2 (M.chiE_one_mem_s1 hχE1))

/-- A pointwise decomposition plus membership-valued characteristic data. -/
structure Prop412PointwiseChiMembershipDatum
    {R : Type*} [COFOC R] {Y : Type}
    (A E : BishopC.BSet Y) (x : Y) (comp bad : R) : Type _ where
  chiA : R
  chiE : R
  chiBad : R
  dval : R
  comp_eq : comp = (1 - chiE) * dval
  bad_eq : bad = chiBad * dval
  chi_membership : Prop412ChiMembershipValueData A E x chiA chiE chiBad
  outside_A_zero : chiA = 0 -> dval = 0

/-- Pointwise chi-membership data sufficient to construct the G178 scalar
support data. -/
structure Prop412ComplementPointwiseChiMembershipData
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
        Prop412PointwiseChiMembershipDatum A E x hcomp.sum hbad.sum

/-- Convert pointwise chi-membership data into the scalar support datum used
by G178. -/
def prop412_scalar_support_data_from_chi_membership
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (hEsubA : E.S1 ⊆ A.S1)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d)
    (CData : Prop412ComplementPointwiseChiMembershipData A E hA hE d hdnn) :
    Prop412ComplementPointwiseScalarData A E hA hE d hdnn where
  data := by
    intro x hx hcomp hbad
    rcases CData.data x hx hcomp hbad with
      ⟨chiA, chiE, chiBad, dval, hcomp_eq, hbad_eq, hmem, houtside⟩
    exact
      { chiA := chiA
        chiE := chiE
        chiBad := chiBad
        dval := dval
        comp_eq := hcomp_eq
        bad_eq := hbad_eq
        cases :=
          prop412_scalar_support_cases_from_chi_membership_data
            hEsubA hmem houtside }

/-- The current full estimate can now be driven by chi-membership data rather
than raw scalar support cases. -/
theorem prop412_full_integral_le_from_value_bound_chi_membership_data
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
    (CData : Prop412ComplementPointwiseChiMembershipData A E hA hE d hdnn) :
    BishopC.Le d.integral
      (eps * BishopC.measure1 S hE +
        (n : R) *
          BishopC.measure1 S (prop412_bad_set_integrable hA hE)) :=
  prop412_full_integral_le_from_value_bound_scalar_support_data
    hE hA hEsubA hEf hEg d hdnn n eps D hfg hbadBound
    (prop412_scalar_support_data_from_chi_membership
      hA hE hEsubA d hdnn CData)

/-- Residual shape after G179. -/
structure Prop412ChiMembershipFrontierAfterG179 : Type where
  bad_set_membership_cases_closed : Prop
  chi_membership_to_scalar_support_closed : Prop
  chi_membership_to_integral_estimate_adapter_closed : Prop
  representative_chi_membership_witnesses_needed : Prop
  concrete_truncated_abs_rep_constructor_needed : Prop
  arbitrary_epsilon_to_truncated_equality_needed : Prop
  old_true_statement_used : Nat

def prop412ChiMembershipFrontierAfterG179 :
    Prop412ChiMembershipFrontierAfterG179 where
  bad_set_membership_cases_closed := True
  chi_membership_to_scalar_support_closed := True
  chi_membership_to_integral_estimate_adapter_closed := True
  representative_chi_membership_witnesses_needed := True
  concrete_truncated_abs_rep_constructor_needed := True
  arbitrary_epsilon_to_truncated_equality_needed := True
  old_true_statement_used := 0

/-- G179 package: `A-E` support cases now follow from chi-membership data. -/
structure Chapter4G179Prop412ChiMembershipPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g178 : BishopRegularSeqChapter4G178Package S
  chi_membership_support_adapter_closed : Prop
  chi_membership_frontier_after_g179 : Prop412ChiMembershipFrontierAfterG179
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_prop412_pass : Nat

def chapter4G179Prop412ChiMembershipPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G179Prop412ChiMembershipPackage S where
  g178 := bishopRegularSeqChapter4G178Package S
  chi_membership_support_adapter_closed := True
  chi_membership_frontier_after_g179 := prop412ChiMembershipFrontierAfterG179
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 2
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G179 package exposed at top level. -/
structure BishopRegularSeqChapter4G179Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G179Prop412ChiMembershipPackage S
  proposition_4_12_chi_membership_closed_this_step : Nat
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_prop412_pass : Nat

def bishopRegularSeqChapter4G179Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G179Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G179Prop412ChiMembershipPackage S
  proposition_4_12_chi_membership_closed_this_step := 1
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 2
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_prop412_pass := 2

/-- Progress after G179. -/
def bishopRegularSeqCh1To4ProgressAfterG179 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 92
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G179: Proposition 4.12 A-E support cases are derived from \
    chi-membership value data and E.S1 subset A.S1. Remaining: construct \
    the concrete representative-level chi-membership/truncated-abs witnesses, \
    then close equality from arbitrary epsilon. Prop. 4.12 countdown remains 2."


end BishopCReal
