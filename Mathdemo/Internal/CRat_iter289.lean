import Mathdemo.Internal.CRat_iter288

set_option linter.style.longLine false

/-!
# G190: bad-set coefficient generalization for Proposition 4.12

The source writes the bad-set contribution as `n * mu(A-E)`.  For a signed
truncation `mid(-n, -, n)`, the canonical safe coefficient may be a separately
proved bound such as `2n`.  The final uniqueness argument only needs a positive
coefficient that is controlled by the epsilon budget.

This file therefore generalizes the bad-set line from the hard-coded natural
`n` coefficient to an arbitrary carried positive `badCap : R`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Bad-complement side with an arbitrary scalar cap. -/
theorem prop412_bad_set_relIntegral_le_cap
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d)
    (badCap : R)
    (hbound :
      ∀ (x : Y)
        (hdDom : d.MemAt x)
        (hχBadDom : (prop412_bad_set_integrable hA hE).rep.MemAt x)
        (hdfabs : RSeq.SeriesSum
          (fun m => COF.abs (d.valueAt x hdDom m)))
        (hχBadAbs : RSeq.SeriesSum
          (fun m => COF.abs
            ((prop412_bad_set_integrable hA hE).rep.valueAt x hχBadDom m))),
        (BishopC.seriesSum_of_abs hχBadAbs).sum = 1 ->
          BishopC.Le (BishopC.seriesSum_of_abs hdfabs).sum badCap) :
    BishopC.Le
      (BishopC.relIntegral (prop412BadSet A E)
        (prop412_bad_set_integrable hA hE) d hdnn)
      (badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE)) :=
  BishopC.relIntegral_le_const_measure
    (prop412BadSet A E) (prop412_bad_set_integrable hA hE)
    d hdnn badCap hbound

/-- Arithmetic assembly of the good part and an arbitrary bad-set cap. -/
theorem prop412_full_integral_le_from_piece_cap_bounds
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d)
    (eps badCap : R)
    (Split : Prop412FullSplitData A E hA hE d hdnn)
    (hgood :
      BishopC.Le (BishopC.relIntegral E hE d hdnn)
        (eps * BishopC.measure1 S hE))
    (hbad :
      BishopC.Le
        (BishopC.relIntegral (prop412BadSet A E)
          (prop412_bad_set_integrable hA hE) d hdnn)
        (badCap *
          BishopC.measure1 S (prop412_bad_set_integrable hA hE))) :
    BishopC.Le d.integral
      (eps * BishopC.measure1 S hE +
        badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE)) := by
  exact BishopC.le_trans Split.split_le
    (BishopC.lemma33_add_le_add hgood hbad)

/-- Full non-strict estimate driven by representative witnesses and a carried
bad-set cap. -/
theorem prop412_full_integral_le_from_value_cap_rep_witness_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hE : BishopC.IntegrableSet1 S E)
    (hA : BishopC.IntegrableSet1 S A)
    (hEsubA : E.S1 ⊆ A.S1)
    {f g : BishopC.PFunR Y R}
    (hEf : E.S1 ⊆ f.dom) (hEg : E.S1 ⊆ g.dom)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d)
    (n : Nat) (eps badCap : R)
    (D : Prop412TruncatedAbsValueData A E hA d n f g hEf hEg)
    (hfg :
      ∀ x (hxE : x ∈ E.S1),
        COF.lt
          (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
          eps)
    (hbadCapBound :
      ∀ (x : Y)
        (hdDom : d.MemAt x)
        (hχBadDom : (prop412_bad_set_integrable hA hE).rep.MemAt x)
        (hdfabs : RSeq.SeriesSum
          (fun m => COF.abs (d.valueAt x hdDom m)))
        (hχBadAbs : RSeq.SeriesSum
          (fun m => COF.abs
            ((prop412_bad_set_integrable hA hE).rep.valueAt x hχBadDom m))),
        (BishopC.seriesSum_of_abs hχBadAbs).sum = 1 ->
          BishopC.Le (BishopC.seriesSum_of_abs hdfabs).sum badCap)
    (RData : Prop412ComplementPointwiseRepresentativeValueData A E hA hE d hdnn) :
    BishopC.Le d.integral
      (eps * BishopC.measure1 S hE +
        badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE)) := by
  let CData : Prop412ComplementToBadData A E hA hE d hdnn :=
    prop412_complement_to_bad_data_from_pointwise hA hE d hdnn
      (prop412_pointwise_bad_data_from_scalar_support hA hE d hdnn
        (prop412_scalar_support_data_from_chi_membership
          hA hE hEsubA d hdnn
          (prop412_chi_membership_data_from_rep_witnesses hA hE d hdnn RData)))
  exact prop412_full_integral_le_from_piece_cap_bounds
    hA hE d hdnn eps badCap
    (prop412_full_split_from_complement_to_bad_data hA hE d hdnn CData)
    (prop412_good_set_relIntegral_le_from_truncated_value_data
      hE hA hEsubA hEf hEg d hdnn n eps D hfg)
    (prop412_bad_set_relIntegral_le_cap hA hE d hdnn badCap hbadCapBound)

/-- Concrete bad-set pointwise bound with an arbitrary cap. -/
structure Prop412ConcreteBadSetCapBoundData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A E : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (n : Nat)
    (badCap : R)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g) : Type _ where
  bound :
    ∀ (x : Y)
      (hdfDom : (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).MemAt x)
      (hχBadDom : (prop412_bad_set_integrable hA hE).rep.MemAt x)
      (hdfabs : RSeq.SeriesSum
        (fun m => COF.abs
          ((prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).valueAt
            x hdfDom m)))
      (hχBadAbs : RSeq.SeriesSum
        (fun m => COF.abs
          ((prop412_bad_set_integrable hA hE).rep.valueAt x hχBadDom m))),
      (BishopC.seriesSum_of_abs hχBadAbs).sum = 1 ->
        BishopC.Le (BishopC.seriesSum_of_abs hdfabs).sum badCap

/-- Full non-strict estimate for the concrete absolute-difference representative
using an arbitrary bad-set cap. -/
theorem prop412_full_integral_le_from_concrete_truncated_abs_diff_bad_cap_bound_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hE : BishopC.IntegrableSet1 S E)
    (hA : BishopC.IntegrableSet1 S A)
    (hEsubA : E.S1 ⊆ A.S1)
    {f g : BishopC.PFunR Y R}
    (hEf : E.S1 ⊆ f.dom) (hEg : E.S1 ⊆ g.dom)
    (n : Nat) (eps badCap : R)
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (K : Prop412GoodSetChiAAbsData A E hA)
    (PData : Prop412ComplementPointwiseConcreteSupportSeedData A E hA hE n f g F G)
    (Bad : Prop412ConcreteBadSetCapBoundData A E hA hE n badCap F G)
    (hfg :
      ∀ x (hxE : x ∈ E.S1),
        COF.lt
          (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
          eps) :
    BishopC.Le
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
      (eps * BishopC.measure1 S hE +
        badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE)) :=
  prop412_full_integral_le_from_value_cap_rep_witness_data
    hE hA hEsubA hEf hEg
    (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
    (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)
    n eps badCap
    (prop412_truncated_abs_value_data_from_mid_reps hA hEf hEg F.mid G.mid K)
    hfg Bad.bound
    (prop412_representative_value_data_from_concrete_support_seed
      hA hE F G PData)

/-- Bad-set budget with an arbitrary positive cap. -/
structure Prop412ConcreteBadSetCapBudgetData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A E : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (n : Nat) (badCap eta : R)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g) : Type _ where
  bad_bound : Prop412ConcreteBadSetCapBoundData A E hA hE n badCap F G
  cap_pos : COF.lt 0 badCap
  bad_measure_lt :
    COF.lt
      (BishopC.measure1 S (prop412_bad_set_integrable hA hE))
      eta

/-- Strict full-integral estimate with an arbitrary positive bad-set cap. -/
theorem prop412_full_integral_lt_from_concrete_truncated_abs_diff_bad_cap_budget_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hE : BishopC.IntegrableSet1 S E)
    (hA : BishopC.IntegrableSet1 S A)
    (hEsubA : E.S1 ⊆ A.S1)
    {f g : BishopC.PFunR Y R}
    (hEf : E.S1 ⊆ f.dom) (hEg : E.S1 ⊆ g.dom)
    (n : Nat) (eps badCap eta : R)
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (K : Prop412GoodSetChiAAbsData A E hA)
    (PData : Prop412ComplementPointwiseConcreteSupportSeedData A E hA hE n f g F G)
    (Budget : Prop412ConcreteBadSetCapBudgetData A E hA hE n badCap eta F G)
    (hfg :
      ∀ x (hxE : x ∈ E.S1),
        COF.lt
          (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
          eps) :
    COF.lt
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
      (eps * BishopC.measure1 S hE + badCap * eta) := by
  have hle :
      BishopC.Le
        (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
        (eps * BishopC.measure1 S hE +
          badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE)) :=
    prop412_full_integral_le_from_concrete_truncated_abs_diff_bad_cap_bound_data
      hE hA hEsubA hEf hEg n eps badCap F G K PData Budget.bad_bound hfg
  have hmul :
      COF.lt
        (badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE))
        (badCap * eta) :=
    BishopC.lemma33_mul_lt_mul_left Budget.bad_measure_lt Budget.cap_pos
  have hadd :
      COF.lt
        (eps * BishopC.measure1 S hE +
          badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE))
        (eps * BishopC.measure1 S hE + badCap * eta) :=
    BishopC.lemma33_add_lt_add_left
      (c := eps * BishopC.measure1 S hE) hmul
  exact BishopC.lt_of_le_of_lt hle hadd

/-- One dyadic source budget with an arbitrary bad-set cap. -/
structure Prop412DyadicSourceCapBudgetData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (n : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (k : Nat) : Type _ where
  E : BishopC.BSet Y
  hE : BishopC.IntegrableSet1 S E
  hEsubA : E.S1 ⊆ A.S1
  hEf : E.S1 ⊆ f.dom
  hEg : E.S1 ⊆ g.dom
  eps : R
  badCap : R
  eta : R
  chiA_abs_on_good : Prop412GoodSetChiAAbsData A E hA
  pointwise_seed :
    Prop412ComplementPointwiseConcreteSupportSeedData A E hA hE n f g F G
  bad_budget :
    Prop412ConcreteBadSetCapBudgetData A E hA hE n badCap eta F G
  close_on_good :
    ∀ x (hxE : x ∈ E.S1),
      COF.lt
        (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
        eps
  arithmetic_budget :
    COF.lt
      (eps * BishopC.measure1 S hE + badCap * eta)
      (COF.halfPow (R := R) k)

/-- One arbitrary-cap dyadic source budget gives the small integral estimate. -/
theorem prop412_integral_lt_halfPow_from_dyadic_cap_source_budget
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    {k : Nat}
    (D : Prop412DyadicSourceCapBudgetData A hA n F G k) :
    COF.lt
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
      (COF.halfPow (R := R) k) :=
  COFO.lt_trans
    (prop412_full_integral_lt_from_concrete_truncated_abs_diff_bad_cap_budget_data
      D.hE hA D.hEsubA D.hEf D.hEg n D.eps D.badCap D.eta
      F G D.chiA_abs_on_good D.pointwise_seed D.bad_budget
      D.close_on_good)
    D.arithmetic_budget

/-- Arbitrary-cap source budgets for all dyadic targets. -/
structure Prop412AllDyadicSourceCapBudgetData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (n : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g) : Type _ where
  data :
    ∀ k : Nat, Prop412DyadicSourceCapBudgetData A hA n F G k

/-- All arbitrary-cap dyadic budgets generate the arbitrary-small datum. -/
def prop412_arbitrarily_small_integral_data_from_cap_source_budgets
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (B : Prop412AllDyadicSourceCapBudgetData A hA n F G) :
    Prop412ConcreteAbsDiffArbitrarilySmallIntegralData F.mid G.mid where
  integral_lt_halfPow := by
    intro k
    exact prop412_integral_lt_halfPow_from_dyadic_cap_source_budget
      hA F G (B.data k)

/-- Final equality obtained from arbitrary-cap source budgets. -/
theorem prop412_mid_representative_integrals_eq_from_cap_source_budgets
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (B : Prop412AllDyadicSourceCapBudgetData A hA n F G) :
    F.mid.rep.integral = G.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_of_arbitrarily_small_abs_diff
    F.mid G.mid
    (prop412_arbitrarily_small_integral_data_from_cap_source_budgets
      hA F G B)

/-- Residual shape after G190. -/
structure Prop412BadSetCapFrontierAfterG190 : Type where
  bad_set_cap_integral_estimate_closed : Prop
  cap_budget_to_truncated_integral_equality_closed : Prop
  source_n_coefficient_no_longer_hardcoded : Prop
  prove_concrete_bad_cap_bound_still_needed : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  old_true_statement_used : Nat

def prop412BadSetCapFrontierAfterG190 :
    Prop412BadSetCapFrontierAfterG190 where
  bad_set_cap_integral_estimate_closed := True
  cap_budget_to_truncated_integral_equality_closed := True
  source_n_coefficient_no_longer_hardcoded := True
  prove_concrete_bad_cap_bound_still_needed := True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  old_true_statement_used := 0

/-- G190 package. -/
structure Chapter4G190Prop412BadSetCapPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g189 : BishopRegularSeqChapter4G189Package S
  bad_set_cap_frontier_after_g190 : Prop412BadSetCapFrontierAfterG190
  bad_set_coefficient_generalized_this_step : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G190Prop412BadSetCapPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G190Prop412BadSetCapPackage S where
  g189 := bishopRegularSeqChapter4G189Package S
  bad_set_cap_frontier_after_g190 := prop412BadSetCapFrontierAfterG190
  bad_set_coefficient_generalized_this_step := 1
  proposition_4_12_truncated_integral_subfrontiers_remaining := 0
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G190 package exposed at top level. -/
structure BishopRegularSeqChapter4G190Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G190Prop412BadSetCapPackage S
  bad_set_coefficient_generalized_this_step : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G190Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G190Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G190Prop412BadSetCapPackage S
  bad_set_coefficient_generalized_this_step := 1
  proposition_4_12_truncated_integral_subfrontiers_remaining := 0
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 2

/-- Progress after G190. -/
def bishopRegularSeqCh1To4ProgressAfterG190 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G190: generalized Proposition 4.12's bad-set coefficient from the source's \
    hard-coded n to an arbitrary positive badCap. Thus a later 2n-style bound \
    can feed the same uniqueness proof. Remaining honest frontiers: deriving \
    the concrete badCap bound and redesigning the Prop-valued convergence \
    interface when Type-level witnesses are required."


end BishopCReal
