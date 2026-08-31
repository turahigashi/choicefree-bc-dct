import Mathdemo.Internal.Real.DirectComplementBadComparisonDefinitionWitnesses

set_option linter.style.longLine false

/-!
# G214: downstream two-nat route without pointwise seeds

G213 removed the low-level need for the previous pointwise seed.  This increment
threads that direct full-definition-witness estimate through the dyadic
source-budget and two-nat convergence route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Full non-strict arbitrary-cap estimate for the concrete representative,
using the G213 full-definition-witness complement bridge instead of a
pointwise seed. -/
theorem prop412_full_integral_le_from_concrete_truncated_abs_diff_bad_cap_bound_full_definition_witnesses
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
    (Bad : Prop412ConcreteBadSetCapBoundData A E hA hE n badCap F G)
    (hfg :
      ∀ x (hxE : x ∈ E.S1),
        COF.lt
          (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
          eps) :
    BishopC.Le
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
      (eps * BishopC.measure1 S hE +
        badCap * BishopC.measure1 S (prop412_bad_set_integrable hA hE)) := by
  let d := prop412AbsTruncatedDiffRepFromMidData F.mid G.mid
  let hdnn := prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid
  exact
    prop412_full_integral_le_from_piece_cap_bounds
      hA hE d hdnn eps badCap
      (prop412_full_split_from_complement_to_bad_data hA hE d hdnn
        (prop412_complement_to_bad_data_from_mid_support_full_definition_witnesses
          hA hE hEsubA F G))
      (prop412_good_set_relIntegral_le_from_truncated_value_data
        hE hA hEsubA hEf hEg d hdnn n eps
        (prop412_truncated_abs_value_data_from_mid_reps
          hA hEf hEg F.mid G.mid K)
        hfg)
      (prop412_bad_set_relIntegral_le_cap hA hE d hdnn badCap Bad.bound)

/-- Strict arbitrary-cap estimate without a pointwise seed. -/
theorem prop412_full_integral_lt_from_concrete_truncated_abs_diff_bad_cap_budget_full_definition_witnesses
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
    prop412_full_integral_le_from_concrete_truncated_abs_diff_bad_cap_bound_full_definition_witnesses
      hE hA hEsubA hEf hEg n eps badCap F G K Budget.bad_bound hfg
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

/-- One arbitrary-cap dyadic source budget, with no pointwise seed field. -/
structure Prop412DyadicSourceCapBudgetNoSeedData
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

/-- One no-seed arbitrary-cap dyadic source budget gives the small integral
estimate. -/
theorem prop412_integral_lt_halfPow_from_dyadic_cap_source_budget_no_seed
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    {k : Nat}
    (D : Prop412DyadicSourceCapBudgetNoSeedData A hA n F G k) :
    COF.lt
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
      (COF.halfPow (R := R) k) :=
  COFO.lt_trans
    (prop412_full_integral_lt_from_concrete_truncated_abs_diff_bad_cap_budget_full_definition_witnesses
      D.hE hA D.hEsubA D.hEf D.hEg n D.eps D.badCap D.eta
      F G D.chiA_abs_on_good D.bad_budget D.close_on_good)
    D.arithmetic_budget

/-- No-seed arbitrary-cap source budgets for all dyadic targets. -/
structure Prop412AllDyadicSourceCapBudgetNoSeedData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (n : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g) : Type _ where
  data :
    ∀ k : Nat, Prop412DyadicSourceCapBudgetNoSeedData A hA n F G k

/-- All no-seed arbitrary-cap dyadic budgets generate the arbitrary-small
datum. -/
def prop412_arbitrarily_small_integral_data_from_cap_source_budgets_no_seed
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (B : Prop412AllDyadicSourceCapBudgetNoSeedData A hA n F G) :
    Prop412ConcreteAbsDiffArbitrarilySmallIntegralData F.mid G.mid where
  integral_lt_halfPow := by
    intro k
    exact prop412_integral_lt_halfPow_from_dyadic_cap_source_budget_no_seed
      hA F G (B.data k)

/-- Final equality obtained from no-seed arbitrary-cap source budgets. -/
theorem prop412_mid_representative_integrals_eq_from_cap_source_budgets_no_seed
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (B : Prop412AllDyadicSourceCapBudgetNoSeedData A hA n F G) :
    F.mid.rep.integral = G.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_of_arbitrarily_small_abs_diff
    F.mid G.mid
    (prop412_arbitrarily_small_integral_data_from_cap_source_budgets_no_seed
      hA F G B)

/-- The local auxiliary data still needed after convergence returns a common
good pair.  This version has no pointwise seed field. -/
structure Prop412DyadicTwoNatCommonGoodAuxNoSeedData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (k : Nat)
    (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
    (eps : R) : Type _ where
  chiA_abs_on_good :
    Prop412GoodSetChiAAbsData A (BishopC.BSet.and B C) hA
  arithmetic_budget :
    COF.lt
      (eps * BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC) +
        ((truncN : R) + (truncN : R)) * eps)
      (COF.halfPow (R := R) k)

/-- Per-dyadic construction data for the `n+n` cap route without pointwise
seeds. -/
structure Prop412DyadicTwoNatCommonGoodConstructionNoSeedData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (k : Nat) : Type _ where
  eps : R
  heps : COF.lt 0 eps
  aux :
    ∀ (seqN : Nat)
      (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      Prop412CommonGoodPair fn f g A hA eps seqN B hB C hC ->
        Prop412DyadicTwoNatCommonGoodAuxNoSeedData A hA truncN F G k B hB C hC eps

/-- Convergence plus no-seed local construction data produce one no-seed
dyadic source budget. -/
noncomputable def prop412_dyadic_two_nat_source_cap_budget_no_seed_from_convergence_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    {k : Nat}
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (FSrc : Prop412MidRepresentativeBoundSourceData F)
    (GSrc : Prop412MidRepresentativeBoundSourceData G)
    (truncN_pos : COF.lt 0 (truncN : R))
    (D : Prop412DyadicTwoNatCommonGoodConstructionNoSeedData fn A hA truncN F G k) :
    Prop412DyadicSourceCapBudgetNoSeedData A hA truncN F G k := by
  obtain ⟨N, hN⟩ :=
    prop412_common_good_pair_data_from_convergence_data
      hf hg A hA D.eps D.heps
  obtain ⟨B, hB, C, hC, hpairData⟩ := hN N (Nat.le_refl N)
  let Common := hpairData.down
  let Aux := D.aux N B hB C hC Common
  let domains := prop412_intersection_domains
    Common.1 Common.2.2.2.1
  exact
    { E := BishopC.BSet.and B C
      hE := BishopC.IntegrableSet1_and hB hC
      hEsubA := domains.1
      hEf := domains.2.1
      hEg := domains.2.2.1
      eps := D.eps
      badCap := ((truncN : R) + (truncN : R))
      eta := D.eps
      chiA_abs_on_good := Aux.chiA_abs_on_good
      bad_budget :=
        prop412_two_nat_bad_budget_from_common_good_pair_bound_sources
          hA hB hC F G Common FSrc GSrc truncN_pos
      close_on_good := by
        intro x hxE
        exact prop412_pointwise_on_intersection_lt
          Common.2.2.1
          Common.2.2.2.2.2
          hxE
          (domains.2.1 hxE)
          (domains.2.2.1 hxE)
          (domains.2.2.2 hxE)
      arithmetic_budget := Aux.arithmetic_budget }

/-- No-seed construction data for all dyadic targets. -/
structure Prop412AllTwoNatCommonGoodConstructionNoSeedData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g) : Type _ where
  data :
    ∀ k : Nat,
      Prop412DyadicTwoNatCommonGoodConstructionNoSeedData fn A hA truncN F G k

/-- All no-seed source budgets obtained from convergence. -/
noncomputable def prop412_all_two_nat_source_cap_budgets_no_seed_from_convergence_data
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (FSrc : Prop412MidRepresentativeBoundSourceData F)
    (GSrc : Prop412MidRepresentativeBoundSourceData G)
    (truncN_pos : COF.lt 0 (truncN : R))
    (D : Prop412AllTwoNatCommonGoodConstructionNoSeedData fn A hA truncN F G) :
    Prop412AllDyadicSourceCapBudgetNoSeedData A hA truncN F G where
  data := by
    intro k
    exact
      prop412_dyadic_two_nat_source_cap_budget_no_seed_from_convergence_data
        hA F G hf hg FSrc GSrc truncN_pos (D.data k)

/-- Final truncated-integral equality from data-carrying convergence through
the corrected no-seed `n+n` cap route. -/
theorem prop412_mid_representative_integrals_eq_from_convergence_data_two_nat_bound_sources_no_seed
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (FSrc : Prop412MidRepresentativeBoundSourceData F)
    (GSrc : Prop412MidRepresentativeBoundSourceData G)
    (truncN_pos : COF.lt 0 (truncN : R))
    (D : Prop412AllTwoNatCommonGoodConstructionNoSeedData fn A hA truncN F G) :
    F.mid.rep.integral = G.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_cap_source_budgets_no_seed
    hA F G
    (prop412_all_two_nat_source_cap_budgets_no_seed_from_convergence_data
      hA F G hf hg FSrc GSrc truncN_pos D)

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G214 audit: the downstream two-nat convergence route no longer requires
the previous pointwise seed. -/
structure Prop412DownstreamNoSeedAuditAfterG214 : Type where
  low_level_seed_removed : Nat
  dyadic_source_budget_seed_removed : Nat
  two_nat_convergence_route_seed_removed : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_pointwise_seed_obligations_on_new_route : Nat

def prop412DownstreamNoSeedAuditAfterG214 :
    Prop412DownstreamNoSeedAuditAfterG214 where
  low_level_seed_removed := 1
  dyadic_source_budget_seed_removed := 1
  two_nat_convergence_route_seed_removed := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_pointwise_seed_obligations_on_new_route := 0

/-- G214 package. -/
structure BishopRegularSeqChapter4G214Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g213 : BishopRegularSeqChapter4G213Package S
  downstream_no_seed_audit : Prop412DownstreamNoSeedAuditAfterG214
  downstream_two_nat_seed_removed_this_step : Nat
  remaining_steps_after_downstream_no_seed_route : Nat

def bishopRegularSeqChapter4G214Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G214Package S where
  g213 := bishopRegularSeqChapter4G213Package S
  downstream_no_seed_audit := prop412DownstreamNoSeedAuditAfterG214
  downstream_two_nat_seed_removed_this_step := 1
  remaining_steps_after_downstream_no_seed_route := 0

/-- Progress after G214. -/
def bishopRegularSeqDownstreamNoSeedProgressAfterG214 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 100
  total_final_goal_percent := 100
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G214: threaded the G213 full-definition-witness estimate through the \
    dyadic source-budget and two-nat convergence route. The new route has no \
    pointwise_seed field, no Prop-to-Type witness extraction, and no added \
    choice principle."


end BishopCReal
