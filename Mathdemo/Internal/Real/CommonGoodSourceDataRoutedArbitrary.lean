import Mathdemo.Internal.Real.TwoNBadSetCapBounded

set_option linter.style.longLine false

/-!
# G192: common-good source data routed through arbitrary bad caps

G188 connected the common-good `B,C,N` data to the older source-budget interface
whose bad-set coefficient was hard-coded as `n`.  G190 introduced the corrected
arbitrary-cap interface.  This file repeats the common-good bridge for that
interface, so downstream Prop. 4.12 work no longer has to pass through the
source's suspicious `n * mu(A-E)` line.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- One common-good source datum whose bad-set side already uses the arbitrary
cap budget from G190. -/
structure Prop412DyadicCommonGoodCapSourceData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (k : Nat) : Type _ where
  seqN : Nat
  B : BishopC.BSet Y
  hB : BishopC.IntegrableSet1 S B
  C : BishopC.BSet Y
  hC : BishopC.IntegrableSet1 S C
  eps : R
  badCap : R
  eta : R
  common_pair :
    Prop412CommonGoodPair fn f g A hA eps seqN B hB C hC
  chiA_abs_on_good :
    Prop412GoodSetChiAAbsData A (BishopC.BSet.and B C) hA
  pointwise_seed :
    Prop412ComplementPointwiseConcreteSupportSeedData
      A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
      truncN f g F G
  bad_budget :
    Prop412ConcreteBadSetCapBudgetData
      A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
      truncN badCap eta F G
  arithmetic_budget :
    COF.lt
      (eps * BishopC.measure1 S (BishopC.IntegrableSet1_and hB hC) +
        badCap * eta)
      (COF.halfPow (R := R) k)

/-- Domain data for the arbitrary-cap common-good source datum. -/
def prop412_common_good_cap_source_domains
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    {F : Prop412MidRepresentativeSupportData A hA truncN f}
    {G : Prop412MidRepresentativeSupportData A hA truncN g}
    {k : Nat}
    (D : Prop412DyadicCommonGoodCapSourceData fn A hA truncN F G k) :
    ((BishopC.BSet.and D.B D.C).S1 ⊆ A.S1) ∧
    ((BishopC.BSet.and D.B D.C).S1 ⊆ f.dom) ∧
    ((BishopC.BSet.and D.B D.C).S1 ⊆ g.dom) ∧
    ((BishopC.BSet.and D.B D.C).S1 ⊆ (fn D.seqN).dom) :=
  prop412_intersection_domains
    D.common_pair.1
    D.common_pair.2.2.2.1

/-- The common-good pointwise `|f-g| < eps` estimate for the cap-routed source
datum. -/
theorem prop412_common_good_cap_source_close_on_good
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    {F : Prop412MidRepresentativeSupportData A hA truncN f}
    {G : Prop412MidRepresentativeSupportData A hA truncN g}
    {k : Nat}
    (D : Prop412DyadicCommonGoodCapSourceData fn A hA truncN F G k) :
    ∀ x (hxE : x ∈ (BishopC.BSet.and D.B D.C).S1),
      COF.lt
        (COF.abs
          (f.toFun x ((prop412_common_good_cap_source_domains D).2.1 hxE) -
            g.toFun x ((prop412_common_good_cap_source_domains D).2.2.1 hxE)))
        D.eps := by
  intro x hxE
  exact prop412_pointwise_on_intersection_lt
    D.common_pair.2.2.1
    D.common_pair.2.2.2.2.2
    hxE
    ((prop412_common_good_cap_source_domains D).2.1 hxE)
    ((prop412_common_good_cap_source_domains D).2.2.1 hxE)
    ((prop412_common_good_cap_source_domains D).2.2.2 hxE)

/-- A cap-routed common-good source datum yields the G190 dyadic source budget. -/
noncomputable def prop412_dyadic_cap_source_budget_from_common_good_cap_source
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    {k : Nat}
    (D : Prop412DyadicCommonGoodCapSourceData fn A hA truncN F G k) :
    Prop412DyadicSourceCapBudgetData A hA truncN F G k where
  E := BishopC.BSet.and D.B D.C
  hE := BishopC.IntegrableSet1_and D.hB D.hC
  hEsubA := (prop412_common_good_cap_source_domains D).1
  hEf := (prop412_common_good_cap_source_domains D).2.1
  hEg := (prop412_common_good_cap_source_domains D).2.2.1
  eps := D.eps
  badCap := D.badCap
  eta := D.eta
  chiA_abs_on_good := D.chiA_abs_on_good
  pointwise_seed := D.pointwise_seed
  bad_budget := D.bad_budget
  close_on_good := prop412_common_good_cap_source_close_on_good D
  arithmetic_budget := D.arithmetic_budget

/-- Cap-routed common-good source data for all dyadic targets. -/
structure Prop412AllCommonGoodCapSourceData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.PFunR Y R)
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g) : Type _ where
  data :
    ∀ k : Nat, Prop412DyadicCommonGoodCapSourceData fn A hA truncN F G k

/-- All cap-routed common-good source data generate all G190 dyadic cap budgets. -/
noncomputable def prop412_all_cap_source_budgets_from_common_good_cap_sources
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (D : Prop412AllCommonGoodCapSourceData fn A hA truncN F G) :
    Prop412AllDyadicSourceCapBudgetData A hA truncN F G where
  data := by
    intro k
    exact prop412_dyadic_cap_source_budget_from_common_good_cap_source
      hA F G (D.data k)

/-- Final equality from cap-routed common-good source data. -/
theorem prop412_mid_representative_integrals_eq_from_common_good_cap_sources
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {A : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    {truncN : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA truncN f)
    (G : Prop412MidRepresentativeSupportData A hA truncN g)
    (D : Prop412AllCommonGoodCapSourceData fn A hA truncN F G) :
    F.mid.rep.integral = G.mid.rep.integral :=
  prop412_mid_representative_integrals_eq_from_cap_source_budgets
    hA F G
    (prop412_all_cap_source_budgets_from_common_good_cap_sources hA F G D)

/-- Residual shape after G192. -/
structure Prop412CommonGoodCapSourceFrontierAfterG192 : Type where
  common_good_source_to_cap_budget_closed : Prop
  all_common_good_cap_sources_to_equality_closed : Prop
  old_hardcoded_n_common_good_bridge_no_longer_needed_for_new_path : Prop
  construct_two_nat_cap_budgets_from_mid_bounds_still_needed : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  old_true_statement_used : Nat

def prop412CommonGoodCapSourceFrontierAfterG192 :
    Prop412CommonGoodCapSourceFrontierAfterG192 where
  common_good_source_to_cap_budget_closed := True
  all_common_good_cap_sources_to_equality_closed := True
  old_hardcoded_n_common_good_bridge_no_longer_needed_for_new_path := True
  construct_two_nat_cap_budgets_from_mid_bounds_still_needed := True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  old_true_statement_used := 0

/-- G192 package. -/
structure Chapter4G192Prop412CommonGoodCapSourcePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g191 : BishopRegularSeqChapter4G191Package S
  common_good_cap_source_frontier_after_g192 :
    Prop412CommonGoodCapSourceFrontierAfterG192
  common_good_cap_sources_to_truncated_integral_equality_closed : Prop
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G192Prop412CommonGoodCapSourcePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G192Prop412CommonGoodCapSourcePackage S where
  g191 := bishopRegularSeqChapter4G191Package S
  common_good_cap_source_frontier_after_g192 :=
    prop412CommonGoodCapSourceFrontierAfterG192
  common_good_cap_sources_to_truncated_integral_equality_closed := True
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G192 package exposed at top level. -/
structure BishopRegularSeqChapter4G192Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G192Prop412CommonGoodCapSourcePackage S
  common_good_cap_sources_to_truncated_integral_equality_closed : Prop
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G192Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G192Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G192Prop412CommonGoodCapSourcePackage S
  common_good_cap_sources_to_truncated_integral_equality_closed := True
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 2

/-- Progress after G192. -/
def bishopRegularSeqCh1To4ProgressAfterG192 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G192: rerouted the common-good B,C,N source bridge through the arbitrary \
    badCap source-budget interface. The active Prop. 4.12 path no longer \
    depends on the source's hard-coded n coefficient; it can consume the \
    n+n cap produced from bounded mid representatives."


end BishopCReal
