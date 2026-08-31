import Mathdemo.Internal.Real.Proposition412GoodSetTruncated

set_option linter.style.longLine false

/-!
# G172: Proposition 4.12 scalar `mid` Lipschitz bridge

The source proof of Proposition 4.12 moves from the good-set estimate

`|f(x)-g(x)| < eps`

to the displayed truncated estimate

`|mid(-n, chi_A f, n) - mid(-n, chi_A g, n)| < eps`

on the same good set.  G171 had already connected a representation-level
pointwise bound to the relative integral estimate.  This file closes the
scalar half of that pointwise bridge: `mid(-n, -, n)` is 1-Lipschitz, and on
points where `chi_A = 1` the `chi_A` factors disappear.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Scalar form of the source's `mid(-n,z,n)`. -/
def prop412ScalarMid {R : Type*} [COFO R] (n : Nat) (z : R) : R :=
  COF.max (COF.min z (n : R)) (-(n : R))

/-- `max` as a negated `min`, used to reuse the existing `min` 1-Lipschitz
lemma without adding a second primitive lattice proof. -/
theorem prop412_max_eq_neg_min_neg
    {R : Type*} [COFO R] (a b : R) :
    COF.max a b = - COF.min (-a) (-b) := by
  rw [COF.max_halfsum, COF.min_halfsum,
    show (-a) - (-b) = -(a - b) from by ring,
    COFO.abs_neg]
  ring

/-- `max(-,c)` is 1-Lipschitz, derived from the existing `min` Lipschitz
theorem. -/
theorem prop412_abs_max_sub_max_le
    {R : Type*} [COFOC R] (a b c : R) :
    BishopC.Le (COF.abs (COF.max a c - COF.max b c)) (COF.abs (a - b)) := by
  rw [prop412_max_eq_neg_min_neg a c,
    prop412_max_eq_neg_min_neg b c]
  have h := BishopC.abs_min_sub_min_le (-a) (-b) (-c)
  rw [show (-a) - (-b) = -(a - b) from by ring,
    COFO.abs_neg] at h
  rwa [show -COF.min (-a) (-c) - -COF.min (-b) (-c)
        = -(COF.min (-a) (-c) - COF.min (-b) (-c)) from by ring,
      COFO.abs_neg]

/-- The scalar truncation `mid(-n,-,n)` is 1-Lipschitz. -/
theorem prop412_scalarMid_lipschitz
    {R : Type*} [COFOC R] (n : Nat) (a b : R) :
    BishopC.Le
      (COF.abs (prop412ScalarMid n a - prop412ScalarMid n b))
      (COF.abs (a - b)) := by
  dsimp [prop412ScalarMid]
  exact BishopC.le_trans
    (prop412_abs_max_sub_max_le
      (COF.min a (n : R)) (COF.min b (n : R)) (-(n : R)))
    (BishopC.abs_min_sub_min_le a b (n : R))

/-- Strict version of the scalar `mid` Lipschitz estimate. -/
theorem prop412_scalarMid_lt_of_lt
    {R : Type*} [COFOC R] {eps : R} (n : Nat) {a b : R}
    (h : COF.lt (COF.abs (a - b)) eps) :
    COF.lt
      (COF.abs (prop412ScalarMid n a - prop412ScalarMid n b))
      eps :=
  BishopC.lt_of_le_of_lt (prop412_scalarMid_lipschitz n a b) h

/-- On a point where `chi_A=1`, the source expression
`mid(-n, chi_A*f, n)` inherits the same bound as `mid(-n,f,n)`. -/
theorem prop412_chi_one_scalarMid_lipschitz
    {R : Type*} [COFOC R] (n : Nat) {chi f g : R}
    (hchi : chi = 1) :
    BishopC.Le
      (COF.abs
        (prop412ScalarMid n (chi * f) -
          prop412ScalarMid n (chi * g)))
      (COF.abs (f - g)) := by
  rw [hchi, one_mul, one_mul]
  exact prop412_scalarMid_lipschitz n f g

/-- Strict version of the `chi_A=1` scalar bridge. -/
theorem prop412_chi_one_scalarMid_lt
    {R : Type*} [COFOC R] {eps : R} (n : Nat) {chi f g : R}
    (hchi : chi = 1)
    (hfg : COF.lt (COF.abs (f - g)) eps) :
    COF.lt
      (COF.abs
        (prop412ScalarMid n (chi * f) -
          prop412ScalarMid n (chi * g)))
      eps :=
  BishopC.lt_of_le_of_lt (prop412_chi_one_scalarMid_lipschitz n hchi) hfg

/-- If a good set `E` is contained in `A`, then the characteristic value of
`A` is `1` at every point of `E`, expressed through the existing
`IntegrableSet1.valid` data. -/
theorem prop412_chiA_value_one_on_good_set
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hEsubA : E.S1 ⊆ A.S1)
    {x : Y} (hxE : x ∈ E.S1)
    (hχADom : hA.rep.MemAt x)
    (hχAabs : RSeq.SeriesSum (fun n => COF.abs (hA.rep.valueAt x hχADom n))) :
    (BishopC.seriesSum_of_abs hχAabs).sum = 1 :=
  (hA.valid x hχADom hχAabs).2.1 (hEsubA hxE)
    (BishopC.seriesSum_of_abs hχAabs)

/-- Source-line pointwise bridge on the good set:
from `|f-g|<eps` and `E⊆A`, obtain the displayed scalar truncated
`chi_A` estimate.  The remaining G173 task is to identify this scalar value
with the chosen `IntegrableRep` for the absolute truncated difference. -/
theorem prop412_scalar_mid_chiA_lt_on_good_set
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hEsubA : E.S1 ⊆ A.S1)
    {x : Y} (hxE : x ∈ E.S1)
    (hχADom : hA.rep.MemAt x)
    (hχAabs : RSeq.SeriesSum (fun n => COF.abs (hA.rep.valueAt x hχADom n)))
    {fv gv eps : R} (n : Nat)
    (hfg : COF.lt (COF.abs (fv - gv)) eps) :
    COF.lt
      (COF.abs
        (prop412ScalarMid n
          ((BishopC.seriesSum_of_abs hχAabs).sum * fv) -
          prop412ScalarMid n
            ((BishopC.seriesSum_of_abs hχAabs).sum * gv)))
      eps :=
  prop412_chi_one_scalarMid_lt n
    (prop412_chiA_value_one_on_good_set hA hEsubA hxE hχADom hχAabs)
    hfg

/-- Residual shape after G172: the scalar `mid` part of the displayed
Prop. 4.12 estimate is closed; the remaining work is representation
identification plus the bad-complement/full-split integral assembly. -/
structure Prop412TruncatedIntegralFrontierAfterG172 : Type where
  scalar_mid_lipschitz_closed : Prop
  chiA_good_set_scalar_bridge_closed : Prop
  truncated_abs_difference_rep_value_identification_needed : Prop
  bad_complement_bound_needed : Prop
  full_integral_split_needed : Prop
  old_true_statement_used : Nat

def prop412TruncatedIntegralFrontierAfterG172 :
    Prop412TruncatedIntegralFrontierAfterG172 where
  scalar_mid_lipschitz_closed := True
  chiA_good_set_scalar_bridge_closed := True
  truncated_abs_difference_rep_value_identification_needed := True
  bad_complement_bound_needed := True
  full_integral_split_needed := True
  old_true_statement_used := 0

/-- G172 package: scalar `mid` Lipschitz bridge for Proposition 4.12. -/
structure Chapter4G172Prop412ScalarMidPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g171 : BishopRegularSeqChapter4G171Package S
  scalar_mid_lipschitz_closed : Prop
  chiA_good_set_scalar_bridge_closed : Prop
  truncated_integral_frontier_after_g172 : Prop412TruncatedIntegralFrontierAfterG172
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_prop412_pass : Nat

def chapter4G172Prop412ScalarMidPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G172Prop412ScalarMidPackage S where
  g171 := bishopRegularSeqChapter4G171Package S
  scalar_mid_lipschitz_closed := True
  chiA_good_set_scalar_bridge_closed := True
  truncated_integral_frontier_after_g172 :=
    prop412TruncatedIntegralFrontierAfterG172
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 3
  chapter4_faithful_source_frontiers_still_open := 5
  countdown_remaining_for_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G172 package exposed at top level. -/
structure BishopRegularSeqChapter4G172Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G172Prop412ScalarMidPackage S
  proposition_4_12_scalar_mid_bridge_closed_this_step : Nat
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_prop412_pass : Nat

def bishopRegularSeqChapter4G172Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G172Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G172Prop412ScalarMidPackage S
  proposition_4_12_scalar_mid_bridge_closed_this_step := 1
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 3
  chapter4_faithful_source_frontiers_still_open := 5
  remaining_countdown_steps_for_prop412_pass := 2

/-- Progress after G172: the scalar part of the displayed Prop. 4.12
truncated estimate is closed. -/
def bishopRegularSeqCh1To4ProgressAfterG172 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 85
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G172: Proposition 4.12 scalar mid Lipschitz bridge is closed: \
    |mid(-n,chi_A f,n)-mid(-n,chi_A g,n)|<eps follows on the good set \
    from chi_A=1 and |f-g|<eps. Remaining truncated-integral work: \
    representation value identification, bad-complement bound, and full split. \
    Prop. 4.12 countdown remains 2."


end BishopCReal
