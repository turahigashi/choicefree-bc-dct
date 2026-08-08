import Mathdemo.Internal.CRat_iter316

set_option linter.style.longLine false

/-!
# G218: Located Lemma 4.5 transfer

This file closes the strengthened, Bishop-facing form of Lemma 4.5.  The
strengthening is source-faithful: the input supremum is located in the
Bishop/Bridges sense, and the directed domination hypothesis carries the
source `s3` witness as data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

/-- From `a - x < e`, move the strict gap to `a - e < x`. -/
theorem sub_left_lt_of_sub_right_lt
    {R : Type*} [COF R] {a e x : R}
    (h : COF.lt (a - x) e) :
    COF.lt (a - e) x := by
  have t := COF.lt_add_left (x - e) h
  rwa [show (x - e) + (a - x) = a - e from by ring,
    show (x - e) + e = x from by ring] at t

/-- From `a - b < e`, derive `a < b + e`. -/
theorem lt_add_of_sub_lt
    {R : Type*} [COF R] {a b e : R}
    (h : COF.lt (a - b) e) :
    COF.lt a (b + e) := by
  have t := COF.lt_add_left b h
  rwa [show b + (a - b) = a from by ring,
    show b + e = b + e from by ring] at t

/-- If `a` is below `b+e` and `e<d`, then `a-d<b`. -/
theorem sub_lt_of_lt_add_of_lt
    {R : Type*} [COFO R] {a b e d : R}
    (h : COF.lt a (b + e))
    (hed : COF.lt e d) :
    COF.lt (a - d) b := by
  have h1 := COF.lt_add_left (-d) h
  have h2 := COF.lt_add_left (b - d) hed
  have h1' : COF.lt (a - d) (b + e - d) := by
    rwa [show -d + a = a - d from by ring,
      show -d + (b + e) = b + e - d from by ring] at h1
  have h2' : COF.lt (b + e - d) b := by
    rwa [show (b - d) + e = b + e - d from by ring,
      show (b - d) + d = b from by ring] at h2
  exact COFO.lt_trans h1' h2'

/-- The actual candidate supremum in Lemma 4.5: the limit of the `φ`-values
at the carried `ψ` near-maximizers. -/
def lemma45_phi_sup_value
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R} {cψ : R}
    (hdir : Lemma45SourceHypothesisData φ ψ)
    (hψ : LocatedRangeSupremum ψ cψ) : R :=
  (lemma45_phi_sup_candidate hdir hψ).val

/-- The candidate supremum has located lower approximants: the same
near-maximizers used to define the Cauchy sequence. -/
def lemma45_phi_sup_candidate_approx
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R} {cψ : R}
    (hdir : Lemma45SourceHypothesisData φ ψ)
    (hψ : LocatedRangeSupremum ψ cψ)
    (k : Nat) :
    { s : T //
      COF.lt (lemma45_phi_sup_value hdir hψ - COF.halfPow (R := R) k)
        (φ s) } := by
  let hlim := lemma45_phi_sup_candidate hdir hψ
  let n := hlim.tends.mod (k + 1)
  refine ⟨lemma45_nearMaximizer hψ n, ?_⟩
  have hclose :
      COF.lt (COF.abs (φ (lemma45_nearMaximizer hψ n) - hlim.val))
        (COF.halfPow (R := R) (k + 1)) :=
    hlim.tends.close (k + 1) n (Nat.le_refl _)
  have hgap :
      COF.lt (hlim.val - φ (lemma45_nearMaximizer hψ n))
        (COF.halfPow (R := R) (k + 1)) := by
    refine BishopC.lt_of_le_of_lt ?_ hclose
    have h := COFO.neg_le_abs (φ (lemma45_nearMaximizer hψ n) - hlim.val)
    rwa [show hlim.val - φ (lemma45_nearMaximizer hψ n) =
      -(φ (lemma45_nearMaximizer hψ n) - hlim.val) from by ring]
  have hgap' :
      COF.lt (hlim.val - φ (lemma45_nearMaximizer hψ n))
        (COF.halfPow (R := R) k) :=
    COFO.lt_trans hgap (BishopC.halfPow_lt_succ (R := R) k)
  change COF.lt (hlim.val - COF.halfPow (R := R) k)
    (φ (lemma45_nearMaximizer hψ n))
  exact sub_left_lt_of_sub_right_lt hgap'

/-- Upper-bound half of the located Lemma 4.5 conclusion. -/
theorem lemma45_phi_sup_candidate_upper
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R} {cψ : R}
    (hdir : Lemma45SourceHypothesisData φ ψ)
    (hψ : LocatedRangeSupremum ψ cψ)
    (s : T) :
    BishopC.Le (φ s) (lemma45_phi_sup_value hdir hψ) := by
  let hlim := lemma45_phi_sup_candidate hdir hψ
  change BishopC.Le (φ s) hlim.val
  apply le_of_forall_sub_halfPow_lt
  intro k
  let level := k + 2
  let n := max (hlim.tends.mod level) level
  let t := lemma45_nearMaximizer hψ n
  let du := hdir.directed_domination s t
  let u := du.val
  have hdata := du.property
  have hs_le_u : BishopC.Le (φ s) (φ u) :=
    BishopC.le_of_nonneg_sub hdata.1.1
  have hgap_u_t :
      COF.lt (φ u - φ t) (COF.halfPow (R := R) level) :=
    lemma45_phi_gap_lt_of_directed hψ hdata.2.2 level n rfl
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_refl _))
  have hs_sub_t_le : BishopC.Le (φ s - φ t) (φ u - φ t) :=
    BishopC.le_sub_right (c := φ t) hs_le_u
  have hs_sub_t_lt :
      COF.lt (φ s - φ t) (COF.halfPow (R := R) level) :=
    BishopC.lt_of_le_of_lt hs_sub_t_le hgap_u_t
  have hs_lt_t_plus :
      COF.lt (φ s) (φ t + COF.halfPow (R := R) level) :=
    lt_add_of_sub_lt hs_sub_t_lt
  have hclose :
      COF.lt (COF.abs (φ t - hlim.val)) (COF.halfPow (R := R) level) :=
    hlim.tends.close level n (Nat.le_max_left _ _)
  have ht_sub_c_lt :
      COF.lt (φ t - hlim.val) (COF.halfPow (R := R) level) :=
    BishopC.lt_of_le_of_lt (COFO.le_abs_self (φ t - hlim.val)) hclose
  have ht_lt_c_plus :
      COF.lt (φ t) (hlim.val + COF.halfPow (R := R) level) :=
    lt_add_of_sub_lt ht_sub_c_lt
  have ht_plus_lt :
      COF.lt (φ t + COF.halfPow (R := R) level)
        ((hlim.val + COF.halfPow (R := R) level)
          + COF.halfPow (R := R) level) := by
    have h := COF.lt_add_left (COF.halfPow (R := R) level) ht_lt_c_plus
    rwa [show COF.halfPow (R := R) level + φ t =
        φ t + COF.halfPow (R := R) level from by ring,
      show COF.halfPow (R := R) level +
          (hlim.val + COF.halfPow (R := R) level) =
        (hlim.val + COF.halfPow (R := R) level)
          + COF.halfPow (R := R) level from by ring] at h
  have hs_lt_c_plus_double :
      COF.lt (φ s)
        ((hlim.val + COF.halfPow (R := R) level)
          + COF.halfPow (R := R) level) :=
    COFO.lt_trans hs_lt_t_plus ht_plus_lt
  have hsum :
      (hlim.val + COF.halfPow (R := R) level)
          + COF.halfPow (R := R) level =
        hlim.val + COF.halfPow (R := R) (k + 1) := by
    rw [show level = k + 1 + 1 by omega,
      show (hlim.val + COF.halfPow (R := R) (k + 1 + 1))
          + COF.halfPow (R := R) (k + 1 + 1) =
        hlim.val +
          (COF.halfPow (R := R) (k + 1 + 1)
            + COF.halfPow (R := R) (k + 1 + 1)) from by ring,
      BishopC.halfPow_succ_add (R := R) (k + 1)]
  have hs_lt_c_plus :
      COF.lt (φ s) (hlim.val + COF.halfPow (R := R) (k + 1)) := by
    rwa [hsum] at hs_lt_c_plus_double
  exact sub_lt_of_lt_add_of_lt hs_lt_c_plus
    (BishopC.halfPow_lt_succ (R := R) k)

/-- Lemma 4.5, strengthened in the Bishop-faithful direction: located
supremum data transfers from `ψ` to `φ`. -/
def lemma45_located_transfer
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R} :
    lemma45_located_transfer_target φ ψ := by
  intro hdir hψpack
  rcases hψpack with ⟨cψ, hψ⟩
  refine ⟨lemma45_phi_sup_value hdir hψ, ?_⟩
  exact
    { upper := lemma45_phi_sup_candidate_upper hdir hψ
      approx := lemma45_phi_sup_candidate_approx hdir hψ }

/-- Located Lemma 4.5 also yields the previous Prop-only wrapper by forgetting the
located data, never by extracting data from the previous wrapper. -/
def lemma45_range_transfer_from_located
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R}
    (hdir : Lemma45SourceHypothesisData φ ψ)
    (hψpack : Sigma fun cψ : R => LocatedRangeSupremum ψ cψ) :
    { cφ : R // RangeSupremum φ cφ } := by
  let hφpack := lemma45_located_transfer hdir hψpack
  exact ⟨hφpack.1, locatedRangeSupremum_to_rangeSupremum hφpack.2⟩

/-- G218 audit. -/
structure Lemma45LocatedTransferAuditAfterG218 : Type where
  located_lemma45_transfer_closed : Nat
  source_directed_domination_hypothesis_used : Nat
  bishop_located_supremum_input_used : Nat
  conclusion_strengthened_to_located_supremum : Nat
  old_rangeSupremum_wrapper_obtained_by_forgetful_projection : Nat
  rangeSupremum_to_locatedSupremum_selector_used : Nat
  classical_choice_inputs_added : Nat
  remaining_steps_for_theorem46_and_cor47 : Nat

def lemma45LocatedTransferAuditAfterG218 :
    Lemma45LocatedTransferAuditAfterG218 where
  located_lemma45_transfer_closed := 1
  source_directed_domination_hypothesis_used := 1
  bishop_located_supremum_input_used := 1
  conclusion_strengthened_to_located_supremum := 1
  old_rangeSupremum_wrapper_obtained_by_forgetful_projection := 1
  rangeSupremum_to_locatedSupremum_selector_used := 0
  classical_choice_inputs_added := 0
  remaining_steps_for_theorem46_and_cor47 := 2

/-- G218 package. -/
structure Chapter4G218Lemma45LocatedPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g217 : Chapter4G217Lemma45CauchyCorePackage S
  audit : Lemma45LocatedTransferAuditAfterG218
  lemma45_located_transfer_closed_this_step : Nat
  remaining_source_completion_steps_for_4_5_to_4_10 : Nat

def chapter4G218Lemma45LocatedPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G218Lemma45LocatedPackage S where
  g217 := chapter4G217Lemma45CauchyCorePackage S
  audit := lemma45LocatedTransferAuditAfterG218
  lemma45_located_transfer_closed_this_step := 1
  remaining_source_completion_steps_for_4_5_to_4_10 := 2

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G218. -/
def bishopRegularSeqChapter4Lemma45LocatedProgressAfterG218 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 83
  total_final_goal_percent := 96
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G218: closed the strengthened Bishop-faithful Lemma 4.5. Located \
    supremum data for psi plus the source directed-domination witness yields \
    located supremum data for phi; the previous RangeSupremum conclusion is only a \
    forgetful wrapper. Countdown for source-complete 4.6-4.10 route: 2."


end BishopCReal
