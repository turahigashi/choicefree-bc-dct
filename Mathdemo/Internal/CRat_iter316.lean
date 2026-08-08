import Mathdemo.Internal.CRat_iter315

set_option linter.style.longLine false

/-!
# G217: Lemma 4.5 core proof, Cauchy sequence of phi-near-maximizers

This file starts the actual proof of Bishop--Cheng Lemma 4.5 on the located
supremum interface.  From a located supremum of `ψ`, take the carried
near-maximizers `t k`; directed domination proves that `φ (t k)` is Cauchy.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

/-- From `a - e < x`, move the strict gap to `a - x < e`. -/
theorem sub_right_lt_of_sub_left_lt
    {R : Type*} [COF R] {a e x : R}
    (h : COF.lt (a - e) x) :
    COF.lt (a - x) e := by
  have t := COF.lt_add_left (e - x) h
  rwa [show (e - x) + (a - e) = a - x from by ring,
    show (e - x) + x = e from by ring] at t

/-- From `e < a - x`, move the strict gap to `x < a - e`. -/
theorem lt_sub_right_of_lt_sub
    {R : Type*} [COF R] {a e x : R}
    (h : COF.lt e (a - x)) :
    COF.lt x (a - e) := by
  have t := COF.lt_add_left (x - e) h
  rwa [show (x - e) + e = x from by ring,
    show (x - e) + (a - x) = a - e from by ring] at t

/-- A nonnegative value is below its double. -/
theorem le_self_add_self_of_nonneg
    {R : Type*} [COFO R] {e : R}
    (he : BishopC.Nonneg e) :
    BishopC.Le e (e + e) := by
  apply BishopC.le_of_nonneg_sub
  rwa [show (e + e) - e = e from by ring]

/-- If two values are below a common upper value and both upper gaps are
strictly below `e`, then their distance is at most `e+e`. -/
theorem abs_sub_le_double_of_common_upper_gaps
    {R : Type*} [COFO R] {a b u e : R}
    (he : BishopC.Nonneg e)
    (ha : BishopC.Le a u)
    (hb : BishopC.Le b u)
    (hua : COF.lt (u - a) e)
    (hub : COF.lt (u - b) e) :
    BishopC.Le (COF.abs (a - b)) (e + e) := by
  have he_le_double : BishopC.Le e (e + e) :=
    le_self_add_self_of_nonneg he
  have h1 : BishopC.Le (a - b) e := by
    exact BishopC.le_trans (BishopC.le_sub_right (c := b) ha)
      (BishopC.le_of_lt hub)
  have h2 : BishopC.Le (-(a - b)) e := by
    have hbua : BishopC.Le (b - a) (u - a) :=
      BishopC.le_sub_right (c := a) hb
    have hle : BishopC.Le (b - a) e :=
      BishopC.le_trans hbua (BishopC.le_of_lt hua)
    rwa [show -(a - b) = b - a from by ring]
  exact COFO.abs_le_of
    (BishopC.le_trans h1 he_le_double)
    (BishopC.le_trans h2 he_le_double)

/-- Specialized strict version for dyadic Cauchy estimates. -/
theorem abs_sub_lt_halfPow_of_common_upper_gaps
    {R : Type*} [COFO R] {a b u : R} {k : Nat}
    (ha : BishopC.Le a u)
    (hb : BishopC.Le b u)
    (hua : COF.lt (u - a) (COF.halfPow (R := R) (k + 2)))
    (hub : COF.lt (u - b) (COF.halfPow (R := R) (k + 2))) :
    COF.lt (COF.abs (a - b)) (COF.halfPow (R := R) k) := by
  have hle :
      BishopC.Le (COF.abs (a - b))
        (COF.halfPow (R := R) (k + 2) + COF.halfPow (R := R) (k + 2)) :=
    abs_sub_le_double_of_common_upper_gaps
      (BishopC.le_of_lt (BishopC.halfPow_pos (R := R) (k + 2)))
      ha hb hua hub
  have hsum :
      COF.halfPow (R := R) (k + 2) + COF.halfPow (R := R) (k + 2) =
        COF.halfPow (R := R) (k + 1) := by
    rw [show k + 2 = k + 1 + 1 by omega]
    exact BishopC.halfPow_succ_add (R := R) (k + 1)
  have hle' :
      BishopC.Le (COF.abs (a - b)) (COF.halfPow (R := R) (k + 1)) := by
    rwa [hsum] at hle
  exact BishopC.lt_of_le_of_lt hle' (BishopC.halfPow_lt_succ (R := R) k)

/-- The carried near-maximizer of `ψ` at dyadic level `k`. -/
def lemma45_nearMaximizer
    {R : Type*} [COFO R] {T : Type*}
    {ψ : T -> R} {cψ : R}
    (hψ : LocatedRangeSupremum ψ cψ) (k : Nat) : T :=
  (hψ.approx k).val

/-- The near-maximizer property gives a strict upper gap estimate. -/
theorem lemma45_psi_gap_lt
    {R : Type*} [COFO R] {T : Type*}
    {ψ : T -> R} {cψ : R}
    (hψ : LocatedRangeSupremum ψ cψ) (k : Nat) :
    COF.lt (cψ - ψ (lemma45_nearMaximizer hψ k))
      (COF.halfPow (R := R) k) :=
  sub_right_lt_of_sub_left_lt (hψ.approx k).property

/-- If `u` dominates `t` in the Lemma 4.5 sense, then the `φ` gap is bounded
by the corresponding `ψ` gap. -/
theorem lemma45_phi_gap_lt_of_directed
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R} {cψ : R}
    (hψ : LocatedRangeSupremum ψ cψ)
    {u t : T}
    (hφψ : BishopC.Le (φ u - φ t) (ψ u - ψ t))
    (level : Nat)
    (ht_index : Nat)
    (ht_eq : t = lemma45_nearMaximizer hψ ht_index)
    (hindex : level <= ht_index) :
    COF.lt (φ u - φ t) (COF.halfPow (R := R) level) := by
  have hψgap0 :
      COF.lt (cψ - ψ (lemma45_nearMaximizer hψ ht_index))
        (COF.halfPow (R := R) ht_index) :=
    lemma45_psi_gap_lt hψ ht_index
  have hψgap :
      COF.lt (cψ - ψ t) (COF.halfPow (R := R) level) := by
    subst ht_eq
    exact BishopC.lt_of_lt_of_le hψgap0
      (BishopC.halfPow_antitone (R := R) hindex)
  have hψu : BishopC.Le (ψ u - ψ t) (cψ - ψ t) :=
    BishopC.le_sub_right (c := ψ t) (hψ.upper u)
  exact BishopC.lt_of_le_of_lt (BishopC.le_trans hφψ hψu) hψgap

/-- The core constructive content of Lemma 4.5: the sequence obtained by
applying `φ` to the carried near-maximizers of `ψ` is Cauchy. -/
def lemma45_phi_nearMaximizer_isCauchy
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R} {cψ : R}
    (hdir : Lemma45SourceHypothesisData φ ψ)
    (hψ : LocatedRangeSupremum ψ cψ) :
    BishopC.IsCauchy (fun k : Nat => φ (lemma45_nearMaximizer hψ k)) where
  cmod := fun k => k + 2
  ccond := by
    intro k m n hm hn
    let tm := lemma45_nearMaximizer hψ m
    let tn := lemma45_nearMaximizer hψ n
    let du := hdir.directed_domination tm tn
    let u := du.val
    have hdata := du.property
    have hφm_le_u : BishopC.Le (φ tm) (φ u) :=
      BishopC.le_of_nonneg_sub hdata.1.1
    have hφn_le_u : BishopC.Le (φ tn) (φ u) :=
      BishopC.le_of_nonneg_sub hdata.2.1
    have hgapm :
        COF.lt (φ u - φ tm) (COF.halfPow (R := R) (k + 2)) :=
      lemma45_phi_gap_lt_of_directed hψ hdata.1.2 (k + 2) m rfl hm
    have hgapn :
        COF.lt (φ u - φ tn) (COF.halfPow (R := R) (k + 2)) :=
      lemma45_phi_gap_lt_of_directed hψ hdata.2.2 (k + 2) n rfl hn
    exact
      abs_sub_lt_halfPow_of_common_upper_gaps
        hφm_le_u hφn_le_u hgapm hgapn

/-- The candidate supremum value for `φ` in Lemma 4.5: the limit of the
near-maximizer sequence. -/
def lemma45_phi_sup_candidate
    {R : Type*} [COFOC R] {T : Type*}
    {φ ψ : T -> R} {cψ : R}
    (hdir : Lemma45SourceHypothesisData φ ψ)
    (hψ : LocatedRangeSupremum ψ cψ) : BishopC.HasLim
      (fun k : Nat => φ (lemma45_nearMaximizer hψ k)) :=
  COFOC.complete (lemma45_phi_nearMaximizer_isCauchy hdir hψ)

/-- G217 audit. -/
structure Lemma45CauchyCoreAuditAfterG217 : Type where
  source_directed_domination_used : Nat
  psi_located_near_maximizers_used : Nat
  phi_near_maximizer_cauchy_closed : Nat
  candidate_supremum_constructed_by_cofoc_complete : Nat
  rangeSupremum_to_locatedSupremum_selector_used : Nat
  classical_choice_inputs_added : Nat
  remaining_steps_for_full_located_lemma45 : Nat

def lemma45CauchyCoreAuditAfterG217 :
    Lemma45CauchyCoreAuditAfterG217 where
  source_directed_domination_used := 1
  psi_located_near_maximizers_used := 1
  phi_near_maximizer_cauchy_closed := 1
  candidate_supremum_constructed_by_cofoc_complete := 1
  rangeSupremum_to_locatedSupremum_selector_used := 0
  classical_choice_inputs_added := 0
  remaining_steps_for_full_located_lemma45 := 2

/-- G217 package. -/
structure Chapter4G217Lemma45CauchyCorePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g216 : Chapter4G216LocatedSupremumPackage S
  audit : Lemma45CauchyCoreAuditAfterG217
  cauchy_core_closed_this_step : Nat
  remaining_source_completion_steps_for_4_5_to_4_10 : Nat

def chapter4G217Lemma45CauchyCorePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G217Lemma45CauchyCorePackage S where
  g216 := chapter4G216LocatedSupremumPackage S
  audit := lemma45CauchyCoreAuditAfterG217
  cauchy_core_closed_this_step := 1
  remaining_source_completion_steps_for_4_5_to_4_10 := 3

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G217. -/
def bishopRegularSeqChapter4Lemma45CauchyProgressAfterG217 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 79
  total_final_goal_percent := 95
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G217: proved the actual Cauchy core of Lemma 4.5. From the located \
    supremum of psi, the carried near-maximizers t_k make phi(t_k) a Cauchy \
    sequence by the source directed-domination condition. Countdown for \
    source-complete 4.5-4.10: 3."


end BishopCReal
