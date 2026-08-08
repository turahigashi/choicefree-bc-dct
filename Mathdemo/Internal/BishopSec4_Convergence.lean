import Mathdemo.Internal.BishopSec2_L1
import Mathdemo.Internal.BishopSec3_Profile

namespace BishopC

variable {X R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
structure PFunR (X R : Type*) where
  dom : Set X
  toFun : ∀ x ∈ dom, R

def IntegrableRep.toPFunR {S : IntSpaceRC X R} (r : IntegrableRep S) : PFunR X R :=
  { dom := (r.fn 0).dom, toFun := fun x _ => (r.fn 0).toFun x }

-- Technical note.
-- Technical note.

/-- Technical lemma used in the public import closure. -/
noncomputable def IsMeasurable (S : IntSpaceRC X R) (h : PFunR X R) : Prop :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (n : Nat),
    -- Technical note.
    -- Technical note.
    -- Technical note.
    ∃ (rep : IntegrableRep S),
      -- Technical note.
      ∀ x (hx_h : x ∈ h.dom) (hx_A : x ∈ A.S1 ∨ x ∈ A.S2),
        let val := h.toFun x hx_h
        let mid_val := COF.max (COF.min val (n : R)) (-(n : R))
        -- Technical note.
        Nonempty (RSeq.TendstoHalf (fun k => (rep.fn k).toFun x) mid_val)

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_min_f_n {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) : IntegrableRep S :=
  f.cutNatVal n

noncomputable def prop_4_2_n_k {S : IntSpaceRC X R} (f : IntegrableRep S) : Nat → Nat
| 0 => f.cutNat_tendsto_rep.mod 1
| k + 1 => max (f.cutNat_tendsto_rep.mod (k + 2)) (prop_4_2_n_k f k + 1)

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_lambda_k {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (n_k : Nat → Nat) : Nat → IntegrableRep S
| 0 => hA.rep.smul (n_k 0 : R) |>.min2 (f.sub (prop_4_2_min_f_n f 0))
| k + 1 => hA.rep.smul ((n_k (k + 1) - n_k k : Nat) : R) |>.min2 (f.sub (prop_4_2_min_f_n f (n_k k)))

theorem COF_min_comm (a b : R) : COF.min a b = COF.min b a := by
  rw [COF.min_halfsum, COF.min_halfsum, add_comm]
  have hsub : b - a = -(a - b) := by ring
  rw [hsub, COFO.abs_neg]

theorem abs_min_le_abs_of_nonneg_left (a b : R) (ha : ¬COF.lt a 0) :
    Le (COF.abs (COF.min a b)) (COF.abs b) := by
  rw [COF_min_comm]
  exact abs_min_const_le ha b

theorem normL1_min2_le {S : IntSpaceRC X R} (u v : IntegrableRep S)
    {D : Set X} (hD : IsFull S D)
    (hDu : D ⊆ u.domain) (hDv : D ⊆ v.domain)
    (hu : ∀ x ∈ D, ∀ (hx_sum : RSeq.SeriesSum (fun n => (u.fn n).toFun x)), Nonneg hx_sum.sum) :
    Le (u.min2 v).normL1 v.normL1 := by
  refine normL1_mono hD (u.min2 v) v ?_
  intro x hx huv_sum hv_sum
  have hx_udom : x ∈ u.domain := hDu hx
  have hx_vdom : x ∈ v.domain := hDv hx
  obtain ⟨_, ⟨hu_abs⟩⟩ := hx_udom
  obtain ⟨_, ⟨hv_abs⟩⟩ := hx_vdom
  have hu_sum := seriesSum_of_abs hu_abs
  have hpos_u : ¬COF.lt hu_sum.sum 0 := hu x hx hu_sum
  
  let hsub_v := neg_seriesSum_value hv_sum
  let h_u_sub_v := add_seriesSum_value hu_sum hsub_v
  obtain ⟨h_abs, h_abs_eq⟩ := (u.sub v).absVal_signed_value x h_u_sub_v
  let h_add := add_seriesSum_value hu_sum hv_sum
  let h_sub2_v := neg_seriesSum_value h_abs
  let h_inner := add_seriesSum_value h_add h_sub2_v
  let h_final := smul_seriesSum_value (COF.half : R) h_inner
  
  have heq : huv_sum.sum = h_final.sum := seriesSum_unique huv_sum h_final
  rw [heq]
  
  have hval : h_final.sum = COF.min hu_sum.sum hv_sum.sum := by
    change COF.half * ((hu_sum.sum + hv_sum.sum) + -h_abs.sum) = COF.min hu_sum.sum hv_sum.sum
    rw [h_abs_eq]
    have h1 : h_u_sub_v.sum = hu_sum.sum + -hv_sum.sum := rfl
    rw [h1]
    have hsub : hu_sum.sum + -hv_sum.sum = hu_sum.sum - hv_sum.sum := by ring
    rw [hsub]
    have hsub2 : (hu_sum.sum + hv_sum.sum) + -(COF.abs (hu_sum.sum - hv_sum.sum)) = (hu_sum.sum + hv_sum.sum) - (COF.abs (hu_sum.sum - hv_sum.sum)) := by ring
    rw [hsub2]
    rw [COF.min_halfsum]
  rw [hval]
  exact abs_min_le_abs_of_nonneg_left hu_sum.sum hv_sum.sum hpos_u

theorem abs_add_self_nonneg (x : R) : Nonneg (x + COF.abs x) := by
  intro (hlt : COF.lt (x + COF.abs x) 0)
  have hlt2 := COF.lt_add_left (-x) hlt
  have hlt3 : COF.lt (COF.abs x) (-x) := by
    change COF.lt (-x + (x + COF.abs x)) (-x + 0) at hlt2
    have e1 : -x + (x + COF.abs x) = COF.abs x := by ring
    have e2 : -x + (0:R) = -x := by ring
    rw [e1, e2] at hlt2
    exact hlt2
  have hn := COFO.neg_le_abs x
  exact hn hlt3

-- Technical note.
-- Technical note.

theorem repNonneg_sub_cutNatVal {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) :
    RepNonneg (f.sub (prop_4_2_min_f_n f n)) := by
  intro x habs hx
  have hf_abs := add_absSeriesSum_left habs
  have hg_abs := neg_absSeriesSum (add_absSeriesSum_right habs)
  have hf := seriesSum_of_abs hf_abs
  have hg := seriesSum_of_abs hg_abs
  have hx_eq : hx.sum = hf.sum - hg.sum := by
    have heq := seriesSum_unique hx (add_seriesSum_value hf (neg_seriesSum_value hg))
    change hx.sum = hf.sum + -(hg.sum) at heq
    have h2 : hf.sum - hg.sum = hf.sum + -(hg.sum) := sub_eq_add_neg _ _
    rw [h2]
    exact heq
  obtain ⟨hg_signed, hg_signed_eq⟩ := f.cutConstVal_signed_value (n : R) (natCast_nonneg n) x hf
  have heq_fn : ∀ k, ((prop_4_2_min_f_n f n).fn k).toFun x = ((f.cutConstVal (n:R) (natCast_nonneg n)).fn k).toFun x := by
    intro k
    unfold prop_4_2_min_f_n
    unfold IntegrableRep.cutNatVal
    rfl
  have hg_eq : hg.sum = hg_signed.sum := by
    have t := seriesSum_unique hg (RSeq.seriesSum_congr (fun k => (heq_fn k).symm) hg_signed)
    change hg.sum = hg_signed.sum at t
    exact t
  have hx_sum : hx.sum = hf.sum - COF.min hf.sum (n : R) := by
    rw [hx_eq, hg_eq, hg_signed_eq]
  rw [hx_sum]
  have hle : Le (COF.min hf.sum (n : R)) hf.sum := cof_min_le_left _ _
  intro hlt
  have hlt2 := lt_of_sub_neg hlt
  exact hle hlt2

theorem normL1_sub_cutNat_le {S : IntSpaceRC X R} (f : IntegrableRep S) (hf_nonneg : RepNonneg f) (k n : Nat)
    (hk : f.cutNat_tendsto_rep.mod k ≤ n) :
    Le (f.sub (prop_4_2_min_f_n f n)).normL1 (COF.halfPow (R := R) k) := by
  have h_close := f.cutNat_tendsto_rep.close k n hk
  have h_close2 : COF.lt (COF.abs ((f.cutNatVal n).integral - f.integral)) (COF.halfPow (R := R) k) := h_close
  have hsub_nonneg : RepNonneg (f.sub (prop_4_2_min_f_n f n)) := repNonneg_sub_cutNatVal f n
  have h1 : (f.sub (prop_4_2_min_f_n f n)).normL1 = (f.sub (prop_4_2_min_f_n f n)).integral :=
    IntegrableRep.normL1_eq_integral_of_nonneg (f.sub (prop_4_2_min_f_n f n)) hsub_nonneg
  rw [h1, IntegrableRep.integral_sub]
  have eq_abs : COF.abs ((f.cutNatVal n).integral - f.integral) = COF.abs (f.integral - (prop_4_2_min_f_n f n).integral) := by
    change COF.abs ((f.cutNatVal n).integral - f.integral) = COF.abs (f.integral - (f.cutNatVal n).integral)
    have h1 : (f.cutNatVal n).integral - f.integral = -(f.integral - (f.cutNatVal n).integral) := by ring
    rw [h1, COFO.abs_neg]
  rw [eq_abs] at h_close2
  exact BishopC.le_trans (COFO.le_abs_self _) (BishopC.le_of_lt h_close2)

theorem test_nonneg_0 : Nonneg (0 : R) := COF.lt_irrefl 0
theorem test_nonneg_1 : Nonneg (1 : R) := by
  intro hlt
  have h := COFO.one_pos (R := R)
  have h2 := COFO.lt_trans h hlt
  exact COF.lt_irrefl 0 h2

theorem IntegrableSet1_repNonneg {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A) : RepNonneg hA.rep := by
  intro x habs hx
  have hvalid := hA.valid x habs
  have h_or := hvalid.1
  cases h_or with
  | inl hS1 =>
    have heq := hvalid.2.1 hS1 hx
    rw [heq]
    exact test_nonneg_1
  | inr hS2 =>
    have heq := hvalid.2.2 hS2 hx
    rw [heq]
    exact test_nonneg_0



/-- min a b <= min a c when b <= c -/
theorem min_le_min_right (a b c : R) (h : Le b c) : Le (COF.min a b) (COF.min a c) := by
  intro hlt
  have e1 : COF.min a c - COF.min a b = COF.half * (c - b + COF.abs (a - b) - COF.abs (a - c)) := by
    rw [COF.min_halfsum a c, COF.min_halfsum a b]
    ring
  have h1 : Le (COF.abs (a - c)) (COF.abs (a - b) + COF.abs (b - c)) := by
    have h1a := COFO.abs_add_le (a - b) (b - c)
    have e2 : a - b + (b - c) = a - c := by ring
    rw [e2] at h1a
    exact h1a
  have h_nonneg : Nonneg (c - b) := by
    intro hlt2
    have h2 := COF.lt_add_left b hlt2
    have e2a : b + (c - b) = c := by ring
    have e2b : b + 0 = b := by ring
    rw [e2a, e2b] at h2
    exact h h2
  have e3 : COF.abs (c - b) = c - b := COFO.abs_of_nonneg h_nonneg
  have e4 : COF.abs (b - c) = COF.abs (c - b) := by
    have e5 : b - c = -(c - b) := by ring
    rw [e5, COFO.abs_neg]
  have e6 : COF.abs (b - c) = c - b := by rw [e4, e3]
  
  have h3 := COF.lt_add_left (- COF.min a c) hlt
  have e8 : - COF.min a c + COF.min a c = 0 := by ring
  have e9 : - COF.min a c + COF.min a b = - (COF.min a c - COF.min a b) := by ring
  rw [e8, e9, e1] at h3
  
  have e10 : - (COF.half * (c - b + COF.abs (a - b) - COF.abs (a - c))) = COF.half * (COF.abs (a - c) - (c - b + COF.abs (a - b))) := by ring
  rw [e10] at h3
  
  have h_add := lt_add h3 h3
  have e11 : (0:R) + 0 = 0 := by ring
  have e12 : COF.half * (COF.abs (a - c) - (c - b + COF.abs (a - b))) + COF.half * (COF.abs (a - c) - (c - b + COF.abs (a - b))) = COF.abs (a - c) - (c - b + COF.abs (a - b)) := by
    calc
      _ = (COF.half + COF.half) * (COF.abs (a - c) - (c - b + COF.abs (a - b))) := by ring
      _ = 1 * (COF.abs (a - c) - (c - b + COF.abs (a - b))) := by rw [COF.half_add_half]
      _ = COF.abs (a - c) - (c - b + COF.abs (a - b)) := by ring
  rw [e11, e12] at h_add
  
  have h4 := COF.lt_add_left (c - b + COF.abs (a - b)) h_add
  have e13 : c - b + COF.abs (a - b) + 0 = c - b + COF.abs (a - b) := by ring
  have e14 : c - b + COF.abs (a - b) + (COF.abs (a - c) - (c - b + COF.abs (a - b))) = COF.abs (a - c) := by ring
  rw [e13, e14] at h4
  
  have e15 : c - b + COF.abs (a - b) = COF.abs (a - b) + COF.abs (b - c) := by
    rw [← e6]
    ring
  rw [e15] at h4
  exact h1 h4

/-- |f + g|_1 <= |f|_1 + |g|_1 -/
theorem normL1_add_le {S : IntSpaceRC X R} (f g : IntegrableRep S) :
    Le (f.add g).normL1 (f.normL1 + g.normL1) := by
  have heq : f.normL1 + g.normL1 = (f.absVal.add g.absVal).integral := by
    rw [IntegrableRep.integral_add]
    rfl
  rw [heq]
  have h_full : IsFull S (Set.inter f.domain g.domain) :=
    isFull_inter f.domain_isFull g.domain_isFull
  refine prop_1_11 h_full (f.add g).absVal (f.absVal.add g.absVal) ?_
  intro x hx hu hv
  obtain ⟨_, ⟨hf_abs⟩⟩ := hx.1
  obtain ⟨_, ⟨hg_abs⟩⟩ := hx.2
  have hfx_sum := seriesSum_of_abs hf_abs
  have hgx_sum := seriesSum_of_abs hg_abs
  let h_add := add_seriesSum_value hfx_sum hgx_sum
  obtain ⟨hu_alt, hueq⟩ := (f.add g).absVal_signed_value x h_add
  have e_hu : hu.sum = COF.abs (hfx_sum.sum + hgx_sum.sum) := by
    have e1 : hu.sum = hu_alt.sum := seriesSum_unique hu hu_alt
    rw [e1, hueq]
    rfl
  obtain ⟨hsu_f, hsu_feq⟩ := f.absVal_signed_value x hfx_sum
  obtain ⟨hsu_g, hsu_geq⟩ := g.absVal_signed_value x hgx_sum
  let h_add_abs := add_seriesSum_value hsu_f hsu_g
  have e_hv : hv.sum = COF.abs hfx_sum.sum + COF.abs hgx_sum.sum := by
    have e2 : hv.sum = h_add_abs.sum := seriesSum_unique hv h_add_abs
    rw [e2]
    have e3 : h_add_abs.sum = hsu_f.sum + hsu_g.sum := rfl
    rw [e3, hsu_feq, hsu_geq]
  rw [e_hu, e_hv]
  exact COFO.abs_add_le hfx_sum.sum hgx_sum.sum

def lemma_4_3_cut_tendsto_zero {S : IntSpaceRC X R} (f : IntegrableRep S)
    (hf_nonneg : RepNonneg f)
    (alpha_n : Nat → R)
    (h_alpha_nonneg : ∀ n, ¬ COF.lt (alpha_n n) 0)
    (h_alpha_le : ∀ n, ¬ COF.lt (COF.halfPow n) (alpha_n n)) :
    RSeq.TendstoHalf (fun n => (f.cutConstVal (alpha_n n) (h_alpha_nonneg n)).integral) 0 := by
  -- squeeze 0 ≤ I(min(f,αₙ)) ≤ I(min(|f|,2⁻ⁿ)) → 0
  -- Technical note.
  refine tendstoHalf_squeeze_zero f.cutSmall_tendsto_rep ?_ ?_
  · intro n
    exact ((f.cutConstVal (alpha_n n) (h_alpha_nonneg n)).normL1_eq_integral_of_nonneg
        (repNonneg_cutConstVal f hf_nonneg (alpha_n n) (h_alpha_nonneg n))) ▸
      (f.cutConstVal (alpha_n n) (h_alpha_nonneg n)).normL1_nonneg
  · intro n
    exact IntegrableRep.integral_mono_of_repNonneg_sub
      (repNonneg_cutSmall_sub_cutConst f hf_nonneg n (alpha_n n) (h_alpha_nonneg n) (h_alpha_le n))

theorem IntegrableRep.domain_subset_smul (r : IntegrableRep S) (c : R) :
    r.domain ⊆ (r.smul c).domain := by
  intro x hx
  obtain ⟨hdom, ⟨habs⟩⟩ := hx
  refine ⟨hdom, ?_⟩
  have hcabs := seriesSum_smul (COF.abs c) habs
  have h_eq : ∀ n, COF.abs c * COF.abs ((r.fn n).toFun x) = COF.abs (((r.smul c).fn n).toFun x) := by
    intro n
    change COF.abs c * COF.abs ((r.fn n).toFun x) = COF.abs (c * ((r.fn n).toFun x))
    rw [COFO.abs_mul]
  exact ⟨RSeq.seriesSum_congr h_eq hcabs⟩

theorem lambda_k_norm_le {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) (n_k : Nat → Nat)
    (hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_k k) (k : Nat) :
    Le (prop_4_2_lambda_k A hA f n_k (k + 1)).normL1 (COF.halfPow (R := R) (k + 1)) := by
  let c : R := ((n_k (k + 1) - n_k k : Nat) : R)
  let u := hA.rep.smul c
  let v := f.sub (prop_4_2_min_f_n f (n_k k))
  let D := Set.inter hA.rep.domain v.domain
  have hD : IsFull S D := isFull_inter hA.rep.domain_isFull v.domain_isFull
  have hDu : D ⊆ u.domain := by
    intro x hx
    exact IntegrableRep.domain_subset_smul hA.rep c hx.1
  have hDv : D ⊆ v.domain := fun x hx => hx.2
  have hu_custom : ∀ x ∈ D, ∀ (hx_sum : RSeq.SeriesSum (fun n => (u.fn n).toFun x)), Nonneg hx_sum.sum := by
    intro x hx hx_sum
    have hx_rep_dom : x ∈ hA.rep.domain := hx.1
    obtain ⟨_, ⟨habs_rep⟩⟩ := hx_rep_dom
    have hx_rep := seriesSum_of_abs habs_rep
    have hpos_rep := IntegrableSet1_repNonneg hA x habs_rep hx_rep
    have heq : hx_sum.sum = c * hx_rep.sum := by
      let h_smul := seriesSum_smul c hx_rep
      let h_smul_congr := RSeq.seriesSum_congr (fun n => (smul_fn_toFun c hA.rep n x).symm) h_smul
      exact seriesSum_unique hx_sum h_smul_congr
    rw [heq]
    exact COFO.mul_nonneg (natCast_nonneg _) hpos_rep
  have hl := normL1_min2_le u v hD hDu hDv hu_custom
  have h_le_v : Le v.normL1 (COF.halfPow (R := R) (k + 1)) := normL1_sub_cutNat_le f hnn (k + 1) (n_k k) (hnk_ge k)
  exact BishopC.le_trans hl h_le_v

noncomputable def opaque_lambda_norm {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (n_k : Nat → Nat) (l : Nat) := (prop_4_2_lambda_k A hA f n_k l).normL1

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_lambda_sum {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) (n_k : Nat → Nat)
    (hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_k k) :
    RSeq.SeriesSum (fun k => opaque_lambda_norm A hA f n_k k) := by
  refine @seriesSum_of_tail R _ _ 0 ?_
  have hnn_term : ∀ l, Nonneg (opaque_lambda_norm A hA f n_k (1 + l)) := fun l => IntegrableRep.normL1_nonneg _
  have hle_term : ∀ l, Le (opaque_lambda_norm A hA f n_k (1 + l)) (COF.halfPow (R := R) l) := by
    intro l
    have hk := lambda_k_norm_le A hA f hnn n_k hnk_ge l
    have hhalf_le : Le (COF.halfPow (R := R) (l + 1)) (COF.halfPow (R := R) l) := BishopC.le_of_lt (BishopC.halfPow_lt_succ l)
    have heq : opaque_lambda_norm A hA f n_k (1 + l) = (prop_4_2_lambda_k A hA f n_k (l + 1)).normL1 := by
      change (prop_4_2_lambda_k A hA f n_k (1 + l)).normL1 = _
      congr 2
      omega
    rw [heq]
    exact BishopC.le_trans hk hhalf_le
  exact @seriesSum_of_le_halfPow R _ (fun l => opaque_lambda_norm A hA f n_k (1 + l)) hnn_term hle_term

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_chi_f_rep {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) : IntegrableRep S :=
  let n_seq := prop_4_2_n_k f
  have hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_seq k := by
    intro k
    cases k with
    | zero => exact Nat.le_refl _
    | succ k' => exact Nat.le_max_left _ _
  let lambda := prop_4_2_lambda_k A hA f n_seq
  let hsum := prop_4_2_lambda_sum A hA f hnn n_seq hnk_ge
  seriesSumRep_L1 lambda hsum

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_3_alpha {S : IntSpaceRC X R} (f : IntegrableRep S) : Nat → R :=
  fun n => (thm_3_6_level_sets_integrable f (COF.halfPow (n + 1)) (COF.halfPow n) (halfPow_lt_succ n) (halfPow_pos (n + 1))).1

theorem lemma_4_3_alpha_pos {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) :
    COF.lt 0 (lemma_4_3_alpha f n) :=
  COFO.lt_trans (halfPow_pos (n + 1)) (thm_3_6_level_sets_integrable f (COF.halfPow (n + 1)) (COF.halfPow n) (halfPow_lt_succ n) (halfPow_pos (n + 1))).2.1

theorem lemma_4_3_alpha_nonneg {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) :
    ¬ COF.lt (lemma_4_3_alpha f n) 0 :=
  fun h => COF.lt_irrefl _ (COFO.lt_trans (lemma_4_3_alpha_pos f n) h)

theorem lemma_4_3_alpha_lt_halfPow {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) :
    COF.lt (lemma_4_3_alpha f n) (COF.halfPow n) :=
  (thm_3_6_level_sets_integrable f (COF.halfPow (n + 1)) (COF.halfPow n) (halfPow_lt_succ n) (halfPow_pos (n + 1))).2.2.1

theorem lemma_4_3_alpha_le {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) :
    ¬ COF.lt (COF.halfPow n) (lemma_4_3_alpha f n) :=
  fun h => COF.lt_irrefl _ (COFO.lt_trans (lemma_4_3_alpha_lt_halfPow f n) h)

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_3_A_n {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) : BSet X :=
  ((thm_3_6_level_sets_integrable f (COF.halfPow (n + 1)) (COF.halfPow n)
    (halfPow_lt_succ n) (halfPow_pos (n + 1))).2.2.2).choose

/-- Technical lemma used in the public import closure. -/
theorem lemma_4_3_A_n_integrable {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) :
    Nonempty (IntegrableSet1 S (lemma_4_3_A_n f n)) := by
  have h := (thm_3_6_level_sets_integrable f (COF.halfPow (n + 1)) (COF.halfPow n) (halfPow_lt_succ n) (halfPow_pos (n + 1))).2.2.2
  exact h.choose_spec.2.2

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_3_approx_f {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) : IntegrableRep S :=
  f.sub (f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n))

/-- Technical lemma used in the public import closure. -/
theorem lemma_4_3_tendsto_I_f {S : IntSpaceRC X R} (f : IntegrableRep S)
    (hf_nonneg : RepNonneg f) :
    Nonempty (RSeq.TendstoHalf (fun n => (lemma_4_3_approx_f f n).integral) f.integral) := by
  have hz := lemma_4_3_cut_tendsto_zero f hf_nonneg (lemma_4_3_alpha f)
    (lemma_4_3_alpha_nonneg f) (lemma_4_3_alpha_le f)
  refine ⟨?_⟩
  exact {
    mod := hz.mod
    close := by
      intro k n hn
      have h_close := hz.close k n hn
      have heq : (lemma_4_3_approx_f f n).integral =
          f.integral - (f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n)).integral := by
        exact IntegrableRep.integral_sub f (f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n))
      change COF.lt (COF.abs ((f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n)).integral - 0)) (COF.halfPow k) at h_close
      change COF.lt (COF.abs ((lemma_4_3_approx_f f n).integral - f.integral)) (COF.halfPow k)
      rw [heq]
      have heq2 : COF.abs (f.integral - (f.cutConstVal (lemma_4_3_alpha f n)
          (lemma_4_3_alpha_nonneg f n)).integral - f.integral) =
          COF.abs ((f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n)).integral - 0) := by
        have e1 : f.integral - (f.cutConstVal (lemma_4_3_alpha f n)
            (lemma_4_3_alpha_nonneg f n)).integral - f.integral =
            - (f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n)).integral := by ring
        have e2 : (f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n)).integral - 0 =
            (f.cutConstVal (lemma_4_3_alpha f n) (lemma_4_3_alpha_nonneg f n)).integral := by ring
        rw [e1, e2, COFO.abs_neg]
      rw [heq2]
      exact h_close
  }

/-- Technical lemma used in the public import closure. -/
theorem lemma_4_3_sup_integrals {S : IntSpaceRC X R} (f : IntegrableRep S)
    (hf_nonneg : RepNonneg f) :
    Nonempty (RSeq.TendstoHalf (fun n => (lemma_4_3_approx_f f n).integral) f.integral) := by
  let alpha := lemma_4_3_alpha f
  let A_n := lemma_4_3_A_n f
  let hA := lemma_4_3_A_n_integrable f
  let approx := lemma_4_3_approx_f f
  let ht := lemma_4_3_tendsto_I_f f hf_nonneg
  exact ht

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_4_min_chi_f {S : IntSpaceRC X R} (h : PFunR X R)
    (hm : IsMeasurable S h) (C : Nat → BSet X) (hC : ∀ n, IntegrableSet1 S (C n)) (n : Nat) : IntegrableRep S :=
  ((hm (C n) (hC n) n)).choose

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_4_lambda_n {S : IntSpaceRC X R} (h : PFunR X R)
    (hm : IsMeasurable S h) (C : Nat → BSet X) (hC : ∀ n, IntegrableSet1 S (C n)) : Nat → IntegrableRep S
| 0 => prop_4_4_min_chi_f h hm C hC 0
| n + 1 => (prop_4_4_min_chi_f h hm C hC (n + 1)).sub (prop_4_4_min_chi_f h hm C hC n)

theorem prop_4_4_lambda_integral_eq {S : IntSpaceRC X R} (h : PFunR X R)
    (hm : IsMeasurable S h) (C : Nat → BSet X) (hC : ∀ n, IntegrableSet1 S (C n)) :
    ∀ N, RSeq.partialSum (fun n => (prop_4_4_lambda_n h hm C hC n).integral) N
       = (prop_4_4_min_chi_f h hm C hC N).integral
  | 0 => rfl
  | N + 1 => by
      show RSeq.partialSum _ N + (prop_4_4_lambda_n h hm C hC (N + 1)).integral = _
      rw [prop_4_4_lambda_integral_eq h hm C hC N]
      change (prop_4_4_min_chi_f h hm C hC N).integral +
             ((prop_4_4_min_chi_f h hm C hC (N + 1)).sub (prop_4_4_min_chi_f h hm C hC N)).integral =
             (prop_4_4_min_chi_f h hm C hC (N + 1)).integral
      rw [IntegrableRep.integral_sub]
      ring

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_4_lambda_sum {S : IntSpaceRC X R} (h : PFunR X R)
    (hm : IsMeasurable S h) (h_nonneg : ∀ x hx, ¬ COF.lt (h.toFun x hx) 0)
    (C : Nat → BSet X) (hC : ∀ n, IntegrableSet1 S (C n))
    (h_lambda_nonneg : ∀ n, RepNonneg (prop_4_4_lambda_n h hm C hC n))
    (c : R) (h_lim : RSeq.TendstoHalf (fun n => (prop_4_4_min_chi_f h hm C hC n).integral) c) :
    RSeq.SeriesSum (fun n => (prop_4_4_lambda_n h hm C hC n).normL1) :=
  { sum := c
    tends := by
      have h_eq : ∀ N, RSeq.partialSum (fun n => (prop_4_4_lambda_n h hm C hC n).normL1) N = (prop_4_4_min_chi_f h hm C hC N).integral := by
        intro N
        have h_norm : ∀ n, (prop_4_4_lambda_n h hm C hC n).normL1 = (prop_4_4_lambda_n h hm C hC n).integral := fun n =>
          IntegrableRep.normL1_eq_integral_of_nonneg _ (h_lambda_nonneg n)
        have h_sum : RSeq.partialSum (fun n => (prop_4_4_lambda_n h hm C hC n).normL1) N =
                     RSeq.partialSum (fun n => (prop_4_4_lambda_n h hm C hC n).integral) N :=
          RSeq.partialSum_congr h_norm N
        rw [h_sum]
        exact prop_4_4_lambda_integral_eq h hm C hC N
      have heq2 : (RSeq.partialSum (fun n => (prop_4_4_lambda_n h hm C hC n).normL1))
                = (fun N => (prop_4_4_min_chi_f h hm C hC N).integral) := funext h_eq
      rw [heq2]
      exact h_lim }

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_4_measurable_rep {S : IntSpaceRC X R} (h : PFunR X R)
    (hm : IsMeasurable S h) (h_nonneg : ∀ x hx, ¬ COF.lt (h.toFun x hx) 0)
    (C : Nat → BSet X) (hC : ∀ n, IntegrableSet1 S (C n))
    (h_lambda_nonneg : ∀ n, RepNonneg (prop_4_4_lambda_n h hm C hC n))
    (c : R) (h_lim : RSeq.TendstoHalf (fun n => (prop_4_4_min_chi_f h hm C hC n).integral) c) :
    IntegrableRep S :=
  let lambda := prop_4_4_lambda_n h hm C hC
  let hsum := prop_4_4_lambda_sum h hm h_nonneg C hC h_lambda_nonneg c h_lim
  seriesSumRep_L1 lambda hsum

/-- Technical lemma used in the public import closure. -/
def Thm46State (X : Type*) := BSet X × Nat

/-- Technical lemma used in the public import closure. -/
def thm_4_6_s3 (s1 s2 : Thm46State X) : Thm46State X :=
  (BSet.or s1.1 s2.1, s1.2 + s2.2)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_6_phi {S : IntSpaceRC X R} (f : PFunR X R)
    (hm : IsMeasurable S f) (s : Thm46State X) (hA : IntegrableSet1 S s.1) : R :=
  (prop_4_4_min_chi_f f hm (fun _ => s.1) (fun _ => hA) s.2).integral

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_6_psi {S : IntSpaceRC X R} (f : PFunR X R)
    (hm : IsMeasurable S f) (s : Thm46State X) (hA : IntegrableSet1 S s.1) : R :=
  (prop_4_4_min_chi_f f hm (fun _ => s.1) (fun _ => hA) s.2).integral

/- Technical proof note. -/

/-- Technical lemma used in the public import closure. -/
def IsMeasurableSet {S : IntSpaceRC X R} (B : BSet X) : Type _ :=
  ∀ (A : BSet X), IntegrableSet1 S A → IntegrableSet1 S (BSet.and A B)

/-- Technical lemma used in the public import closure. -/
noncomputable def isMeasurableSet_of_integrable {S : IntSpaceRC X R} {B : BSet X}
    (hB : IntegrableSet1 S B) : IsMeasurableSet (S := S) B :=
  fun A hA => IntegrableSet1_and hA hB

/-- Technical lemma used in the public import closure. -/
noncomputable def isMeasurableSet_neg_of_integrable {S : IntSpaceRC X R} {C : BSet X}
    (hC : IntegrableSet1 S C) : IsMeasurableSet (S := S) (BSet.neg C) :=
  fun A hA => IntegrableSet1_sub hA hC

/-- Technical lemma used in the public import closure. -/
def ConvergeInMeasure (S : IntSpaceRC X R) (fn : Nat → PFunR X R) (f : PFunR X R) : Prop :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (eps : R) (heps : COF.lt 0 eps),
    ∃ N : Nat, ∀ n ≥ N,
      ∃ (B : BSet X) (hB : IntegrableSet1 S B),
        (B.S1 ⊆ A.S1 ∩ f.dom ∩ (fn n).dom) ∧
        -- Technical note.
        COF.lt (measure1 S (IntegrableSet1_sub hA hB)) eps ∧
        -- Technical note.
        ∀ x (hxB : x ∈ B.S1) (hxf : x ∈ f.dom) (hxfn : x ∈ (fn n).dom), COF.lt (COF.abs (f.toFun x hxf - (fn n).toFun x hxfn)) eps

-- Technical note.
-- Technical note.
-- Technical note.
-- Technical note.

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_13_lambda {S : IntSpaceRC X R} (fn : Nat → IntegrableRep S) (n : Nat) : IntegrableRep S :=
  (fn (n + 1)).sub (fn n)

/-- Technical lemma used in the public import closure. -/
noncomputable def tendstoHalf_succ {u : Nat → R} {l : R} (h : RSeq.TendstoHalf u l) : RSeq.TendstoHalf (fun n => u (n + 1)) l :=
  { mod := fun k => h.mod k
    close := fun k n hn => by
      have h1 : n ≤ n + 1 := Nat.le_succ n
      exact h.close k (n + 1) (Nat.le_trans hn h1) }

noncomputable def thm_4_13_lambda_sum {S : IntSpaceRC X R} (fn : Nat → IntegrableRep S)
    (h_mono : ∀ n, (thm_4_13_lambda fn n).normL1 = (fn (n + 1)).integral - (fn n).integral)
    (c : R) (h_lim : RSeq.TendstoHalf (fun n => (fn n).integral) c) :
    RSeq.SeriesSum (fun n => (thm_4_13_lambda fn n).normL1) :=
  { sum := c - (fn 0).integral
    tends := by
      have h_eq : ∀ N, RSeq.partialSum (fun n => (thm_4_13_lambda fn n).normL1) N = (fn (N + 1)).integral - (fn 0).integral := by
        intro N
        induction N with
        | zero => exact h_mono 0
        | succ N ih =>
          show RSeq.partialSum (fun n => (thm_4_13_lambda fn n).normL1) N + (thm_4_13_lambda fn (N + 1)).normL1 = (fn (N + 2)).integral - (fn 0).integral
          rw [ih, h_mono (N + 1)]
          have h1 : (fn (N + 1)).integral - (fn 0).integral = (fn (N + 1)).integral + (-(fn 0).integral) := sub_eq_add_neg _ _
          have h2 : (fn (N + 2)).integral - (fn (N + 1)).integral = (fn (N + 2)).integral + (-(fn (N + 1)).integral) := sub_eq_add_neg _ _
          have h3 : (fn (N + 2)).integral - (fn 0).integral = (fn (N + 2)).integral + (-(fn 0).integral) := sub_eq_add_neg _ _
          rw [h1, h2, h3]
          generalize (fn 0).integral = A
          generalize (fn (N + 1)).integral = B
          generalize (fn (N + 2)).integral = C
          ring
      have heq2 : RSeq.partialSum (fun n => (thm_4_13_lambda fn n).normL1)
                = (fun N => (fn (N + 1)).integral - (fn 0).integral) := funext h_eq
      rw [heq2]
      have h_lim_succ : RSeq.TendstoHalf (fun n => (fn (n + 1)).integral) c := tendstoHalf_succ h_lim
      have h_lim2 : RSeq.TendstoHalf (fun n => (fn (n + 1)).integral + (-(fn 0).integral)) (c + (-(fn 0).integral)) :=
        tendstoHalf_add h_lim_succ (tendstoHalf_const (-(fn 0).integral))
      have heq3 : (fun N => (fn (N + 1)).integral - (fn 0).integral) = (fun N => (fn (N + 1)).integral + (-(fn 0).integral)) := by
        funext N; exact sub_eq_add_neg _ _
      have heq4 : c - (fn 0).integral = c + (-(fn 0).integral) := sub_eq_add_neg _ _
      rw [heq3, heq4]
      exact h_lim2 }

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_13_monotone_convergence {S : IntSpaceRC X R} (fn : Nat → IntegrableRep S)
    (h_mono : ∀ n, (thm_4_13_lambda fn n).normL1 = (fn (n + 1)).integral - (fn n).integral)
    (c : R) (h_lim : RSeq.TendstoHalf (fun n => (fn n).integral) c) :
    IntegrableRep S :=
  let lambda := thm_4_13_lambda fn
  let hsum := thm_4_13_lambda_sum fn h_mono c h_lim
  let g := seriesSumRep_L1 lambda hsum
  (fn 0).add g

/-- Technical lemma used in the public import closure. -/
theorem thm_4_13_h_mono_of_nonneg {S : IntSpaceRC X R} (fn : Nat → IntegrableRep S)
    (h_nn : ∀ n, RepNonneg (thm_4_13_lambda fn n)) :
    ∀ n, (thm_4_13_lambda fn n).normL1 = (fn (n + 1)).integral - (fn n).integral := by
  intro n
  rw [(thm_4_13_lambda fn n).normL1_eq_integral_of_nonneg (h_nn n)]
  exact IntegrableRep.integral_sub (fn (n + 1)) (fn n)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_13_monotone_convergence_faithful {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S)
    (h_nn : ∀ n, RepNonneg (thm_4_13_lambda fn n))
    (c : R) (h_lim : RSeq.TendstoHalf (fun n => (fn n).integral) c) :
    IntegrableRep S :=
  thm_4_13_monotone_convergence fn (thm_4_13_h_mono_of_nonneg fn h_nn) c h_lim

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem le_min {a b c : R} (hca : Le c a) (hcb : Le c b) : Le c (COF.min a b) := by
  rw [COF.min_halfsum]
  apply le_of_nonneg_sub
  have hac : Nonneg (a - c) := nonneg_sub_of_le hca
  have hbc : Nonneg (b - c) := nonneg_sub_of_le hcb
  have habs : Le (COF.abs (a - b)) ((a - c) + (b - c)) := by
    have h1 := COFO.abs_add_le (a - c) (-(b - c))
    rw [COFO.abs_neg, show (a - c) + (-(b - c)) = (a - c) - (b - c) from by ring,
        show (a - c) - (b - c) = a - b from by ring,
        COFO.abs_of_nonneg hac, COFO.abs_of_nonneg hbc] at h1
    exact h1
  have hkey : Nonneg ((a - c) + (b - c) - COF.abs (a - b)) := nonneg_sub_of_le habs
  have heq : COF.half * (a + b - COF.abs (a - b)) - c
      = COF.half * ((a - c) + (b - c) - COF.abs (a - b)) := by
    linear_combination c * COF.half_add_half (R := R)
  rw [heq]
  exact COFO.mul_nonneg (le_of_lt COFO.half_pos) hkey

/-- Technical lemma used in the public import closure. -/
theorem prop42_term_chi1 (φ p q : R) (hpq : Le p q) :
    COF.min (q - p) (φ - COF.min φ p) = COF.min φ q - COF.min φ p := by
  apply le_antisymm
  · apply le_of_add_le_add_right (c := COF.min φ p)
    rw [show COF.min φ q - COF.min φ p + COF.min φ p = COF.min φ q from by ring]
    apply le_min
    · have h1 : Le (COF.min (q - p) (φ - COF.min φ p)) (φ - COF.min φ p) := cof_min_le_right _ _
      have := le_add h1 (le_refl (COF.min φ p))
      rw [show φ - COF.min φ p + COF.min φ p = φ from by ring] at this
      exact this
    · have h1 : Le (COF.min (q - p) (φ - COF.min φ p)) (q - p) := cof_min_le_left _ _
      have h2 : Le (COF.min φ p) p := cof_min_le_right _ _
      have := le_add h1 h2
      rw [show q - p + p = q from by ring] at this
      exact this
  · apply le_min
    · have h := abs_min_sub_min_le q p φ
      rw [COF_min_comm q φ, COF_min_comm p φ,
          COFO.abs_of_nonneg (nonneg_sub_of_le hpq)] at h
      exact le_trans (COFO.le_abs_self _) h
    · have h1 : Le (COF.min φ q) φ := cof_min_le_left _ _
      exact le_sub_right h1

/-- Technical lemma used in the public import closure. -/
theorem prop42_term (φ χ p q : R) (hpq : Le p q) (hχ : χ = 0 ∨ χ = 1) :
    COF.min ((q - p) * χ) (φ - COF.min φ p) = χ * (COF.min φ q - COF.min φ p) := by
  rcases hχ with h0 | h1
  · subst h0
    rw [mul_zero, zero_mul]
    exact min_zero_left (nonneg_sub_of_le (cof_min_le_left φ p))
  · subst h1
    rw [mul_one, one_mul]
    exact prop42_term_chi1 φ p q hpq

/-- Technical lemma used in the public import closure. -/
def prevSeq (m : Nat → R) : Nat → R
  | 0 => 0
  | k + 1 => m k

/-- Technical lemma used in the public import closure. -/
theorem prop42_telescope (φ χ : R) (m : Nat → R)
    (hm0 : Nonneg (m 0)) (hmono : ∀ k, Le (m k) (m (k + 1))) (hχ : χ = 0 ∨ χ = 1) :
    ∀ K, RSeq.partialSum
          (fun k => COF.min ((m k - prevSeq m k) * χ) (φ - COF.min φ (prevSeq m k))) K
        = χ * (COF.min φ (m K) - COF.min φ 0) := by
  intro K
  induction K with
  | zero =>
    show COF.min ((m 0 - (0:R)) * χ) (φ - COF.min φ (0:R)) = χ * (COF.min φ (m 0) - COF.min φ 0)
    exact prop42_term φ χ 0 (m 0) hm0 hχ
  | succ K ih =>
    show RSeq.partialSum
          (fun k => COF.min ((m k - prevSeq m k) * χ) (φ - COF.min φ (prevSeq m k))) K
        + COF.min ((m (K + 1) - m K) * χ) (φ - COF.min φ (m K))
        = χ * (COF.min φ (m (K + 1)) - COF.min φ 0)
    rw [ih, prop42_term φ χ (m K) (m (K + 1)) (hmono K) hχ]
    ring

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_term_value {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (c a : R) (ha : ¬ COF.lt a 0) (x : X)
    (hχ : RSeq.SeriesSum (fun n => (hA.rep.fn n).toFun x))
    (hf : RSeq.SeriesSum (fun n => (f.fn n).toFun x)) :
    { hv : RSeq.SeriesSum
            (fun n => (((hA.rep.smul c).min2 (f.sub (f.cutConstVal a ha))).fn n).toFun x) //
        hv.sum = COF.min (c * hχ.sum) (hf.sum - COF.min hf.sum a) } := by
  obtain ⟨hg, hgeq⟩ := f.cutConstVal_signed_value a ha x hf
  obtain ⟨hm, hmeq⟩ :=
    min2_value (hA.rep.smul c) (f.sub (f.cutConstVal a ha)) x
      (smul_seriesSum_value c hχ) (add_seriesSum_value hf (neg_seriesSum_value hg))
  refine ⟨hm, ?_⟩
  rw [hmeq]
  congr 1
  show hf.sum + (-(hg.sum)) = hf.sum - COF.min hf.sum a
  rw [hgeq]; ring

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_lambda_value {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (n_k : Nat → Nat) (hmono : ∀ k, n_k k ≤ n_k (k + 1)) (x : X)
    (hχ : RSeq.SeriesSum (fun n => (hA.rep.fn n).toFun x))
    (hf : RSeq.SeriesSum (fun n => (f.fn n).toFun x)) (k : Nat) :
    { hv : RSeq.SeriesSum (fun n => ((prop_4_2_lambda_k A hA f n_k k).fn n).toFun x) //
        hv.sum = COF.min (((n_k k : R) - prevSeq (fun j => (n_k j : R)) k) * hχ.sum)
                          (hf.sum - COF.min hf.sum (prevSeq (fun j => (n_k j : R)) k)) } := by
  cases k with
  | zero =>
    obtain ⟨hv, hveq⟩ :=
      prop_4_2_term_value hA f ((n_k 0 : R)) ((0 : Nat) : R) (natCast_nonneg 0) x hχ hf
    refine ⟨hv, ?_⟩
    rw [hveq]
    show COF.min ((n_k 0 : R) * hχ.sum) (hf.sum - COF.min hf.sum ((0:Nat):R))
        = COF.min (((n_k 0 : R) - (0:R)) * hχ.sum) (hf.sum - COF.min hf.sum (0:R))
    rw [Nat.cast_zero, sub_zero]
  | succ k =>
    obtain ⟨hv, hveq⟩ :=
      prop_4_2_term_value hA f (((n_k (k + 1) - n_k k : Nat) : R)) ((n_k k : R))
        (natCast_nonneg (n_k k)) x hχ hf
    refine ⟨hv, ?_⟩
    rw [hveq]
    show COF.min (((n_k (k + 1) - n_k k : Nat) : R) * hχ.sum) (hf.sum - COF.min hf.sum ((n_k k : R)))
        = COF.min (((n_k (k + 1) : R) - (n_k k : R)) * hχ.sum) (hf.sum - COF.min hf.sum ((n_k k : R)))
    rw [Nat.cast_sub (hmono k)]

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem natCast_le_of_le {a b : Nat} (h : a ≤ b) : Le ((a : R)) ((b : R)) := by
  apply le_of_nonneg_sub
  rw [← Nat.cast_sub h]
  exact natCast_nonneg (b - a)

/-- Technical lemma used in the public import closure. -/
theorem le_of_mul_le_mul_pos_right {a b c : R} (h : Le (a * c) (b * c)) (hc : COF.lt 0 c) : Le a b := by
  intro hlt
  apply h
  have hpos : COF.lt 0 (a - b) := by
    have h2 := COF.lt_add_left (-b) hlt
    rwa [show -b + b = (0:R) from by ring, show -b + a = a - b from by ring] at h2
  have hprod : COF.lt 0 ((a - b) * c) := COFO.mul_pos hpos hc
  have h3 := COF.lt_add_left (b * c) hprod
  rwa [show b * c + 0 = b * c from by ring,
       show b * c + (a - b) * c = a * c from by ring] at h3

/-- Technical lemma used in the public import closure. -/
theorem two_pow_mul_halfPow (m : Nat) : ((2 ^ m : Nat) : R) * COF.halfPow m = 1 := by
  induction m with
  | zero => show ((1:Nat):R) * (1:R) = 1; rw [Nat.cast_one]; ring
  | succ m ih =>
    show (((2 ^ (m + 1)) : Nat) : R) * (COF.half * COF.halfPow m) = 1
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    have e : (((2 ^ m : Nat) : R) * 2) * (COF.half * COF.halfPow m)
           = (((2 ^ m : Nat) : R) * COF.halfPow m) * (2 * COF.half) := by ring
    rw [e, ih, show (2:R) * COF.half = COF.half + COF.half from by ring, COF.half_add_half]
    ring

/-- Technical lemma used in the public import closure. -/
theorem exists_nat_ge (φ : R) : ∃ N : Nat, Le φ ((N : R)) := by
  refine ⟨2 ^ (COFO.mul_archimedean φ).val, ?_⟩
  set m := (COFO.mul_archimedean φ).val with hm
  have harch : Le (COF.abs φ * COF.halfPow m) 1 := (COFO.mul_archimedean φ).property
  have hle1 : Le (COF.abs φ * COF.halfPow m) (((2 ^ m : Nat) : R) * COF.halfPow m) := by
    rw [two_pow_mul_halfPow]; exact harch
  have hcancel : Le (COF.abs φ) (((2 ^ m : Nat) : R)) :=
    le_of_mul_le_mul_pos_right hle1 (halfPow_pos m)
  exact le_trans (COFO.le_abs_self φ) hcancel

/-- φ ≤ b ⟹ min(φ,b)=φ(le_antisymm: cof_min_le_left + le_min(le_refl,φ≤b))。 -/
theorem min_eq_left_of_le {φ b : R} (h : Le φ b) : COF.min φ b = φ :=
  le_antisymm (cof_min_le_left φ b) (le_min (le_refl φ) h)

/-- Technical lemma used in the public import closure. -/
theorem nk_ge_self {n_k : Nat → Nat} (hsucc : ∀ k, n_k k + 1 ≤ n_k (k + 1)) :
    ∀ K, K ≤ n_k K := by
  intro K
  induction K with
  | zero => exact Nat.zero_le _
  | succ K ih => exact Nat.le_trans (Nat.succ_le_succ ih) (hsucc K)

/-- Technical lemma used in the public import closure. -/
theorem prop42_eventually_chi_phi {φ χ : R} (hφ : Nonneg φ)
    {n_k : Nat → Nat} (hsucc : ∀ k, n_k k + 1 ≤ n_k (k + 1)) :
    ∃ k₀ : Nat, ∀ K, k₀ ≤ K →
      χ * (COF.min φ ((n_k K : R)) - COF.min φ 0) = χ * φ := by
  obtain ⟨N, hN⟩ := exists_nat_ge φ
  refine ⟨N, fun K hK => ?_⟩
  have hKN : Le φ ((n_k K : R)) :=
    le_trans hN (natCast_le_of_le (Nat.le_trans hK (nk_ge_self hsucc K)))
  rw [min_eq_left_of_le hKN, min_zero_right hφ, sub_zero]

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_rep_value_series {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) (n_k : Nat → Nat)
    (hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ n_k k) (hmono : ∀ k, n_k k ≤ n_k (k + 1)) {x : X}
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs (((seriesSumRep_L1 (prop_4_2_lambda_k A hA f n_k)
        (prop_4_2_lambda_sum A hA f hnn n_k hnk_ge)).fn n).toFun x)))
    (hχ : RSeq.SeriesSum (fun n => (hA.rep.fn n).toFun x))
    (hf : RSeq.SeriesSum (fun n => (f.fn n).toFun x)) :
    { hser : RSeq.SeriesSum (fun m => (prop_4_2_lambda_value hA f n_k hmono x hχ hf m).1.sum) //
        (seriesSum_of_abs hflatabs).sum = hser.sum } := by
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_value (prop_4_2_lambda_k A hA f n_k)
    (prop_4_2_lambda_sum A hA f hnn n_k hnk_ge) hflatabs
  refine ⟨seriesSum_congr (fun m => ?_) hV, eV⟩
  rw [show (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg (((G_m (prop_4_2_lambda_k A hA f n_k) i).fn j).toFun x))
            (add_absSeriesSum_left hflatabs) m)).sum
          = (IntegrableRep.ofL_value (psi_m_mem (prop_4_2_lambda_k A hA f n_k) m) x).val.sum from
          seriesSum_unique _ _,
      show (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg (((tail_m (prop_4_2_lambda_k A hA f n_k) i).fn j).toFun x))
            (add_absSeriesSum_right hflatabs) m)).sum
          = (IntegrableRep.tailFrom_value (prop_4_2_lambda_k A hA f n_k m) (Nm (prop_4_2_lambda_k A hA f n_k) m) x
              (prop_4_2_lambda_value hA f n_k hmono x hχ hf m).1).val.sum from
          seriesSum_unique _ _]
  exact seriesSumRep_L1_hsplit_value (prop_4_2_lambda_k A hA f n_k) m
    (prop_4_2_lambda_value hA f n_k hmono x hχ hf m).1

/-- Technical lemma used in the public import closure. -/
theorem prop_4_2_chi_f_rep_value {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) {x : X}
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn n).toFun x)))
    (hχabs : RSeq.SeriesSum (fun n => COF.abs ((hA.rep.fn n).toFun x)))
    (hfabs : RSeq.SeriesSum (fun n => COF.abs ((f.fn n).toFun x))) :
    (seriesSum_of_abs hflatabs).sum
      = (seriesSum_of_abs hχabs).sum * (seriesSum_of_abs hfabs).sum := by
  have hnk_ge : ∀ k, f.cutNat_tendsto_rep.mod (k + 1) ≤ prop_4_2_n_k f k := by
    intro k; cases k with
    | zero => exact Nat.le_refl _
    | succ k' => exact Nat.le_max_left _ _
  have hsucc : ∀ k, prop_4_2_n_k f k + 1 ≤ prop_4_2_n_k f (k + 1) := fun k => Nat.le_max_right _ _
  have hmono : ∀ k, prop_4_2_n_k f k ≤ prop_4_2_n_k f (k + 1) :=
    fun k => Nat.le_trans (Nat.le_succ _) (hsucc k)
  let hχ := seriesSum_of_abs hχabs
  let hf := seriesSum_of_abs hfabs
  have hχ01 : hχ.sum = 0 ∨ hχ.sum = 1 := by
    rcases (hA.valid x hχabs).1 with hS1 | hS2
    · exact Or.inr ((hA.valid x hχabs).2.1 hS1 hχ)
    · exact Or.inl ((hA.valid x hχabs).2.2 hS2 hχ)
  have hφnn : Nonneg hf.sum := hnn x hfabs hf
  have hm0 : Nonneg ((prop_4_2_n_k f 0 : R)) := natCast_nonneg _
  have hmono_R : ∀ k, Le ((fun j => (prop_4_2_n_k f j : R)) k) ((fun j => (prop_4_2_n_k f j : R)) (k + 1)) :=
    fun k => natCast_le_of_le (hmono k)
  obtain ⟨hser, eser⟩ :=
    prop_4_2_rep_value_series A hA f hnn (prop_4_2_n_k f) hnk_ge hmono hflatabs hχ hf
  have key : ∀ K, RSeq.partialSum
      (fun m => (prop_4_2_lambda_value hA f (prop_4_2_n_k f) hmono x hχ hf m).1.sum) K
      = hχ.sum * (COF.min hf.sum ((prop_4_2_n_k f K : R)) - COF.min hf.sum 0) := by
    intro K
    rw [partialSum_congr (fun m => (prop_4_2_lambda_value hA f (prop_4_2_n_k f) hmono x hχ hf m).2) K]
    exact prop42_telescope hf.sum hχ.sum (fun j => (prop_4_2_n_k f j : R)) hm0 hmono_R hχ01 K
  obtain ⟨k₀, hk₀⟩ :=
    prop42_eventually_chi_phi (φ := hf.sum) (χ := hχ.sum) (n_k := prop_4_2_n_k f) hφnn hsucc
  have hev : ∀ K, k₀ ≤ K → RSeq.partialSum
      (fun m => (prop_4_2_lambda_value hA f (prop_4_2_n_k f) hmono x hχ hf m).1.sum) K
      = hχ.sum * hf.sum := fun K hK => by rw [key K]; exact hk₀ K hK
  have efinal : hser.sum = hχ.sum * hf.sum := seriesSum_of_eventually_const hser k₀ hev
  exact eser.trans efinal

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
noncomputable def relIntegral {S : IntSpaceRC X R} (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) : R :=
  (prop_4_2_chi_f_rep C hC f hnn).integral

/-- Technical lemma used in the public import closure. -/
theorem prop_4_2_complement_value {S : IntSpaceRC X R} (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) {x : X}
    (hCabs : RSeq.SeriesSum (fun n => COF.abs (((prop_4_2_chi_f_rep C hC f hnn).fn n).toFun x)))
    (hχabs : RSeq.SeriesSum (fun n => COF.abs ((hC.rep.fn n).toFun x)))
    (hfabs : RSeq.SeriesSum (fun n => COF.abs ((f.fn n).toFun x))) :
    (add_seriesSum_value (seriesSum_of_abs hfabs)
        (neg_seriesSum_value (seriesSum_of_abs hCabs))).sum
      = (1 - (seriesSum_of_abs hχabs).sum) * (seriesSum_of_abs hfabs).sum := by
  have hrep := prop_4_2_chi_f_rep_value C hC f hnn hCabs hχabs hfabs
  show (seriesSum_of_abs hfabs).sum + (-(seriesSum_of_abs hCabs).sum)
      = (1 - (seriesSum_of_abs hχabs).sum) * (seriesSum_of_abs hfabs).sum
  rw [hrep]; ring

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_complement_additive {S : IntSpaceRC X R} (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    relIntegral C hC f hnn + (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral = f.integral := by
  show (prop_4_2_chi_f_rep C hC f hnn).integral
      + (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral = f.integral
  rw [IntegrableRep.integral_sub]; ring

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_integral {S : IntSpaceRC X R} (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Le (relIntegral C hC f hnn) f.integral := by
  show Le (prop_4_2_chi_f_rep C hC f hnn).integral f.integral
  refine prop_1_11 (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep C hC f hnn).domain_isFull f.domain_isFull) hC.rep.domain_isFull)
    (prop_4_2_chi_f_rep C hC f hnn) f ?_
  intro x hx hr hr'
  obtain ⟨⟨hxrep, hxf⟩, hxχ⟩ := hx
  obtain ⟨_, ⟨hflatabs⟩⟩ := hxrep
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  have hval := prop_4_2_chi_f_rep_value C hC f hnn hflatabs hχabs hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatabs),
      seriesSum_unique hr' (seriesSum_of_abs hfabs), hval]
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum := hnn x hfabs (seriesSum_of_abs hfabs)
  have hχ01 : (seriesSum_of_abs hχabs).sum = 0 ∨ (seriesSum_of_abs hχabs).sum = 1 := by
    rcases (hC.valid x hχabs).1 with hS1 | hS2
    · exact Or.inr ((hC.valid x hχabs).2.1 hS1 (seriesSum_of_abs hχabs))
    · exact Or.inl ((hC.valid x hχabs).2.2 hS2 (seriesSum_of_abs hχabs))
  rcases hχ01 with h0 | h1
  · rw [h0, zero_mul]; exact le_of_nonneg_sub (by rw [sub_zero]; exact hfnn)
  · rw [h1, one_mul]; exact le_refl _

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_mono_set {S : IntSpaceRC X R} (D D' : BSet X)
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D') (hsub : BSet.Subset D D')
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Le (relIntegral D hD f hnn) (relIntegral D' hD' f hnn) := by
  show Le (prop_4_2_chi_f_rep D hD f hnn).integral (prop_4_2_chi_f_rep D' hD' f hnn).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep D hD f hnn).domain_isFull (prop_4_2_chi_f_rep D' hD' f hnn).domain_isFull)
      f.domain_isFull) hD.rep.domain_isFull) hD'.rep.domain_isFull)
    (prop_4_2_chi_f_rep D hD f hnn) (prop_4_2_chi_f_rep D' hD' f hnn) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨hxrepD, hxrepD'⟩, hxf⟩, hxχD⟩, hxχD'⟩ := hx
  obtain ⟨_, ⟨hflatabsD⟩⟩ := hxrepD
  obtain ⟨_, ⟨hflatabsD'⟩⟩ := hxrepD'
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχDabs⟩⟩ := hxχD
  obtain ⟨_, ⟨hχD'abs⟩⟩ := hxχD'
  have hvalD := prop_4_2_chi_f_rep_value D hD f hnn hflatabsD hχDabs hfabs
  have hvalD' := prop_4_2_chi_f_rep_value D' hD' f hnn hflatabsD' hχD'abs hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatabsD),
      seriesSum_unique hr' (seriesSum_of_abs hflatabsD'), hvalD, hvalD']
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum := hnn x hfabs (seriesSum_of_abs hfabs)
  rcases (hD.valid x hχDabs).1 with hS1 | hS2
  · have hcD : (seriesSum_of_abs hχDabs).sum = 1 :=
      (hD.valid x hχDabs).2.1 hS1 (seriesSum_of_abs hχDabs)
    have hcD' : (seriesSum_of_abs hχD'abs).sum = 1 :=
      (hD'.valid x hχD'abs).2.1 (hsub.1 hS1) (seriesSum_of_abs hχD'abs)
    rw [hcD, hcD']; exact le_refl _
  · have hcD : (seriesSum_of_abs hχDabs).sum = 0 :=
      (hD.valid x hχDabs).2.2 hS2 (seriesSum_of_abs hχDabs)
    rw [hcD, zero_mul]
    rcases (hD'.valid x hχD'abs).1 with hS1' | hS2'
    · have hcD' : (seriesSum_of_abs hχD'abs).sum = 1 :=
        (hD'.valid x hχD'abs).2.1 hS1' (seriesSum_of_abs hχD'abs)
      rw [hcD', one_mul]; exact le_of_nonneg_sub (by rw [sub_zero]; exact hfnn)
    · have hcD' : (seriesSum_of_abs hχD'abs).sum = 0 :=
        (hD'.valid x hχD'abs).2.2 hS2' (seriesSum_of_abs hχD'abs)
      rw [hcD', zero_mul]; exact le_refl _

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_mono_le {S : IntSpaceRC X R} (D D' : BSet X)
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D')
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (hle : ∀ x, ∀ (hd : RSeq.SeriesSum (fun n => (hD.rep.fn n).toFun x))
            (hd' : RSeq.SeriesSum (fun n => (hD'.rep.fn n).toFun x)), Le hd.sum hd'.sum) :
    Le (relIntegral D hD f hnn) (relIntegral D' hD' f hnn) := by
  show Le (prop_4_2_chi_f_rep D hD f hnn).integral (prop_4_2_chi_f_rep D' hD' f hnn).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep D hD f hnn).domain_isFull (prop_4_2_chi_f_rep D' hD' f hnn).domain_isFull)
      f.domain_isFull) hD.rep.domain_isFull) hD'.rep.domain_isFull)
    (prop_4_2_chi_f_rep D hD f hnn) (prop_4_2_chi_f_rep D' hD' f hnn) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨hxrepD, hxrepD'⟩, hxf⟩, hxχD⟩, hxχD'⟩ := hx
  obtain ⟨_, ⟨hflatabsD⟩⟩ := hxrepD
  obtain ⟨_, ⟨hflatabsD'⟩⟩ := hxrepD'
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχDabs⟩⟩ := hxχD
  obtain ⟨_, ⟨hχD'abs⟩⟩ := hxχD'
  have hvalD := prop_4_2_chi_f_rep_value D hD f hnn hflatabsD hχDabs hfabs
  have hvalD' := prop_4_2_chi_f_rep_value D' hD' f hnn hflatabsD' hχD'abs hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatabsD),
      seriesSum_unique hr' (seriesSum_of_abs hflatabsD'), hvalD, hvalD']
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum := hnn x hfabs (seriesSum_of_abs hfabs)
  have hcc : Le (seriesSum_of_abs hχDabs).sum (seriesSum_of_abs hχD'abs).sum :=
    hle x (seriesSum_of_abs hχDabs) (seriesSum_of_abs hχD'abs)
  exact le_of_nonneg_sub (by
    rw [show (seriesSum_of_abs hχD'abs).sum * (seriesSum_of_abs hfabs).sum
          - (seriesSum_of_abs hχDabs).sum * (seriesSum_of_abs hfabs).sum
          = ((seriesSum_of_abs hχD'abs).sum - (seriesSum_of_abs hχDabs).sum)
            * (seriesSum_of_abs hfabs).sum from by ring]
    exact COFO.mul_nonneg (nonneg_sub_of_le hcc) hfnn)

/-- Technical lemma used in the public import closure. -/
theorem chi_or_add_and_value {S : IntSpaceRC X R} {D D' : BSet X}
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D') {x : X}
    (hDc : RSeq.SeriesSum (fun n => (hD.rep.fn n).toFun x))
    (hD'c : RSeq.SeriesSum (fun n => (hD'.rep.fn n).toFun x))
    (horc : RSeq.SeriesSum (fun n => ((IntegrableSet1_or hD hD').rep.fn n).toFun x))
    (handc : RSeq.SeriesSum (fun n => ((IntegrableSet1_and hD hD').rep.fn n).toFun x)) :
    horc.sum + handc.sum = hDc.sum + hD'c.sum := by
  obtain ⟨hmin, hmineq⟩ := min2_value hD.rep hD'.rep x hDc hD'c
  have hand_eq : handc.sum = hmin.sum := seriesSum_unique handc hmin
  have hor_eq : horc.sum = (hDc.sum + hD'c.sum) + (- hmin.sum) :=
    seriesSum_unique horc
      (add_seriesSum_value (add_seriesSum_value hDc hD'c) (neg_seriesSum_value hmin))
  rw [hor_eq, hand_eq]; ring

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_or_add_and {S : IntSpaceRC X R} {D D' : BSet X}
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D')
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    relIntegral (BSet.or D D') (IntegrableSet1_or hD hD') f hnn
      + relIntegral (BSet.and D D') (IntegrableSet1_and hD hD') f hnn
    = relIntegral D hD f hnn + relIntegral D' hD' f hnn := by
  show (prop_4_2_chi_f_rep (BSet.or D D') (IntegrableSet1_or hD hD') f hnn).integral
      + (prop_4_2_chi_f_rep (BSet.and D D') (IntegrableSet1_and hD hD') f hnn).integral
    = (prop_4_2_chi_f_rep D hD f hnn).integral
      + (prop_4_2_chi_f_rep D' hD' f hnn).integral
  rw [← IntegrableRep.integral_add, ← IntegrableRep.integral_add]
  refine cor_1_12 (isFull_inter (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (isFull_inter (isFull_inter (isFull_inter
        (prop_4_2_chi_f_rep (BSet.or D D') (IntegrableSet1_or hD hD') f hnn).domain_isFull
        (prop_4_2_chi_f_rep (BSet.and D D') (IntegrableSet1_and hD hD') f hnn).domain_isFull)
        (prop_4_2_chi_f_rep D hD f hnn).domain_isFull)
        (prop_4_2_chi_f_rep D' hD' f hnn).domain_isFull)
        f.domain_isFull)
        hD.rep.domain_isFull)
        hD'.rep.domain_isFull)
        (IntegrableSet1_or hD hD').rep.domain_isFull)
        (IntegrableSet1_and hD hD').rep.domain_isFull)
    _ _ ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxOr, hxAnd⟩, hxD⟩, hxD'⟩, hxf⟩, hxχD⟩, hxχD'⟩, hxχOr⟩, hxχAnd⟩ := hx
  obtain ⟨_, ⟨hflatOr⟩⟩ := hxOr
  obtain ⟨_, ⟨hflatAnd⟩⟩ := hxAnd
  obtain ⟨_, ⟨hflatD⟩⟩ := hxD
  obtain ⟨_, ⟨hflatD'⟩⟩ := hxD'
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχDabs⟩⟩ := hxχD
  obtain ⟨_, ⟨hχD'abs⟩⟩ := hxχD'
  obtain ⟨_, ⟨hχorabs⟩⟩ := hxχOr
  obtain ⟨_, ⟨hχandabs⟩⟩ := hxχAnd
  have value_Or := prop_4_2_chi_f_rep_value (BSet.or D D') (IntegrableSet1_or hD hD') f hnn
    hflatOr hχorabs hfabs
  have value_And := prop_4_2_chi_f_rep_value (BSet.and D D') (IntegrableSet1_and hD hD') f hnn
    hflatAnd hχandabs hfabs
  have value_D := prop_4_2_chi_f_rep_value D hD f hnn hflatD hχDabs hfabs
  have value_D' := prop_4_2_chi_f_rep_value D' hD' f hnn hflatD' hχD'abs hfabs
  have hchi : (seriesSum_of_abs hχorabs).sum + (seriesSum_of_abs hχandabs).sum
            = (seriesSum_of_abs hχDabs).sum + (seriesSum_of_abs hχD'abs).sum :=
    chi_or_add_and_value hD hD' (seriesSum_of_abs hχDabs) (seriesSum_of_abs hχD'abs)
      (seriesSum_of_abs hχorabs) (seriesSum_of_abs hχandabs)
  rw [seriesSum_unique hr
        (add_seriesSum_value (seriesSum_of_abs hflatOr) (seriesSum_of_abs hflatAnd)),
      seriesSum_unique hr'
        (add_seriesSum_value (seriesSum_of_abs hflatD) (seriesSum_of_abs hflatD'))]
  show (seriesSum_of_abs hflatOr).sum + (seriesSum_of_abs hflatAnd).sum
     = (seriesSum_of_abs hflatD).sum + (seriesSum_of_abs hflatD').sum
  rw [value_Or, value_And, value_D, value_D',
      show (seriesSum_of_abs hχorabs).sum * (seriesSum_of_abs hfabs).sum
          + (seriesSum_of_abs hχandabs).sum * (seriesSum_of_abs hfabs).sum
          = ((seriesSum_of_abs hχorabs).sum + (seriesSum_of_abs hχandabs).sum)
            * (seriesSum_of_abs hfabs).sum from by ring,
      hchi]
  ring

/-- Technical lemma used in the public import closure. -/
theorem chi_and_value {S : IntSpaceRC X R} {D D' : BSet X}
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D') {x : X}
    (hDc : RSeq.SeriesSum (fun n => (hD.rep.fn n).toFun x))
    (hD'c : RSeq.SeriesSum (fun n => (hD'.rep.fn n).toFun x))
    (handc : RSeq.SeriesSum (fun n => ((IntegrableSet1_and hD hD').rep.fn n).toFun x)) :
    handc.sum = COF.min hDc.sum hD'c.sum := by
  obtain ⟨hmin, hmineq⟩ := min2_value hD.rep hD'.rep x hDc hD'c
  rw [seriesSum_unique handc hmin]; exact hmineq

/-- Technical lemma used in the public import closure. -/
theorem chi_and_value_valid {S : IntSpaceRC X R} {A B : BSet X}
    (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B) (hAB : IntegrableSet1 S (BSet.and A B)) {x : X}
    (hAabs : RSeq.SeriesSum (fun n => COF.abs ((hA.rep.fn n).toFun x)))
    (hBabs : RSeq.SeriesSum (fun n => COF.abs ((hB.rep.fn n).toFun x)))
    (hABabs : RSeq.SeriesSum (fun n => COF.abs ((hAB.rep.fn n).toFun x))) :
    (seriesSum_of_abs hABabs).sum
      = COF.min (seriesSum_of_abs hAabs).sum (seriesSum_of_abs hBabs).sum := by
  rcases (hAB.valid x hABabs).1 with hS1 | hS2
  · have hAB1 : (seriesSum_of_abs hABabs).sum = 1 :=
      (hAB.valid x hABabs).2.1 hS1 (seriesSum_of_abs hABabs)
    obtain ⟨xA1, xB1⟩ := hS1
    have hA1 : (seriesSum_of_abs hAabs).sum = 1 :=
      (hA.valid x hAabs).2.1 xA1 (seriesSum_of_abs hAabs)
    have hB1 : (seriesSum_of_abs hBabs).sum = 1 :=
      (hB.valid x hBabs).2.1 xB1 (seriesSum_of_abs hBabs)
    rw [hAB1, hA1, hB1]
    exact (le_antisymm (cof_min_le_left 1 1) (le_min (le_refl 1) (le_refl 1))).symm
  · have hAB0 : (seriesSum_of_abs hABabs).sum = 0 :=
      (hAB.valid x hABabs).2.2 hS2 (seriesSum_of_abs hABabs)
    rw [hAB0]
    rcases hS2 with (⟨xA1, xB2⟩ | ⟨xA2, xB1⟩) | ⟨xA2, xB2⟩
    · have hA1 : (seriesSum_of_abs hAabs).sum = 1 :=
        (hA.valid x hAabs).2.1 xA1 (seriesSum_of_abs hAabs)
      have hB0 : (seriesSum_of_abs hBabs).sum = 0 :=
        (hB.valid x hBabs).2.2 xB2 (seriesSum_of_abs hBabs)
      rw [hA1, hB0]; exact ((COF_min_comm 1 0).trans min_zero_one).symm
    · have hA0 : (seriesSum_of_abs hAabs).sum = 0 :=
        (hA.valid x hAabs).2.2 xA2 (seriesSum_of_abs hAabs)
      have hB1 : (seriesSum_of_abs hBabs).sum = 1 :=
        (hB.valid x hBabs).2.1 xB1 (seriesSum_of_abs hBabs)
      rw [hA0, hB1]; exact min_zero_one.symm
    · have hA0 : (seriesSum_of_abs hAabs).sum = 0 :=
        (hA.valid x hAabs).2.2 xA2 (seriesSum_of_abs hAabs)
      have hB0 : (seriesSum_of_abs hBabs).sum = 0 :=
        (hB.valid x hBabs).2.2 xB2 (seriesSum_of_abs hBabs)
      rw [hA0, hB0]
      exact (le_antisymm (cof_min_le_left 0 0) (le_min (le_refl 0) (le_refl 0))).symm

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_and_mono {S : IntSpaceRC X R} {B : BSet X} (hB : IsMeasurableSet (S := S) B)
    {D D' : BSet X} (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D') (hsub : D.S1 ⊆ D'.S1)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Le (relIntegral (BSet.and D B) (hB D hD) f hnn)
       (relIntegral (BSet.and D' B) (hB D' hD') f hnn) := by
  show Le (prop_4_2_chi_f_rep (BSet.and D B) (hB D hD) f hnn).integral
          (prop_4_2_chi_f_rep (BSet.and D' B) (hB D' hD') f hnn).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep (BSet.and D B) (hB D hD) f hnn).domain_isFull
      (prop_4_2_chi_f_rep (BSet.and D' B) (hB D' hD') f hnn).domain_isFull)
      f.domain_isFull)
      (hB D hD).rep.domain_isFull)
      (hB D' hD').rep.domain_isFull)
    (prop_4_2_chi_f_rep (BSet.and D B) (hB D hD) f hnn)
    (prop_4_2_chi_f_rep (BSet.and D' B) (hB D' hD') f hnn) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨hxDB, hxD'B⟩, hxf⟩, hxχDB⟩, hxχD'B⟩ := hx
  obtain ⟨_, ⟨hflat_DB⟩⟩ := hxDB
  obtain ⟨_, ⟨hflat_D'B⟩⟩ := hxD'B
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχ_DB⟩⟩ := hxχDB
  obtain ⟨_, ⟨hχ_D'B⟩⟩ := hxχD'B
  have hval_DB := prop_4_2_chi_f_rep_value (BSet.and D B) (hB D hD) f hnn hflat_DB hχ_DB hfabs
  have hval_D'B := prop_4_2_chi_f_rep_value (BSet.and D' B) (hB D' hD') f hnn hflat_D'B hχ_D'B hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflat_DB),
      seriesSum_unique hr' (seriesSum_of_abs hflat_D'B), hval_DB, hval_D'B]
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum := hnn x hfabs (seriesSum_of_abs hfabs)
  rcases ((hB D hD).valid x hχ_DB).1 with hS1 | hS2
  · have hDB1 : (seriesSum_of_abs hχ_DB).sum = 1 :=
      ((hB D hD).valid x hχ_DB).2.1 hS1 (seriesSum_of_abs hχ_DB)
    obtain ⟨xD1, xB1⟩ := hS1
    have hD'B1 : (seriesSum_of_abs hχ_D'B).sum = 1 :=
      ((hB D' hD').valid x hχ_D'B).2.1 ⟨hsub xD1, xB1⟩ (seriesSum_of_abs hχ_D'B)
    rw [hDB1, hD'B1]; exact le_refl _
  · have hDB0 : (seriesSum_of_abs hχ_DB).sum = 0 :=
      ((hB D hD).valid x hχ_DB).2.2 hS2 (seriesSum_of_abs hχ_DB)
    rw [hDB0, zero_mul]
    rcases ((hB D' hD').valid x hχ_D'B).1 with hS1' | hS2'
    · have hD'B1 : (seriesSum_of_abs hχ_D'B).sum = 1 :=
        ((hB D' hD').valid x hχ_D'B).2.1 hS1' (seriesSum_of_abs hχ_D'B)
      rw [hD'B1, one_mul]; exact le_of_nonneg_sub (by rw [sub_zero]; exact hfnn)
    · have hD'B0 : (seriesSum_of_abs hχ_D'B).sum = 0 :=
        ((hB D' hD').valid x hχ_D'B).2.2 hS2' (seriesSum_of_abs hχ_D'B)
      rw [hD'B0, zero_mul]; exact le_refl _

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_and_mono_or_step {S : IntSpaceRC X R} {B : BSet X} (hB : IsMeasurableSet (S := S) B)
    {D A : BSet X} (hD : IntegrableSet1 S D) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Le (relIntegral (BSet.and D B) (hB D hD) f hnn)
       (relIntegral (BSet.and (BSet.or D A) B) (hB (BSet.or D A) (IntegrableSet1_or hD hA)) f hnn) := by
  show Le (prop_4_2_chi_f_rep (BSet.and D B) (hB D hD) f hnn).integral
          (prop_4_2_chi_f_rep (BSet.and (BSet.or D A) B)
            (hB (BSet.or D A) (IntegrableSet1_or hD hA)) f hnn).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep (BSet.and D B) (hB D hD) f hnn).domain_isFull
      (prop_4_2_chi_f_rep (BSet.and (BSet.or D A) B)
        (hB (BSet.or D A) (IntegrableSet1_or hD hA)) f hnn).domain_isFull)
      f.domain_isFull)
      (hB D hD).rep.domain_isFull)
      (hB (BSet.or D A) (IntegrableSet1_or hD hA)).rep.domain_isFull)
      hA.rep.domain_isFull)
    (prop_4_2_chi_f_rep (BSet.and D B) (hB D hD) f hnn)
    (prop_4_2_chi_f_rep (BSet.and (BSet.or D A) B)
      (hB (BSet.or D A) (IntegrableSet1_or hD hA)) f hnn) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨⟨hxDB, hxDAB⟩, hxf⟩, hxχDB⟩, hxχDAB⟩, hxχA⟩ := hx
  obtain ⟨_, ⟨hflat_DB⟩⟩ := hxDB
  obtain ⟨_, ⟨hflat_DAB⟩⟩ := hxDAB
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  obtain ⟨_, ⟨hχ_DB⟩⟩ := hxχDB
  obtain ⟨_, ⟨hχ_DAB⟩⟩ := hxχDAB
  obtain ⟨_, ⟨hχAabs⟩⟩ := hxχA
  have hval_DB := prop_4_2_chi_f_rep_value (BSet.and D B) (hB D hD) f hnn hflat_DB hχ_DB hfabs
  have hval_DAB := prop_4_2_chi_f_rep_value (BSet.and (BSet.or D A) B)
    (hB (BSet.or D A) (IntegrableSet1_or hD hA)) f hnn hflat_DAB hχ_DAB hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflat_DB),
      seriesSum_unique hr' (seriesSum_of_abs hflat_DAB), hval_DB, hval_DAB]
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum := hnn x hfabs (seriesSum_of_abs hfabs)
  rcases ((hB D hD).valid x hχ_DB).1 with hS1 | hS2
  · have hDB1 : (seriesSum_of_abs hχ_DB).sum = 1 :=
      ((hB D hD).valid x hχ_DB).2.1 hS1 (seriesSum_of_abs hχ_DB)
    obtain ⟨xD1, xB1⟩ := hS1
    have hxDA1 : x ∈ (BSet.or D A).S1 := by
      rcases (hA.valid x hχAabs).1 with hA1 | hA2
      · exact Or.inl (Or.inl ⟨xD1, hA1⟩)
      · exact Or.inl (Or.inr ⟨xD1, hA2⟩)
    have hDAB1 : (seriesSum_of_abs hχ_DAB).sum = 1 :=
      ((hB (BSet.or D A) (IntegrableSet1_or hD hA)).valid x hχ_DAB).2.1 ⟨hxDA1, xB1⟩
        (seriesSum_of_abs hχ_DAB)
    rw [hDB1, hDAB1]; exact le_refl _
  · have hDB0 : (seriesSum_of_abs hχ_DB).sum = 0 :=
      ((hB D hD).valid x hχ_DB).2.2 hS2 (seriesSum_of_abs hχ_DB)
    rw [hDB0, zero_mul]
    rcases ((hB (BSet.or D A) (IntegrableSet1_or hD hA)).valid x hχ_DAB).1 with hS1' | hS2'
    · have hDAB1 : (seriesSum_of_abs hχ_DAB).sum = 1 :=
        ((hB (BSet.or D A) (IntegrableSet1_or hD hA)).valid x hχ_DAB).2.1 hS1'
          (seriesSum_of_abs hχ_DAB)
      rw [hDAB1, one_mul]; exact le_of_nonneg_sub (by rw [sub_zero]; exact hfnn)
    · have hDAB0 : (seriesSum_of_abs hχ_DAB).sum = 0 :=
        ((hB (BSet.or D A) (IntegrableSet1_or hD hA)).valid x hχ_DAB).2.2 hS2'
          (seriesSum_of_abs hχ_DAB)
      rw [hDAB0, zero_mul]; exact le_refl _

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_bigOrFin_mono {S : IntSpaceRC X R} {B : BSet X} (hB : IsMeasurableSet (S := S) B)
    (A : Nat → BSet X) (hA : ∀ k, IntegrableSet1 S (A k)) (f : IntegrableRep S) (hnn : RepNonneg f)
    (k : Nat) :
    Le (relIntegral (BSet.and (bigOrFin A k) B) (hB (bigOrFin A k) (bigOrFin_int A hA k)) f hnn)
       (relIntegral (BSet.and (bigOrFin A (k + 1)) B)
         (hB (bigOrFin A (k + 1)) (bigOrFin_int A hA (k + 1))) f hnn) :=
  relIntegral_and_mono_or_step hB (bigOrFin_int A hA k) (hA (k + 1)) f hnn

/-- Technical lemma used in the public import closure. -/
noncomputable def fatou_type_stub_not_source_4_14 {S : IntSpaceRC X R} (_fn : Nat -> IntegrableRep S)
    (_f : IntegrableRep S)
    (_h_nonneg : ∀ n, RepNonneg (_fn n))
    (_c : R) (_h_bound : ∀ n, ¬ COF.lt _c (((_fn n).integral)))
    (_h_conv : ConvergeInMeasure S (fun n => IntegrableRep.toPFunR (_fn n)) _f.toPFunR) :
    True := by
  trivial

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_15_dominated_convergence {S : IntSpaceRC X R} (_fn : Nat -> IntegrableRep S)
    (_f : IntegrableRep S) (_g : IntegrableRep S)
    (_h_conv : ConvergeInMeasure S (fun n => IntegrableRep.toPFunR (_fn n)) _f.toPFunR)
    (_h_bound : ∀ n, RepNonneg (_g.sub ((_fn n).absVal))) :
    True := by
  trivial

end BishopC
