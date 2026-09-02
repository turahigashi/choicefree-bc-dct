import Mathdemo.Internal.BishopSec2_L1
import Mathdemo.Internal.BishopSec3_Profile

namespace BishopC

variable {X R : Type*} [COFOC R]



-- Technical note.
-- Technical note.


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
    (hu : ∀ x ∈ D, ∀ (hudom : u.MemAt x)
      (hx_sum : RSeq.SeriesSum (fun n => u.valueAt x hudom n)),
      Nonneg hx_sum.sum) :
    Le (u.min2 v).normL1 v.normL1 := by
  refine normL1_mono hD (u.min2 v) v ?_
  intro x hx huvDom hvDom huvSum hvSum
  let huDom : u.MemAt x := min2_dom_left huvDom
  obtain ⟨huDom', ⟨huAbs⟩⟩ := hDu hx
  have huSum : RSeq.SeriesSum (fun n => u.valueAt x huDom n) := by
    simpa using seriesSum_of_abs huAbs
  obtain ⟨hmin, hminEq⟩ := min2_value u v x huDom hvDom
    huSum hvSum
  have hpos_u : Nonneg huSum.sum := hu x hx huDom huSum
  rw [seriesSum_unique huvSum hmin, hminEq]
  exact abs_min_le_abs_of_nonneg_left huSum.sum hvSum.sum hpos_u


-- Technical note.
-- Technical note.

theorem repNonneg_sub_cutNatVal {S : IntSpaceRC X R} (f : IntegrableRep S) (n : Nat) :
    RepNonneg (f.sub (prop_4_2_min_f_n f n)) := by
  intro x hdom habs hx
  let hfDom : f.MemAt x := add_dom_left hdom
  let hnegGDom : (prop_4_2_min_f_n f n).neg.MemAt x := add_dom_right hdom
  let hgDom : (prop_4_2_min_f_n f n).MemAt x := neg_dom hnegGDom
  have hf_abs := add_absSeriesSum_left hdom habs
  have hg_abs := neg_absSeriesSum hnegGDom (add_absSeriesSum_right hdom habs)
  have hf := seriesSum_of_abs hf_abs
  have hg := seriesSum_of_abs hg_abs
  have hx_eq : hx.sum = hf.sum - hg.sum := by
    have heq := seriesSum_unique hx
      (add_seriesSum_value hfDom hnegGDom hf (neg_seriesSum_value hgDom hg))
    change hx.sum = hf.sum + -(hg.sum) at heq
    have h2 : hf.sum - hg.sum = hf.sum + -(hg.sum) := sub_eq_add_neg _ _
    rw [h2]
    exact heq
  obtain ⟨hg_signed, hg_signed_eq⟩ := f.cutConstVal_signed_value
    (n : R) (natCast_nonneg n) x hfDom hf
  have hg_eq : hg.sum = hg_signed.sum := seriesSum_unique hg hg_signed
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
  intro x hdom habs hx
  have hvalid := hA.valid x hdom habs
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
  let hsmulDom : (r.smul c).MemAt x :=
    IntegrableRep.smul_memAt (a := c) hdom
  refine ⟨hsmulDom, ?_⟩
  have hcabs := seriesSum_smul (COF.abs c) habs
  have h_eq : ∀ n, COF.abs c * COF.abs (r.valueAt x hdom n) =
      COF.abs ((r.smul c).valueAt x hsmulDom n) := by
    intro n
    change COF.abs c * COF.abs (r.valueAt x hdom n) =
      COF.abs (c * r.valueAt x hdom n)
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
  have hu_custom : ∀ x ∈ D, ∀ (huDom : u.MemAt x)
      (hx_sum : RSeq.SeriesSum (fun n => u.valueAt x huDom n)),
      Nonneg hx_sum.sum := by
    intro x hx huDom hx_sum
    have hx_rep_dom : x ∈ hA.rep.domain := hx.1
    obtain ⟨hrepDom, ⟨habs_rep⟩⟩ := hx_rep_dom
    have hx_rep := seriesSum_of_abs habs_rep
    have hpos_rep := IntegrableSet1_repNonneg hA x hrepDom habs_rep hx_rep
    have heq : hx_sum.sum = c * hx_rep.sum := by
      let h_smul_congr := smul_seriesSum_value c hrepDom hx_rep
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




















/- Technical proof note. -/

/-- Technical lemma used in the public import closure. -/
def IsMeasurableSet {S : IntSpaceRC X R} (B : BSet X) : Type _ :=
  ∀ (A : BSet X), IntegrableSet1 S A → IntegrableSet1 S (BSet.and A B)

/-- Technical lemma used in the public import closure. -/
noncomputable def isMeasurableSet_of_integrable {S : IntSpaceRC X R} {B : BSet X}
    (hB : IntegrableSet1 S B) : IsMeasurableSet (S := S) B :=
  fun A hA => IntegrableSet1_and hA hB



-- Technical note.
-- Technical note.
-- Technical note.
-- Technical note.







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
theorem prop_4_2_term_memAt {S : IntSpaceRC X R} {A : BSet X}
    (hA : IntegrableSet1 S A) (f : IntegrableRep S)
    (c a : R) (ha : Nonneg a) {x : X}
    (hχDom : hA.rep.MemAt x) (hfDom : f.MemAt x) :
    ((hA.rep.smul c).min2 (f.sub (f.cutConstVal a ha))).MemAt x :=
  IntegrableRep.min2_memAt
    (IntegrableRep.smul_memAt hχDom)
    (IntegrableRep.add_memAt hfDom
      (IntegrableRep.neg_memAt (f.mem_cutConstVal_dom a ha hfDom)))

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_term_value {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (c a : R) (ha : ¬ COF.lt a 0) (x : X)
    (hχDom : hA.rep.MemAt x) (hfDom : f.MemAt x)
    (hχ : RSeq.SeriesSum (fun n => hA.rep.valueAt x hχDom n))
    (hf : RSeq.SeriesSum (fun n => f.valueAt x hfDom n)) :
    { hv : RSeq.SeriesSum
            (fun n => ((hA.rep.smul c).min2
              (f.sub (f.cutConstVal a ha))).valueAt x
                (prop_4_2_term_memAt hA f c a ha hχDom hfDom) n) //
        hv.sum = COF.min (c * hχ.sum) (hf.sum - COF.min hf.sum a) } := by
  let hgDom := f.mem_cutConstVal_dom a ha hfDom
  obtain ⟨hg, hgeq⟩ := f.cutConstVal_signed_value a ha x hfDom hf
  let hχSmulDom : (hA.rep.smul c).MemAt x :=
    IntegrableRep.smul_memAt (a := c) hχDom
  let hnegGDom := IntegrableRep.neg_memAt hgDom
  let hsubDom := IntegrableRep.add_memAt hfDom hnegGDom
  obtain ⟨hm, hmeq⟩ :=
    min2_value (hA.rep.smul c) (f.sub (f.cutConstVal a ha)) x
      hχSmulDom hsubDom
      (smul_seriesSum_value c hχDom hχ)
      (add_seriesSum_value hfDom hnegGDom hf
        (neg_seriesSum_value hgDom hg))
  refine ⟨hm, ?_⟩
  rw [hmeq]
  congr 1
  show hf.sum + (-(hg.sum)) = hf.sum - COF.min hf.sum a
  rw [hgeq]; ring

/-- Technical lemma used in the public import closure. -/
theorem prop_4_2_lambda_memAt {S : IntSpaceRC X R} {A : BSet X}
    (hA : IntegrableSet1 S A) (f : IntegrableRep S)
    (n_k : Nat → Nat) (k : Nat) {x : X}
    (hχDom : hA.rep.MemAt x) (hfDom : f.MemAt x) :
    (prop_4_2_lambda_k A hA f n_k k).MemAt x := by
  cases k with
  | zero =>
      simpa [prop_4_2_lambda_k, prop_4_2_min_f_n,
        IntegrableRep.cutNatVal] using
        (prop_4_2_term_memAt hA f (n_k 0 : R) (0 : R)
          (nonneg_zero : Nonneg (0 : R)) hχDom hfDom)
  | succ k =>
      simpa [prop_4_2_lambda_k, prop_4_2_min_f_n,
        IntegrableRep.cutNatVal] using
        (prop_4_2_term_memAt hA f
          ((n_k (k + 1) - n_k k : Nat) : R) (n_k k : R)
          (natCast_nonneg (n_k k)) hχDom hfDom)

/-- Technical lemma used in the public import closure. -/
noncomputable def prop_4_2_lambda_value {S : IntSpaceRC X R} {A : BSet X} (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (n_k : Nat → Nat) (hmono : ∀ k, n_k k ≤ n_k (k + 1)) (x : X)
    (hχDom : hA.rep.MemAt x) (hfDom : f.MemAt x)
    (hχ : RSeq.SeriesSum (fun n => hA.rep.valueAt x hχDom n))
    (hf : RSeq.SeriesSum (fun n => f.valueAt x hfDom n)) (k : Nat) :
    { hv : RSeq.SeriesSum (fun n =>
        (prop_4_2_lambda_k A hA f n_k k).valueAt x
          (prop_4_2_lambda_memAt hA f n_k k hχDom hfDom) n) //
        hv.sum = COF.min (((n_k k : R) - prevSeq (fun j => (n_k j : R)) k) * hχ.sum)
                          (hf.sum - COF.min hf.sum (prevSeq (fun j => (n_k j : R)) k)) } := by
  cases k with
  | zero =>
    obtain ⟨hv, hveq⟩ :=
      prop_4_2_term_value hA f ((n_k 0 : R)) ((0 : Nat) : R)
        (natCast_nonneg (R := R) 0) x hχDom hfDom hχ hf
    refine ⟨hv, ?_⟩
    rw [hveq]
    show COF.min ((n_k 0 : R) * hχ.sum) (hf.sum - COF.min hf.sum ((0:Nat):R))
        = COF.min (((n_k 0 : R) - (0:R)) * hχ.sum) (hf.sum - COF.min hf.sum (0:R))
    rw [Nat.cast_zero, sub_zero]
  | succ k =>
    obtain ⟨hv, hveq⟩ :=
      prop_4_2_term_value hA f (((n_k (k + 1) - n_k k : Nat) : R)) ((n_k k : R))
        (natCast_nonneg (n_k k)) x hχDom hfDom hχ hf
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
    (hflatDom : (seriesSumRep_L1 (prop_4_2_lambda_k A hA f n_k)
      (prop_4_2_lambda_sum A hA f hnn n_k hnk_ge)).MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((seriesSumRep_L1 (prop_4_2_lambda_k A hA f n_k)
        (prop_4_2_lambda_sum A hA f hnn n_k hnk_ge)).valueAt x hflatDom n)))
    (hχDom : hA.rep.MemAt x) (hfDom : f.MemAt x)
    (hχ : RSeq.SeriesSum (fun n => hA.rep.valueAt x hχDom n))
    (hf : RSeq.SeriesSum (fun n => f.valueAt x hfDom n)) :
    { hser : RSeq.SeriesSum (fun m =>
        (prop_4_2_lambda_value hA f n_k hmono x hχDom hfDom hχ hf m).1.sum) //
        (seriesSum_of_abs hflatabs).sum = hser.sum } := by
  let F := prop_4_2_lambda_k A hA f n_k
  let hsum := prop_4_2_lambda_sum A hA f hnn n_k hnk_ge
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_value F hsum hflatDom hflatabs
  refine ⟨seriesSum_congr (fun m => ?_) hV, eV⟩
  let hFmDom : (F m).MemAt x :=
    seriesSumRep_L1_F_memAt F hsum hflatDom m
  let hterm := prop_4_2_lambda_value hA f n_k hmono x
    hχDom hfDom hχ hf m
  let htermAt : RSeq.SeriesSum (fun n => (F m).valueAt x hFmDom n) := by
    simpa [F] using hterm.val
  let hprefix := IntegrableRep.ofL_value (psi_m_mem F m) x
    (BFunR.seqSum_mem (F m).fn x hFmDom (Nm F m))
  let htail := IntegrableRep.tailFrom_value (F m) (Nm F m) x hFmDom htermAt
  calc
    (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
      ((G_m F i).valueAt x
        (seriesSumRep_L1_Grow_memAt F hsum hflatDom i) j))
      (add_absSeriesSum_left hflatDom hflatabs) m)).sum
        + (seriesSum_of_abs (row_seriesSum (fun i j => abs_nonneg
          ((tail_m F i).valueAt x
            (seriesSumRep_L1_tailRow_memAt F hsum hflatDom i) j))
          (add_absSeriesSum_right hflatDom hflatabs) m)).sum
      = hprefix.val.sum + htail.val.sum := by
          rw [seriesSum_unique _ hprefix.val, seriesSum_unique _ htail.val]
    _ = htermAt.sum :=
      seriesSumRep_L1_hsplit_value F m hFmDom htermAt
    _ = hterm.val.sum := seriesSum_unique htermAt hterm.val

/-- Technical lemma used in the public import closure. -/
theorem prop_4_2_chi_f_rep_value {S : IntSpaceRC X R} (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f) {x : X}
    (hflatDom : (prop_4_2_chi_f_rep A hA f hnn).MemAt x)
    (hχDom : hA.rep.MemAt x) (hfDom : f.MemAt x)
    (hflatabs : RSeq.SeriesSum (fun n => COF.abs
      ((prop_4_2_chi_f_rep A hA f hnn).valueAt x hflatDom n)))
    (hχabs : RSeq.SeriesSum (fun n => COF.abs (hA.rep.valueAt x hχDom n)))
    (hfabs : RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n))) :
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
    rcases (hA.valid x hχDom hχabs).1 with hS1 | hS2
    · exact Or.inr ((hA.valid x hχDom hχabs).2.1 hS1 hχ)
    · exact Or.inl ((hA.valid x hχDom hχabs).2.2 hS2 hχ)
  have hφnn : Nonneg hf.sum := hnn x hfDom hfabs hf
  have hm0 : Nonneg ((prop_4_2_n_k f 0 : R)) := natCast_nonneg _
  have hmono_R : ∀ k, Le ((fun j => (prop_4_2_n_k f j : R)) k) ((fun j => (prop_4_2_n_k f j : R)) (k + 1)) :=
    fun k => natCast_le_of_le (hmono k)
  obtain ⟨hser, eser⟩ :=
    prop_4_2_rep_value_series A hA f hnn (prop_4_2_n_k f)
      hnk_ge hmono hflatDom hflatabs hχDom hfDom hχ hf
  have key : ∀ K, RSeq.partialSum
      (fun m => (prop_4_2_lambda_value hA f (prop_4_2_n_k f) hmono x
        hχDom hfDom hχ hf m).1.sum) K
      = hχ.sum * (COF.min hf.sum ((prop_4_2_n_k f K : R)) - COF.min hf.sum 0) := by
    intro K
    rw [partialSum_congr (fun m => (prop_4_2_lambda_value hA f
      (prop_4_2_n_k f) hmono x hχDom hfDom hχ hf m).2) K]
    exact prop42_telescope hf.sum hχ.sum (fun j => (prop_4_2_n_k f j : R)) hm0 hmono_R hχ01 K
  obtain ⟨k₀, hk₀⟩ :=
    prop42_eventually_chi_phi (φ := hf.sum) (χ := hχ.sum) (n_k := prop_4_2_n_k f) hφnn hsucc
  have hev : ∀ K, k₀ ≤ K → RSeq.partialSum
      (fun m => (prop_4_2_lambda_value hA f (prop_4_2_n_k f) hmono x
        hχDom hfDom hχ hf m).1.sum) K
      = hχ.sum * hf.sum := fun K hK => by rw [key K]; exact hk₀ K hK
  have efinal : hser.sum = hχ.sum * hf.sum := seriesSum_of_eventually_const hser k₀ hev
  exact eser.trans efinal

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
noncomputable def relIntegral {S : IntSpaceRC X R} (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) : R :=
  (prop_4_2_chi_f_rep C hC f hnn).integral


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
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨hxrep, hxf⟩, hxχ⟩ := hx
  obtain ⟨hflatDom, ⟨hflatabs⟩⟩ := hxrep
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχDom, ⟨hχabs⟩⟩ := hxχ
  have hval := prop_4_2_chi_f_rep_value C hC f hnn
    hflatDom hχDom hfDom hflatabs hχabs hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatabs),
      seriesSum_unique hr' (seriesSum_of_abs hfabs), hval]
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  have hχ01 : (seriesSum_of_abs hχabs).sum = 0 ∨ (seriesSum_of_abs hχabs).sum = 1 := by
    rcases (hC.valid x hχDom hχabs).1 with hS1 | hS2
    · exact Or.inr ((hC.valid x hχDom hχabs).2.1 hS1 (seriesSum_of_abs hχabs))
    · exact Or.inl ((hC.valid x hχDom hχabs).2.2 hS2 (seriesSum_of_abs hχabs))
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
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨⟨⟨hxrepD, hxrepD'⟩, hxf⟩, hxχD⟩, hxχD'⟩ := hx
  obtain ⟨hflatDomD, ⟨hflatabsD⟩⟩ := hxrepD
  obtain ⟨hflatDomD', ⟨hflatabsD'⟩⟩ := hxrepD'
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχDDom, ⟨hχDabs⟩⟩ := hxχD
  obtain ⟨hχD'Dom, ⟨hχD'abs⟩⟩ := hxχD'
  have hvalD := prop_4_2_chi_f_rep_value D hD f hnn
    hflatDomD hχDDom hfDom hflatabsD hχDabs hfabs
  have hvalD' := prop_4_2_chi_f_rep_value D' hD' f hnn
    hflatDomD' hχD'Dom hfDom hflatabsD' hχD'abs hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatabsD),
      seriesSum_unique hr' (seriesSum_of_abs hflatabsD'), hvalD, hvalD']
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  rcases (hD.valid x hχDDom hχDabs).1 with hS1 | hS2
  · have hcD : (seriesSum_of_abs hχDabs).sum = 1 :=
      (hD.valid x hχDDom hχDabs).2.1 hS1 (seriesSum_of_abs hχDabs)
    have hcD' : (seriesSum_of_abs hχD'abs).sum = 1 :=
      (hD'.valid x hχD'Dom hχD'abs).2.1 (hsub.1 hS1)
        (seriesSum_of_abs hχD'abs)
    rw [hcD, hcD']; exact le_refl _
  · have hcD : (seriesSum_of_abs hχDabs).sum = 0 :=
      (hD.valid x hχDDom hχDabs).2.2 hS2 (seriesSum_of_abs hχDabs)
    rw [hcD, zero_mul]
    rcases (hD'.valid x hχD'Dom hχD'abs).1 with hS1' | hS2'
    · have hcD' : (seriesSum_of_abs hχD'abs).sum = 1 :=
        (hD'.valid x hχD'Dom hχD'abs).2.1 hS1' (seriesSum_of_abs hχD'abs)
      rw [hcD', one_mul]; exact le_of_nonneg_sub (by rw [sub_zero]; exact hfnn)
    · have hcD' : (seriesSum_of_abs hχD'abs).sum = 0 :=
        (hD'.valid x hχD'Dom hχD'abs).2.2 hS2' (seriesSum_of_abs hχD'abs)
      rw [hcD', zero_mul]; exact le_refl _

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_mono_le {S : IntSpaceRC X R} (D D' : BSet X)
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D')
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (hle : ∀ x, ∀ (hdDom : hD.rep.MemAt x) (hd'Dom : hD'.rep.MemAt x)
      (hd : RSeq.SeriesSum (fun n => hD.rep.valueAt x hdDom n))
      (hd' : RSeq.SeriesSum (fun n => hD'.rep.valueAt x hd'Dom n)),
      Le hd.sum hd'.sum) :
    Le (relIntegral D hD f hnn) (relIntegral D' hD' f hnn) := by
  show Le (prop_4_2_chi_f_rep D hD f hnn).integral (prop_4_2_chi_f_rep D' hD' f hnn).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep D hD f hnn).domain_isFull (prop_4_2_chi_f_rep D' hD' f hnn).domain_isFull)
      f.domain_isFull) hD.rep.domain_isFull) hD'.rep.domain_isFull)
    (prop_4_2_chi_f_rep D hD f hnn) (prop_4_2_chi_f_rep D' hD' f hnn) ?_
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨⟨⟨hxrepD, hxrepD'⟩, hxf⟩, hxχD⟩, hxχD'⟩ := hx
  obtain ⟨hflatDomD, ⟨hflatabsD⟩⟩ := hxrepD
  obtain ⟨hflatDomD', ⟨hflatabsD'⟩⟩ := hxrepD'
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχDDom, ⟨hχDabs⟩⟩ := hxχD
  obtain ⟨hχD'Dom, ⟨hχD'abs⟩⟩ := hxχD'
  have hvalD := prop_4_2_chi_f_rep_value D hD f hnn
    hflatDomD hχDDom hfDom hflatabsD hχDabs hfabs
  have hvalD' := prop_4_2_chi_f_rep_value D' hD' f hnn
    hflatDomD' hχD'Dom hfDom hflatabsD' hχD'abs hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatabsD),
      seriesSum_unique hr' (seriesSum_of_abs hflatabsD'), hvalD, hvalD']
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  have hcc : Le (seriesSum_of_abs hχDabs).sum (seriesSum_of_abs hχD'abs).sum :=
    hle x hχDDom hχD'Dom (seriesSum_of_abs hχDabs)
      (seriesSum_of_abs hχD'abs)
  exact le_of_nonneg_sub (by
    rw [show (seriesSum_of_abs hχD'abs).sum * (seriesSum_of_abs hfabs).sum
          - (seriesSum_of_abs hχDabs).sum * (seriesSum_of_abs hfabs).sum
          = ((seriesSum_of_abs hχD'abs).sum - (seriesSum_of_abs hχDabs).sum)
            * (seriesSum_of_abs hfabs).sum from by ring]
    exact COFO.mul_nonneg (nonneg_sub_of_le hcc) hfnn)

/-- Technical lemma used in the public import closure. -/
theorem chi_or_add_and_value {S : IntSpaceRC X R} {D D' : BSet X}
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D') {x : X}
    (hDDom : hD.rep.MemAt x) (hD'Dom : hD'.rep.MemAt x)
    (horDom : (IntegrableSet1_or hD hD').rep.MemAt x)
    (handDom : (IntegrableSet1_and hD hD').rep.MemAt x)
    (hDc : RSeq.SeriesSum (fun n => hD.rep.valueAt x hDDom n))
    (hD'c : RSeq.SeriesSum (fun n => hD'.rep.valueAt x hD'Dom n))
    (horc : RSeq.SeriesSum (fun n =>
      (IntegrableSet1_or hD hD').rep.valueAt x horDom n))
    (handc : RSeq.SeriesSum (fun n =>
      (IntegrableSet1_and hD hD').rep.valueAt x handDom n)) :
    horc.sum + handc.sum = hDc.sum + hD'c.sum := by
  let hminDom := IntegrableRep.min2_memAt hDDom hD'Dom
  obtain ⟨hmin, hmineq⟩ := min2_value hD.rep hD'.rep x
    hDDom hD'Dom hDc hD'c
  have hand_eq : handc.sum = hmin.sum := seriesSum_unique handc hmin
  let haddDom := IntegrableRep.add_memAt hDDom hD'Dom
  let hnegMinDom := IntegrableRep.neg_memAt hminDom
  have hor_eq : horc.sum = (hDc.sum + hD'c.sum) + (- hmin.sum) :=
    seriesSum_unique horc
      (add_seriesSum_value haddDom hnegMinDom
        (add_seriesSum_value hDDom hD'Dom hDc hD'c)
        (neg_seriesSum_value hminDom hmin))
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
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxOr, hxAnd⟩, hxD⟩, hxD'⟩, hxf⟩, hxχD⟩, hxχD'⟩, hxχOr⟩, hxχAnd⟩ := hx
  obtain ⟨hflatOrDom, ⟨hflatOr⟩⟩ := hxOr
  obtain ⟨hflatAndDom, ⟨hflatAnd⟩⟩ := hxAnd
  obtain ⟨hflatDDom, ⟨hflatD⟩⟩ := hxD
  obtain ⟨hflatD'Dom, ⟨hflatD'⟩⟩ := hxD'
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχDDom, ⟨hχDabs⟩⟩ := hxχD
  obtain ⟨hχD'Dom, ⟨hχD'abs⟩⟩ := hxχD'
  obtain ⟨hχOrDom, ⟨hχorabs⟩⟩ := hxχOr
  obtain ⟨hχAndDom, ⟨hχandabs⟩⟩ := hxχAnd
  have value_Or := prop_4_2_chi_f_rep_value (BSet.or D D') (IntegrableSet1_or hD hD') f hnn
    hflatOrDom hχOrDom hfDom hflatOr hχorabs hfabs
  have value_And := prop_4_2_chi_f_rep_value (BSet.and D D') (IntegrableSet1_and hD hD') f hnn
    hflatAndDom hχAndDom hfDom hflatAnd hχandabs hfabs
  have value_D := prop_4_2_chi_f_rep_value D hD f hnn
    hflatDDom hχDDom hfDom hflatD hχDabs hfabs
  have value_D' := prop_4_2_chi_f_rep_value D' hD' f hnn
    hflatD'Dom hχD'Dom hfDom hflatD' hχD'abs hfabs
  have hchi : (seriesSum_of_abs hχorabs).sum + (seriesSum_of_abs hχandabs).sum
            = (seriesSum_of_abs hχDabs).sum + (seriesSum_of_abs hχD'abs).sum :=
    chi_or_add_and_value hD hD' hχDDom hχD'Dom hχOrDom hχAndDom
      (seriesSum_of_abs hχDabs) (seriesSum_of_abs hχD'abs)
      (seriesSum_of_abs hχorabs) (seriesSum_of_abs hχandabs)
  rw [seriesSum_unique hr
        (add_seriesSum_value hflatOrDom hflatAndDom
          (seriesSum_of_abs hflatOr) (seriesSum_of_abs hflatAnd)),
      seriesSum_unique hr'
        (add_seriesSum_value hflatDDom hflatD'Dom
          (seriesSum_of_abs hflatD) (seriesSum_of_abs hflatD'))]
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
theorem chi_and_value_valid {S : IntSpaceRC X R} {A B : BSet X}
    (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B) (hAB : IntegrableSet1 S (BSet.and A B)) {x : X}
    (hADom : hA.rep.MemAt x) (hBDom : hB.rep.MemAt x)
    (hABDom : hAB.rep.MemAt x)
    (hAabs : RSeq.SeriesSum (fun n => COF.abs (hA.rep.valueAt x hADom n)))
    (hBabs : RSeq.SeriesSum (fun n => COF.abs (hB.rep.valueAt x hBDom n)))
    (hABabs : RSeq.SeriesSum (fun n => COF.abs (hAB.rep.valueAt x hABDom n))) :
    (seriesSum_of_abs hABabs).sum
      = COF.min (seriesSum_of_abs hAabs).sum (seriesSum_of_abs hBabs).sum := by
  rcases (hAB.valid x hABDom hABabs).1 with hS1 | hS2
  · have hAB1 : (seriesSum_of_abs hABabs).sum = 1 :=
      (hAB.valid x hABDom hABabs).2.1 hS1 (seriesSum_of_abs hABabs)
    obtain ⟨xA1, xB1⟩ := hS1
    have hA1 : (seriesSum_of_abs hAabs).sum = 1 :=
      (hA.valid x hADom hAabs).2.1 xA1 (seriesSum_of_abs hAabs)
    have hB1 : (seriesSum_of_abs hBabs).sum = 1 :=
      (hB.valid x hBDom hBabs).2.1 xB1 (seriesSum_of_abs hBabs)
    rw [hAB1, hA1, hB1]
    exact (le_antisymm (cof_min_le_left 1 1) (le_min (le_refl 1) (le_refl 1))).symm
  · have hAB0 : (seriesSum_of_abs hABabs).sum = 0 :=
      (hAB.valid x hABDom hABabs).2.2 hS2 (seriesSum_of_abs hABabs)
    rw [hAB0]
    rcases hS2 with (⟨xA1, xB2⟩ | ⟨xA2, xB1⟩) | ⟨xA2, xB2⟩
    · have hA1 : (seriesSum_of_abs hAabs).sum = 1 :=
        (hA.valid x hADom hAabs).2.1 xA1 (seriesSum_of_abs hAabs)
      have hB0 : (seriesSum_of_abs hBabs).sum = 0 :=
        (hB.valid x hBDom hBabs).2.2 xB2 (seriesSum_of_abs hBabs)
      rw [hA1, hB0]; exact ((COF_min_comm 1 0).trans min_zero_one).symm
    · have hA0 : (seriesSum_of_abs hAabs).sum = 0 :=
        (hA.valid x hADom hAabs).2.2 xA2 (seriesSum_of_abs hAabs)
      have hB1 : (seriesSum_of_abs hBabs).sum = 1 :=
        (hB.valid x hBDom hBabs).2.1 xB1 (seriesSum_of_abs hBabs)
      rw [hA0, hB1]; exact min_zero_one.symm
    · have hA0 : (seriesSum_of_abs hAabs).sum = 0 :=
        (hA.valid x hADom hAabs).2.2 xA2 (seriesSum_of_abs hAabs)
      have hB0 : (seriesSum_of_abs hBabs).sum = 0 :=
        (hB.valid x hBDom hBabs).2.2 xB2 (seriesSum_of_abs hBabs)
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
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨⟨⟨hxDB, hxD'B⟩, hxf⟩, hxχDB⟩, hxχD'B⟩ := hx
  obtain ⟨hflat_DBDom, ⟨hflat_DB⟩⟩ := hxDB
  obtain ⟨hflat_D'BDom, ⟨hflat_D'B⟩⟩ := hxD'B
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχ_DBDom, ⟨hχ_DB⟩⟩ := hxχDB
  obtain ⟨hχ_D'BDom, ⟨hχ_D'B⟩⟩ := hxχD'B
  have hval_DB := prop_4_2_chi_f_rep_value (BSet.and D B) (hB D hD) f hnn
    hflat_DBDom hχ_DBDom hfDom hflat_DB hχ_DB hfabs
  have hval_D'B := prop_4_2_chi_f_rep_value (BSet.and D' B) (hB D' hD') f hnn
    hflat_D'BDom hχ_D'BDom hfDom hflat_D'B hχ_D'B hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflat_DB),
      seriesSum_unique hr' (seriesSum_of_abs hflat_D'B), hval_DB, hval_D'B]
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  rcases ((hB D hD).valid x hχ_DBDom hχ_DB).1 with hS1 | hS2
  · have hDB1 : (seriesSum_of_abs hχ_DB).sum = 1 :=
      ((hB D hD).valid x hχ_DBDom hχ_DB).2.1 hS1 (seriesSum_of_abs hχ_DB)
    obtain ⟨xD1, xB1⟩ := hS1
    have hD'B1 : (seriesSum_of_abs hχ_D'B).sum = 1 :=
      ((hB D' hD').valid x hχ_D'BDom hχ_D'B).2.1
        ⟨hsub xD1, xB1⟩ (seriesSum_of_abs hχ_D'B)
    rw [hDB1, hD'B1]; exact le_refl _
  · have hDB0 : (seriesSum_of_abs hχ_DB).sum = 0 :=
      ((hB D hD).valid x hχ_DBDom hχ_DB).2.2 hS2 (seriesSum_of_abs hχ_DB)
    rw [hDB0, zero_mul]
    rcases ((hB D' hD').valid x hχ_D'BDom hχ_D'B).1 with hS1' | hS2'
    · have hD'B1 : (seriesSum_of_abs hχ_D'B).sum = 1 :=
        ((hB D' hD').valid x hχ_D'BDom hχ_D'B).2.1 hS1'
          (seriesSum_of_abs hχ_D'B)
      rw [hD'B1, one_mul]; exact le_of_nonneg_sub (by rw [sub_zero]; exact hfnn)
    · have hD'B0 : (seriesSum_of_abs hχ_D'B).sum = 0 :=
        ((hB D' hD').valid x hχ_D'BDom hχ_D'B).2.2 hS2'
          (seriesSum_of_abs hχ_D'B)
      rw [hD'B0, zero_mul]; exact le_refl _



end BishopC
