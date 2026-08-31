import Mathdemo.Internal.BishopSec4_Convergence
import Mathdemo.Internal.Sec4_relIntegral_le_const_measure_iteration1
import Mathdemo.Internal.Sec4_Phase2_IB_D1_valueConsistency_iteration1
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b22_remainingAtomsAssembly_iteration1
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b25_rowSeedTools_iteration1

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
theorem repNonneg_cutNatVal {S : IntSpaceRC X R} (g : IntegrableRep S) (hnn : RepNonneg g)
    (n : Nat) : RepNonneg (prop_4_2_min_f_n g n) :=
  repNonneg_cutConstVal g hnn (n : R) (natCast_nonneg n)

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_const_measure_plus_diff {S : IntSpaceRC X R} (C : BSet X)
    (hC : IntegrableSet1 S C) (g : IntegrableRep S) (hnn : RepNonneg g) (n : Nat) :
    Le (relIntegral C hC g hnn)
       ((n : R) * measure1 S hC + (g.sub (prop_4_2_min_f_n g n)).integral) := by
  change Le (prop_4_2_chi_f_rep C hC g hnn).integral
          ((n : R) * hC.rep.integral + (g.sub (prop_4_2_min_f_n g n)).integral)
  rw [← IntegrableRep.integral_smul (n : R) hC.rep, ← IntegrableRep.integral_add]
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep C hC g hnn).domain_isFull
      g.domain_isFull) hC.rep.domain_isFull) (prop_4_2_min_f_n g n).domain_isFull)
    (prop_4_2_chi_f_rep C hC g hnn)
    ((hC.rep.smul (n : R)).add (g.sub (prop_4_2_min_f_n g n))) ?_
  intro x hx _hrArgDom _hr'ArgDom hr hr'
  obtain ⟨⟨⟨hx_repg, hx_g⟩, hx_χ⟩, hx_cut⟩ := hx
  obtain ⟨hflatDom, ⟨hflatg⟩⟩ := hx_repg
  obtain ⟨hgDom, ⟨hgabs⟩⟩ := hx_g
  obtain ⟨hχDom, ⟨hχabs⟩⟩ := hx_χ
  obtain ⟨hcutDom, ⟨hcutabs⟩⟩ := hx_cut
  -- Technical note.
  have hval := prop_4_2_chi_f_rep_value C hC g hnn
    hflatDom hχDom hgDom hflatg hχabs hgabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatg), hval]
  -- Technical note.
  obtain ⟨hcutsigned, hcutsigned_eq⟩ :=
    g.cutConstVal_signed_value (n : R) (natCast_nonneg n) x hgDom
      (seriesSum_of_abs hgabs)
  have hcut_eq : (seriesSum_of_abs hcutabs).sum
      = COF.min (seriesSum_of_abs hgabs).sum (n : R) := by
    rw [seriesSum_unique (seriesSum_of_abs hcutabs) hcutsigned]; exact hcutsigned_eq
  -- Technical note.
  rw [seriesSum_unique hr' (add_seriesSum_value
        (IntegrableRep.smul_memAt hχDom)
        (IntegrableRep.add_memAt hgDom (IntegrableRep.neg_memAt hcutDom))
        (smul_seriesSum_value (n : R) hχDom (seriesSum_of_abs hχabs))
        (add_seriesSum_value hgDom (IntegrableRep.neg_memAt hcutDom)
          (seriesSum_of_abs hgabs)
          (neg_seriesSum_value hcutDom (seriesSum_of_abs hcutabs))))]
  change Le ((seriesSum_of_abs hχabs).sum * (seriesSum_of_abs hgabs).sum)
        ((n : R) * (seriesSum_of_abs hχabs).sum
          + ((seriesSum_of_abs hgabs).sum + -(seriesSum_of_abs hcutabs).sum))
  rw [hcut_eq]
  -- Technical note.
  have hχ01 : (seriesSum_of_abs hχabs).sum = 0 ∨ (seriesSum_of_abs hχabs).sum = 1 := by
    rcases (hC.valid x hχDom hχabs).1 with hS1 | hS2
    · exact Or.inr ((hC.valid x hχDom hχabs).2.1 hS1 (seriesSum_of_abs hχabs))
    · exact Or.inl ((hC.valid x hχDom hχabs).2.2 hS2 (seriesSum_of_abs hχabs))
  refine le_of_nonneg_sub ?_
  rcases hχ01 with h0 | h1
  · rw [h0]
    have heq : ((n : R) * 0 + ((seriesSum_of_abs hgabs).sum
        + -COF.min (seriesSum_of_abs hgabs).sum (n : R))) - 0 * (seriesSum_of_abs hgabs).sum
        = (seriesSum_of_abs hgabs).sum - COF.min (seriesSum_of_abs hgabs).sum (n : R) := by ring
    rw [heq]
    exact nonneg_sub_of_le (cof_min_le_left _ _)
  · rw [h1]
    have heq : ((n : R) * 1 + ((seriesSum_of_abs hgabs).sum
        + -COF.min (seriesSum_of_abs hgabs).sum (n : R))) - 1 * (seriesSum_of_abs hgabs).sum
        = (n : R) - COF.min (seriesSum_of_abs hgabs).sum (n : R) := by ring
    rw [heq]
    exact nonneg_sub_of_le (cof_min_le_right _ _)


/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_cut_bound {S : IntSpaceRC X R} (C : BSet X)
    (hC : IntegrableSet1 S C) (g : IntegrableRep S) (hnn : RepNonneg g) (k : Nat) :
    Le (relIntegral C hC g hnn)
       ((g.cutNat_tendsto_rep.mod k : R) * measure1 S hC + COF.halfPow (R := R) k) := by
  have h1 := relIntegral_le_const_measure_plus_diff C hC g hnn (g.cutNat_tendsto_rep.mod k)
  have htail : Le (g.sub (prop_4_2_min_f_n g (g.cutNat_tendsto_rep.mod k))).integral
      (COF.halfPow (R := R) k) := by
    have h2 := normL1_sub_cutNat_le g hnn k (g.cutNat_tendsto_rep.mod k) (Nat.le_refl _)
    rwa [IntegrableRep.normL1_eq_integral_of_nonneg _
      (repNonneg_sub_cutNatVal g (g.cutNat_tendsto_rep.mod k))] at h2
  refine BishopC.le_trans h1 (le_of_nonneg_sub ?_)
  have heq : ((g.cutNat_tendsto_rep.mod k : R) * measure1 S hC + COF.halfPow (R := R) k)
      - ((g.cutNat_tendsto_rep.mod k : R) * measure1 S hC
        + (g.sub (prop_4_2_min_f_n g (g.cutNat_tendsto_rep.mod k))).integral)
      = COF.halfPow (R := R) k
        - (g.sub (prop_4_2_min_f_n g (g.cutNat_tendsto_rep.mod k))).integral := by ring
  rw [heq]
  exact nonneg_sub_of_le htail


/-- Technical lemma used in the public import closure. -/
noncomputable def relIntegral_abs_continuous_delta {S : IntSpaceRC X R}
    (g : IntegrableRep S) (hnn : RepNonneg g) (eps : R) (heps : COF.lt 0 eps) :
    Sigma (fun delta : R =>
      PProd (COF.lt 0 delta)
        (∀ (C : BSet X) (hC : IntegrableSet1 S C),
          COF.lt (measure1 S hC) delta → COF.lt (relIntegral C hC g hnn) eps)) := by
  let k0 : Nat := (COFO.archimedean_pos eps heps).1
  have hk0 : COF.lt (COF.halfPow (R := R) k0) eps :=
    (COFO.archimedean_pos eps heps).2
  let k : Nat := k0 + 1
  let n : Nat := g.cutNat_tendsto_rep.mod k
  let denom : R := ((n + 1 : Nat) : R)
  let delta : R := COF.halfPow (R := R) k * COFO.inv denom
  have hden_pos : COF.lt 0 denom := by
    dsimp [denom]
    exact lemma33_natCast_succ_pos n
  have hdelta_pos : COF.lt 0 delta := by
    dsimp [delta]
    exact COFO.mul_pos (halfPow_pos k) (COFO.inv_pos hden_pos)
  refine ⟨delta, ⟨hdelta_pos, ?_⟩⟩
  intro C hC hmu
  have hmain := relIntegral_le_cut_bound C hC g hnn k
  refine lt_of_le_of_lt hmain ?_
  change COF.lt ((n : R) * measure1 S hC + COF.halfPow (R := R) k) eps
  have hden_delta : denom * delta = COF.halfPow (R := R) k := by
    dsimp [delta]
    calc
      denom * (COF.halfPow (R := R) k * COFO.inv denom)
          = COF.halfPow (R := R) k * (denom * COFO.inv denom) := by ring
      _ = COF.halfPow (R := R) k * 1 := by rw [COFO.mul_inv_cancel hden_pos]
      _ = COF.halfPow (R := R) k := by ring
  have hsucc_mu_lt_hp : COF.lt (((n + 1 : Nat) : R) * measure1 S hC)
      (COF.halfPow (R := R) k) := by
    have hmul := lemma33_mul_lt_mul_left (a := measure1 S hC) (b := delta)
      (c := denom) hmu hden_pos
    rw [hden_delta] at hmul
    simpa [denom] using hmul
  have hmu_nonneg : Nonneg (measure1 S hC) := measure1_nonneg hC
  have hn_le_succ : Le ((n : R)) (((n + 1 : Nat) : R)) :=
    natCast_le_of_le (Nat.le_succ n)
  have hn_mu_le_succ : Le ((n : R) * measure1 S hC)
      (((n + 1 : Nat) : R) * measure1 S hC) :=
    lemma33_mul_le_mul_right hn_le_succ hmu_nonneg
  have hn_mu_lt_hp : COF.lt ((n : R) * measure1 S hC)
      (COF.halfPow (R := R) k) :=
    lt_of_le_of_lt hn_mu_le_succ hsucc_mu_lt_hp
  have hsum_lt_twice : COF.lt
      ((n : R) * measure1 S hC + COF.halfPow (R := R) k)
      (COF.halfPow (R := R) k + COF.halfPow (R := R) k) := by
    have h := COF.lt_add_left (COF.halfPow (R := R) k) hn_mu_lt_hp
    convert h using 1
    ring
  have hsum_lt_half0 : COF.lt
      ((n : R) * measure1 S hC + COF.halfPow (R := R) k)
      (COF.halfPow (R := R) k0) := by
    have heq : COF.halfPow (R := R) k + COF.halfPow (R := R) k
        = COF.halfPow (R := R) k0 := by
      dsimp [k]
      exact halfPow_succ_add k0
    rwa [heq] at hsum_lt_twice
  exact COFO.lt_trans hsum_lt_half0 hk0


/-- Technical lemma used in the public import closure. -/
noncomputable def relIntegral_abs_continuous_setdiff {S : IntSpaceRC X R}
    (g : IntegrableRep S) (hnn : RepNonneg g) (eps : R) (heps : COF.lt 0 eps) :
    Sigma (fun delta : R =>
      PProd (COF.lt 0 delta)
        (∀ (A B : BSet X) (hA : IntegrableSet1 S A) (hB : IntegrableSet1 S B),
          COF.lt (measure1 S (IntegrableSet1_sub hA hB)) delta →
            COF.lt (relIntegral (BSet.sub A B) (IntegrableSet1_sub hA hB) g hnn) eps)) := by
  rcases relIntegral_abs_continuous_delta g hnn eps heps with ⟨delta, hpack⟩
  obtain ⟨hdelta_pos, hsmall⟩ := hpack
  refine ⟨delta, ⟨hdelta_pos, ?_⟩⟩
  intro A B hA hB hmu
  exact hsmall (BSet.sub A B) (IntegrableSet1_sub hA hB) hmu


/-- Technical lemma used in the public import closure. -/
theorem convergeInMeasure_badSet_relIntegral_small {S : IntSpaceRC X R}
    (fn : Nat → PFunR X R) (f : PFunR X R)
    (hconv : ConvergeInMeasure S fn f)
    (A : BSet X) (hA : IntegrableSet1 S A)
    (g : IntegrableRep S) (hnn : RepNonneg g)
    (eps : R) (heps : COF.lt 0 eps) :
    ∃ N : Nat, ∀ n ≥ N,
      ∃ (B : BSet X) (hB : IntegrableSet1 S B),
        (B.S1 ⊆ A.S1 ∩ f.dom ∩ (fn n).dom) ∧
        COF.lt (relIntegral (BSet.sub A B) (IntegrableSet1_sub hA hB) g hnn) eps := by
  rcases relIntegral_abs_continuous_setdiff g hnn eps heps with ⟨delta, hpack⟩
  obtain ⟨hdelta_pos, hsmall⟩ := hpack
  obtain ⟨N, hN⟩ := hconv A hA delta hdelta_pos
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨B, hB, hsubset, hmeasure, _hpoint⟩ := hN n hn
  refine ⟨B, hB, hsubset, ?_⟩
  exact hsmall A B hA hB hmeasure


/-- Technical lemma used in the public import closure. -/
theorem relIntegral_lt_of_const_measure_lt {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) (c eps : R)
    (hbound : ∀ (x : X)
      (hfDom : f.MemAt x) (hχDom : hC.rep.MemAt x)
      (hfabs : RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)))
      (hχabs : RSeq.SeriesSum (fun n => COF.abs (hC.rep.valueAt x hχDom n))),
      (seriesSum_of_abs hχabs).sum = 1 → Le (seriesSum_of_abs hfabs).sum c)
    (hcmu : COF.lt (c * measure1 S hC) eps) :
    COF.lt (relIntegral C hC f hnn) eps :=
  lt_of_le_of_lt (relIntegral_le_const_measure C hC f hnn c hbound) hcmu


/-- Technical lemma used in the public import closure. -/
theorem measure1_mono_set {S : IntSpaceRC X R} (C A : BSet X)
    (hC : IntegrableSet1 S C) (hA : IntegrableSet1 S A)
    (hsub : BSet.Subset C A) :
    Le (measure1 S hC) (measure1 S hA) := by
  change Le hC.rep.integral hA.rep.integral
  refine prop_1_11 (isFull_inter hC.rep.domain_isFull hA.rep.domain_isFull)
    hC.rep hA.rep ?_
  intro x hx _hcxArgDom _haxArgDom hcx hax
  obtain ⟨hxC, hxA⟩ := hx
  obtain ⟨hCDom, ⟨hCabs⟩⟩ := hxC
  obtain ⟨hADom, ⟨hAabs⟩⟩ := hxA
  rcases (hC.valid x hCDom hCabs).1 with hxC1 | hxC2
  · have hcv : hcx.sum = 1 := (hC.valid x hCDom hCabs).2.1 hxC1 hcx
    have hav : hax.sum = 1 := (hA.valid x hADom hAabs).2.1 (hsub.1 hxC1) hax
    rw [hcv, hav]
    exact le_refl _
  · have hcv : hcx.sum = 0 := (hC.valid x hCDom hCabs).2.2 hxC2 hcx
    rw [hcv]
    rcases (hA.valid x hADom hAabs).1 with hxA1 | hxA2
    · have hav : hax.sum = 1 := (hA.valid x hADom hAabs).2.1 hxA1 hax
      rw [hav]
      exact le_of_lt COFO.one_pos
    · have hav : hax.sum = 0 := (hA.valid x hADom hAabs).2.2 hxA2 hax
      rw [hav]
      exact le_refl _


/-- Technical lemma used in the public import closure. -/
theorem measure1_add_one_pos {S : IntSpaceRC X R} {A : BSet X}
    (hA : IntegrableSet1 S A) : COF.lt 0 (measure1 S hA + 1) := by
  have hA_lt : COF.lt (measure1 S hA) (measure1 S hA + 1) :=
    lemma33_lt_add_of_pos_right (a := measure1 S hA) COFO.one_pos
  exact lt_of_le_of_lt (measure1_nonneg hA) hA_lt


/-- Technical lemma used in the public import closure. -/
theorem scaled_measure_lt_of_subset {S : IntSpaceRC X R}
    (C A : BSet X) (hC : IntegrableSet1 S C) (hA : IntegrableSet1 S A)
    (hsub : BSet.Subset C A) (eps : R) (heps : COF.lt 0 eps) :
    COF.lt ((eps * COFO.inv (measure1 S hA + 1)) * measure1 S hC) eps := by
  let denom : R := measure1 S hA + 1
  have hden_pos : COF.lt 0 denom := by
    dsimp [denom]
    exact measure1_add_one_pos hA
  have hA_lt_den : COF.lt (measure1 S hA) denom := by
    dsimp [denom]
    exact lemma33_lt_add_of_pos_right (a := measure1 S hA) COFO.one_pos
  have hC_le_A : Le (measure1 S hC) (measure1 S hA) :=
    measure1_mono_set C A hC hA hsub
  have hC_lt_den : COF.lt (measure1 S hC) denom :=
    lt_of_le_of_lt hC_le_A hA_lt_den
  have hinvC_lt_one : COF.lt (COFO.inv denom * measure1 S hC) 1 := by
    have hmul := lemma33_mul_lt_mul_left hC_lt_den (COFO.inv_pos hden_pos)
    have hcancel : COFO.inv denom * denom = (1 : R) := by
      calc
        COFO.inv denom * denom = denom * COFO.inv denom := by ring
        _ = 1 := COFO.mul_inv_cancel hden_pos
    rwa [hcancel] at hmul
  have hscaled := lemma33_mul_lt_mul_left hinvC_lt_one heps
  convert hscaled using 1
  · ring
  · ring


/-- Technical lemma used in the public import closure. -/
theorem relIntegral_goodSet_small_of_subset {S : IntSpaceRC X R}
    (C A : BSet X) (hC : IntegrableSet1 S C) (hA : IntegrableSet1 S A)
    (hsub : BSet.Subset C A)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (eps : R) (heps : COF.lt 0 eps)
    (hbound : ∀ (x : X)
      (hfDom : f.MemAt x) (hχDom : hC.rep.MemAt x)
      (hfabs : RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)))
      (hχabs : RSeq.SeriesSum (fun n => COF.abs (hC.rep.valueAt x hχDom n))),
      (seriesSum_of_abs hχabs).sum = 1 →
        Le (seriesSum_of_abs hfabs).sum
          (eps * COFO.inv (measure1 S hA + 1))) :
    COF.lt (relIntegral C hC f hnn) eps :=
  relIntegral_lt_of_const_measure_lt C hC f hnn
    (eps * COFO.inv (measure1 S hA + 1)) eps hbound
    (scaled_measure_lt_of_subset C A hC hA hsub eps heps)


/-- Technical lemma used in the public import closure. -/
theorem measure1_mono_s1_subset {S : IntSpaceRC X R} (C A : BSet X)
    (hC : IntegrableSet1 S C) (hA : IntegrableSet1 S A)
    (hsub1 : C.S1 ⊆ A.S1) :
    Le (measure1 S hC) (measure1 S hA) := by
  change Le hC.rep.integral hA.rep.integral
  refine prop_1_11 (isFull_inter hC.rep.domain_isFull hA.rep.domain_isFull)
    hC.rep hA.rep ?_
  intro x hx _hcxArgDom _haxArgDom hcx hax
  obtain ⟨hxC, hxA⟩ := hx
  obtain ⟨hCDom, ⟨hCabs⟩⟩ := hxC
  obtain ⟨hADom, ⟨hAabs⟩⟩ := hxA
  rcases (hC.valid x hCDom hCabs).1 with hxC1 | hxC2
  · have hcv : hcx.sum = 1 := (hC.valid x hCDom hCabs).2.1 hxC1 hcx
    have hav : hax.sum = 1 := (hA.valid x hADom hAabs).2.1 (hsub1 hxC1) hax
    rw [hcv, hav]
    exact le_refl _
  · have hcv : hcx.sum = 0 := (hC.valid x hCDom hCabs).2.2 hxC2 hcx
    rw [hcv]
    rcases (hA.valid x hADom hAabs).1 with hxA1 | hxA2
    · have hav : hax.sum = 1 := (hA.valid x hADom hAabs).2.1 hxA1 hax
      rw [hav]
      exact le_of_lt COFO.one_pos
    · have hav : hax.sum = 0 := (hA.valid x hADom hAabs).2.2 hxA2 hax
      rw [hav]
      exact le_refl _


/-- Technical lemma used in the public import closure. -/
theorem scaled_measure_lt_of_s1_subset {S : IntSpaceRC X R}
    (C A : BSet X) (hC : IntegrableSet1 S C) (hA : IntegrableSet1 S A)
    (hsub1 : C.S1 ⊆ A.S1) (eps : R) (heps : COF.lt 0 eps) :
    COF.lt ((eps * COFO.inv (measure1 S hA + 1)) * measure1 S hC) eps := by
  let denom : R := measure1 S hA + 1
  have hden_pos : COF.lt 0 denom := by
    dsimp [denom]
    exact measure1_add_one_pos hA
  have hA_lt_den : COF.lt (measure1 S hA) denom := by
    dsimp [denom]
    exact lemma33_lt_add_of_pos_right (a := measure1 S hA) COFO.one_pos
  have hC_le_A : Le (measure1 S hC) (measure1 S hA) :=
    measure1_mono_s1_subset C A hC hA hsub1
  have hC_lt_den : COF.lt (measure1 S hC) denom :=
    lt_of_le_of_lt hC_le_A hA_lt_den
  have hinvC_lt_one : COF.lt (COFO.inv denom * measure1 S hC) 1 := by
    have hmul := lemma33_mul_lt_mul_left hC_lt_den (COFO.inv_pos hden_pos)
    have hcancel : COFO.inv denom * denom = (1 : R) := by
      calc
        COFO.inv denom * denom = denom * COFO.inv denom := by ring
        _ = 1 := COFO.mul_inv_cancel hden_pos
    rwa [hcancel] at hmul
  have hscaled := lemma33_mul_lt_mul_left hinvC_lt_one heps
  convert hscaled using 1
  · ring
  · ring


/-- Technical lemma used in the public import closure. -/
theorem relIntegral_goodSet_small_of_s1_subset {S : IntSpaceRC X R}
    (C A : BSet X) (hC : IntegrableSet1 S C) (hA : IntegrableSet1 S A)
    (hsub1 : C.S1 ⊆ A.S1)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (eps : R) (heps : COF.lt 0 eps)
    (hbound : ∀ (x : X)
      (hfDom : f.MemAt x) (hχDom : hC.rep.MemAt x)
      (hfabs : RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)))
      (hχabs : RSeq.SeriesSum (fun n => COF.abs (hC.rep.valueAt x hχDom n))),
      (seriesSum_of_abs hχabs).sum = 1 →
        Le (seriesSum_of_abs hfabs).sum
          (eps * COFO.inv (measure1 S hA + 1))) :
    COF.lt (relIntegral C hC f hnn) eps :=
  relIntegral_lt_of_const_measure_lt C hC f hnn
    (eps * COFO.inv (measure1 S hA + 1)) eps hbound
    (scaled_measure_lt_of_s1_subset C A hC hA hsub1 eps heps)


/-- Technical lemma used in the public import closure. -/
theorem relIntegral_complement_lt_add {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (eps : R)
    (hgood : COF.lt (relIntegral C hC f hnn) eps)
    (hbad : COF.lt (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral eps) :
    COF.lt f.integral (eps + eps) := by
  have hsum : COF.lt
      (relIntegral C hC f hnn
        + (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral)
      (eps + eps) := lt_add hgood hbad
  rwa [relIntegral_complement_additive C hC f hnn] at hsum


/-- Technical lemma used in the public import closure. -/
theorem lemma_4_14_local_two_epsilon {S : IntSpaceRC X R}
    (C A : BSet X) (hC : IntegrableSet1 S C) (hA : IntegrableSet1 S A)
    (hsub1 : C.S1 ⊆ A.S1)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (eps : R) (heps : COF.lt 0 eps)
    (hbound : ∀ (x : X)
      (hfDom : f.MemAt x) (hχDom : hC.rep.MemAt x)
      (hfabs : RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)))
      (hχabs : RSeq.SeriesSum (fun n => COF.abs (hC.rep.valueAt x hχDom n))),
      (seriesSum_of_abs hχabs).sum = 1 →
        Le (seriesSum_of_abs hfabs).sum
          (eps * COFO.inv (measure1 S hA + 1)))
    (hbad : COF.lt (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral eps) :
    COF.lt f.integral (eps + eps) :=
  relIntegral_complement_lt_add C hC f hnn eps
    (relIntegral_goodSet_small_of_s1_subset C A hC hA hsub1 f hnn eps heps hbound)
    hbad


/-- Technical lemma used in the public import closure. -/
theorem convergeInMeasure_goodSet_witness {S : IntSpaceRC X R}
    (fn : Nat → PFunR X R) (f : PFunR X R)
    (hconv : ConvergeInMeasure S fn f)
    (A : BSet X) (hA : IntegrableSet1 S A)
    (eps : R) (heps : COF.lt 0 eps) :
    ∃ N : Nat, ∀ n ≥ N,
      ∃ (C : BSet X) (hC : IntegrableSet1 S C),
        (C.S1 ⊆ A.S1) ∧
        COF.lt (measure1 S (IntegrableSet1_sub hA hC))
          (eps * COFO.inv (measure1 S hA + 1)) ∧
        ∀ x (_hxC : x ∈ C.S1) (hxf : x ∈ f.dom) (hxfn : x ∈ (fn n).dom),
          COF.lt (COF.abs (f.toFun x hxf - (fn n).toFun x hxfn))
            (eps * COFO.inv (measure1 S hA + 1)) := by
  let eta : R := eps * COFO.inv (measure1 S hA + 1)
  have heta : COF.lt 0 eta := by
    dsimp [eta]
    exact COFO.mul_pos heps (COFO.inv_pos (measure1_add_one_pos hA))
  obtain ⟨N, hN⟩ := hconv A hA eta heta
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨C, hC, hsubset, hmeasure, hpoint⟩ := hN n hn
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro x hxC
    exact (hsubset hxC).1.1
  · simpa [eta] using hmeasure
  · intro x hxC hxf hxfn
    simpa [eta] using hpoint x hxC hxf hxfn


/-- Technical lemma used in the public import closure. -/
structure Lemma414LocalData {S : IntSpaceRC X R} (fn : Nat → IntegrableRep S)
    (hnn : ∀ n, RepNonneg (fn n)) (eps : R) : Type _ where
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  close : ∀ n, N ≤ n →
    Sigma (fun C : BSet X =>
      Sigma (fun hC : IntegrableSet1 S C =>
        PProd (C.S1 ⊆ A.S1)
          (PProd
            (∀ (x : X)
              (hfDom : (fn n).MemAt x) (hχDom : hC.rep.MemAt x)
              (hfabs : RSeq.SeriesSum
                (fun m => COF.abs ((fn n).valueAt x hfDom m)))
              (hχabs : RSeq.SeriesSum
                (fun m => COF.abs (hC.rep.valueAt x hχDom m))),
              (seriesSum_of_abs hχabs).sum = 1 →
                Le (seriesSum_of_abs hfabs).sum
                  (eps * COFO.inv (measure1 S hA + 1)))
            (COF.lt
              ((fn n).sub (prop_4_2_chi_f_rep C hC (fn n) (hnn n))).integral
              eps))))

/-- Technical lemma used in the public import closure. -/
def lemma_4_14_tendsto_zero_from_local_data {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hdata : ∀ eps, COF.lt 0 eps → Lemma414LocalData (S := S) fn hnn eps) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 where
  mod := fun k => (hdata (COF.halfPow (R := R) (k + 1)) (halfPow_pos (k + 1))).N
  close := by
    intro k n hn
    let eps : R := COF.halfPow (R := R) (k + 1)
    let D := hdata eps (halfPow_pos (k + 1))
    obtain ⟨C, hC, hpack⟩ := D.close n hn
    obtain ⟨hsub1, hpack2⟩ := hpack
    obtain ⟨hbound, hbad⟩ := hpack2
    have hlt_two : COF.lt (fn n).integral (eps + eps) :=
      lemma_4_14_local_two_epsilon C D.A hC D.hA hsub1 (fn n) (hnn n)
        eps (halfPow_pos (k + 1)) hbound hbad
    have hlt_half : COF.lt (fn n).integral (COF.halfPow (R := R) k) := by
      have heq : eps + eps = COF.halfPow (R := R) k := by
        dsimp [eps]
        exact halfPow_succ_add k
      rwa [heq] at hlt_two
    have hnon : Nonneg ((fn n).integral) := by
      rw [← IntegrableRep.normL1_eq_integral_of_nonneg (fn n) (hnn n)]
      exact IntegrableRep.normL1_nonneg (fn n)
    change COF.lt (COF.abs ((fn n).integral - 0)) (COF.halfPow (R := R) k)
    rw [sub_zero, COFO.abs_of_nonneg hnon]
    exact hlt_half


/-- Technical lemma used in the public import closure. -/
structure Lemma414UniformComplementData {S : IntSpaceRC X R} (fn : Nat → IntegrableRep S)
    (hnn : ∀ n, RepNonneg (fn n)) (eps : R) : Type _ where
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  delta : R
  delta_pos : COF.lt 0 delta
  small : ∀ n, N ≤ n → ∀ (C : BSet X) (hC : IntegrableSet1 S C),
    COF.lt (measure1 S (IntegrableSet1_sub hA hC)) delta →
      COF.lt ((fn n).sub (prop_4_2_chi_f_rep C hC (fn n) (hnn n))).integral eps

/-- Technical lemma used in the public import closure. -/
structure Lemma414GoodSetData {S : IntSpaceRC X R} (fn : Nat → IntegrableRep S)
    (hnn : ∀ n, RepNonneg (fn n)) (A : BSet X) (hA : IntegrableSet1 S A)
    (delta eps : R) : Type _ where
  N : Nat
  close : ∀ n, N ≤ n →
    Sigma (fun C : BSet X =>
      Sigma (fun hC : IntegrableSet1 S C =>
        PProd (C.S1 ⊆ A.S1)
          (PProd
            (COF.lt (measure1 S (IntegrableSet1_sub hA hC)) delta)
            (∀ (x : X)
              (hfDom : (fn n).MemAt x) (hχDom : hC.rep.MemAt x)
              (hfabs : RSeq.SeriesSum
                (fun m => COF.abs ((fn n).valueAt x hfDom m)))
              (hχabs : RSeq.SeriesSum
                (fun m => COF.abs (hC.rep.valueAt x hχDom m))),
              (seriesSum_of_abs hχabs).sum = 1 →
                Le (seriesSum_of_abs hfabs).sum
                  (eps * COFO.inv (measure1 S hA + 1))))))

/-- Technical lemma used in the public import closure. -/
structure Lemma414RepConvergeToZeroData {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) : Type _ where
  close : ∀ (A : BSet X) (hA : IntegrableSet1 S A)
      (delta eta : R), COF.lt 0 delta → COF.lt 0 eta →
    Sigma (fun N : Nat =>
      ∀ n, N ≤ n →
        Sigma (fun C : BSet X =>
          Sigma (fun hC : IntegrableSet1 S C =>
            PProd (C.S1 ⊆ A.S1)
              (PProd
                (COF.lt (measure1 S (IntegrableSet1_sub hA hC)) delta)
                (∀ (x : X)
                  (hfDom : (fn n).MemAt x) (hχDom : hC.rep.MemAt x)
                  (hfabs : RSeq.SeriesSum
                    (fun m => COF.abs ((fn n).valueAt x hfDom m)))
                  (hχabs : RSeq.SeriesSum
                    (fun m => COF.abs (hC.rep.valueAt x hχDom m))),
                  (seriesSum_of_abs hχabs).sum = 1 →
                    Le (seriesSum_of_abs hfabs).sum eta)))))

/-- Technical lemma used in the public import closure. -/
structure Lemma414ConvergeInMeasureToZeroData {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) : Type _ where
  close : ∀ (A : BSet X) (hA : IntegrableSet1 S A)
      (eps : R), COF.lt 0 eps →
    Sigma (fun N : Nat =>
      ∀ n, N ≤ n →
        Sigma (fun C : BSet X =>
          Sigma (fun hC : IntegrableSet1 S C =>
            PProd (C.S1 ⊆ A.S1)
              (PProd
                (COF.lt (measure1 S (IntegrableSet1_sub hA hC)) eps)
                (∀ (x : X)
                  (hfDom : (fn n).MemAt x) (hχDom : hC.rep.MemAt x)
                  (hfabs : RSeq.SeriesSum
                    (fun m => COF.abs ((fn n).valueAt x hfDom m)))
                  (hχabs : RSeq.SeriesSum
                    (fun m => COF.abs (hC.rep.valueAt x hχDom m))),
                  (seriesSum_of_abs hχabs).sum = 1 →
                    COF.lt (COF.abs (seriesSum_of_abs hfabs).sum) eps)))))

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_rep_converge_from_source_measure_converge_zero
    {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hconv : Lemma414ConvergeInMeasureToZeroData (S := S) fn) :
    Lemma414RepConvergeToZeroData (S := S) fn where
  close := by
    intro A hA delta eta hdelta heta
    let rho : R := COF.min delta eta
    have hrho : COF.lt 0 rho := by
      dsimp [rho]
      exact lemma34_min_pos hdelta heta
    obtain ⟨N, hN⟩ := hconv.close A hA rho hrho
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hsub1, hmeasure, hsmall⟩ := hN n hn
    refine ⟨C, hC, ?_⟩
    refine ⟨hsub1, ?_⟩
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le hmeasure (cof_min_le_left delta eta)
    · intro x hfDom hχDom hfabs hχabs hχone
      have hpt := hsmall x hfDom hχDom hfabs hχabs hχone
      have hnon : Nonneg (seriesSum_of_abs hfabs).sum :=
        hnn n x hfDom hfabs (seriesSum_of_abs hfabs)
      rw [COFO.abs_of_nonneg hnon] at hpt
      exact le_of_lt (lt_of_lt_of_le hpt (cof_min_le_right delta eta))


/-- Technical lemma used in the public import closure. -/
structure Lemma414RepresentsPFunR {S : IntSpaceRC X R}
    (r : IntegrableRep S) (p : PFunR X R) : Type _ where
  value : ∀ (x : X) (hp : x ∈ p.dom)
    (hrDom : r.MemAt x)
    (hrabs : RSeq.SeriesSum (fun m => COF.abs (r.valueAt x hrDom m))),
      (seriesSum_of_abs hrabs).sum = p.toFun x hp

/-- Technical lemma used in the public import closure. -/
structure Lemma414ZeroPFunR (p : PFunR X R) : Type _ where
  value_zero : ∀ (x : X) (hp : x ∈ p.dom), p.toFun x hp = 0

/-- Technical lemma used in the public import closure. -/
structure Lemma414PFunConvergeToZeroData {S : IntSpaceRC X R}
    (pfn : Nat → PFunR X R) (zero : PFunR X R) : Type _ where
  close : ∀ (A : BSet X) (hA : IntegrableSet1 S A) (eps : R) (_heps : COF.lt 0 eps),
    Sigma (fun N : Nat =>
      ∀ n, N ≤ n →
        Sigma (fun C : BSet X =>
          Sigma (fun hC : IntegrableSet1 S C =>
            PProd (C.S1 ⊆ A.S1 ∩ zero.dom ∩ (pfn n).dom)
              (PProd
                (COF.lt (measure1 S (IntegrableSet1_sub hA hC)) eps)
                (∀ x (_hxC : x ∈ C.S1) (hxz : x ∈ zero.dom) (hxfn : x ∈ (pfn n).dom),
                  COF.lt (COF.abs (zero.toFun x hxz - (pfn n).toFun x hxfn)) eps)))))

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_rep_converge_from_pfun_converge_zero {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    Lemma414RepConvergeToZeroData (S := S) fn where
  close := by
    intro A hA delta eta hdelta heta
    let rho : R := COF.min delta eta
    have hrho : COF.lt 0 rho := by
      dsimp [rho]
      exact lemma34_min_pos hdelta heta
    obtain ⟨N, hN⟩ := hconv.close A hA rho hrho
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hsubset, hmeasure, hpoint⟩ := hN n hn
    refine ⟨C, hC, ?_⟩
    refine ⟨?_, ?_⟩
    · intro x hxC
      exact (hsubset hxC).1.1
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le hmeasure (cof_min_le_left delta eta)
    · intro x hfDom hχDom hfabs hχabs hχone
      have hvalid := hC.valid x hχDom hχabs
      rcases hvalid.1 with hxC | hxC2
      · have hxzero : x ∈ zero.dom := (hsubset hxC).1.2
        have hxfn : x ∈ (pfn n).dom := (hsubset hxC).2
        have hpt := hpoint x hxC hxzero hxfn
        have hrepv := (hrep n).value x hxfn hfDom hfabs
        have hzv := hzero.value_zero x hxzero
        rw [hzv, ← hrepv] at hpt
        have hnon : Nonneg (seriesSum_of_abs hfabs).sum :=
          hnn n x hfDom hfabs (seriesSum_of_abs hfabs)
        rw [show (0 : R) - (seriesSum_of_abs hfabs).sum =
              - (seriesSum_of_abs hfabs).sum from by ring,
            COFO.abs_neg, COFO.abs_of_nonneg hnon] at hpt
        exact le_of_lt (lt_of_lt_of_le hpt (cof_min_le_right delta eta))
      · exfalso
        have hzeroχ : (seriesSum_of_abs hχabs).sum = 0 :=
          hvalid.2.2 hxC2 (seriesSum_of_abs hχabs)
        have h01 : (0 : R) = 1 := by
          rw [← hzeroχ, hχone]
        have hbad : COF.lt (0 : R) 0 := by
          have hone := COFO.one_pos (R := R)
          rwa [← h01] at hone
        exact COF.lt_irrefl 0 hbad


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_good_set_data_from_rep_converge {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hconv : Lemma414RepConvergeToZeroData (S := S) fn) :
    ∀ eps, COF.lt 0 eps → ∀ (A : BSet X) (hA : IntegrableSet1 S A)
      (delta : R), COF.lt 0 delta →
        Lemma414GoodSetData (S := S) fn hnn A hA delta eps := by
  intro eps heps A hA delta hdelta
  let eta : R := eps * COFO.inv (measure1 S hA + 1)
  have heta : COF.lt 0 eta := by
    dsimp [eta]
    exact COFO.mul_pos heps (COFO.inv_pos (measure1_add_one_pos hA))
  obtain ⟨N, hN⟩ := hconv.close A hA delta eta hdelta heta
  exact
    { N := N
      close := by
        intro n hn
        obtain ⟨C, hC, hpack⟩ := hN n hn
        obtain ⟨hsub1, hpack2⟩ := hpack
        obtain ⟨hmeasure, hbound⟩ := hpack2
        exact ⟨C, hC, ⟨hsub1, ⟨hmeasure, by simpa [eta] using hbound⟩⟩⟩ }


/-- Technical lemma used in the public import closure. -/
def lemma_4_14_local_data_from_uniform_and_good {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hui : ∀ eps, COF.lt 0 eps → Lemma414UniformComplementData (S := S) fn hnn eps)
    (hgood : ∀ eps, COF.lt 0 eps → ∀ (A : BSet X) (hA : IntegrableSet1 S A)
        (delta : R), COF.lt 0 delta →
          Lemma414GoodSetData (S := S) fn hnn A hA delta eps) :
    ∀ eps, COF.lt 0 eps → Lemma414LocalData (S := S) fn hnn eps := by
  intro eps heps
  let U := hui eps heps
  let G := hgood eps heps U.A U.hA U.delta U.delta_pos
  exact
    { A := U.A
      hA := U.hA
      N := Nat.max U.N G.N
      close := by
        intro n hn
        have hnU : U.N ≤ n := Nat.le_trans (Nat.le_max_left U.N G.N) hn
        have hnG : G.N ≤ n := Nat.le_trans (Nat.le_max_right U.N G.N) hn
        obtain ⟨C, hC, hpack⟩ := G.close n hnG
        obtain ⟨hsub1, hpack2⟩ := hpack
        obtain ⟨hmeasure, hbound⟩ := hpack2
        have hbad := U.small n hnU C hC hmeasure
        exact ⟨C, hC, ⟨hsub1, ⟨hbound, hbad⟩⟩⟩ }


/-- Technical lemma used in the public import closure. -/
def lemma_4_14_tendsto_zero_from_uniform_and_good_data {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hui : ∀ eps, COF.lt 0 eps → Lemma414UniformComplementData (S := S) fn hnn eps)
    (hgood : ∀ eps, COF.lt 0 eps → ∀ (A : BSet X) (hA : IntegrableSet1 S A)
        (delta : R), COF.lt 0 delta →
          Lemma414GoodSetData (S := S) fn hnn A hA delta eps) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_local_data fn hnn
    (lemma_4_14_local_data_from_uniform_and_good fn hnn hui hgood)


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_uniform_and_rep_converge {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hui : ∀ eps, COF.lt 0 eps → Lemma414UniformComplementData (S := S) fn hnn eps)
    (hconv : Lemma414RepConvergeToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_uniform_and_good_data fn hnn hui
    (lemma_4_14_good_set_data_from_rep_converge fn hnn hconv)


/-- Technical lemma used in the public import closure. -/
structure Lemma414IBInterface {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n)) : Type _ where
  IMeas : ∀ (B : BSet X), IsMeasurableSet (S := S) B → Nat → R
  complement_eq : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
    IMeas (BSet.neg C) (isMeasurableSet_neg_of_integrable (S := S) hC) n =
      ((fn n).sub (prop_4_2_chi_f_rep C hC (fn n) (hnn n))).integral

/-- Support for comparing the direct measurable `I_{-C}` representative with
  the previous complement representative `f - χ_C f`. -/
def Sec4ComplementConsistencySupport {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Set X :=
  ((((genIB_rep_from_measurable (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn).domain ∩
      (f.sub (prop_4_2_chi_f_rep C hC f hnn)).domain) ∩
      (prop_4_2_chi_f_rep C hC f hnn).domain) ∩
      hC.rep.domain) ∩
      f.domain

/-- Fullness of the support used for the complement comparison. -/
theorem sec4ComplementConsistencySupport_full {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IsFull S (Sec4ComplementConsistencySupport (S := S) C hC f hnn) := by
  unfold Sec4ComplementConsistencySupport
  exact isFull_inter
    (isFull_inter
      (isFull_inter
        (isFull_inter
          (IntegrableRep.domain_isFull
            (genIB_rep_from_measurable (BSet.neg C)
              (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn))
          (IntegrableRep.domain_isFull
            (f.sub (prop_4_2_chi_f_rep C hC f hnn))))
        (IntegrableRep.domain_isFull (prop_4_2_chi_f_rep C hC f hnn)))
      (IntegrableRep.domain_isFull hC.rep))
    (IntegrableRep.domain_isFull f)

/-- Pointwise equality between direct `I_{-C}` and the complement
  representative, assuming the general measurable value bridge for `-C`. -/
theorem sec4_genIB_complement_value_eq_subRep_on_support {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBValueBridge (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn) :
    ∀ x ∈ Sec4ComplementConsistencySupport (S := S) C hC f hnn,
      ∀ (hgenArgDom : (genIB_rep_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn).MemAt x),
      ∀ (hcompArgDom : (f.sub
        (prop_4_2_chi_f_rep C hC f hnn)).MemAt x),
      ∀ (hgen : RSeq.SeriesSum
        (fun n => (genIB_rep_from_measurable (BSet.neg C)
          (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn).valueAt
            x hgenArgDom n))
        (hcomp : RSeq.SeriesSum
        (fun n => (f.sub (prop_4_2_chi_f_rep C hC f hnn)).valueAt
          x hcompArgDom n)),
        hgen.sum = hcomp.sum := by
  intro x hx _hgenArgDom _hcompArgDom hgen hcomp
  rcases hx with ⟨⟨⟨⟨hgenDom, hcompDom⟩, hchiFDom⟩, hχDom⟩, hfDom⟩
  rcases hgenDom with ⟨hgenDomAll, ⟨hgenabs⟩⟩
  rcases hcompDom with ⟨_hcompSupportDom, ⟨_hcompabs⟩⟩
  rcases hchiFDom with ⟨hchiFDomAll, ⟨hchiFabs⟩⟩
  rcases hχDom with ⟨hχDomAll, ⟨hχabs⟩⟩
  rcases hfDom with ⟨hfDomAll, ⟨hfabs⟩⟩
  let hcompValue :=
    add_seriesSum_value hfDomAll (IntegrableRep.neg_memAt hchiFDomAll)
      (seriesSum_of_abs hfabs)
      (neg_seriesSum_value hchiFDomAll (seriesSum_of_abs hchiFabs))
  have hcomp_value :
      hcompValue.sum =
        (1 - (seriesSum_of_abs hχabs).sum) *
          (seriesSum_of_abs hfabs).sum :=
    prop_4_2_complement_value C hC f hnn
      hchiFDomAll hχDomAll hfDomAll hchiFabs hχabs hfabs
  have hχvalid := hC.valid x hχDomAll hχabs
  cases hχvalid.1 with
  | inl hxC1 =>
      have hχ_one :
          (seriesSum_of_abs hχabs).sum = 1 :=
        hχvalid.2.1 hxC1 (seriesSum_of_abs hχabs)
      have hgen_value :
          (seriesSum_of_abs hgenabs).sum = 0 :=
        V.value_s2 x (by simpa [BSet.neg] using hxC1)
          hgenDomAll hgenabs
      calc
        hgen.sum = (seriesSum_of_abs hgenabs).sum :=
          seriesSum_unique hgen (seriesSum_of_abs hgenabs)
        _ = 0 := hgen_value
        _ = (1 - 1) * (seriesSum_of_abs hfabs).sum := by ring
        _ = (1 - (seriesSum_of_abs hχabs).sum) *
            (seriesSum_of_abs hfabs).sum := by rw [hχ_one]
        _ = hcompValue.sum := hcomp_value.symm
        _ = hcomp.sum := (seriesSum_unique hcomp hcompValue).symm
  | inr hxC2 =>
      have hχ_zero :
          (seriesSum_of_abs hχabs).sum = 0 :=
        hχvalid.2.2 hxC2 (seriesSum_of_abs hχabs)
      have hgen_value :
          (seriesSum_of_abs hgenabs).sum =
            (seriesSum_of_abs hfabs).sum :=
        V.value_s1 x (by simpa [BSet.neg] using hxC2)
          hgenDomAll hgenabs hfDomAll hfabs
      calc
        hgen.sum = (seriesSum_of_abs hgenabs).sum :=
          seriesSum_unique hgen (seriesSum_of_abs hgenabs)
        _ = (seriesSum_of_abs hfabs).sum := hgen_value
        _ = (1 - 0) * (seriesSum_of_abs hfabs).sum := by ring
        _ = (1 - (seriesSum_of_abs hχabs).sum) *
            (seriesSum_of_abs hfabs).sum := by rw [hχ_zero]
        _ = hcompValue.sum := hcomp_value.symm
        _ = hcomp.sum := (seriesSum_unique hcomp hcompValue).symm


/-- Direct measurable `I_{-C}` agrees with the previous complement expression,
  assuming the value bridge for `-C`. -/
theorem sec4_genRelIntegral_eq_complement_of_valueBridge {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBValueBridge (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn) :
    genRelIntegral_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn =
      (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral := by
  unfold genRelIntegral_from_measurable
  exact cor_1_12
    (sec4ComplementConsistencySupport_full C hC f hnn)
    (genIB_rep_from_measurable (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn)
    (f.sub (prop_4_2_chi_f_rep C hC f hnn))
    (sec4_genIB_complement_value_eq_subRep_on_support C hC f hnn V)


/-- The `Lemma414IBInterface` instantiated by the direct general measurable
  construction `genRelIntegral_from_measurable`.  The only remaining analytic
  input needed by 4.14 is the value bridge for complement sets. -/
noncomputable def lemma_4_14_ib_interface_from_genIB {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hV : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) (fn n) (hnn n)) :
    Lemma414IBInterface (S := S) fn hnn where
  IMeas := fun B hB n => genRelIntegral_from_measurable B hB (fn n) (hnn n)
  complement_eq := by
    intro n C hC
    exact sec4_genRelIntegral_eq_complement_of_valueBridge
      C hC (fn n) (hnn n) (hV n C hC)


/-- Technical lemma used in the public import closure. -/
structure Lemma414UniformIBData {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (IB : Lemma414IBInterface (S := S) fn hnn) (eps : R) : Type _ where
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  delta : R
  delta_pos : COF.lt 0 delta
  small : ∀ n, N ≤ n → ∀ (B : BSet X) (hB : IsMeasurableSet (S := S) B),
    COF.lt (measure1 S (hB A hA)) delta →
      COF.lt (IB.IMeas B hB n) eps

/-- Technical lemma used in the public import closure. -/
structure Lemma414UniformIBSourceData {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (IB : Lemma414IBInterface (S := S) fn hnn) (eps : R) : Type _ where
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 ≤ N
  delta : R
  delta_pos : COF.lt 0 delta
  small : ∀ n, N ≤ n → ∀ (B : BSet X) (hB : IsMeasurableSet (S := S) B),
    COF.lt (measure1 S (hB A hA)) delta →
      COF.lt (IB.IMeas B hB n) eps

/-- Technical lemma used in the public import closure. -/
def lemma_4_14_uniform_ib_data_from_source {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (IB : Lemma414IBInterface (S := S) fn hnn)
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBSourceData (S := S) fn hnn IB eps) :
    ∀ eps, COF.lt 0 eps → Lemma414UniformIBData (S := S) fn hnn IB eps := by
  intro eps heps
  let U := hui eps heps
  exact
    { A := U.A
      hA := U.hA
      N := U.N
      delta := U.delta
      delta_pos := U.delta_pos
      small := U.small }


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_uniform_complement_data_from_ib {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (IB : Lemma414IBInterface (S := S) fn hnn)
    (hui : ∀ eps, COF.lt 0 eps → Lemma414UniformIBData (S := S) fn hnn IB eps) :
    ∀ eps, COF.lt 0 eps → Lemma414UniformComplementData (S := S) fn hnn eps := by
  intro eps heps
  let U := hui eps heps
  exact
    { A := U.A
      hA := U.hA
      N := U.N
      delta := U.delta
      delta_pos := U.delta_pos
      small := by
        intro n hn C hC hmeasure
        let B : BSet X := BSet.neg C
        let hB : IsMeasurableSet (S := S) B :=
          isMeasurableSet_neg_of_integrable (S := S) hC
        have hsmall : COF.lt (IB.IMeas B hB n) eps := by
          exact U.small n hn B hB hmeasure
        have heq := IB.complement_eq n C hC
        simpa [B, hB, heq] using hsmall }


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_ib_and_rep_converge {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (IB : Lemma414IBInterface (S := S) fn hnn)
    (hui : ∀ eps, COF.lt 0 eps → Lemma414UniformIBData (S := S) fn hnn IB eps)
    (hconv : Lemma414RepConvergeToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_uniform_and_rep_converge fn hnn
    (lemma_4_14_uniform_complement_data_from_ib fn hnn IB hui) hconv


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_ib_and_pfun_converge {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (IB : Lemma414IBInterface (S := S) fn hnn)
    (hui : ∀ eps, COF.lt 0 eps → Lemma414UniformIBData (S := S) fn hnn IB eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_rep_converge fn hnn IB hui
    (lemma_4_14_rep_converge_from_pfun_converge_zero fn hnn pfn zero hconv hzero hrep)


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_genIB_and_rep_converge {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hV : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB fn hnn hV) eps)
    (hconv : Lemma414RepConvergeToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_rep_converge fn hnn
    (lemma_4_14_ib_interface_from_genIB fn hnn hV) hui hconv


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_genIB_and_pfun_converge {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (hV : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB fn hnn hV) eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_pfun_converge
    fn hnn pfn zero
    (lemma_4_14_ib_interface_from_genIB fn hnn hV)
    hui hconv hzero hrep


/-- Direct measurable `I_{-C}` agrees with the previous complement expression,
  provided the Phase2 `remainingAtoms` package for the integrand. -/
theorem sec4_genRelIntegral_eq_complement_of_remainingAtoms
    {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    genRelIntegral_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn =
      (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral :=
  sec4_genRelIntegral_eq_complement_of_valueBridge C hC f hnn
    (sec4_genIBValueBridge_of_remainingAtoms
      (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC)
      f hnn T)


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_ib_interface_from_genIB_remainingAtoms
    {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hAtoms : ∀ n, Sec4Prop42RemainingAtomTools (S := S) (fn n) (hnn n)) :
    Lemma414IBInterface (S := S) fn hnn :=
  lemma_4_14_ib_interface_from_genIB fn hnn
    (fun n C hC =>
      sec4_genIBValueBridge_of_remainingAtoms
        (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC)
        (fn n) (hnn n) (hAtoms n))


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_remainingAtoms_and_rep_converge
    {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hAtoms : ∀ n, Sec4Prop42RemainingAtomTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn hAtoms) eps)
    (hconv : Lemma414RepConvergeToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_rep_converge fn hnn
    (lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn hAtoms)
    hui hconv


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_remainingAtoms_and_pfun_converge
    {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (hAtoms : ∀ n, Sec4Prop42RemainingAtomTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn hAtoms) eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_pfun_converge
    fn hnn pfn zero
    (lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn hAtoms)
    hui hconv hzero hrep


/-- Direct measurable `I_{-C}` agrees with the previous complement expression,
  provided the Phase2 row-seed package for the integrand. -/
theorem sec4_genRelIntegral_eq_complement_of_rowSeedTools
    {S : IntSpaceRC X R}
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    genRelIntegral_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn =
      (f.sub (prop_4_2_chi_f_rep C hC f hnn)).integral :=
  sec4_genRelIntegral_eq_complement_of_remainingAtoms C hC f hnn
    (sec4_remainingAtoms_of_rowSeedTools f hnn T)


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_ib_interface_from_genIB_rowSeedTools
    {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hSeeds : ∀ n, Sec4Prop42RowSeedTools (S := S) (fn n) (hnn n)) :
    Lemma414IBInterface (S := S) fn hnn :=
  lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn
    (fun n => sec4_remainingAtoms_of_rowSeedTools (fn n) (hnn n) (hSeeds n))


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_rowSeedTools_and_rep_converge
    {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hSeeds : ∀ n, Sec4Prop42RowSeedTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_rowSeedTools fn hnn hSeeds) eps)
    (hconv : Lemma414RepConvergeToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_rep_converge fn hnn
    (lemma_4_14_ib_interface_from_genIB_rowSeedTools fn hnn hSeeds)
    hui hconv


/-- Technical lemma used in the public import closure. -/
noncomputable def lemma_4_14_tendsto_zero_from_rowSeedTools_and_pfun_converge
    {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (hSeeds : ∀ n, Sec4Prop42RowSeedTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_rowSeedTools fn hnn hSeeds) eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_pfun_converge
    fn hnn pfn zero
    (lemma_4_14_ib_interface_from_genIB_rowSeedTools fn hnn hSeeds)
    hui hconv hzero hrep


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_faithful {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (IB : Lemma414IBInterface (S := S) fn hnn)
    (hui : ∀ eps, COF.lt 0 eps → Lemma414UniformIBData (S := S) fn hnn IB eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_pfun_converge
    fn hnn pfn zero IB hui hconv hzero hrep


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_source_complete {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (IB : Lemma414IBInterface (S := S) fn hnn)
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBSourceData (S := S) fn hnn IB eps)
    (hconv : Lemma414ConvergeInMeasureToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_ib_and_rep_converge fn hnn IB
    (lemma_4_14_uniform_ib_data_from_source fn hnn IB hui)
    (lemma_4_14_rep_converge_from_source_measure_converge_zero fn hnn hconv)


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_faithful_from_genIB {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (hV : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB fn hnn hV) eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_genIB_and_pfun_converge
    fn hnn pfn zero hV hui hconv hzero hrep


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_source_complete_from_genIB {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hV : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBSourceData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB fn hnn hV) eps)
    (hconv : Lemma414ConvergeInMeasureToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  thm_4_14_source_complete fn hnn
    (lemma_4_14_ib_interface_from_genIB fn hnn hV) hui hconv


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_faithful_from_remainingAtoms {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (hAtoms : ∀ n, Sec4Prop42RemainingAtomTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn hAtoms) eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_remainingAtoms_and_pfun_converge
    fn hnn pfn zero hAtoms hui hconv hzero hrep


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_source_complete_from_remainingAtoms {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hAtoms : ∀ n, Sec4Prop42RemainingAtomTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBSourceData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn hAtoms) eps)
    (hconv : Lemma414ConvergeInMeasureToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  thm_4_14_source_complete fn hnn
    (lemma_4_14_ib_interface_from_genIB_remainingAtoms fn hnn hAtoms) hui hconv


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_faithful_from_rowSeedTools {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (pfn : Nat → PFunR X R) (zero : PFunR X R)
    (hSeeds : ∀ n, Sec4Prop42RowSeedTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_rowSeedTools fn hnn hSeeds) eps)
    (hconv : Lemma414PFunConvergeToZeroData (S := S) pfn zero)
    (hzero : Lemma414ZeroPFunR zero)
    (hrep : ∀ n, Lemma414RepresentsPFunR (S := S) (fn n) (pfn n)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  lemma_4_14_tendsto_zero_from_rowSeedTools_and_pfun_converge
    fn hnn pfn zero hSeeds hui hconv hzero hrep


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_4_14_source_complete_from_rowSeedTools {S : IntSpaceRC X R}
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hSeeds : ∀ n, Sec4Prop42RowSeedTools (S := S) (fn n) (hnn n))
    (hui : ∀ eps, COF.lt 0 eps →
      Lemma414UniformIBSourceData (S := S) fn hnn
        (lemma_4_14_ib_interface_from_genIB_rowSeedTools fn hnn hSeeds) eps)
    (hconv : Lemma414ConvergeInMeasureToZeroData (S := S) fn) :
    RSeq.TendstoHalf (fun n => (fn n).integral) 0 :=
  thm_4_14_source_complete fn hnn
    (lemma_4_14_ib_interface_from_genIB_rowSeedTools fn hnn hSeeds) hui hconv


end BishopC
