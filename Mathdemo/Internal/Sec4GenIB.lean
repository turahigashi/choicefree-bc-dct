import Mathdemo.Internal.BishopSec4_Convergence

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
noncomputable def coverApart {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) :
    Thm36B1ApartPointData
      (lemma35_exceptionSeq
        (thm36A2_profile f (COF.halfPow (k+1)) (COF.halfPow k)
          (halfPow_lt_succ k) (halfPow_pos (k+1))))
      (COF.halfPow (k+1)) (COF.halfPow k) (halfPow_lt_succ k) :=
  thm36B1_apartPointData _ (halfPow_lt_succ k)

/-- Technical lemma used in the public import closure. -/
noncomputable def coverSet {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) : BSet X :=
  thm36D_levelBSet f (coverApart f k).t

/-- Technical lemma used in the public import closure. -/
noncomputable def coverSet_int {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (coverSet f k) :=
  (thm_3_6_forall_apart_measure f (COF.halfPow (k+1)) (COF.halfPow k)
    (halfPow_lt_succ k) (halfPow_pos (k+1))
    (coverApart f k).t (coverApart f k).a_lt (coverApart f k).lt_b (coverApart f k).apart).1

-- Technical note.

/-- Technical lemma used in the public import closure. -/
theorem coverApart_decr {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) :
    COF.lt (coverApart f (k+1)).t (coverApart f k).t :=
  COFO.lt_trans (coverApart f (k+1)).lt_b (coverApart f k).a_lt

/-- Technical lemma used in the public import closure. -/
theorem coverSet_mono {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) :
    (coverSet f k).S1 ⊆ (coverSet f (k+1)).S1 := by
  intro x hx
  obtain ⟨hdom, habs, hsum, hle⟩ := hx
  exact ⟨hdom, habs, hsum, le_trans (le_of_lt (coverApart_decr f k)) hle⟩


/-- Technical lemma used in the public import closure. -/
theorem coverApart_t_pos {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) :
    COF.lt 0 (coverApart f k).t :=
  COFO.lt_trans (halfPow_pos (k+1)) (coverApart f k).a_lt

/-- Technical lemma used in the public import closure. -/
theorem coverApart_t_nonneg {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) :
    ¬ COF.lt (coverApart f k).t 0 :=
  fun h => COF.lt_irrefl _ (COFO.lt_trans (coverApart_t_pos f k) h)

/-- Technical lemma used in the public import closure. -/
theorem coverApart_t_le_halfPow {S : IntSpaceRC X R} (f : IntegrableRep S) (k : Nat) :
    ¬ COF.lt (COF.halfPow k) (coverApart f k).t :=
  fun h => COF.lt_irrefl _ (COFO.lt_trans (coverApart f k).lt_b h)

/-- Technical lemma used in the public import closure. -/
theorem coverSet_approx_le {S : IntSpaceRC X R} (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) :
    Le (f.sub (f.cutConstVal (coverApart f k).t (coverApart_t_nonneg f k))).integral
       (relIntegral (coverSet f k) (coverSet_int f k) f hnn) := by
  show Le (f.sub (f.cutConstVal (coverApart f k).t (coverApart_t_nonneg f k))).integral
          (prop_4_2_chi_f_rep (coverSet f k) (coverSet_int f k) f hnn).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter
      (f.sub (f.cutConstVal (coverApart f k).t (coverApart_t_nonneg f k))).domain_isFull
      (prop_4_2_chi_f_rep (coverSet f k) (coverSet_int f k) f hnn).domain_isFull)
      f.domain_isFull) (coverSet_int f k).rep.domain_isFull) _ _ ?_
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨⟨_hxLk, hxchi⟩, hxf⟩, hxχ⟩ := hx
  obtain ⟨hflatDom, ⟨hflatabs⟩⟩ := hxchi
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχDom, ⟨hχabs⟩⟩ := hxχ
  have hval := prop_4_2_chi_f_rep_value
    (coverSet f k) (coverSet_int f k) f hnn
      hflatDom hχDom hfDom hflatabs hχabs hfabs
  let hcutDom := f.mem_cutConstVal_dom
    (coverApart f k).t (coverApart_t_nonneg f k) hfDom
  let hnegCutDom := IntegrableRep.neg_memAt hcutDom
  obtain ⟨hcut, hcuteq⟩ :=
    f.cutConstVal_signed_value (coverApart f k).t (coverApart_t_nonneg f k)
      x hfDom (seriesSum_of_abs hfabs)
  rw [seriesSum_unique hr
        (add_seriesSum_value hfDom hnegCutDom (seriesSum_of_abs hfabs)
          (neg_seriesSum_value hcutDom hcut)),
      seriesSum_unique hr' (seriesSum_of_abs hflatabs), hval]
  show Le ((seriesSum_of_abs hfabs).sum + (-(hcut.sum)))
          ((seriesSum_of_abs hχabs).sum * (seriesSum_of_abs hfabs).sum)
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  rcases ((coverSet_int f k).valid x hχDom hχabs).1 with hS1 | hS2
  · -- χ = 1, min ≥ 0
    rw [((coverSet_int f k).valid x hχDom hχabs).2.1
      hS1 (seriesSum_of_abs hχabs), one_mul, hcuteq]
    refine le_of_nonneg_sub ?_
    rw [show (seriesSum_of_abs hfabs).sum
          - ((seriesSum_of_abs hfabs).sum + (-(COF.min (seriesSum_of_abs hfabs).sum (coverApart f k).t)))
          = COF.min (seriesSum_of_abs hfabs).sum (coverApart f k).t from by ring]
    exact le_min hfnn (coverApart_t_nonneg f k)
  · -- χ = 0, min = hf.sum (hf.sum < t_k)
    rw [((coverSet_int f k).valid x hχDom hχabs).2.2
      hS2 (seriesSum_of_abs hχabs), zero_mul, hcuteq]
    obtain ⟨_hfDom2, _hfabs2, hxf2, hlt⟩ := hS2
    rw [seriesSum_unique hxf2 (seriesSum_of_abs hfabs)] at hlt
    rw [min_eq_left_of_le (le_of_lt hlt)]
    rw [show (seriesSum_of_abs hfabs).sum + (-((seriesSum_of_abs hfabs).sum)) = (0:R) from by ring]
    exact le_refl 0


/-- Technical lemma used in the public import closure. -/
noncomputable def coverSet_tendsto {S : IntSpaceRC X R} (f : IntegrableRep S) (hnn : RepNonneg f) :
    RSeq.TendstoHalf (fun k => relIntegral (coverSet f k) (coverSet_int f k) f hnn) f.integral := by
  have hz := lemma_4_3_cut_tendsto_zero f hnn (fun k => (coverApart f k).t)
    (fun k => coverApart_t_nonneg f k) (fun k => coverApart_t_le_halfPow f k)
  exact {
    mod := hz.mod
    close := by
      intro k n hn
      have h_close := hz.close k n hn
      have hub : Le (relIntegral (coverSet f n) (coverSet_int f n) f hnn) f.integral :=
        relIntegral_le_integral (coverSet f n) (coverSet_int f n) f hnn
      have hlb : Le (f.integral
            - (f.cutConstVal (coverApart f n).t (coverApart_t_nonneg f n)).integral)
            (relIntegral (coverSet f n) (coverSet_int f n) f hnn) := by
        have h := coverSet_approx_le f hnn n
        rwa [IntegrableRep.integral_sub] at h
      -- f.integral − relIntegral ≤ I(cutConst t_n)
      have hdiff : Le (f.integral - relIntegral (coverSet f n) (coverSet_int f n) f hnn)
            (f.cutConstVal (coverApart f n).t (coverApart_t_nonneg f n)).integral := by
        refine le_of_nonneg_sub ?_
        rw [show (f.cutConstVal (coverApart f n).t (coverApart_t_nonneg f n)).integral
              - (f.integral - relIntegral (coverSet f n) (coverSet_int f n) f hnn)
            = relIntegral (coverSet f n) (coverSet_int f n) f hnn
              - (f.integral - (f.cutConstVal (coverApart f n).t (coverApart_t_nonneg f n)).integral)
            from by ring]
        exact nonneg_sub_of_le hlb
      -- |relIntegral − f.integral| = f.integral − relIntegral
      have habs_eq : COF.abs (relIntegral (coverSet f n) (coverSet_int f n) f hnn - f.integral)
            = f.integral - relIntegral (coverSet f n) (coverSet_int f n) f hnn := by
        rw [show relIntegral (coverSet f n) (coverSet_int f n) f hnn - f.integral
              = -(f.integral - relIntegral (coverSet f n) (coverSet_int f n) f hnn) from by ring,
            COFO.abs_neg, COFO.abs_of_nonneg (nonneg_sub_of_le hub)]
      change COF.lt (COF.abs ((f.cutConstVal (coverApart f n).t (coverApart_t_nonneg f n)).integral - 0))
        (COF.halfPow k) at h_close
      rw [show ((f.cutConstVal (coverApart f n).t (coverApart_t_nonneg f n)).integral - 0 : R)
            = (f.cutConstVal (coverApart f n).t (coverApart_t_nonneg f n)).integral from by ring] at h_close
      change COF.lt (COF.abs (relIntegral (coverSet f n) (coverSet_int f n) f hnn - f.integral))
        (COF.halfPow k)
      rw [habs_eq]
      exact lt_of_le_of_lt (le_trans hdiff (COFO.le_abs_self _)) h_close
  }


end BishopC
