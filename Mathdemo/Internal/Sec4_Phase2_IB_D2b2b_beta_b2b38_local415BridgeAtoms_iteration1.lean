import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b37_localGenIBBridge_iteration1

/-!
# Sec4 Phase2-D2b2b_beta-b2b38: local bridge atoms for theorem 4.15

The source-complete 4.15 file still contains several downstream estimates
phrased with the previous global `Sec4GenIBValueBridge`.  This file reproves the
same estimates from `Sec4GenIBLocalValueBridge`, keeping the calculations on a
common full support where the relevant pointwise witnesses are already present.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Direct measurable integral: monotonicity in the integrand -/

/-- Local-bridge version of direct measurable integrand monotonicity.

The pointwise comparison is unchanged from the previous global-bridge proof; the
only difference is that the bridge is applied to explicit local witnesses built
from the full support used by `prop_1_11`. -/
theorem genRelIntegral_from_measurable_mono_integrand_of_localBridges
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Vu : Sec4GenIBLocalValueBridge (S := S) B hB u hnn_u)
    (Vv : Sec4GenIBLocalValueBridge (S := S) B hB v hnn_v)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable B hB u hnn_u)
      (genRelIntegral_from_measurable B hB v hnn_v) := by
  unfold genRelIntegral_from_measurable
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull (genIB_rep_from_measurable B hB u hnn_u))
      (IntegrableRep.domain_isFull (genIB_rep_from_measurable B hB v hnn_v)))
      u.domain_isFull) v.domain_isFull)
    (genIB_rep_from_measurable B hB u hnn_u)
    (genIB_rep_from_measurable B hB v hnn_v) ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨hxgenU, hxgenV⟩, hxu⟩, hxv⟩ := hx
  obtain ⟨hgenUDom, ⟨hgenUabs⟩⟩ := hxgenU
  obtain ⟨hgenVDom, ⟨hgenVabs⟩⟩ := hxgenV
  obtain ⟨huDom, ⟨huabs⟩⟩ := hxu
  obtain ⟨hvDom, ⟨hvabs⟩⟩ := hxv
  let Wu : Sec4GenIBLocalWitness (S := S) B hB u hnn_u x := {
    gen_dom := hgenUDom
    gen_abs := hgenUabs
    f_dom := huDom
    f_abs := huabs
  }
  let Wv : Sec4GenIBLocalWitness (S := S) B hB v hnn_v x := {
    gen_dom := hgenVDom
    gen_abs := hgenVabs
    f_dom := hvDom
    f_abs := hvabs
  }
  let hu : RSeq.SeriesSum (fun n => (u.fn n).toFun x) :=
    seriesSum_of_abs huabs
  let hv : RSeq.SeriesSum (fun n => (v.fn n).toFun x) :=
    seriesSum_of_abs hvabs
  have hgenU_sum :
      hr.sum = (seriesSum_of_abs hgenUabs).sum :=
    seriesSum_unique hr (seriesSum_of_abs hgenUabs)
  have hgenV_sum :
      hr'.sum = (seriesSum_of_abs hgenVabs).sum :=
    seriesSum_unique hr' (seriesSum_of_abs hgenVabs)
  have huv_le : Le hu.sum hv.sum := by
    have hsubAbs : RSeq.SeriesSum
        (fun n => COF.abs (((v.sub u).fn n).toFun x)) :=
      sec4_sub_absSeriesSum_fwd hvabs huabs
    have hnonneg : Nonneg (hv.sum + -hu.sum) := by
      let hsub : RSeq.SeriesSum (fun n => ((v.sub u).fn n).toFun x) :=
        add_seriesSum_value hv (neg_seriesSum_value hu)
      have h := hvu x hsubAbs hsub
      change Nonneg (hv.sum + -hu.sum) at h
      exact h
    exact le_of_nonneg_sub (by
      rw [show hv.sum - hu.sum = hv.sum + -hu.sum from by ring]
      exact hnonneg)
  rcases Vu.domain x Wu with hxB1 | hxB2
  · have hU : (seriesSum_of_abs hgenUabs).sum = hu.sum :=
      Vu.value_s1 x hxB1 Wu
    have hV : (seriesSum_of_abs hgenVabs).sum = hv.sum :=
      Vv.value_s1 x hxB1 Wv
    rw [hgenU_sum, hgenV_sum, hU, hV]
    exact huv_le
  · have hU : (seriesSum_of_abs hgenUabs).sum = 0 :=
      Vu.value_s2 x hxB2 Wu
    have hV : (seriesSum_of_abs hgenVabs).sum = 0 :=
      Vv.value_s2 x hxB2 Wv
    rw [hgenU_sum, hgenV_sum, hU, hV]
    exact le_refl _


/-! ## 2. Direct measurable integral: additivity in the integrand -/

/-- Local-bridge version of additivity for the direct general-measurable
relative integral. -/
theorem genRelIntegral_from_measurable_add_integrand_of_localBridges
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (u v : IntegrableRep S)
    (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (hnn_add : RepNonneg (u.add v))
    (Vu : Sec4GenIBLocalValueBridge (S := S) B hB u hnn_u)
    (Vv : Sec4GenIBLocalValueBridge (S := S) B hB v hnn_v)
    (Vadd : Sec4GenIBLocalValueBridge (S := S) B hB (u.add v) hnn_add) :
    genRelIntegral_from_measurable B hB (u.add v) hnn_add =
      genRelIntegral_from_measurable B hB u hnn_u +
        genRelIntegral_from_measurable B hB v hnn_v := by
  unfold genRelIntegral_from_measurable
  rw [← IntegrableRep.integral_add]
  refine cor_1_12
    (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull
        (genIB_rep_from_measurable B hB (u.add v) hnn_add))
      (IntegrableRep.domain_isFull
        ((genIB_rep_from_measurable B hB u hnn_u).add
          (genIB_rep_from_measurable B hB v hnn_v))))
      (IntegrableRep.domain_isFull (u.add v)))
    (genIB_rep_from_measurable B hB (u.add v) hnn_add)
    ((genIB_rep_from_measurable B hB u hnn_u).add
      (genIB_rep_from_measurable B hB v hnn_v)) ?_
  intro x hx hgenAdd hgenSum
  obtain ⟨⟨hxgenAdd, hxgenSum⟩, hxuv⟩ := hx
  obtain ⟨hgenAddDom, ⟨hgenAddAbs⟩⟩ := hxgenAdd
  obtain ⟨hgenSumDom, ⟨hgenSumAbs⟩⟩ := hxgenSum
  obtain ⟨huvDom, ⟨huvAbs⟩⟩ := hxuv
  have huAbs : RSeq.SeriesSum (fun k => COF.abs ((u.fn k).toFun x)) :=
    add_absSeriesSum_left huvAbs
  have hvAbs : RSeq.SeriesSum (fun k => COF.abs ((v.fn k).toFun x)) :=
    add_absSeriesSum_right huvAbs
  have hgenUAbs : RSeq.SeriesSum
      (fun k => COF.abs (((genIB_rep_from_measurable B hB u hnn_u).fn k).toFun x)) :=
    add_absSeriesSum_left hgenSumAbs
  have hgenVAbs : RSeq.SeriesSum
      (fun k => COF.abs (((genIB_rep_from_measurable B hB v hnn_v).fn k).toFun x)) :=
    add_absSeriesSum_right hgenSumAbs
  let Wadd : Sec4GenIBLocalWitness (S := S) B hB (u.add v) hnn_add x := {
    gen_dom := hgenAddDom
    gen_abs := hgenAddAbs
    f_dom := huvDom
    f_abs := huvAbs
  }
  let Wu : Sec4GenIBLocalWitness (S := S) B hB u hnn_u x := {
    gen_dom := add_dom_left hgenSumDom
    gen_abs := hgenUAbs
    f_dom := add_dom_left huvDom
    f_abs := huAbs
  }
  let Wv : Sec4GenIBLocalWitness (S := S) B hB v hnn_v x := {
    gen_dom := add_dom_right hgenSumDom
    gen_abs := hgenVAbs
    f_dom := add_dom_right huvDom
    f_abs := hvAbs
  }
  let huSum : RSeq.SeriesSum (fun k => (u.fn k).toFun x) :=
    seriesSum_of_abs huAbs
  let hvSum : RSeq.SeriesSum (fun k => (v.fn k).toFun x) :=
    seriesSum_of_abs hvAbs
  let hgenUSum : RSeq.SeriesSum
      (fun k => ((genIB_rep_from_measurable B hB u hnn_u).fn k).toFun x) :=
    seriesSum_of_abs hgenUAbs
  let hgenVSum : RSeq.SeriesSum
      (fun k => ((genIB_rep_from_measurable B hB v hnn_v).fn k).toFun x) :=
    seriesSum_of_abs hgenVAbs
  have hgenSum_eq :
      hgenSum.sum = hgenUSum.sum + hgenVSum.sum :=
    seriesSum_unique hgenSum (add_seriesSum_value hgenUSum hgenVSum)
  rcases Vadd.domain x Wadd with hxB1 | hxB2
  · have hAddVal :
        (seriesSum_of_abs hgenAddAbs).sum =
          (seriesSum_of_abs huvAbs).sum :=
      Vadd.value_s1 x hxB1 Wadd
    have hUVal : hgenUSum.sum = huSum.sum :=
      Vu.value_s1 x hxB1 Wu
    have hVVal : hgenVSum.sum = hvSum.sum :=
      Vv.value_s1 x hxB1 Wv
    have huv_eq : (seriesSum_of_abs huvAbs).sum = huSum.sum + hvSum.sum :=
      seriesSum_unique (seriesSum_of_abs huvAbs)
        (add_seriesSum_value huSum hvSum)
    calc
      hgenAdd.sum = (seriesSum_of_abs hgenAddAbs).sum :=
        seriesSum_unique hgenAdd (seriesSum_of_abs hgenAddAbs)
      _ = (seriesSum_of_abs huvAbs).sum := hAddVal
      _ = huSum.sum + hvSum.sum := huv_eq
      _ = hgenUSum.sum + hgenVSum.sum := by rw [hUVal, hVVal]
      _ = hgenSum.sum := hgenSum_eq.symm
  · have hAddVal : (seriesSum_of_abs hgenAddAbs).sum = 0 :=
      Vadd.value_s2 x hxB2 Wadd
    have hUVal : hgenUSum.sum = 0 :=
      Vu.value_s2 x hxB2 Wu
    have hVVal : hgenVSum.sum = 0 :=
      Vv.value_s2 x hxB2 Wv
    calc
      hgenAdd.sum = (seriesSum_of_abs hgenAddAbs).sum :=
        seriesSum_unique hgenAdd (seriesSum_of_abs hgenAddAbs)
      _ = 0 := hAddVal
      _ = 0 + 0 := by ring
      _ = hgenUSum.sum + hgenVSum.sum := by rw [hUVal, hVVal]
      _ = hgenSum.sum := hgenSum_eq.symm


/-! ## 3. Mixed comparison with the ordinary relative integral -/

/-- Local-bridge version of the mixed comparison with ordinary `relIntegral`. -/
theorem genRelIntegral_from_measurable_le_relIntegral_of_localBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Vu : Sec4GenIBLocalValueBridge (S := S) C
      (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable C
        (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
      (relIntegral C hC v hnn_v) := by
  unfold genRelIntegral_from_measurable relIntegral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull
        (genIB_rep_from_measurable C
          (isMeasurableSet_of_integrable (S := S) hC) u hnn_u))
      (IntegrableRep.domain_isFull (prop_4_2_chi_f_rep C hC v hnn_v)))
      u.domain_isFull) v.domain_isFull) hC.rep.domain_isFull)
    (genIB_rep_from_measurable C
      (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
    (prop_4_2_chi_f_rep C hC v hnn_v) ?_
  intro x hx hgen hrel
  obtain ⟨⟨⟨⟨hxgen, hxrel⟩, hxu⟩, hxv⟩, hxχ⟩ := hx
  obtain ⟨hgenDom, ⟨hgenabs⟩⟩ := hxgen
  obtain ⟨_, ⟨hrelabs⟩⟩ := hxrel
  obtain ⟨huDom, ⟨huabs⟩⟩ := hxu
  obtain ⟨_, ⟨hvabs⟩⟩ := hxv
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  let W : Sec4GenIBLocalWitness
      (S := S) C (isMeasurableSet_of_integrable (S := S) hC) u hnn_u x := {
    gen_dom := hgenDom
    gen_abs := hgenabs
    f_dom := huDom
    f_abs := huabs
  }
  let hu : RSeq.SeriesSum (fun n => (u.fn n).toFun x) :=
    seriesSum_of_abs huabs
  let hv : RSeq.SeriesSum (fun n => (v.fn n).toFun x) :=
    seriesSum_of_abs hvabs
  have hgen_sum :
      hgen.sum = (seriesSum_of_abs hgenabs).sum :=
    seriesSum_unique hgen (seriesSum_of_abs hgenabs)
  have hrel_sum :
      hrel.sum = (seriesSum_of_abs hrelabs).sum :=
    seriesSum_unique hrel (seriesSum_of_abs hrelabs)
  have hrel_value :
      (seriesSum_of_abs hrelabs).sum =
        (seriesSum_of_abs hχabs).sum * hv.sum :=
    prop_4_2_chi_f_rep_value C hC v hnn_v hrelabs hχabs hvabs
  have huv_le : Le hu.sum hv.sum := by
    have hsubAbs : RSeq.SeriesSum
        (fun n => COF.abs (((v.sub u).fn n).toFun x)) :=
      sec4_sub_absSeriesSum_fwd hvabs huabs
    have hnonneg : Nonneg (hv.sum + -hu.sum) := by
      let hsub : RSeq.SeriesSum (fun n => ((v.sub u).fn n).toFun x) :=
        add_seriesSum_value hv (neg_seriesSum_value hu)
      have h := hvu x hsubAbs hsub
      change Nonneg (hv.sum + -hu.sum) at h
      exact h
    exact le_of_nonneg_sub (by
      rw [show hv.sum - hu.sum = hv.sum + -hu.sum from by ring]
      exact hnonneg)
  rcases Vu.domain x W with hxC1 | hxC2
  · have hgen_value :
        (seriesSum_of_abs hgenabs).sum = hu.sum :=
      Vu.value_s1 x hxC1 W
    have hχ_one :
        (seriesSum_of_abs hχabs).sum = 1 :=
      (hC.valid x hχabs).2.1 hxC1 (seriesSum_of_abs hχabs)
    rw [hgen_sum, hrel_sum, hgen_value, hrel_value, hχ_one, one_mul]
    exact huv_le
  · have hgen_value :
        (seriesSum_of_abs hgenabs).sum = 0 :=
      Vu.value_s2 x hxC2 W
    have hχ_zero :
        (seriesSum_of_abs hχabs).sum = 0 :=
      (hC.valid x hχabs).2.2 hxC2 (seriesSum_of_abs hχabs)
    rw [hgen_sum, hrel_sum, hgen_value, hrel_value, hχ_zero, zero_mul]
    exact le_refl _


/-! ## 4. Complement comparison -/

/-- Local-bridge version of the comparison for direct measurable `I_{-C}`. -/
theorem genRelIntegral_neg_le_complementIntegral_of_localBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Vu : Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
      ((v.sub (prop_4_2_chi_f_rep C hC v hnn_v)).integral) := by
  unfold genRelIntegral_from_measurable
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull
        (genIB_rep_from_measurable (BSet.neg C)
          (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u))
      (IntegrableRep.domain_isFull
        (v.sub (prop_4_2_chi_f_rep C hC v hnn_v))))
      (IntegrableRep.domain_isFull (prop_4_2_chi_f_rep C hC v hnn_v)))
      (IntegrableRep.domain_isFull hC.rep))
      (isFull_inter (IntegrableRep.domain_isFull u)
        (IntegrableRep.domain_isFull v)))
    (genIB_rep_from_measurable (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
    (v.sub (prop_4_2_chi_f_rep C hC v hnn_v)) ?_
  intro x hx hgen hcomp
  obtain ⟨⟨⟨⟨hxgen, hxcomp⟩, hxchiF⟩, hxχ⟩, hxuv⟩ := hx
  obtain ⟨hxu, hxv⟩ := hxuv
  obtain ⟨hgenDom, ⟨hgenabs⟩⟩ := hxgen
  obtain ⟨_, ⟨_hcompabs⟩⟩ := hxcomp
  obtain ⟨_, ⟨hchiFabs⟩⟩ := hxchiF
  obtain ⟨_, ⟨hχabs⟩⟩ := hxχ
  obtain ⟨huDom, ⟨huabs⟩⟩ := hxu
  obtain ⟨_, ⟨hvabs⟩⟩ := hxv
  let W : Sec4GenIBLocalWitness
      (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u x := {
    gen_dom := hgenDom
    gen_abs := hgenabs
    f_dom := huDom
    f_abs := huabs
  }
  let hu : RSeq.SeriesSum (fun n => (u.fn n).toFun x) :=
    seriesSum_of_abs huabs
  let hv : RSeq.SeriesSum (fun n => (v.fn n).toFun x) :=
    seriesSum_of_abs hvabs
  let hcompValue :=
    add_seriesSum_value hv (neg_seriesSum_value (seriesSum_of_abs hchiFabs))
  have hcomp_value :
      hcompValue.sum =
        (1 - (seriesSum_of_abs hχabs).sum) * hv.sum :=
    prop_4_2_complement_value C hC v hnn_v hchiFabs hχabs hvabs
  have hgen_sum :
      hgen.sum = (seriesSum_of_abs hgenabs).sum :=
    seriesSum_unique hgen (seriesSum_of_abs hgenabs)
  have hcomp_sum :
      hcomp.sum = hcompValue.sum :=
    seriesSum_unique hcomp hcompValue
  have huv_le : Le hu.sum hv.sum := by
    have hsubAbs : RSeq.SeriesSum
        (fun n => COF.abs (((v.sub u).fn n).toFun x)) :=
      sec4_sub_absSeriesSum_fwd hvabs huabs
    have hnonneg : Nonneg (hv.sum + -hu.sum) := by
      let hsub : RSeq.SeriesSum (fun n => ((v.sub u).fn n).toFun x) :=
        add_seriesSum_value hv (neg_seriesSum_value hu)
      have h := hvu x hsubAbs hsub
      change Nonneg (hv.sum + -hu.sum) at h
      exact h
    exact le_of_nonneg_sub (by
      rw [show hv.sum - hu.sum = hv.sum + -hu.sum from by ring]
      exact hnonneg)
  rcases (hC.valid x hχabs).1 with hxC1 | hxC2
  · have hχ_one :
        (seriesSum_of_abs hχabs).sum = 1 :=
      (hC.valid x hχabs).2.1 hxC1 (seriesSum_of_abs hχabs)
    have hgen_value :
        (seriesSum_of_abs hgenabs).sum = 0 :=
      Vu.value_s2 x (by simpa [BSet.neg] using hxC1) W
    rw [hgen_sum, hcomp_sum, hgen_value, hcomp_value, hχ_one]
    ring_nf
    exact le_refl _
  · have hχ_zero :
        (seriesSum_of_abs hχabs).sum = 0 :=
      (hC.valid x hχabs).2.2 hxC2 (seriesSum_of_abs hχabs)
    have hgen_value :
        (seriesSum_of_abs hgenabs).sum = hu.sum :=
      Vu.value_s1 x (by simpa [BSet.neg] using hxC2) W
    rw [hgen_sum, hcomp_sum, hgen_value, hcomp_value, hχ_zero]
    ring_nf
    exact huv_le


/-! ## 5. Source split inequality with local bridges -/

/-- Local-bridge version of the pointwise source inequality
`chi_B u <= chi_{A and B} u + chi_{-A} u`. -/
theorem thm_4_15_genIB_split_le_on_support_of_localBridges
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u)
    (VB : Sec4GenIBLocalValueBridge (S := S) B hB u hnn)
    (VAB : Sec4GenIBLocalValueBridge (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
    (VnegA : Sec4GenIBLocalValueBridge (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn) :
    ∀ x ∈ thm_4_15_ib_split_support (S := S) A B hA hB u hnn,
      ∀ (hleft : RSeq.SeriesSum
        (fun n => ((genIB_rep_from_measurable B hB u hnn).fn n).toFun x))
        (hright : RSeq.SeriesSum
        (fun n =>
          (((genIB_rep_from_measurable (BSet.and A B)
              (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn).add
            (genIB_rep_from_measurable (BSet.neg A)
              (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)).fn n).toFun x)),
        Le hleft.sum hright.sum := by
  intro x hx hleft hright
  rcases hx with ⟨⟨⟨⟨hBDom, hABDom⟩, hNegDom⟩, hADom⟩, huDom⟩
  rcases hBDom with ⟨hBDomAll, ⟨hBabs⟩⟩
  rcases hABDom with ⟨hABDomAll, ⟨hABabs⟩⟩
  rcases hNegDom with ⟨hNegDomAll, ⟨hNegabs⟩⟩
  rcases hADom with ⟨_, ⟨hAabs⟩⟩
  rcases huDom with ⟨huDomAll, ⟨huabs⟩⟩
  let WB : Sec4GenIBLocalWitness (S := S) B hB u hnn x := {
    gen_dom := hBDomAll
    gen_abs := hBabs
    f_dom := huDomAll
    f_abs := huabs
  }
  let WAB : Sec4GenIBLocalWitness (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn x := {
    gen_dom := hABDomAll
    gen_abs := hABabs
    f_dom := huDomAll
    f_abs := huabs
  }
  let WnegA : Sec4GenIBLocalWitness (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn x := {
    gen_dom := hNegDomAll
    gen_abs := hNegabs
    f_dom := huDomAll
    f_abs := huabs
  }
  let hBsum : RSeq.SeriesSum
      (fun n => ((genIB_rep_from_measurable B hB u hnn).fn n).toFun x) :=
    seriesSum_of_abs hBabs
  let hABsum : RSeq.SeriesSum
      (fun n => ((genIB_rep_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn).fn n).toFun x) :=
    seriesSum_of_abs hABabs
  let hNegsum : RSeq.SeriesSum
      (fun n => ((genIB_rep_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn).fn n).toFun x) :=
    seriesSum_of_abs hNegabs
  have hleft_eq : hleft.sum = hBsum.sum :=
    seriesSum_unique hleft hBsum
  have hright_eq : hright.sum = hABsum.sum + hNegsum.sum :=
    seriesSum_unique hright (add_seriesSum_value hABsum hNegsum)
  have hAB_nonneg : Nonneg hABsum.sum :=
    genIB_rep_from_measurable_repNonneg
      (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA))
      u hnn x hABabs hABsum
  have hNeg_nonneg : Nonneg hNegsum.sum :=
    genIB_rep_from_measurable_repNonneg
      (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA)
      u hnn x hNegabs hNegsum
  have hBcases := VB.domain x WB
  have hAcases := (hA.valid x hAabs).1
  cases hBcases with
  | inl hxB1 =>
      have hB_value : hBsum.sum = (seriesSum_of_abs huabs).sum :=
        VB.value_s1 x hxB1 WB
      cases hAcases with
      | inl hxA1 =>
          have hAB_value : hABsum.sum = (seriesSum_of_abs huabs).sum :=
            VAB.value_s1 x ⟨hxA1, hxB1⟩ WAB
          rw [hleft_eq, hright_eq, hB_value, hAB_value]
          exact le_of_nonneg_sub (by
            rw [show ((seriesSum_of_abs huabs).sum + hNegsum.sum
                  - (seriesSum_of_abs huabs).sum) = hNegsum.sum from by ring]
            exact hNeg_nonneg)
      | inr hxA2 =>
          have hNeg_value : hNegsum.sum = (seriesSum_of_abs huabs).sum :=
            VnegA.value_s1 x hxA2 WnegA
          rw [hleft_eq, hright_eq, hB_value, hNeg_value]
          exact le_of_nonneg_sub (by
            rw [show (hABsum.sum + (seriesSum_of_abs huabs).sum
                  - (seriesSum_of_abs huabs).sum) = hABsum.sum from by ring]
            exact hAB_nonneg)
  | inr hxB2 =>
      have hB_value : hBsum.sum = 0 :=
        VB.value_s2 x hxB2 WB
      rw [hleft_eq, hright_eq, hB_value]
      exact le_of_nonneg_sub (by
        rw [sub_zero]
        exact nonneg_add hAB_nonneg hNeg_nonneg)


/-- Local-bridge version of the integral split inequality
`I_B(u) <= I_{A and B}(u) + I_{-A}(u)`. -/
theorem thm_4_15_genIB_split_le_of_localBridges
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u)
    (VB : Sec4GenIBLocalValueBridge (S := S) B hB u hnn)
    (VAB : Sec4GenIBLocalValueBridge (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
    (VnegA : Sec4GenIBLocalValueBridge (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn) :
    Le
      (genRelIntegral_from_measurable B hB u hnn)
      (genRelIntegral_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn
        + genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn) := by
  unfold genRelIntegral_from_measurable
  rw [← IntegrableRep.integral_add]
  exact prop_1_11
    (thm_4_15_ib_split_support_full (S := S) A B hA hB u hnn)
    (genIB_rep_from_measurable B hB u hnn)
    ((genIB_rep_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn).add
      (genIB_rep_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn))
    (thm_4_15_genIB_split_le_on_support_of_localBridges
      (S := S) A B hA hB u hnn VB VAB VnegA)


/-- Local-bridge strict split estimate from small right-hand pieces. -/
theorem thm_4_15_genIB_split_lt_of_piece_bounds_localBridges
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u)
    (VB : Sec4GenIBLocalValueBridge (S := S) B hB u hnn)
    (VAB : Sec4GenIBLocalValueBridge (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
    (VnegA : Sec4GenIBLocalValueBridge (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
    (epsAB epsNeg eps : R)
    (hAB : COF.lt
      (genRelIntegral_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
      epsAB)
    (hNeg : COF.lt
      (genRelIntegral_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
      epsNeg)
    (hsum : COF.lt (epsAB + epsNeg) eps) :
    COF.lt (genRelIntegral_from_measurable B hB u hnn) eps := by
  have hsplit :=
    thm_4_15_genIB_split_le_of_localBridges
      (S := S) A B hA hB u hnn VB VAB VnegA
  have hpieces : COF.lt
      (genRelIntegral_from_measurable (BSet.and A B)
          (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn
        + genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
      (epsAB + epsNeg) :=
    lt_add hAB hNeg
  exact COFO.lt_trans (lt_of_le_of_lt hsplit hpieces) hsum


end BishopC
