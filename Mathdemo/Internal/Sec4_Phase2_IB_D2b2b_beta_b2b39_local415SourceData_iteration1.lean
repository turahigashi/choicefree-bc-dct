import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b38_local415BridgeAtoms_iteration1

/-!
# Sec4 Phase2-D2b2b_beta-b2b39: local source data for 4.14/4.15

This file removes another global-bridge dependency from the theorem-4.15 route.
The `Lemma414IBInterface` only needs complement consistency for `I_{-C}`; here
that consistency is built from `Sec4GenIBLocalValueBridge`, i.e. from explicit
full-set witnesses.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Complement consistency from local value bridges -/

/-- Local-bridge version of the pointwise equality between direct `I_{-C}` and
the previous complement representative. -/
theorem sec4_genIB_complement_value_eq_subRep_on_support_of_localBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn) :
    ∀ x ∈ Sec4ComplementConsistencySupport (S := S) C hC f hnn,
      ∀ (hgen : RSeq.SeriesSum
        (fun n => ((genIB_rep_from_measurable (BSet.neg C)
          (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn).fn n).toFun x))
        (hcomp : RSeq.SeriesSum
        (fun n => (((f.sub (prop_4_2_chi_f_rep C hC f hnn)).fn n).toFun x))),
        hgen.sum = hcomp.sum := by
  intro x hx hgen hcomp
  rcases hx with ⟨⟨⟨⟨hgenDom, hcompDom⟩, hchiFDom⟩, hχDom⟩, hfDom⟩
  rcases hgenDom with ⟨hgenDomAll, ⟨hgenabs⟩⟩
  rcases hcompDom.2 with ⟨_hcompabs⟩
  rcases hchiFDom.2 with ⟨hchiFabs⟩
  rcases hχDom.2 with ⟨hχabs⟩
  rcases hfDom with ⟨hfDomAll, ⟨hfabs⟩⟩
  let W : Sec4GenIBLocalWitness
      (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) f hnn x := {
    gen_dom := hgenDomAll
    gen_abs := hgenabs
    f_dom := hfDomAll
    f_abs := hfabs
  }
  let hcompValue :=
    add_seriesSum_value (seriesSum_of_abs hfabs)
      (neg_seriesSum_value (seriesSum_of_abs hchiFabs))
  have hcomp_value :
      hcompValue.sum =
        (1 - (seriesSum_of_abs hχabs).sum) *
          (seriesSum_of_abs hfabs).sum :=
    prop_4_2_complement_value C hC f hnn hchiFabs hχabs hfabs
  have hχvalid := hC.valid x hχabs
  cases hχvalid.1 with
  | inl hxC1 =>
      have hχ_one :
          (seriesSum_of_abs hχabs).sum = 1 :=
        hχvalid.2.1 hxC1 (seriesSum_of_abs hχabs)
      have hgen_value :
          (seriesSum_of_abs hgenabs).sum = 0 :=
        V.value_s2 x (by simpa [BSet.neg] using hxC1) W
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
        V.value_s1 x (by simpa [BSet.neg] using hxC2) W
      calc
        hgen.sum = (seriesSum_of_abs hgenabs).sum :=
          seriesSum_unique hgen (seriesSum_of_abs hgenabs)
        _ = (seriesSum_of_abs hfabs).sum := hgen_value
        _ = (1 - 0) * (seriesSum_of_abs hfabs).sum := by ring
        _ = (1 - (seriesSum_of_abs hχabs).sum) *
            (seriesSum_of_abs hfabs).sum := by rw [hχ_zero]
        _ = hcompValue.sum := hcomp_value.symm
        _ = hcomp.sum := (seriesSum_unique hcomp hcompValue).symm


/-- Direct measurable `I_{-C}` agrees with the previous complement expression from a
local complement bridge. -/
theorem sec4_genRelIntegral_eq_complement_of_localValueBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (V : Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
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
    (sec4_genIB_complement_value_eq_subRep_on_support_of_localBridge
      C hC f hnn V)


/-- The 4.14 `I_B` interface instantiated from local complement bridges. -/
noncomputable def lemma_4_14_ib_interface_from_genIB_localComplements
    (fn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (fn n))
    (hV : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) (fn n) (hnn n)) :
    Lemma414IBInterface (S := S) fn hnn where
  IMeas := fun B hB n => genRelIntegral_from_measurable B hB (fn n) (hnn n)
  complement_eq := by
    intro n C hC
    exact sec4_genRelIntegral_eq_complement_of_localValueBridge
      C hC (fn n) (hnn n) (hV n C hC)


/-! ## 2. Theorem 4.15 split data with local bridges -/

/-- Source-shaped split data whose value bridges are local full-set bridges. -/
structure Lemma415SplitUniformLocalSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) (eps : R) :
    Type _ where
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  delta : R
  delta_pos : COF.lt 0 delta
  epsAB : R
  epsNeg : R
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  pieceBounds : forall (n : Nat), N <= n ->
    forall (B : BSet X) (hB : IsMeasurableSet (S := S) B),
      COF.lt (measure1 S (hB A hA)) delta ->
        Exists (fun _VB : Sec4GenIBLocalValueBridge (S := S) B hB
            (thm_4_15_abs_error (S := S) fn f n)
            (thm_4_15_abs_error_nonneg (S := S) fn f n) =>
          Exists (fun _VAB : Sec4GenIBLocalValueBridge (S := S) (BSet.and A B)
              (isMeasurableSet_of_integrable (S := S) (hB A hA))
              (thm_4_15_abs_error (S := S) fn f n)
              (thm_4_15_abs_error_nonneg (S := S) fn f n) =>
            Exists (fun _VnegA : Sec4GenIBLocalValueBridge (S := S) (BSet.neg A)
                (isMeasurableSet_neg_of_integrable (S := S) hA)
                (thm_4_15_abs_error (S := S) fn f n)
                (thm_4_15_abs_error_nonneg (S := S) fn f n) =>
              And
                (COF.lt
                  (genRelIntegral_from_measurable (BSet.and A B)
                    (isMeasurableSet_of_integrable (S := S) (hB A hA))
                    (thm_4_15_abs_error (S := S) fn f n)
                    (thm_4_15_abs_error_nonneg (S := S) fn f n))
                  epsAB)
                (COF.lt
                  (genRelIntegral_from_measurable (BSet.neg A)
                    (isMeasurableSet_neg_of_integrable (S := S) hA)
                    (thm_4_15_abs_error (S := S) fn f n)
                    (thm_4_15_abs_error_nonneg (S := S) fn f n))
                  epsNeg))))


/-- Convert local split data into lemma 4.14's source-form uniform `I_B`
hypothesis. -/
noncomputable def lemma_4_15_uniform_ib_source_data_from_local_split_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hComp : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (eps : R) (D : Lemma415SplitUniformLocalSourceData (S := S) fn f eps) :
    Lemma414UniformIBSourceData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (thm_4_15_abs_error (S := S) fn f)
        (thm_4_15_abs_error_nonneg (S := S) fn f)
        hComp)
      eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := D.delta
  delta_pos := D.delta_pos
  small := by
    intro n hn B hB hmu
    obtain ⟨VB, VAB, VnegA, hAB, hNeg⟩ :=
      D.pieceBounds n hn B hB hmu
    change COF.lt
      (genRelIntegral_from_measurable B hB
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
      eps
    exact thm_4_15_genIB_split_lt_of_piece_bounds_localBridges
      (S := S) D.A B D.hA hB
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
      VB VAB VnegA D.epsAB D.epsNeg eps hAB hNeg D.pieces_sum_lt


/-! ## 3. Building local split data from the source majorant estimate -/

/-- Convert the existing source majorant split estimate into local split data.

This mirrors `lemma_4_15_split_uniform_source_data_from_majorant_data`, but the
returned bridges are local full-set bridges.  The compatibility wrapper from
the previous bridge is used only as an implementation bridge here; downstream users
consume the local API. -/
noncomputable def lemma_4_15_local_split_uniform_source_data_from_majorant_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R)
    (D : Lemma415MajorantSplitUniformSourceData
      (S := S) fn f majorant majorant_nonneg eps) :
    Lemma415SplitUniformLocalSourceData (S := S) fn f eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := D.delta
  delta_pos := D.delta_pos
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  pieces_sum_lt := D.pieces_sum_lt
  pieceBounds := by
    intro n _hn B hB hmu
    let u : IntegrableRep S := thm_4_15_abs_error (S := S) fn f n
    let hnn_u : RepNonneg u :=
      thm_4_15_abs_error_nonneg (S := S) fn f n
    let Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u := hSeeds n
    let VB : Sec4GenIBLocalValueBridge (S := S) B hB u hnn_u :=
      sec4_genIBLocalValueBridge_of_valueBridge B hB u hnn_u
        (sec4_genIBValueBridge_of_rowSeedTools B hB u hnn_u Tu)
    let VAB : Sec4GenIBLocalValueBridge (S := S) (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA)) u hnn_u :=
      sec4_genIBLocalValueBridge_of_valueBridge
        (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        u hnn_u
        (sec4_genIBValueBridge_of_rowSeedTools
          (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u Tu)
    let VnegA : Sec4GenIBLocalValueBridge (S := S) (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA) u hnn_u :=
      sec4_genIBLocalValueBridge_of_valueBridge
        (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        u hnn_u
        (sec4_genIBValueBridge_of_rowSeedTools
          (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u Tu)
    let VABmajorant : Sec4GenIBLocalValueBridge (S := S) (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        majorant majorant_nonneg :=
      sec4_genIBLocalValueBridge_of_valueBridge
        (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        majorant majorant_nonneg
        (sec4_genIBValueBridge_of_rowSeedTools
          (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          majorant majorant_nonneg D.majorantSeeds)
    let VnegAmajorant : Sec4GenIBLocalValueBridge (S := S) (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        majorant majorant_nonneg :=
      sec4_genIBLocalValueBridge_of_valueBridge
        (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        majorant majorant_nonneg
        (sec4_genIBValueBridge_of_rowSeedTools
          (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          majorant majorant_nonneg D.majorantSeeds)
    have hAB_le : Le
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          majorant majorant_nonneg) :=
      genRelIntegral_from_measurable_mono_integrand_of_localBridges
        (S := S)
        (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        u majorant hnn_u majorant_nonneg VAB VABmajorant
        (D.dominatesError n)
    have hNeg_le : Le
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          majorant majorant_nonneg) :=
      genRelIntegral_from_measurable_mono_integrand_of_localBridges
        (S := S)
        (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        u majorant hnn_u majorant_nonneg VnegA VnegAmajorant
        (D.dominatesError n)
    have hAB_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        D.epsAB :=
      lt_of_le_of_lt hAB_le (D.majorantABSmall B hB hmu)
    have hNeg_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        D.epsNeg :=
      lt_of_le_of_lt hNeg_le D.majorantNegSmall
    exact ⟨VB, VAB, VnegA, hAB_lt, hNeg_lt⟩


/-! ## 4. Local-source theorem 4.15 entry point -/

/-- Abs-error data for 4.15 using the local `I_B` interface. -/
structure Lemma415AbsErrorLocalSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  complementBridge : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
    Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  uniform : forall eps, COF.lt 0 eps ->
    Lemma414UniformIBSourceData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (lemma_4_14_ib_interface_from_genIB_localComplements
        (S := S)
        (thm_4_15_abs_error (S := S) fn f)
        (thm_4_15_abs_error_nonneg (S := S) fn f)
        complementBridge)
      eps
  converge :
    Lemma414ConvergeInMeasureToZeroData (S := S)
      (thm_4_15_abs_error (S := S) fn f)


/-- Assemble local abs-error data from local split data. -/
noncomputable def Lemma415AbsErrorLocalSourceData.of_localSplitUniformData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hComp : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformLocalSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorLocalSourceData (S := S) fn f where
  complementBridge := hComp
  uniform := fun eps heps =>
    lemma_4_15_uniform_ib_source_data_from_local_split_data
      (S := S) fn f hComp eps (hSplit eps heps)
  converge := hconv


/-- 4.15 abs-error convergence from the local source package. -/
noncomputable def thm_4_15_abs_error_tendsto_from_local_source_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (D : Lemma415AbsErrorLocalSourceData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  thm_4_14_source_complete
    (S := S)
    (thm_4_15_abs_error (S := S) fn f)
    (thm_4_15_abs_error_nonneg (S := S) fn f)
    (lemma_4_14_ib_interface_from_genIB_localComplements
      (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      D.complementBridge)
    D.uniform D.converge


/-- The theorem-4.15 integral convergence endpoint from local abs-error data. -/
noncomputable def thm_4_15_source_from_local_abs_error_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (D : Lemma415AbsErrorLocalSourceData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_tendsto_of_abs_error_tendsto
    (S := S) fn f
    (thm_4_15_abs_error_tendsto_from_local_source_data (S := S) fn f D)


/-- Final 4.15 endpoint through the local full-set route, starting from the
source majorant split estimate.

This has the same analytic shape as the existing majorant-split endpoint, but
the 4.14 interface and the split estimate are assembled through local full-set
bridges rather than by requiring a global `Sec4GenIBValueBridge` as downstream
data. -/
noncomputable def thm_4_15_source_from_majorant_split_uniform_data_localRoute
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hMajor : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantSplitUniformSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  let hComp : ∀ (n : Nat) (C : BSet X) (hC : IntegrableSet1 S C),
      Sec4GenIBLocalValueBridge (S := S) (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n) :=
    fun n C hC =>
      sec4_genIBLocalValueBridge_of_valueBridge
        (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)
        (sec4_genIBValueBridge_of_rowSeedTools
          (BSet.neg C)
          (isMeasurableSet_neg_of_integrable (S := S) hC)
          (thm_4_15_abs_error (S := S) fn f n)
          (thm_4_15_abs_error_nonneg (S := S) fn f n)
          (hSeeds n))
  let hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformLocalSourceData (S := S) fn f eps :=
    fun eps heps =>
      lemma_4_15_local_split_uniform_source_data_from_majorant_data
        (S := S) fn f hSeeds majorant majorant_nonneg eps (hMajor eps heps)
  thm_4_15_source_from_local_abs_error_data
    (S := S) fn f
    (Lemma415AbsErrorLocalSourceData.of_localSplitUniformData
      (S := S) fn f hComp hSplit hconv)


end BishopC
