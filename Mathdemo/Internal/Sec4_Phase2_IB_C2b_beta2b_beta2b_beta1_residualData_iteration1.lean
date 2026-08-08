import Mathdemo.Internal.Sec4_Phase2_IB_C2b_beta2b_beta2b_alpha_rawMaps_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bβ2bβ2bβ1: residual analytic data

The previous chunk closed the raw BSet algebra and reduced the construction to
`Sec4IBLayerResidualData`.

This file supplies the two analytic helpers requested by the kernel response:

* `sec4_relIntegral_zero_of_s1_empty`;
* `sec4_chiLe_of_s1Map`.

Then it instantiates them with the raw maps already verified in the preceding
chunk.  This gives an unconditional `genIB_rep_from_measurable` and
`genRelIntegral_from_measurable` for measurable `B` and non-negative
integrable `f`.
-/

#check Sec4IBLayerResidualData
#check Sec4IBLayerResidualData.mk
#check sec4_coverAndDiff_s1_empty_raw
#check sec4_fullCoverAndDiff_s1_empty_raw
#check sec4_coverDiff_s1_to_full_raw
#check prop_4_2_chi_f_rep_value
#check chi_and_value_valid
#check cor_1_12
#check IntegrableRep.integral_smul
#check smul_seriesSum_value

/-! ## 1. Zero integral for an integrable set with empty positive side -/

/--
Support used to compare `χ_C·f` with the zero scalar multiple of `f`.
It contains the domains needed for:
* the relative representative,
* the zero scalar multiple,
* the characteristic representative of `C`,
* and `f` itself.
-/
def Sec4RelZeroSupport
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Set X :=
  (((sec4RelRep C hC f hnn).domain ∩
      (f.smul (0 : R)).domain) ∩
      hC.rep.domain) ∩
      f.domain


/-- Fullness of `Sec4RelZeroSupport`. -/
theorem sec4RelZeroSupport_full
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IsFull S (Sec4RelZeroSupport (S := S) C hC f hnn) := by
  unfold Sec4RelZeroSupport
  exact isFull_inter
    (isFull_inter
      (isFull_inter
        (IntegrableRep.domain_isFull (sec4RelRep C hC f hnn))
        (IntegrableRep.domain_isFull (f.smul (0 : R))))
      (IntegrableRep.domain_isFull hC.rep))
    (IntegrableRep.domain_isFull f)


/-- The zero scalar multiple has zero integral. -/
theorem sec4_smul_zero_integral
    (f : IntegrableRep S) :
    (f.smul (0 : R)).integral = 0 := by
  rw [IntegrableRep.integral_smul]
  ring


/--
If the positive side of `C` is empty, then the relative integral of `f` over
`C` is zero.
-/
theorem sec4_relIntegral_zero_of_s1_empty
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (hempty : ∀ x : X, x ∈ C.S1 → False) :
    relIntegral C hC f hnn = 0 := by
  change (sec4RelRep C hC f hnn).integral = 0
  have hEq :
      (sec4RelRep C hC f hnn).integral =
        (f.smul (0 : R)).integral := by
    refine cor_1_12
      (sec4RelZeroSupport_full C hC f hnn)
      (sec4RelRep C hC f hnn)
      (f.smul (0 : R)) ?_
    intro x hx hr hz
    rcases hx with ⟨⟨⟨hrDom, hzDom⟩, hχDom⟩, hfDom⟩
    rcases hrDom.2 with ⟨hflat⟩
    rcases hχDom.2 with ⟨hχ⟩
    rcases hfDom.2 with ⟨hfabs⟩
    let hfval : RSeq.SeriesSum (fun n => (f.fn n).toFun x) :=
      seriesSum_of_abs hfabs
    let hz0 : RSeq.SeriesSum
        (fun n => ((f.smul (0 : R)).fn n).toFun x) :=
      smul_seriesSum_value (0 : R) hfval
    have hval :
        (seriesSum_of_abs hflat).sum =
          (seriesSum_of_abs hχ).sum * hfval.sum :=
      prop_4_2_chi_f_rep_value C hC f hnn hflat hχ hfabs
    have hχzero : (seriesSum_of_abs hχ).sum = 0 := by
      have vC := hC.valid x hχ
      cases vC.1 with
      | inl hxC1 =>
          exact False.elim (hempty x hxC1)
      | inr hxC2 =>
          exact vC.2.2 hxC2 (seriesSum_of_abs hχ)
    have hr_zero : hr.sum = 0 := by
      calc
        hr.sum = (seriesSum_of_abs hflat).sum :=
          seriesSum_unique hr (seriesSum_of_abs hflat)
        _ = (seriesSum_of_abs hχ).sum * hfval.sum := hval
        _ = 0 * hfval.sum := by rw [hχzero]
        _ = 0 := by ring
    have hz_zero : hz.sum = 0 := by
      calc
        hz.sum = hz0.sum := seriesSum_unique hz hz0
        _ = 0 * hfval.sum := by rfl
        _ = 0 := by ring
    rw [hr_zero, hz_zero]
  exact hEq.trans (sec4_smul_zero_integral f)


/-! Technical auxiliary material for the public import closure. -/

/-! ## 3. Instantiate the residual data -/

/-- The restricted empty-intersection residual field. -/
theorem sec4_coverAndZero_from_emptyS1
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4PD_coverAndZero (S := S) B hB f hnn := by
  intro k
  change
    relIntegral (sec4CoverAndDiff B f k)
      (sec4CoverAndDiff_int B hB f k) f hnn = 0
  exact sec4_relIntegral_zero_of_s1_empty
    (sec4CoverAndDiff B f k)
    (sec4CoverAndDiff_int B hB f k)
    f hnn
    (sec4_coverAndDiff_s1_empty_raw B f k)


/-- The full-cover empty-intersection residual field. -/
theorem sec4_fullAndZero_from_emptyS1
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4PD_fullAndZero (S := S) f hnn := by
  intro k
  change
    relIntegral (sec4FullCoverAndDiff f k)
      (sec4FullCoverAndDiff_int f k) f hnn = 0
  exact sec4_relIntegral_zero_of_s1_empty
    (sec4FullCoverAndDiff f k)
    (sec4FullCoverAndDiff_int f k)
    f hnn
    (sec4_fullCoverAndDiff_s1_empty_raw f k)


/-- Technical lemma used in the public import closure. -/
theorem sec4_diffLeFull_from_s1Map
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4PD_diffLeFull (S := S) B hB f hnn :=
  fun k => sec4_coverDiff_s1_to_full_raw B f k


/-- Residual data for all layers. -/
noncomputable def sec4IBLayerResidualData_mk
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4IBLayerResidualData (S := S) B hB f hnn :=
  Sec4IBLayerResidualData.mk
    (cover_and_zero := sec4_coverAndZero_from_emptyS1 B hB f hnn)
    (full_and_zero := sec4_fullAndZero_from_emptyS1 B hB f hnn)
    (diff_le_full_value := sec4_diffLeFull_from_s1Map B hB f hnn)


/-! ## 4. Unconditional direct representative and relative integral -/

/-- Direct representative of `χ_B · f` for measurable `B`. -/
noncomputable def genIB_rep_from_measurable
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IntegrableRep S :=
  genIB_rep_from_residualData B hB f hnn
    (sec4IBLayerResidualData_mk B hB f hnn)


/-- General relative integral over a measurable `B`. -/
noncomputable def genRelIntegral_from_measurable
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : R :=
  (genIB_rep_from_measurable B hB f hnn).integral


/-- Non-negativity of the direct representative. -/
noncomputable def genIB_rep_from_measurable_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    RepNonneg (genIB_rep_from_measurable B hB f hnn) := by
  unfold genIB_rep_from_measurable
  exact genIB_rep_from_residualData_repNonneg B hB f hnn
    (sec4IBLayerResidualData_mk B hB f hnn)


end BishopC
