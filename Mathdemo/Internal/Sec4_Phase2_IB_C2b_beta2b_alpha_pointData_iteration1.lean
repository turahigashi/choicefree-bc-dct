import Mathdemo.Internal.Sec4_Phase2_IB_C2b_beta2a_layerRelData_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bβ2bα: pointwise layer data → `Sec4IBLayerRelData`

C2bβ2a succeeded with the safer field

`diff_le_full : I_D ≤ I_Dfull`.

This chunk lowers the remaining task one more level.  It does not ask for
global `BSet.Subset`; instead it asks only for:

* pointwise equality of the two `χ_C·f` representatives used in the two union
  identities;
* zero integral for the two empty-intersection representatives;
* pointwise χ-value comparison for the two difference layers.

The first item is converted to integral equality by `cor_1_12`; the last item
is converted to `diff_le_full` by `relIntegral_mono_le`.

The next chunk should build `Sec4IBLayerPointData` from
`prop_4_2_chi_f_rep_value`, `chi_or_add_and_value`, `chi_and_value_valid`, and
raw `BSet` case analysis.
-/

#check cor_1_12
#check relIntegral_mono_le
#check prop_4_2_chi_f_rep_value
#check chi_or_add_and_value
#check chi_and_value_valid
#check Sec4IBLayerRelData

/-! ## 1. Representatives used by the four layer identities -/

/-- The representative used by `relIntegral C hC f hnn`. -/
noncomputable def sec4RelRep
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) : IntegrableRep S :=
  prop_4_2_chi_f_rep C hC f hnn


/-- Representative for `(A_k∧B)∨((A_{k+1}∧B)\(A_k∧B))`. -/
noncomputable def sec4CoverOrDiffRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : IntegrableRep S :=
  sec4RelRep (sec4CoverOrDiff B f k) (sec4CoverOrDiff_int B hB f k) f hnn


/-- Representative for `A_{k+1}∧B`. -/
noncomputable def sec4CoverSuccRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : IntegrableRep S :=
  sec4RelRep (sec4CoverAnd B f (k + 1)) (sec4CoverAnd_int B hB f (k + 1)) f hnn


/-- Representative for `(A_k∧B)∧((A_{k+1}∧B)\(A_k∧B))`. -/
noncomputable def sec4CoverAndDiffRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : IntegrableRep S :=
  sec4RelRep (sec4CoverAndDiff B f k) (sec4CoverAndDiff_int B hB f k) f hnn


/-- Representative for `A_k∨(A_{k+1}\A_k)`. -/
noncomputable def sec4FullCoverOrDiffRep
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : IntegrableRep S :=
  sec4RelRep (sec4FullCoverOrDiff f k) (sec4FullCoverOrDiff_int f k) f hnn


/-- Representative for `A_{k+1}`. -/
noncomputable def sec4FullCoverSuccRep
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : IntegrableRep S :=
  sec4RelRep (coverSet f (k + 1)) (coverSet_int f (k + 1)) f hnn


/-- Representative for `A_k∧(A_{k+1}\A_k)`. -/
noncomputable def sec4FullCoverAndDiffRep
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : IntegrableRep S :=
  sec4RelRep (sec4FullCoverAndDiff f k) (sec4FullCoverAndDiff_int f k) f hnn


/-! ## 2. Pointwise data packages -/

/--
Pointwise equality of two representatives on a full set.
-/
structure Sec4RepValueEq (r r' : IntegrableRep S) where
  support : Set X
  support_full : IsFull S support
  value_eq :
    ∀ x ∈ support,
      ∀ (hrDom : r.MemAt x) (hr'Dom : r'.MemAt x)
        (hr : RSeq.SeriesSum (fun n => r.valueAt x hrDom n))
        (hr' : RSeq.SeriesSum (fun n => r'.valueAt x hr'Dom n)),
        hr.sum = hr'.sum


/-- Convert pointwise equality on a full set to equality of integrals. -/
theorem sec4_integral_eq_of_repValueEq
    (r r' : IntegrableRep S)
    (H : Sec4RepValueEq (S := S) r r') :
    r.integral = r'.integral :=
  cor_1_12 H.support_full r r' H.value_eq


/-! Technical auxiliary material for the public import closure. -/
def Sec4PD_coverOr
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ k : Nat,
    Sec4RepValueEq (S := S)
      (sec4CoverOrDiffRep B hB f hnn k)
      (sec4CoverSuccRep B hB f hnn k)

def Sec4PD_coverAndZero
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ k : Nat, (sec4CoverAndDiffRep B hB f hnn k).integral = 0

def Sec4PD_fullOr
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ k : Nat,
    Sec4RepValueEq (S := S)
      (sec4FullCoverOrDiffRep (S := S) f hnn k)
      (sec4FullCoverSuccRep (S := S) f hnn k)

def Sec4PD_fullAndZero
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ k : Nat, (sec4FullCoverAndDiffRep (S := S) f hnn k).integral = 0

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_mono_of_s1_subset {S : IntSpaceRC X R} (D D' : BSet X)
    (hD : IntegrableSet1 S D) (hD' : IntegrableSet1 S D')
    (hsub : ∀ x : X, x ∈ D.S1 → x ∈ D'.S1)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Le (relIntegral D hD f hnn) (relIntegral D' hD' f hnn) := by
  show Le (prop_4_2_chi_f_rep D hD f hnn).integral (prop_4_2_chi_f_rep D' hD' f hnn).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep D hD f hnn).domain_isFull (prop_4_2_chi_f_rep D' hD' f hnn).domain_isFull)
      f.domain_isFull) hD.rep.domain_isFull) hD'.rep.domain_isFull)
    (prop_4_2_chi_f_rep D hD f hnn) (prop_4_2_chi_f_rep D' hD' f hnn) ?_
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨⟨⟨hxD, hxD'⟩, hxf⟩, hxχD⟩, hxχD'⟩ := hx
  obtain ⟨hflat_DDom, ⟨hflat_D⟩⟩ := hxD
  obtain ⟨hflat_D'Dom, ⟨hflat_D'⟩⟩ := hxD'
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχ_DDom, ⟨hχ_D⟩⟩ := hxχD
  obtain ⟨hχ_D'Dom, ⟨hχ_D'⟩⟩ := hxχD'
  have hval_D := prop_4_2_chi_f_rep_value D hD f hnn
    hflat_DDom hχ_DDom hfDom hflat_D hχ_D hfabs
  have hval_D' := prop_4_2_chi_f_rep_value D' hD' f hnn
    hflat_D'Dom hχ_D'Dom hfDom hflat_D' hχ_D' hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflat_D),
      seriesSum_unique hr' (seriesSum_of_abs hflat_D'), hval_D, hval_D']
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  rcases (hD.valid x hχ_DDom hχ_D).1 with hS1 | hS2
  · have hD1 : (seriesSum_of_abs hχ_D).sum = 1 :=
      (hD.valid x hχ_DDom hχ_D).2.1 hS1 (seriesSum_of_abs hχ_D)
    have hD'1 : (seriesSum_of_abs hχ_D').sum = 1 :=
      (hD'.valid x hχ_D'Dom hχ_D').2.1
        (hsub x hS1) (seriesSum_of_abs hχ_D')
    rw [hD1, hD'1]; exact le_refl _
  · have hD0 : (seriesSum_of_abs hχ_D).sum = 0 :=
      (hD.valid x hχ_DDom hχ_D).2.2 hS2 (seriesSum_of_abs hχ_D)
    rw [hD0, zero_mul]
    rcases (hD'.valid x hχ_D'Dom hχ_D').1 with hS1' | hS2'
    · have hD'1 : (seriesSum_of_abs hχ_D').sum = 1 :=
        (hD'.valid x hχ_D'Dom hχ_D').2.1 hS1'
          (seriesSum_of_abs hχ_D')
      rw [hD'1, one_mul]; exact le_of_nonneg_sub (by rw [sub_zero]; exact hfnn)
    · have hD'0 : (seriesSum_of_abs hχ_D').sum = 0 :=
        (hD'.valid x hχ_D'Dom hχ_D').2.2 hS2'
          (seriesSum_of_abs hχ_D')
      rw [hD'0, zero_mul]; exact le_refl _

/-- Technical lemma used in the public import closure. -/
def Sec4PD_diffLeFull
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ k : Nat, ∀ x : X,
    x ∈ (sec4CoverDiff B f k).S1 → x ∈ (sec4FullCoverDiff f k).S1

/-- Technical lemma used in the public import closure. -/
def Sec4IBLayerPointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4PD_coverOr (S := S) B hB f hnn)
    (PProd (Sec4PD_coverAndZero (S := S) B hB f hnn)
      (PProd (Sec4PD_fullOr (S := S) f hnn)
        (PProd (Sec4PD_fullAndZero (S := S) f hnn)
          (Sec4PD_diffLeFull (S := S) B hB f hnn))))


/-- Technical lemma used in the public import closure. -/
def Sec4IBLayerPointData.mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (cover_or_value : Sec4PD_coverOr (S := S) B hB f hnn)
    (cover_and_zero : Sec4PD_coverAndZero (S := S) B hB f hnn)
    (full_or_value : Sec4PD_fullOr (S := S) f hnn)
    (full_and_zero : Sec4PD_fullAndZero (S := S) f hnn)
    (diff_le_full_value : Sec4PD_diffLeFull (S := S) B hB f hnn) :
    Sec4IBLayerPointData (S := S) B hB f hnn :=
  ⟨cover_or_value, cover_and_zero, full_or_value, full_and_zero, diff_le_full_value⟩

/-- Technical lemma used in the public import closure. -/
def Sec4IBLayerPointData.cover_or_value
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    Sec4PD_coverOr (S := S) B hB f hnn := G.1

def Sec4IBLayerPointData.cover_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    Sec4PD_coverAndZero (S := S) B hB f hnn := G.2.1

def Sec4IBLayerPointData.full_or_value
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    Sec4PD_fullOr (S := S) f hnn := G.2.2.1

def Sec4IBLayerPointData.full_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    Sec4PD_fullAndZero (S := S) f hnn := G.2.2.2.1

def Sec4IBLayerPointData.diff_le_full_value
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    Sec4PD_diffLeFull (S := S) B hB f hnn := G.2.2.2.2

/-! ## 3. Extract `Sec4IBLayerRelData` from pointwise data -/

/-- The restricted union identity from pointwise equality. -/
theorem sec4_cover_or_eq_of_pointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    ∀ k : Nat,
      relIntegral (sec4CoverOrDiff B f k)
        (sec4CoverOrDiff_int B hB f k) f hnn =
      sec4IB_coverIntegral B hB f hnn (k + 1) := by
  intro k
  change (sec4CoverOrDiffRep B hB f hnn k).integral =
    (sec4CoverSuccRep B hB f hnn k).integral
  exact sec4_integral_eq_of_repValueEq
    (sec4CoverOrDiffRep B hB f hnn k)
    (sec4CoverSuccRep B hB f hnn k)
    (G.cover_or_value k)


/-- The full-cover union identity from pointwise equality. -/
theorem sec4_full_or_eq_of_pointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    ∀ k : Nat,
      relIntegral (sec4FullCoverOrDiff f k)
        (sec4FullCoverOrDiff_int f k) f hnn =
      sec4FullCoverIntegral f hnn (k + 1) := by
  intro k
  change (sec4FullCoverOrDiffRep (S := S) f hnn k).integral =
    (sec4FullCoverSuccRep (S := S) f hnn k).integral
  exact sec4_integral_eq_of_repValueEq
    (sec4FullCoverOrDiffRep (S := S) f hnn k)
    (sec4FullCoverSuccRep (S := S) f hnn k)
    (G.full_or_value k)


/-- The restricted empty-intersection identity. -/
theorem sec4_cover_and_zero_of_pointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    ∀ k : Nat,
      relIntegral (sec4CoverAndDiff B f k)
        (sec4CoverAndDiff_int B hB f k) f hnn = 0 := by
  intro k
  change (sec4CoverAndDiffRep B hB f hnn k).integral = 0
  exact G.cover_and_zero k


/-- The full-cover empty-intersection identity. -/
theorem sec4_full_and_zero_of_pointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    ∀ k : Nat,
      relIntegral (sec4FullCoverAndDiff f k)
        (sec4FullCoverAndDiff_int f k) f hnn = 0 := by
  intro k
  change (sec4FullCoverAndDiffRep (S := S) f hnn k).integral = 0
  exact G.full_and_zero k


/-- The layer comparison from pointwise χ-value comparison. -/
theorem sec4_diff_le_full_of_pointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    ∀ k : Nat,
      Le (sec4IB_diffRelIntegral B hB f hnn k)
        (sec4FullDiffRelIntegral f hnn k) := by
  intro k
  exact relIntegral_mono_of_s1_subset
    (sec4CoverDiff B f k)
    (sec4FullCoverDiff f k)
    (sec4CoverDiff_int B hB f k)
    (sec4FullCoverDiff_int f k)
    (G.diff_le_full_value k)
    f hnn


/-- Build the layer relative data required by C2bβ2a. -/
noncomputable def sec4IBLayerRelData_of_pointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    Sec4IBLayerRelData (S := S) B hB f hnn := {
  cover_or_eq := sec4_cover_or_eq_of_pointData B hB f hnn G
  cover_and_zero := sec4_cover_and_zero_of_pointData B hB f hnn G
  full_or_eq := sec4_full_or_eq_of_pointData B hB f hnn G
  full_and_zero := sec4_full_and_zero_of_pointData B hB f hnn G
  diff_le_full := sec4_diff_le_full_of_pointData B hB f hnn G
}


/-- Direct representative from pointwise layer data. -/
noncomputable def genIB_rep_from_layerPointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    IntegrableRep S :=
  genIB_rep_from_layerRelData B hB f hnn
    (sec4IBLayerRelData_of_pointData B hB f hnn G)


/-- General relative integral from pointwise layer data. -/
noncomputable def genRelIntegral_from_layerPointData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) : R :=
  (genIB_rep_from_layerPointData B hB f hnn G).integral


/-- Non-negativity from pointwise layer data. -/
noncomputable def genIB_rep_from_layerPointData_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerPointData (S := S) B hB f hnn) :
    RepNonneg (genIB_rep_from_layerPointData B hB f hnn G) := by
  unfold genIB_rep_from_layerPointData
  exact genIB_rep_from_layerRelData_repNonneg B hB f hnn
    (sec4IBLayerRelData_of_pointData B hB f hnn G)


end BishopC
