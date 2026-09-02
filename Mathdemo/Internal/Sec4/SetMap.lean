import Mathdemo.Internal.Sec4.ChiValueInputsSec4IBLayerPointData

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bβ2bβ2a: χ-value witnesses from S1/S2 maps

The β1 kernel pass showed that the remaining work is independent of `f`:
`Sec4RelRepChiEqInput` only needs equality of the characteristic values.
This file provides the generic conversion

```
BSet value-map A A'  ⇒  Sec4RelRepChiEqInput A A'
```

and then packages the layer-level construction.  Thus the next kernel-loop
chunk only has to prove raw `BSet` membership maps and the two zero/difference
χ-value facts.
-/

#check Sec4RelRepChiEqInput
#check Sec4IBLayerChiData
#check Sec4IBLayerChiData.mk
#check Sec4PD_coverAndZero
#check Sec4PD_diffLeFull
#check IntegrableRep.domain_isFull
#check isFull_inter
#check IntegrableSet1.valid

/-! ## 1. Characteristic-value maps -/

/--
A one-way value map for complemented sets.

For the characteristic value equality needed here, one direction is enough:
given a point in the left characteristic domain, validness of the left
characteristic representative puts it either in `A.S1` or in `A.S2`; these two
fields move the point to the corresponding side of `A'`.
-/
structure Sec4BSetValueMap (A A' : BSet X) : Prop where
  s1 : ∀ x : X, x ∈ A.S1 → x ∈ A'.S1
  s2 : ∀ x : X, x ∈ A.S2 → x ∈ A'.S2




/--
Move a characteristic value through a `Sec4BSetValueMap`.

The proof uses only `IntegrableSet1.valid`: the value is `1` on `S1` and `0`
on `S2`.
-/
theorem sec4_chiValue_eq_of_valueMap
    (A A' : BSet X)
    (hA : IntegrableSet1 S A) (hA' : IntegrableSet1 S A')
    (M : Sec4BSetValueMap A A')
    (x : X)
    (hChiDom : hA.rep.MemAt x)
    (hChi : RSeq.SeriesSum
      (fun n => COF.abs (hA.rep.valueAt x hChiDom n)))
    (hChi'Dom : hA'.rep.MemAt x)
    (hChi' : RSeq.SeriesSum
      (fun n => COF.abs (hA'.rep.valueAt x hChi'Dom n))) :
    (seriesSum_of_abs hChi).sum = (seriesSum_of_abs hChi').sum := by
  have vA := hA.valid x hChiDom hChi
  have vA' := hA'.valid x hChi'Dom hChi'
  cases vA.1 with
  | inl hxA1 =>
      have hxA'1 : x ∈ A'.S1 := M.s1 x hxA1
      calc
        (seriesSum_of_abs hChi).sum = 1 :=
          vA.2.1 hxA1 (seriesSum_of_abs hChi)
        _ = (seriesSum_of_abs hChi').sum :=
          (vA'.2.1 hxA'1 (seriesSum_of_abs hChi')).symm
  | inr hxA2 =>
      have hxA'2 : x ∈ A'.S2 := M.s2 x hxA2
      calc
        (seriesSum_of_abs hChi).sum = 0 :=
          vA.2.2 hxA2 (seriesSum_of_abs hChi)
        _ = (seriesSum_of_abs hChi').sum :=
          (vA'.2.2 hxA'2 (seriesSum_of_abs hChi')).symm


/-! ## 2. Generic construction of `Sec4RelRepChiEqInput` -/

/--
The full support on which all five absolute-convergence witnesses needed by
`Sec4RelRepChiEqInput` are available.
-/
def Sec4RelRepChiSupport
    (A A' : BSet X)
    (hA : IntegrableSet1 S A) (hA' : IntegrableSet1 S A')
    (f : IntegrableRep S) (hnn : RepNonneg f) : Set X :=
  ((((sec4RelRep A hA f hnn).domain ∩
      (sec4RelRep A' hA' f hnn).domain) ∩
      (hA.rep).domain) ∩
      (hA'.rep).domain) ∩
      f.domain


/-- Fullness of the generic support. -/
theorem sec4RelRepChiSupport_full
    (A A' : BSet X)
    (hA : IntegrableSet1 S A) (hA' : IntegrableSet1 S A')
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    IsFull S (Sec4RelRepChiSupport (S := S) A A' hA hA' f hnn) := by
  unfold Sec4RelRepChiSupport
  exact isFull_inter
    (isFull_inter
      (isFull_inter
        (isFull_inter
          (IntegrableRep.domain_isFull (sec4RelRep A hA f hnn))
          (IntegrableRep.domain_isFull (sec4RelRep A' hA' f hnn)))
        (IntegrableRep.domain_isFull hA.rep))
      (IntegrableRep.domain_isFull hA'.rep))
    (IntegrableRep.domain_isFull f)


/--
Construct a `Sec4RelRepChiEqInput` from a one-way value map.

All required witnesses are read from the explicit support; no choice is used,
because the target of each extraction is a proposition.
-/
noncomputable def sec4RelRepChiEqInput_of_valueMap
    (A A' : BSet X)
    (hA : IntegrableSet1 S A) (hA' : IntegrableSet1 S A')
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (M : Sec4BSetValueMap A A') :
    Sec4RelRepChiEqInput (S := S) A A' hA hA' f hnn := by
  refine ⟨Sec4RelRepChiSupport (S := S) A A' hA hA' f hnn,
    ⟨sec4RelRepChiSupport_full A A' hA hA' f hnn, ?_⟩⟩
  intro x hx
  rcases hx with ⟨⟨⟨⟨hr, hr'⟩, hChiDom⟩, hChiDom'⟩, hfDom⟩
  rcases hr with ⟨hrDom, ⟨hflat⟩⟩
  rcases hr' with ⟨hr'Dom, ⟨hflat'⟩⟩
  rcases hChiDom with ⟨hChiAt, ⟨hChi⟩⟩
  rcases hChiDom' with ⟨hChiAt', ⟨hChi'⟩⟩
  rcases hfDom with ⟨hfAt, ⟨hfabs⟩⟩
  exact ⟨hrDom, hflat, hr'Dom, hflat', hChiAt, hChi,
    hChiAt', hChi', hfAt, hfabs,
    sec4_chiValue_eq_of_valueMap A A' hA hA' M x
      hChiAt hChi hChiAt' hChi'⟩


/-! ## 3. Layer set-map data -/

/-- Raw S1/S2 map for the restricted union identity. -/
def Sec4PD_coverOrMap
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ k : Nat,
    Sec4BSetValueMap
      (sec4CoverOrDiff B f k)
      (sec4CoverAnd B f (k + 1))


/-- Raw S1/S2 map for the full-cover union identity. -/
def Sec4PD_fullOrMap
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ k : Nat,
    Sec4BSetValueMap
      (sec4FullCoverOrDiff f k)
      (coverSet f (k + 1))


/--
Data sufficient to build `Sec4IBLayerChiData`.

The remaining fields `cover_and_zero`, `full_and_zero`, and
`diff_le_full_value` keep exactly the types already isolated in the previous
chunks.
-/
def Sec4IBLayerSetMapData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4PD_coverOrMap (S := S) B hB f hnn)
    (PProd (Sec4PD_coverAndZero (S := S) B hB f hnn)
      (PProd (Sec4PD_fullOrMap (S := S) f hnn)
        (PProd (Sec4PD_fullAndZero (S := S) f hnn)
          (Sec4PD_diffLeFull (S := S) B hB f hnn))))


namespace Sec4IBLayerSetMapData

/-- Constructor with stable named arguments. -/
def mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (cover_or_map : Sec4PD_coverOrMap (S := S) B hB f hnn)
    (cover_and_zero : Sec4PD_coverAndZero (S := S) B hB f hnn)
    (full_or_map : Sec4PD_fullOrMap (S := S) f hnn)
    (full_and_zero : Sec4PD_fullAndZero (S := S) f hnn)
    (diff_le_full_value : Sec4PD_diffLeFull (S := S) B hB f hnn) :
    Sec4IBLayerSetMapData (S := S) B hB f hnn :=
  ⟨cover_or_map, cover_and_zero, full_or_map,
    full_and_zero, diff_le_full_value⟩


def cover_or_map
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    Sec4PD_coverOrMap (S := S) B hB f hnn :=
  G.1


def cover_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    Sec4PD_coverAndZero (S := S) B hB f hnn :=
  G.2.1


def full_or_map
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    Sec4PD_fullOrMap (S := S) f hnn :=
  G.2.2.1


def full_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    Sec4PD_fullAndZero (S := S) f hnn :=
  G.2.2.2.1


def diff_le_full_value
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    Sec4PD_diffLeFull (S := S) B hB f hnn :=
  G.2.2.2.2


end Sec4IBLayerSetMapData

/-! ## 4. Build `Sec4IBLayerChiData` from S1/S2 maps -/

/--
Construct the χ-data required by β1 from raw S1/S2 maps and the already
isolated zero/comparison fields.
-/
noncomputable def sec4IBLayerChiData_of_setMapData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    Sec4IBLayerChiData (S := S) B hB f hnn :=
  Sec4IBLayerChiData.mk
    (cover_or_chi := fun k =>
      sec4RelRepChiEqInput_of_valueMap
        (sec4CoverOrDiff B f k)
        (sec4CoverAnd B f (k + 1))
        (sec4CoverOrDiff_int B hB f k)
        (sec4CoverAnd_int B hB f (k + 1))
        f hnn
        (G.cover_or_map k))
    (cover_and_zero := G.cover_and_zero)
    (full_or_chi := fun k =>
      sec4RelRepChiEqInput_of_valueMap
        (sec4FullCoverOrDiff f k)
        (coverSet f (k + 1))
        (sec4FullCoverOrDiff_int f k)
        (coverSet_int f (k + 1))
        f hnn
        (G.full_or_map k))
    (full_and_zero := G.full_and_zero)
    (diff_le_full_value := G.diff_le_full_value)


/-- Layer relative data from raw S1/S2 maps. -/
noncomputable def sec4IBLayerRelData_of_setMapData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    Sec4IBLayerRelData (S := S) B hB f hnn :=
  sec4IBLayerRelData_of_chiData B hB f hnn
    (sec4IBLayerChiData_of_setMapData B hB f hnn G)


/-- Direct representative from raw S1/S2 maps. -/
noncomputable def genIB_rep_from_setMapData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    IntegrableRep S :=
  genIB_rep_from_layerChiData B hB f hnn
    (sec4IBLayerChiData_of_setMapData B hB f hnn G)




/-- Non-negativity from raw S1/S2 maps. -/
noncomputable def genIB_rep_from_setMapData_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerSetMapData (S := S) B hB f hnn) :
    RepNonneg (genIB_rep_from_setMapData B hB f hnn G) := by
  unfold genIB_rep_from_setMapData
  exact genIB_rep_from_layerChiData_repNonneg B hB f hnn
    (sec4IBLayerChiData_of_setMapData B hB f hnn G)


end BishopC
