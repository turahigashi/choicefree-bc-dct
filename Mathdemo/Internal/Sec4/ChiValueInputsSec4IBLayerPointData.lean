import Mathdemo.Internal.Sec4.PointData

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bβ2bβ1: χ-value inputs → `Sec4IBLayerPointData`

C2bβ2bα passed after `Sec4IBLayerPointData` was changed from a heavy
structure to a `PProd`-based `def` with manual accessors.  This file uses the
new constructor API and lowers the remaining work to explicit χ-value witness
data.

The key reusable lemma is

```lean
sec4_repValueEq_of_chiEqInput
```

It turns pointwise equality of characteristic values into pointwise equality
of the corresponding `χ_C·f` representatives, using
`prop_4_2_chi_f_rep_value`.

The next chunk should construct `Sec4IBLayerChiData` by raw BSet case
analysis and the existing `chi_or_add_and_value` / `chi_and_value_valid`
lemmas.
-/

#check Sec4IBLayerPointData
#check Sec4IBLayerPointData.mk
#check Sec4IBLayerPointData.cover_or_value
#check Sec4PD_coverAndZero
#check Sec4PD_diffLeFull
#check prop_4_2_chi_f_rep_value
#check sec4IBLayerRelData_of_pointData
#check genIB_rep_from_layerPointData

/-! ## 1. Generic χ-value input for two `χ_C·f` representatives -/

/--
Data saying that two characteristic representatives have the same χ-value on a
full set, with all absolute-convergence witnesses exposed.

This is a `def` rather than a `structure` to avoid projection generation over
heavy representative expressions.
-/
def Sec4RelRepChiEqInput
    (A A' : BSet X)
    (hA : IntegrableSet1 S A) (hA' : IntegrableSet1 S A')
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  Sigma (fun support : Set X =>
    PProd (IsFull S support)
      (∀ x ∈ support,
        ∃ hflatDom : (sec4RelRep A hA f hnn).MemAt x,
        ∃ hflat :
          RSeq.SeriesSum
            (fun n => COF.abs
              ((sec4RelRep A hA f hnn).valueAt x hflatDom n)),
        ∃ hflat'Dom : (sec4RelRep A' hA' f hnn).MemAt x,
        ∃ hflat' :
          RSeq.SeriesSum
            (fun n => COF.abs
              ((sec4RelRep A' hA' f hnn).valueAt x hflat'Dom n)),
        ∃ hχDom : hA.rep.MemAt x,
        ∃ hχ :
          RSeq.SeriesSum
            (fun n => COF.abs (hA.rep.valueAt x hχDom n)),
        ∃ hχ'Dom : hA'.rep.MemAt x,
        ∃ hχ' :
          RSeq.SeriesSum
            (fun n => COF.abs (hA'.rep.valueAt x hχ'Dom n)),
        ∃ hfDom : f.MemAt x,
        ∃ hfabs :
          RSeq.SeriesSum
            (fun n => COF.abs (f.valueAt x hfDom n)),
          (seriesSum_of_abs hχ).sum = (seriesSum_of_abs hχ').sum))


namespace Sec4RelRepChiEqInput

/-- Support of a χ-value equality input. -/
def support
    {A A' : BSet X}
    {hA : IntegrableSet1 S A} {hA' : IntegrableSet1 S A'}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4RelRepChiEqInput (S := S) A A' hA hA' f hnn) :
    Set X :=
  G.1


/-- Fullness of the support. -/
def support_full
    {A A' : BSet X}
    {hA : IntegrableSet1 S A} {hA' : IntegrableSet1 S A'}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4RelRepChiEqInput (S := S) A A' hA hA' f hnn) :
    IsFull S G.support :=
  G.2.1


/-- Witness extractor. -/
def witnesses
    {A A' : BSet X}
    {hA : IntegrableSet1 S A} {hA' : IntegrableSet1 S A'}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4RelRepChiEqInput (S := S) A A' hA hA' f hnn) :
    ∀ x ∈ G.support,
      ∃ hflatDom : (sec4RelRep A hA f hnn).MemAt x,
      ∃ hflat :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((sec4RelRep A hA f hnn).valueAt x hflatDom n)),
      ∃ hflat'Dom : (sec4RelRep A' hA' f hnn).MemAt x,
      ∃ hflat' :
        RSeq.SeriesSum
          (fun n => COF.abs
            ((sec4RelRep A' hA' f hnn).valueAt x hflat'Dom n)),
      ∃ hχDom : hA.rep.MemAt x,
      ∃ hχ :
        RSeq.SeriesSum
          (fun n => COF.abs (hA.rep.valueAt x hχDom n)),
      ∃ hχ'Dom : hA'.rep.MemAt x,
      ∃ hχ' :
        RSeq.SeriesSum
          (fun n => COF.abs (hA'.rep.valueAt x hχ'Dom n)),
      ∃ hfDom : f.MemAt x,
      ∃ hfabs :
        RSeq.SeriesSum
          (fun n => COF.abs (f.valueAt x hfDom n)),
        (seriesSum_of_abs hχ).sum = (seriesSum_of_abs hχ').sum :=
  G.2.2


end Sec4RelRepChiEqInput

/-- Technical lemma used in the public import closure. -/
noncomputable def sec4_repValueEq_of_chiEqInput
    (A A' : BSet X)
    (hA : IntegrableSet1 S A) (hA' : IntegrableSet1 S A')
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4RelRepChiEqInput (S := S) A A' hA hA' f hnn) :
    Sec4RepValueEq (S := S)
      (sec4RelRep A hA f hnn)
      (sec4RelRep A' hA' f hnn) := {
  support := G.support
  support_full := G.support_full
  value_eq := by
    intro x hx hrDom hr'Dom hr hr'
    obtain ⟨hflatDom, hflat, hflat'Dom, hflat',
      hχDom, hχ, hχ'Dom, hχ', hfDom, hfabs, hχeq⟩ :=
      G.witnesses x hx
    have hval :
        (seriesSum_of_abs hflat).sum =
          (seriesSum_of_abs hχ).sum * (seriesSum_of_abs hfabs).sum :=
      prop_4_2_chi_f_rep_value A hA f hnn
        hflatDom hχDom hfDom hflat hχ hfabs
    have hval' :
        (seriesSum_of_abs hflat').sum =
          (seriesSum_of_abs hχ').sum * (seriesSum_of_abs hfabs).sum :=
      prop_4_2_chi_f_rep_value A' hA' f hnn
        hflat'Dom hχ'Dom hfDom hflat' hχ' hfabs
    calc
      hr.sum = (seriesSum_of_abs hflat).sum :=
        seriesSum_unique hr (seriesSum_of_abs hflat)
      _ = (seriesSum_of_abs hχ).sum * (seriesSum_of_abs hfabs).sum := hval
      _ = (seriesSum_of_abs hχ').sum * (seriesSum_of_abs hfabs).sum := by
        rw [hχeq]
      _ = (seriesSum_of_abs hflat').sum := hval'.symm
      _ = hr'.sum :=
        (seriesSum_unique hr' (seriesSum_of_abs hflat')).symm
}


/-! ## 2. Layer χ-data package -/

/-- χ-value equality input for the restricted union identity. -/
def Sec4PD_coverOrChi
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ k : Nat,
    Sec4RelRepChiEqInput (S := S)
      (sec4CoverOrDiff B f k) (sec4CoverAnd B f (k + 1))
      (sec4CoverOrDiff_int B hB f k)
      (sec4CoverAnd_int B hB f (k + 1)) f hnn


/-- χ-value equality input for the full-cover union identity. -/
def Sec4PD_fullOrChi
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ k : Nat,
    Sec4RelRepChiEqInput (S := S)
      (sec4FullCoverOrDiff f k) (coverSet f (k + 1))
      (sec4FullCoverOrDiff_int f k)
      (coverSet_int f (k + 1)) f hnn


/--
Remaining χ-level data for the layer identities.

This is also a `def` for the same projection-timeout reason as
`Sec4IBLayerPointData`.
-/
def Sec4IBLayerChiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4PD_coverOrChi (S := S) B hB f hnn)
    (PProd (Sec4PD_coverAndZero (S := S) B hB f hnn)
      (PProd (Sec4PD_fullOrChi (S := S) f hnn)
        (PProd (Sec4PD_fullAndZero (S := S) f hnn)
          (Sec4PD_diffLeFull (S := S) B hB f hnn))))


namespace Sec4IBLayerChiData

/-- Constructor with stable named arguments. -/
def mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (cover_or_chi : Sec4PD_coverOrChi (S := S) B hB f hnn)
    (cover_and_zero : Sec4PD_coverAndZero (S := S) B hB f hnn)
    (full_or_chi : Sec4PD_fullOrChi (S := S) f hnn)
    (full_and_zero : Sec4PD_fullAndZero (S := S) f hnn)
    (diff_le_full_value : Sec4PD_diffLeFull (S := S) B hB f hnn) :
    Sec4IBLayerChiData (S := S) B hB f hnn :=
  ⟨cover_or_chi, cover_and_zero, full_or_chi,
    full_and_zero, diff_le_full_value⟩


def cover_or_chi
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    Sec4PD_coverOrChi (S := S) B hB f hnn :=
  G.1


def cover_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    Sec4PD_coverAndZero (S := S) B hB f hnn :=
  G.2.1


def full_or_chi
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    Sec4PD_fullOrChi (S := S) f hnn :=
  G.2.2.1


def full_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    Sec4PD_fullAndZero (S := S) f hnn :=
  G.2.2.2.1


def diff_le_full_value
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    Sec4PD_diffLeFull (S := S) B hB f hnn :=
  G.2.2.2.2


end Sec4IBLayerChiData

/-! ## 3. Construct `Sec4IBLayerPointData` from χ-data -/

/--
Build the `Sec4IBLayerPointData` required by C2bβ2bα from explicit χ-value
data.
-/
noncomputable def sec4IBLayerPointData_of_chiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    Sec4IBLayerPointData (S := S) B hB f hnn :=
  Sec4IBLayerPointData.mk
    (cover_or_value := fun k =>
      sec4_repValueEq_of_chiEqInput
        (sec4CoverOrDiff B f k) (sec4CoverAnd B f (k + 1))
        (sec4CoverOrDiff_int B hB f k)
        (sec4CoverAnd_int B hB f (k + 1)) f hnn
        (G.cover_or_chi k))
    (cover_and_zero := G.cover_and_zero)
    (full_or_value := fun k =>
      sec4_repValueEq_of_chiEqInput
        (sec4FullCoverOrDiff f k) (coverSet f (k + 1))
        (sec4FullCoverOrDiff_int f k)
        (coverSet_int f (k + 1)) f hnn
        (G.full_or_chi k))
    (full_and_zero := G.full_and_zero)
    (diff_le_full_value := G.diff_le_full_value)


/-- Layer relative data from χ-data. -/
noncomputable def sec4IBLayerRelData_of_chiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    Sec4IBLayerRelData (S := S) B hB f hnn :=
  sec4IBLayerRelData_of_pointData B hB f hnn
    (sec4IBLayerPointData_of_chiData B hB f hnn G)


/-- Direct representative from χ-data. -/
noncomputable def genIB_rep_from_layerChiData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    IntegrableRep S :=
  genIB_rep_from_layerPointData B hB f hnn
    (sec4IBLayerPointData_of_chiData B hB f hnn G)




/-- Non-negativity from χ-data. -/
noncomputable def genIB_rep_from_layerChiData_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerChiData (S := S) B hB f hnn) :
    RepNonneg (genIB_rep_from_layerChiData B hB f hnn G) := by
  unfold genIB_rep_from_layerChiData
  exact genIB_rep_from_layerPointData_repNonneg B hB f hnn
    (sec4IBLayerPointData_of_chiData B hB f hnn G)


end BishopC
