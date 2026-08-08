import Mathdemo.Internal.CRat_iter108

/-!
# Data-valued quotient COF order layer

`CRat_iter108` separated the positive inverse laws from total inverse
selection.  The remaining strict-order-decidability dependency now lives in the
order interface: the live `BishopC.COF` class stores `lt` as a `Prop`, but also
asks for a Type-valued cotransitivity split.

This file records the alternative order encoding explicitly.  If the quotient
order is carried as data, cotransitivity and add-left transport are already
constructive under representative supply.  The Prop-to-data bridge is needed
only when converting this data-valued order layer back to the live `COF`
interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A quotient `COF`-shaped seed whose strict order is carried as data rather
than as a Prop-valued relation. -/
structure CRealQuotDataCOFSeed
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  commRing : CommRing CRealQuot
  ltData : CRealQuot → CRealQuot → Type
  ltData_to_ltQuot : ∀ {a b : CRealQuot}, ltData a b → ltQuot a b
  ltData_irrefl : ∀ x : CRealQuot, ltData x x → False
  ltData_cotrans : ∀ {a b : CRealQuot}, ltData a b → ∀ c : CRealQuot,
    PSum (ltData a c) (ltData c b)
  ltData_add_left :
    letI : CommRing CRealQuot := commRing
    ∀ c a b : CRealQuot, ltData a b → ltData (c + a) (c + b)
  abs : CRealQuot → CRealQuot
  max : CRealQuot → CRealQuot → CRealQuot
  min : CRealQuot → CRealQuot → CRealQuot
  half : CRealQuot
  half_add_half :
    letI : CommRing CRealQuot := commRing
    half + half = 1
  max_halfsum :
    letI : CommRing CRealQuot := commRing
    ∀ x y : CRealQuot, max x y = half * (x + y + abs (x - y))
  min_halfsum :
    letI : CommRing CRealQuot := commRing
    ∀ x y : CRealQuot, min x y = half * (x + y - abs (x - y))

/-- The existing representative-indexed data order supplies the data-valued
quotient `COF` seed without any strict-order decidability. -/
def cRealQuotDataCOFSeedWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x) :
    CRealQuotDataCOFSeed A where
  rep := rep
  commRing := cRealQuotCommRingConcreteWith A
  ltData := ltQuotData
  ltData_to_ltQuot := fun h => ltQuotData_to_ltQuot h
  ltData_irrefl := ltQuotData_irrefl
  ltData_cotrans := fun h c => ltQuotData_cotrans_with_rep h c (rep c)
  ltData_add_left := fun c a b h =>
    ltQuotData_add_left_with_rep c a b (rep c) h
  abs := absQuot
  max := maxQuotCOFWith A
  min := minQuotCOFWith A
  half := halfQuot
  half_add_half := halfQuot_add_half
  max_halfsum := by
    intro x y
    rfl
  min_halfsum := by
    intro x y
    rfl

/-- Map data-valued cotransitivity back to Prop-valued cotransitivity.  This
does not require deciding the Prop order; it starts from an explicit data
witness. -/
def cRealQuotDataCOFSeed_cotrans_to_prop
    {A : ScalarMulArchimedeanData}
    (D : CRealQuotDataCOFSeed A)
    {a b : CRealQuot} (h : D.ltData a b) (c : CRealQuot) :
    PSum (ltQuot a c) (ltQuot c b) := by
  cases D.ltData_cotrans h c with
  | inl hac => exact PSum.inl (D.ltData_to_ltQuot hac)
  | inr hcb => exact PSum.inr (D.ltData_to_ltQuot hcb)

/-- Convert a data-valued quotient order seed back into the live `COF`
interface once the missing Prop-to-data bridge is supplied. -/
@[reducible] def cRealQuotCOFConditionalOfDataCOF
    (A : ScalarMulArchimedeanData)
    (D : CRealQuotDataCOFSeed A)
    (propToData : ∀ {a b : CRealQuot}, ltQuot a b → D.ltData a b) :
    BishopC.COF CRealQuot where
  toCommRing := D.commRing
  lt := ltQuot
  lt_irrefl := ltQuot_irrefl
  lt_cotrans := fun {a b} h c => ltQuot_cotrans a b c h
  lt_cotrans_data := fun {_ _} h c =>
    cRealQuotDataCOFSeed_cotrans_to_prop D (propToData h) c
  lt_add_left := fun c {a b} h =>
    D.ltData_to_ltQuot (D.ltData_add_left c a b (propToData h))
  abs := D.abs
  max := D.max
  min := D.min
  half := D.half
  half_add_half := D.half_add_half
  max_halfsum := D.max_halfsum
  min_halfsum := D.min_halfsum

/-- Package exposing the data-valued order seed and the exact extra bridge
needed to return to the live Prop-valued `COF` interface. -/
structure CRealQuotDataCOFToLiveCOFPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  dataCOF : CRealQuotDataCOFSeed A
  propToData : ∀ {a b : CRealQuot}, ltQuot a b → dataCOF.ltData a b
  cof : BishopC.COF CRealQuot

def cRealQuotDataCOFToLiveCOFPackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (propToData :
      ∀ {a b : CRealQuot}, ltQuot a b →
        (cRealQuotDataCOFSeedWith A rep).ltData a b) :
    CRealQuotDataCOFToLiveCOFPackage A where
  dataCOF := cRealQuotDataCOFSeedWith A rep
  propToData := propToData
  cof := cRealQuotCOFConditionalOfDataCOF
    A (cRealQuotDataCOFSeedWith A rep) propToData

/-- Frontier after separating the data-valued order layer from the live
Prop-valued `COF` encoding. -/
structure CRealQuotAfterDataCOFEncodingSplitFrontier : Type where
  data_order_layer_avoids_strict_order_decidability : Prop
  live_prop_cof_still_needs_prop_to_data_bridge : Prop
  representative_supply_for_data_cotransitivity : Prop
  choose_data_order_interface_or_construct_prop_to_data : Prop
  positive_inverse_totalization_is_separate : Prop

def cRealQuotAfterDataCOFEncodingSplitFrontier :
    CRealQuotAfterDataCOFEncodingSplitFrontier where
  data_order_layer_avoids_strict_order_decidability := True
  live_prop_cof_still_needs_prop_to_data_bridge := True
  representative_supply_for_data_cotransitivity := True
  choose_data_order_interface_or_construct_prop_to_data := True
  positive_inverse_totalization_is_separate := True

end BishopCReal

set_option linter.style.longLine false

