import Mathdemo.Internal.CRat_iter44

/-!
# CReal quotient data-order package

`CRat_iter44` closed the Type-valued cotransitivity split once quotient
representatives and positive-tail data are supplied explicitly.  This file
packages that idea as a data-carrying quotient order:

* the data order is `CRealQuotLTDataWitness`;
* it maps back to the existing Prop-valued `ltQuot`;
* it is irreflexive;
* it is cotransitive when a representative for the third point is supplied;
* it is preserved by adding a common left term when a representative for that
  common term is supplied.

This is still not the final `BishopC.COF CRealQuot` instance, because the live
`COF` interface stores `lt` as a `Prop`.  The remaining step is to decide how
the final COF layer will obtain the data witness needed by `lt_cotrans_data`
from that Prop-valued interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

abbrev ltQuotData (a b : CRealQuot) : Type :=
  CRealQuotLTDataWitness a b

/-- Forget the data-carrying quotient order back to the existing Prop order. -/
def ltQuotData_to_ltQuot {a b : CRealQuot} (h : ltQuotData a b) :
    ltQuot a b := by
  rcases h with ⟨ar, br, ha, hb, hpos⟩
  rw [ha, hb]
  change PosEventually (subSeq br ar)
  exact hpos.toProp

/-- The data-carrying quotient order is irreflexive. -/
def ltQuotData_irrefl (x : CRealQuot) : ltQuotData x x → False := by
  intro hx
  exact ltQuot_irrefl x (ltQuotData_to_ltQuot hx)

/-- Positivity data transports through adding the same representative on the
left. -/
def posEventuallyData_sub_add_left (c a b : RegularSeq) :
    PosEventuallyData (subSeq b a) →
    PosEventuallyData (subSeq (addSeq c b) (addSeq c a)) := by
  intro hpos
  rcases hpos with ⟨k, N, hN⟩
  refine ⟨k, N, ?_⟩
  intro n hn
  have hn' : N ≤ n + 1 := Nat.le_trans hn (Nat.le_succ n)
  have h := hN (n + 1) hn'
  change COF.lt (eps k) (b.val ((n + 1) + 1) - a.val ((n + 1) + 1)) at h
  change COF.lt (eps k)
    ((c.val ((n + 1) + 1) + b.val ((n + 1) + 1)) -
      (c.val ((n + 1) + 1) + a.val ((n + 1) + 1)))
  rwa [show
      (c.val ((n + 1) + 1) + b.val ((n + 1) + 1) -
          (c.val ((n + 1) + 1) + a.val ((n + 1) + 1)))
        = b.val ((n + 1) + 1) - a.val ((n + 1) + 1)
      from by ring]

/-- Data-order cotransitivity, provided a representative of the comparison
point is supplied. -/
def ltQuotData_cotrans_with_rep {a b : CRealQuot}
    (h : ltQuotData a b) (c : CRealQuot) (hc : CRealQuotRepWitness c) :
    PSum (ltQuotData a c) (ltQuotData c b) := by
  rcases h with ⟨ar, br, ha, hb, hpos⟩
  rcases hc with ⟨cr, hc⟩
  cases ltQuot_cotrans_mk_data ar br cr hpos with
  | inl hca =>
      exact PSum.inl
        { left := ar
          right := cr
          left_eq := ha
          right_eq := hc
          pos := hca }
  | inr hbc =>
      exact PSum.inr
        { left := cr
          right := br
          left_eq := hc
          right_eq := hb
          pos := hbc }

/-- Data-order left-additive transport, provided a representative of the common
left term is supplied. -/
def ltQuotData_add_left_with_rep
    (c a b : CRealQuot) (hc : CRealQuotRepWitness c) :
    ltQuotData a b → ltQuotData (addQuot c a) (addQuot c b) := by
  intro h
  rcases h with ⟨ar, br, ha, hb, hpos⟩
  rcases hc with ⟨cr, hc⟩
  refine
    { left := addSeq cr ar
      right := addSeq cr br
      left_eq := ?_
      right_eq := ?_
      pos := posEventuallyData_sub_add_left cr ar br hpos }
  · rw [hc, ha]
    rfl
  · rw [hc, hb]
    rfl

/-- With representative extraction, the data order gives fully quantified
cotransitivity and add-left transport. -/
structure CRealQuotDataOrderWithReps : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  ltData : CRealQuot → CRealQuot → Type
  ltData_to_ltQuot : ∀ {a b : CRealQuot}, ltData a b → ltQuot a b
  ltData_irrefl : ∀ x : CRealQuot, ltData x x → False
  ltData_cotrans : ∀ {a b : CRealQuot}, ltData a b → ∀ c : CRealQuot,
    PSum (ltData a c) (ltData c b)
  ltData_add_left : ∀ c a b : CRealQuot,
    ltData a b → ltData (addQuot c a) (addQuot c b)

def cRealQuotDataOrderWithReps
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x) :
    CRealQuotDataOrderWithReps where
  rep := rep
  ltData := ltQuotData
  ltData_to_ltQuot := fun h => ltQuotData_to_ltQuot h
  ltData_irrefl := ltQuotData_irrefl
  ltData_cotrans := fun h c => ltQuotData_cotrans_with_rep h c (rep c)
  ltData_add_left := fun c a b h => ltQuotData_add_left_with_rep c a b (rep c) h

/-- Current honest frontier to turn the data order into the live `COF` field:
either provide representative extraction and use a data relation throughout, or
provide a constructive translation from the Prop-valued `ltQuot` into
`ltQuotData`. -/
structure CRealQuotCOFOrderEncodingFrontier : Type where
  representative_extraction : Prop
  prop_lt_to_data_lt : Prop
  cof_lt_encoding_decision : Prop

def cRealQuotCOFOrderEncodingFrontier : CRealQuotCOFOrderEncodingFrontier where
  representative_extraction := True
  prop_lt_to_data_lt := True
  cof_lt_encoding_decision := True

end BishopCReal

