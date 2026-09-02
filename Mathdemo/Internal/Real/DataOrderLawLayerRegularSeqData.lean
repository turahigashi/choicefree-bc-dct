import Mathdemo.Internal.Real.AlgebraLawLayerRegularSeqDataInterface

/-!
# Data-order law layer for the RegularSeq data-interface

The RegularSeq route uses data-valued strict order:

`x < y` is positive-tail data for `y - x`.

This file packages the order laws that can already be stated directly on the
representatives: irreflexivity, left-additive transport, transitivity, and
cotransitivity.  These are source-shaped data laws and do not require selecting
representatives from quotient classes.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Prop-valued strict order on regular representatives. -/
abbrev regularSeqLtProp (x y : RegularSeq) : Prop :=
  PosEventually (subSeq y x)

/-- Data-valued strict order on regular representatives. -/
abbrev regularSeqLtData (x y : RegularSeq) : Type :=
  PosEventuallyData (subSeq y x)

/-- Data-valued representative order refines the Prop-valued order. -/
theorem regularSeqLtData_to_prop
    {x y : RegularSeq} (h : regularSeqLtData x y) :
    regularSeqLtProp x y :=
  h.toProp

/-- Prop-valued representative strict order is irreflexive. -/
theorem regularSeqLtProp_irrefl (x : RegularSeq) :
    ¬ regularSeqLtProp x x := by
  intro h
  have hz : PosEventually zeroSeq :=
    posEventually_respects (subSeq x x) zeroSeq
      (subSeq_self_eventually x) h
  exact not_posEventually_zero hz



/-- Prop-valued left-additive transport of representative strict order. -/
theorem regularSeqLtProp_add_left
    (c x y : RegularSeq) :
    regularSeqLtProp x y →
      regularSeqLtProp (addSeq c x) (addSeq c y) :=
  posEventually_sub_add_left c x y


/-- Prop-valued transitivity of representative strict order. -/
theorem regularSeqLtProp_trans
    (a b c : RegularSeq) :
    regularSeqLtProp a b →
      regularSeqLtProp b c →
        regularSeqLtProp a c :=
  posEventually_sub_trans a b c

/-- Data-valued cotransitivity of representative strict order. -/
def regularSeqLtData_cotrans
    (a b c : RegularSeq)
    (h : regularSeqLtData a b) :
    PSum (regularSeqLtData a c) (regularSeqLtData c b) :=
  ltQuot_cotrans_mk_data a b c h

/-- Prop-valued cotransitivity of representative strict order. -/
theorem regularSeqLtProp_cotrans
    (a b c : RegularSeq)
    (h : regularSeqLtProp a b) :
    regularSeqLtProp a c ∨ regularSeqLtProp c b := by
  change ltQuot (mkQuot a) (mkQuot c) ∨ ltQuot (mkQuot c) (mkQuot b)
  exact ltQuot_cotrans_mk a b c h

/-- Data-order law layer for RegularSeq reals. -/
structure CRealRegularSeqDataOrderLawLayer : Type 1 where
  ltProp : RegularSeq → RegularSeq → Prop
  ltData : RegularSeq → RegularSeq → Type
  data_to_prop :
    ∀ {x y : RegularSeq}, ltData x y → ltProp x y
  ltProp_irrefl :
    ∀ x : RegularSeq, ¬ ltProp x x
  ltData_irrefl :
    ∀ x : RegularSeq, ltData x x → False
  ltData_add_left :
    ∀ c x y : RegularSeq, ltData x y → ltData (addSeq c x) (addSeq c y)
  ltProp_add_left :
    ∀ c x y : RegularSeq, ltProp x y → ltProp (addSeq c x) (addSeq c y)
  ltData_trans :
    ∀ a b c : RegularSeq, ltData a b → ltData b c → ltData a c
  ltProp_trans :
    ∀ a b c : RegularSeq, ltProp a b → ltProp b c → ltProp a c
  ltData_cotrans :
    ∀ a b c : RegularSeq, ltData a b → PSum (ltData a c) (ltData c b)
  ltProp_cotrans :
    ∀ a b c : RegularSeq, ltProp a b → ltProp a c ∨ ltProp c b


/-- Extended RegularSeq package after adding the data-order law layer. -/
structure CRealRegularSeqDataCOFOCOrderPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  algebraPackage : CRealRegularSeqDataCOFOCAlgebraPackage A
  orderLaws : CRealRegularSeqDataOrderLawLayer
  order_laws_use_positive_tail_data : Prop
  no_quotient_representative_selection_needed : Prop
  archimedean_and_total_old_cofo_adapter_remain : Prop




end BishopCReal

set_option linter.style.longLine false

