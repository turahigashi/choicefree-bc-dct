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

/-- Data-valued representative strict order is irreflexive. -/
theorem regularSeqLtData_irrefl (x : RegularSeq) :
    regularSeqLtData x x → False := by
  intro h
  exact regularSeqLtProp_irrefl x h.toProp

/-- Data-valued left-additive transport of representative strict order. -/
def regularSeqLtData_add_left
    (c x y : RegularSeq) (h : regularSeqLtData x y) :
    regularSeqLtData (addSeq c x) (addSeq c y) where
  k := h.k
  N := h.N
  tail_pos := by
    intro n hn
    have htail := h.tail_pos (n + 1) (Nat.le_trans hn (Nat.le_succ n))
    change COF.lt (eps h.k) (y.val ((n + 1) + 1) - x.val ((n + 1) + 1))
      at htail
    change COF.lt (eps h.k)
      ((c.val ((n + 1) + 1) + y.val ((n + 1) + 1)) -
        (c.val ((n + 1) + 1) + x.val ((n + 1) + 1)))
    rwa [show
        c.val ((n + 1) + 1) + y.val ((n + 1) + 1) -
          (c.val ((n + 1) + 1) + x.val ((n + 1) + 1)) =
            y.val ((n + 1) + 1) - x.val ((n + 1) + 1)
      from by ring]

/-- Prop-valued left-additive transport of representative strict order. -/
theorem regularSeqLtProp_add_left
    (c x y : RegularSeq) :
    regularSeqLtProp x y →
      regularSeqLtProp (addSeq c x) (addSeq c y) :=
  posEventually_sub_add_left c x y

/-- Data-valued transitivity of representative strict order. -/
def regularSeqLtData_trans
    (a b c : RegularSeq)
    (hab : regularSeqLtData a b)
    (hbc : regularSeqLtData b c) :
    regularSeqLtData a c := by
  let j : Nat := Nat.max hab.k hbc.k
  refine
    { k := j
      N := hab.N + hbc.N
      tail_pos := ?_ }
  intro n hn
  have hnA : hab.N ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hnB : hbc.N ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have h1 := hab.tail_pos n hnA
  have h2 := hbc.tail_pos n hnB
  change COF.lt (eps hab.k) (b.val (n + 1) - a.val (n + 1)) at h1
  change COF.lt (eps hbc.k) (c.val (n + 1) - b.val (n + 1)) at h2
  have hle1 : Le (eps (j + 1)) (eps hab.k) := by
    have hk : hab.k ≤ j + 1 := by
      exact Nat.le_trans (by unfold j; exact Nat.le_max_left _ _) (Nat.le_succ j)
    exact eps_le_of_le hk
  have hle2 : Le (eps (j + 1)) (eps hbc.k) := by
    have hk : hbc.k ≤ j + 1 := by
      exact Nat.le_trans (by unfold j; exact Nat.le_max_right _ _) (Nat.le_succ j)
    exact eps_le_of_le hk
  have h1fine :
      COF.lt (eps (j + 1)) (b.val (n + 1) - a.val (n + 1)) :=
    scalar_lt_of_le_of_lt hle1 h1
  have h2fine :
      COF.lt (eps (j + 1)) (c.val (n + 1) - b.val (n + 1)) :=
    scalar_lt_of_le_of_lt hle2 h2
  have hsum := scalar_lt_add h1fine h2fine
  rw [eps_succ_add_self j] at hsum
  change COF.lt (eps j) ((subSeq c a).val n)
  change COF.lt (eps j) (c.val (n + 1) - a.val (n + 1))
  rwa [show
      (b.val (n + 1) - a.val (n + 1)) +
          (c.val (n + 1) - b.val (n + 1)) =
        c.val (n + 1) - a.val (n + 1)
    from by ring] at hsum

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

def cRealRegularSeqDataOrderLawLayer :
    CRealRegularSeqDataOrderLawLayer where
  ltProp := regularSeqLtProp
  ltData := regularSeqLtData
  data_to_prop := regularSeqLtData_to_prop
  ltProp_irrefl := regularSeqLtProp_irrefl
  ltData_irrefl := regularSeqLtData_irrefl
  ltData_add_left := regularSeqLtData_add_left
  ltProp_add_left := regularSeqLtProp_add_left
  ltData_trans := regularSeqLtData_trans
  ltProp_trans := regularSeqLtProp_trans
  ltData_cotrans := regularSeqLtData_cotrans
  ltProp_cotrans := regularSeqLtProp_cotrans

/-- Extended RegularSeq package after adding the data-order law layer. -/
structure CRealRegularSeqDataCOFOCOrderPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  algebraPackage : CRealRegularSeqDataCOFOCAlgebraPackage A
  orderLaws : CRealRegularSeqDataOrderLawLayer
  order_laws_use_positive_tail_data : Prop
  no_quotient_representative_selection_needed : Prop
  archimedean_and_total_old_cofo_adapter_remain : Prop

def cRealRegularSeqDataCOFOCOrderPackage
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqDataCOFOCOrderPackage A where
  algebraPackage := cRealRegularSeqDataCOFOCAlgebraPackage A
  orderLaws := cRealRegularSeqDataOrderLawLayer
  order_laws_use_positive_tail_data := True
  no_quotient_representative_selection_needed := True
  archimedean_and_total_old_cofo_adapter_remain := True

/-- Roadmap checkpoint after RegularSeq data-order laws. -/
structure CRealAfterRegularSeqDataOrderLawLayerFrontier : Type where
  data_order_laws_available : Prop
  prop_and_data_order_layers_separated : Prop
  quotient_rep_selection_still_not_needed : Prop
  next_archimedean_and_old_cofo_adapter : Prop

def cRealAfterRegularSeqDataOrderLawLayerFrontier :
    CRealAfterRegularSeqDataOrderLawLayerFrontier where
  data_order_laws_available := True
  prop_and_data_order_layers_separated := True
  quotient_rep_selection_still_not_needed := True
  next_archimedean_and_old_cofo_adapter := True

end BishopCReal

set_option linter.style.longLine false

