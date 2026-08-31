import Mathdemo.Internal.Real.SplittingPropOrderDataOrderExtraction

/-!
# PosEventually witness selector frontier

`SplittingPropOrderDataOrderExtraction` reduced Prop-valued quotient order extraction to two separate
ingredients:

* a representative selector for quotient elements;
* a representative-level bridge from `PosEventually : Prop` to
  `PosEventuallyData : Type`.

The scalar rational order is decidable, but this does not by itself select the
`k, N` hidden behind the infinite tail condition in `PosEventually`.  This file
therefore records the exact Type-valued selector that is still needed and wires
that selector back into the `SplittingPropOrderDataOrderExtraction` route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Type-valued selector for the witnesses hidden in a Prop-level
`PosEventually` proof. -/
structure CRealPosEventuallySelector : Type where
  k : ∀ {x : RegularSeq}, PosEventually x → Nat
  N : ∀ {x : RegularSeq}, PosEventually x → Nat
  tail_pos :
    ∀ {x : RegularSeq} (hx : PosEventually x) (n : Nat),
      N (x := x) hx ≤ n → COF.lt (eps (k (x := x) hx)) (x.val n)

/-- A selector immediately supplies the representative-level Prop-to-data
positivity bridge isolated in `SplittingPropOrderDataOrderExtraction`. -/
def cRealPosEventuallyDataOf_of_selector
    (sel : CRealPosEventuallySelector) : CRealPosEventuallyDataOf :=
  fun {x} hx => {
    k := sel.k (x := x) hx
    N := sel.N (x := x) hx
    tail_pos := fun n hn => sel.tail_pos (x := x) hx n hn
  }

/-- Conversely, any bridge from `PosEventually` to `PosEventuallyData` contains
exactly such a witness selector. -/
def cRealPosEventuallySelector_of_dataOf
    (dataOf : CRealPosEventuallyDataOf) : CRealPosEventuallySelector where
  k := fun {x} hx => (dataOf (x := x) hx).k
  N := fun {x} hx => (dataOf (x := x) hx).N
  tail_pos := fun {x} hx n hn => (dataOf (x := x) hx).tail_pos n hn

/-- Lightweight record of the two directions, kept explicit so later files can
depend on the selector form without re-opening the Prop-to-data question. -/
structure CRealPosEventuallyDataOfSelectorEquiv : Type where
  from_selector : CRealPosEventuallySelector → CRealPosEventuallyDataOf
  to_selector : CRealPosEventuallyDataOf → CRealPosEventuallySelector

def cRealPosEventuallyDataOfSelectorEquiv :
    CRealPosEventuallyDataOfSelectorEquiv where
  from_selector := cRealPosEventuallyDataOf_of_selector
  to_selector := cRealPosEventuallySelector_of_dataOf

/-- The `SplittingPropOrderDataOrderExtraction` quotient-order extraction route restated with the
selector frontier instead of the abbreviation `CRealPosEventuallyDataOf`. -/
def cRealQuotLTDataOf_of_globalRep_and_posEventuallySelector
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotPropLTToDataLTObligation :=
  cRealQuotLTDataOf_of_globalRep_and_posEventuallyDataOf
    rep (cRealPosEventuallyDataOf_of_selector sel)

/-- Positive-order specialization of the selector-frontier route. -/
def cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallySelector
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    CRealQuotPositiveLTDataOf :=
  cRealQuotPositiveLTDataOf_of_globalRep_and_posEventuallyDataOf
    rep (cRealPosEventuallyDataOf_of_selector sel)

/-- Frontier after exposing the representative-level `PosEventually` selector.
The remaining issue is not pointwise scalar order decidability, but selection
of witnesses for the infinite tail predicate. -/
structure CRealQuotAfterPosEventuallySelectorFrontier : Type where
  pos_eventually_data_bridge_is_selector : Prop
  scalar_lt_decidable_is_only_pointwise : Prop
  tail_universal_witness_selector : Prop
  representative_selector : Prop
  construct_or_replace_pos_eventually_prop_bridge : Prop

def cRealQuotAfterPosEventuallySelectorFrontier :
    CRealQuotAfterPosEventuallySelectorFrontier where
  pos_eventually_data_bridge_is_selector := True
  scalar_lt_decidable_is_only_pointwise := True
  tail_universal_witness_selector := True
  representative_selector := True
  construct_or_replace_pos_eventually_prop_bridge := True

end BishopCReal

set_option linter.style.longLine false

