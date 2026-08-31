import Mathdemo.Internal.Real.BishopSourceHintAuditRemainingCReal

/-!
# RegularSeq data-interface fork for Bishop-style CReal

`BishopSourceHintAuditRemainingCReal` classified the remaining assumptions in the opaque quotient
route.  The source-guided fork is to expose the Bishop real carrier as regular
sequences with Bishop equality and Type-valued positive evidence.  This file
packages that fork as a data interface.

This is intentionally not a `CommRing RegularSeq` or `BishopC.COFOC
RegularSeq`: those typeclasses use Lean's structural equality, while Bishop's
real equality is the relation `rel`.  The interface below records the correct
setoid-style carrier shape and the already constructed positive-data inverse
and diagonal completeness layers.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Sequence-level max, using the same half-sum formula as the quotient COF
encoding but staying on regular representatives. -/
def maxSeqWith (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) : RegularSeq :=
  mulSeqConcreteWith A halfSeq
    (addSeq (addSeq x y) (absSeq (subSeq x y)))

/-- Sequence-level min, using the same half-sum formula as the quotient COF
encoding but staying on regular representatives. -/
def minSeqWith (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) : RegularSeq :=
  mulSeqConcreteWith A halfSeq
    (subSeq (addSeq x y) (absSeq (subSeq x y)))

/-- Positive-data reciprocal layer on representatives.

This is the Bishop-style reciprocal shape: inverse is indexed by positivity
data and is not a total function on all reals. -/
structure CRealRegularSeqPositiveDataInverseLayer
    (A : ScalarMulArchimedeanData) : Type 1 where
  invData : ∀ {x : RegularSeq}, PosEventuallyData x → RegularSeq
  invData_agrees :
    ∀ {x : RegularSeq}, ∀ h : PosEventuallyData x,
      invData h = positiveTailInvSeqWithBound A x h
  invData_posData :
    ∀ {x : RegularSeq}, ∀ h : PosEventuallyData x,
      PosEventuallyData (subSeq (invData h) zeroSeq)
  mul_inv_eventually_one :
    ∀ {x : RegularSeq}, ∀ h : PosEventuallyData x,
      relEventually (mulSeqConcreteWith A x (invData h)) oneSeq

def cRealRegularSeqPositiveDataInverseLayer
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqPositiveDataInverseLayer A where
  invData := fun {x} h => positiveTailInvSeqWithBound A x h
  invData_agrees := by
    intro x h
    rfl
  invData_posData := by
    intro x h
    exact positiveTailInvSeqWithBound_sub_zero_posData A x h
  mul_inv_eventually_one := by
    intro x h
    exact positiveTail_mulSeqConcreteWith_invSeq_eventually_one A x h

/-- Data-valued Bishop-real scalar interface over representatives.

The strict order is represented by data: `x < y` means positive data for
`y - x`.  Positivity and inverse are also data-valued.  Sequential
completeness is the representative diagonal layer already closed in
`FaithfulDataCarryingScalarPackageCReal`. -/
structure CRealRegularSeqDataCOFOCInterface
    (A : ScalarMulArchimedeanData) : Type 1 where
  carrier : Type
  carrier_is_regular_seq : carrier = RegularSeq
  eqRel : RegularSeq → RegularSeq → Prop
  zero : RegularSeq
  one : RegularSeq
  half : RegularSeq
  add : RegularSeq → RegularSeq → RegularSeq
  neg : RegularSeq → RegularSeq
  sub : RegularSeq → RegularSeq → RegularSeq
  mul : RegularSeq → RegularSeq → RegularSeq
  abs : RegularSeq → RegularSeq
  max : RegularSeq → RegularSeq → RegularSeq
  min : RegularSeq → RegularSeq → RegularSeq
  ltData : RegularSeq → RegularSeq → Type
  ltData_to_posEventually :
    ∀ {x y : RegularSeq}, ltData x y → PosEventually (subSeq y x)
  positiveData : RegularSeq → Type
  positiveData_to_posEventually :
    ∀ {x : RegularSeq}, positiveData x → PosEventually x
  positiveInverse : CRealRegularSeqPositiveDataInverseLayer A
  repSequenceComplete : CRealRepSequenceCompleteLayer
  no_global_rep_extraction : Prop
  no_total_inverse_required_for_positive_inverse_laws : Prop
  quotient_adapter_is_optional_later_step : Prop

def cRealRegularSeqDataCOFOCInterface
    (A : ScalarMulArchimedeanData) :
    CRealRegularSeqDataCOFOCInterface A where
  carrier := RegularSeq
  carrier_is_regular_seq := rfl
  eqRel := rel
  zero := zeroSeq
  one := oneSeq
  half := halfSeq
  add := addSeq
  neg := negSeq
  sub := subSeq
  mul := mulSeqConcreteWith A
  abs := absSeq
  max := maxSeqWith A
  min := minSeqWith A
  ltData := fun x y => PosEventuallyData (subSeq y x)
  ltData_to_posEventually := by
    intro x y h
    exact h.toProp
  positiveData := PosEventuallyData
  positiveData_to_posEventually := by
    intro x h
    exact h.toProp
  positiveInverse := cRealRegularSeqPositiveDataInverseLayer A
  repSequenceComplete := cRealRepSequenceCompleteLayer
  no_global_rep_extraction := True
  no_total_inverse_required_for_positive_inverse_laws := True
  quotient_adapter_is_optional_later_step := True

/-- G7 checkpoint after choosing the regular-sequence data-interface branch. -/
structure CRealAfterRegularSeqDataInterfaceFrontier : Type where
  regularseq_data_interface_available : Prop
  positive_inverse_is_data_indexed : Prop
  representative_completeness_available : Prop
  old_quotient_cofoc_adapter_still_possible : Prop
  old_quotient_cofoc_adapter_needs_global_rep_and_total_inv : Prop
  next_step_formalize_setoid_laws_or_adapter : Prop

def cRealAfterRegularSeqDataInterfaceFrontier :
    CRealAfterRegularSeqDataInterfaceFrontier where
  regularseq_data_interface_available := True
  positive_inverse_is_data_indexed := True
  representative_completeness_available := True
  old_quotient_cofoc_adapter_still_possible := True
  old_quotient_cofoc_adapter_needs_global_rep_and_total_inv := True
  next_step_formalize_setoid_laws_or_adapter := True

end BishopCReal

set_option linter.style.longLine false

