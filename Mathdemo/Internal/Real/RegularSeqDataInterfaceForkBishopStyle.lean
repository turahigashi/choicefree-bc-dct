import Mathdemo.Internal.Real.FaithfulDataCarryingScalarPackageCReal
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




end BishopCReal

set_option linter.style.longLine false

