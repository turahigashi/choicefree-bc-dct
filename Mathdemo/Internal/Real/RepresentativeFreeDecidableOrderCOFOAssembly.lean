import Mathdemo.Internal.Real.RepresentativeDiagonalLimitCloseData

/-!
# Representative-free decidable-order COFO assembly

`RepresentativeDiagonalLimitCloseData` closed the representative-carrying diagonal limit closure data.
This file returns to the non-completeness `COFO` layer and removes the global
representative selector from that assembly path.

The price is explicit: this branch still assumes decidability of quotient
strict order, and the positive inverse still consumes `ltQuotData` for positive
inputs.  The point closed here is narrower: all non-completeness `COFO` fields
can be packaged for the decidable-order `COF` without a global
`rep : forall x, CRealQuotRepWitness x`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Decidable-order branch package including the two Archimedean fields.

The Prop-valued Archimedean theorem supplies existence.  For the positive
data-valued field, strict-order decidability lets us search constructively for
the first dyadic gauge that lies below the positive quotient element. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinFieldDataWithDecidableLT
      A hdec
  archimedean := by
    intro t ht
    rcases archimedeanQuot_const t ht with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rwa [halfPowQuot_eq_const_eps_with_decidable A hdec k]
  archimedean_pos := by
    intro t ht
    let p : Nat → Prop := fun k => ltQuot (constQuot (eps k)) t
    have hp : ∃ k : Nat, p k := archimedeanQuot_const t ht
    haveI : DecidablePred p := fun k => by
      dsimp [p]
      exact hdec (constQuot (eps k)) t
    refine ⟨Nat.find hp, ?_⟩
    have hfind : ltQuot (constQuot (eps (Nat.find hp))) t := by
      simpa [p] using Nat.find_spec hp
    change ltQuot
      (@COF.halfPow CRealQuot
        (cRealQuotCOFConditionalWithDecidableLT A hdec) (Nat.find hp))
      t
    rw [halfPowQuot_eq_const_eps_with_decidable A hdec (Nat.find hp)]
    exact hfind

/-- Decidable-order branch package including `abs_of_nonneg`. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsNonnegFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsNonnegFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldDataWithDecidableLT
      A hdec
  abs_of_nonneg := by
    intro a ha
    change absQuot a = a
    exact absQuot_of_nonneg a ha

/-- Decidable-order branch package including `abs_le_of`. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsNonnegFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsNonnegFieldDataWithDecidableLT
      A hdec
  abs_le_of := by
    intro a b ha hna
    change ¬ ltQuot b (absQuot a)
    exact absQuot_le_of ha hna

/-- Decidable-order branch package including `mul_nonneg`. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderFieldDataWithDecidableLT
      A hdec
  mul_nonneg := by
    intro a b ha hb
    change ¬ ltQuot (mulQuotConcreteWith A a b) zeroQuot
    exact mul_nonnegQuotConcreteWith A ha hb

/-- Prop-valued quotient multiplicative Archimedean bound against constant
dyadic gauges.  This is the representative-free form needed for later
decidable search. -/
theorem mulArchimedeanQuot_const_exists
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    ∃ m : Nat,
      ¬ ltQuot oneQuot
        (mulQuotConcreteWith A (absQuot x) (constQuot (eps m))) := by
  refine Quotient.inductionOn x ?_
  intro xr
  refine ⟨standardBoundWith A xr, ?_⟩
  change ¬ PosEventually
    (subSeq
      (mulSeqConcreteWith A (absSeq xr)
        (constSeq (eps (standardBoundWith A xr))))
      oneSeq)
  exact not_posEventually_abs_mul_standard_sub_one_with A xr

/-- Data-valued multiplicative Archimedean bound for the decidable-order
branch. -/
def mulArchimedeanQuot_const_with_decidable
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (x : CRealQuot) :
    { m : Nat //
      ¬ ltQuot oneQuot
        (mulQuotConcreteWith A (absQuot x) (constQuot (eps m))) } := by
  let p : Nat → Prop := fun m =>
    ¬ ltQuot oneQuot
      (mulQuotConcreteWith A (absQuot x) (constQuot (eps m)))
  have hp : ∃ m : Nat, p m := mulArchimedeanQuot_const_exists A x
  haveI : DecidablePred p := fun m => by
    dsimp [p]
    letI : Decidable
        (ltQuot oneQuot
          (mulQuotConcreteWith A (absQuot x) (constQuot (eps m)))) :=
      hdec oneQuot
        (mulQuotConcreteWith A (absQuot x) (constQuot (eps m)))
    infer_instance
  exact ⟨Nat.find hp, Nat.find_spec hp⟩

/-- Decidable-order branch package including `mul_archimedean`. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegMulArchFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegMulArchFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldDataWithDecidableLT
      A hdec
  mul_archimedean := by
    intro x
    rcases mulArchimedeanQuot_const_with_decidable A hdec x with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    change ¬ ltQuot oneQuot
      (mulQuotConcreteWith A (absQuot x)
        (@COF.halfPow CRealQuot
          (cRealQuotCOFConditionalWithDecidableLT A hdec) m))
    rwa [halfPowQuot_eq_const_eps_with_decidable A hdec m]

/-- Decidable-order branch package including `eq_of_small`. -/
def cRealQuotCOFOAfterEqSmallFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOAfterEqSmallFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegMulArchFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegMulArchFieldDataWithDecidableLT
      A hdec
  eq_of_small := by
    intro a b hsmall
    apply eqQuot_of_no_const_lt_abs_sub
    intro k
    have hk := hsmall k
    change ¬ ltQuot
      (@COF.halfPow CRealQuot
        (cRealQuotCOFConditionalWithDecidableLT A hdec) k)
      (absQuot (addQuot a (negQuot b))) at hk
    rw [halfPowQuot_eq_const_eps_with_decidable A hdec k,
      ← subQuot_eq_add_neg a b] at hk
    exact hk

/-- Positive-inverse field data for the decidable-order quotient `COF`
branch.  This keeps the existing `ltQuotData` assumption needed by the
positive inverse selector, but no longer asks for a global quotient
representative selector. -/
def cRealQuotPositiveInverseFieldDataWithDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotPositiveInverseFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  inv := positiveQuotInvOrZeroWithDecidable A hdec ltDataOf
  mul_inv_cancel := by
    intro x hx
    change
      mulQuotConcreteWith A x
        (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x) = oneQuot
    change ltQuot zeroQuot x at hx
    exact positiveQuotInvOrZeroWithDecidable_mul_inv_cancel A hdec ltDataOf hx
  inv_pos := by
    intro x hx
    change
      ltQuot zeroQuot
        (positiveQuotInvOrZeroWithDecidable A hdec ltDataOf x)
    change ltQuot zeroQuot x at hx
    exact positiveQuotInvOrZeroWithDecidable_inv_pos A hdec ltDataOf hx

/-- Full quotient `COFO` field data for the decidable-order branch, with no
global representative selector. -/
def cRealQuotCOFOFieldDataWithPositiveInverseDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) := by
  let base := cRealQuotCOFOAfterEqSmallFieldDataWithDecidableLT A hdec
  let pinv := cRealQuotPositiveInverseFieldDataWithDecidableLTData
    A hdec ltDataOf
  exact {
    lt_trans := base.lt_trans
    abs_zero := base.abs_zero
    abs_neg := base.abs_neg
    neg_le_abs := base.neg_le_abs
    le_abs_self := base.le_abs_self
    abs_le_of := base.abs_le_of
    one_pos := base.one_pos
    half_pos := base.half_pos
    mul_pos := base.mul_pos
    archimedean := base.archimedean
    archimedean_pos := base.archimedean_pos
    abs_add_le := base.abs_add_le
    eq_of_small := base.eq_of_small
    abs_of_nonneg := base.abs_of_nonneg
    max_zero_nonneg := base.max_zero_nonneg
    max_le_abs := base.max_le_abs
    neg_min_zero_nonneg := base.neg_min_zero_nonneg
    neg_min_le_abs := base.neg_min_le_abs
    lt_or_lt_of_abs_pos := base.lt_or_lt_of_abs_pos
    abs_mul := base.abs_mul
    mul_nonneg := base.mul_nonneg
    mul_archimedean := base.mul_archimedean
    inv := pinv.inv
    mul_inv_cancel := pinv.mul_inv_cancel
    inv_pos := pinv.inv_pos
  }

/-- A live quotient `COFO` record in the decidable-order branch, with
positive-inverse data and no global representative selector. -/
@[reducible] def cRealQuotCOFOWithPositiveInverseDecidableLTData
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOConditionalWithDecidableLT A hdec
    (cRealQuotCOFOFieldDataWithPositiveInverseDecidableLTData A hdec ltDataOf)

/-- Compact package for the representative-free decidable-order `COFO` branch. -/
structure CRealQuotDecidableLTPositiveInverseCOFOPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  pinv : CRealQuotPositiveInverseFieldData
    (cRealQuotCOFConditionalWithDecidableLT A strict_order_decidable)
  cofo : BishopC.COFO CRealQuot

def cRealQuotDecidableLTPositiveInverseCOFOPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotDecidableLTPositiveInverseCOFOPackage A where
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  pinv := cRealQuotPositiveInverseFieldDataWithDecidableLTData
    A hdec ltDataOf
  cofo := cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf

/-- Frontier after removing the global representative selector from the
non-completeness `COFO` branch. -/
structure CRealQuotAfterRepFreeDecidableLTCOFOFrontier : Type where
  remove_ltDataOf_for_positive_inverse : Prop
  construct_or_remove_strict_order_decidability : Prop
  rep_free_cauchy_completeness_bridge : Prop

def cRealQuotAfterRepFreeDecidableLTCOFOFrontier :
    CRealQuotAfterRepFreeDecidableLTCOFOFrontier where
  remove_ltDataOf_for_positive_inverse := True
  construct_or_remove_strict_order_decidability := True
  rep_free_cauchy_completeness_bridge := True

end BishopCReal

