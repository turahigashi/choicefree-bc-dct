import Mathdemo.Internal.CRat_iter84

/-!
# Unfolding the local quotient-close bridge to concrete quotient order

`CRat_iter84` localized quotient-Cauchy extraction to a record-level bridge:

```
COF.lt (COF.abs (x - y)) (COF.halfPow k) → representative tail close
```

For the current positive-inverse conditional branch, the `COF` record is
concrete: `lt = ltQuot`, `abs = absQuot`, and `halfPow k = constQuot (eps k)`.
This file proves the checked plumbing from that record-level statement to the
still-mathematical core obligation:

```
ltQuot (absQuot (subQuot (mkQuot x) (mkQuot y))) (constQuot (eps k))
  → RepCloseAtGauge k x y
```

No scalar tail estimate is claimed here.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Concrete core of the local close frontier.  This is now free of the live
`COF` record and names exactly the quotient-order statement that still has to
be converted into representative tail bounds. -/
structure CRealQuotConcreteAbsSubCloseToRepCloseData : Type 1 where
  close_of_abs_sub_const :
    ∀ x y : RegularSeq, ∀ k : Nat,
      ltQuot
        (absQuot (subQuot (mkQuot x) (mkQuot y)))
        (constQuot (eps k)) →
          RepCloseAtGauge k x y

/-- In the positive-inverse conditional branch, record-level quotient closeness
reduces to the concrete `ltQuot/absQuot/subQuot/constQuot` core above. -/
def cRealQuotCloseToRepCloseData_of_concreteAbsSubClose
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (concreteData : CRealQuotConcreteAbsSubCloseToRepCloseData) :
    CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf) where
  close_of_quot_close := by
    intro x y hx hy k hclose
    letI : BishopC.COFO CRealQuot :=
      cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf
    have h_record :
        ltQuot
          (absQuot (x - y))
          (constQuot (eps k)) := by
      change
        ltQuot
          (absQuot (x - y))
          (@COF.halfPow CRealQuot
            (cRealQuotCOFConditionalWith A rep ltDataOf) k) at hclose
      rwa [halfPowQuot_eq_const_eps_with A rep ltDataOf k] at hclose
    have h_mk :
        ltQuot
          (absQuot (mkQuot hx.rep - mkQuot hy.rep))
          (constQuot (eps k)) := by
      rw [hx.eq_mk, hy.eq_mk] at h_record
      exact h_record
    have h_sub :
        mkQuot hx.rep - mkQuot hy.rep =
          subQuot (mkQuot hx.rep) (mkQuot hy.rep) := by
      change addQuot (mkQuot hx.rep) (negQuot (mkQuot hy.rep)) =
        subQuot (mkQuot hx.rep) (mkQuot hy.rep)
      exact (subQuot_eq_add_neg (mkQuot hx.rep) (mkQuot hy.rep)).symm
    rw [h_sub] at h_mk
    exact concreteData.close_of_abs_sub_const hx.rep hy.rep k h_mk

/-- Final assembly after replacing `CRealQuotCloseToRepCloseData` by its
concrete quotient-order core. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableOfConcreteCloseAndDiagonal
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (concreteData : CRealQuotConcreteAbsSubCloseToRepCloseData)
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithPositiveInverseDecidableOfCloseBridgeAndDiagonal
    A rep hdec ltDataOf
    (cRealQuotCloseToRepCloseData_of_concreteAbsSubClose
      A rep hdec ltDataOf concreteData)
    diagData

/-- Compact package for the frontier after the record-level close bridge has
been unfolded to concrete quotient order. -/
structure CRealQuotPositiveInverseCOFOCConcreteClosePackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  concreteData : CRealQuotConcreteAbsSubCloseToRepCloseData
  diagData : CRealRepDiagonalLimitData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  closeData : CRealQuotCloseToRepCloseData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotPositiveInverseCOFOCConcreteClosePackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (concreteData : CRealQuotConcreteAbsSubCloseToRepCloseData)
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    CRealQuotPositiveInverseCOFOCConcreteClosePackage A where
  rep := rep
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  concreteData := concreteData
  diagData := diagData
  closeData :=
    cRealQuotCloseToRepCloseData_of_concreteAbsSubClose
      A rep hdec ltDataOf concreteData
  cofoc :=
    cRealQuotCOFOCWithPositiveInverseDecidableOfConcreteCloseAndDiagonal
      A rep hdec ltDataOf concreteData diagData

/-- Exact frontier after this file: record-field unfolding is done; the
mathematical core is now the concrete quotient-order close-to-tail-close lemma,
plus the representative diagonal limit. -/
structure CRealQuotAfterConcreteCloseFrontier : Type where
  concrete_abs_sub_close_to_rep_close : Prop
  representative_diagonal_limit : Prop
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterConcreteCloseFrontier :
    CRealQuotAfterConcreteCloseFrontier where
  concrete_abs_sub_close_to_rep_close := True
  representative_diagonal_limit := True
  remove_global_rep_witness := True
  remove_decidable_order_fork := True

end BishopCReal

