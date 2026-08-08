import Mathdemo.Internal.CRat_iter85

/-!
# From concrete quotient closeness to representative gap data

`CRat_iter85` reduced the record-level local close bridge to a concrete
quotient-order statement.  This file removes one more layer of quotient
packaging.  The remaining mathematical obligation is now the representative
gap estimate:

```
PosEventually (const eps k - |x - y|) → RepCloseAtGauge k x y
```

This is the scalar-tail estimate still to be proved; the quotient-unfolding
plumbing is checked here.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative-level gap-to-close core.  This is the scalar analytic heart
of the local close bridge: an eventual positive gap below `eps k` must yield
tail closeness at gauge `k`. -/
structure CRealRepAbsGapToCloseData : Type 1 where
  gap_to_close :
    ∀ x y : RegularSeq, ∀ k : Nat,
      PosEventually
        (subSeq (constSeq (eps k)) (absSeq (subSeq x y))) →
          RepCloseAtGauge k x y

/-- The concrete quotient-order close statement unfolds to the representative
gap statement for the displayed representatives. -/
def cRealQuotConcreteAbsSubCloseToRepCloseData_of_repAbsGap
    (gapData : CRealRepAbsGapToCloseData) :
    CRealQuotConcreteAbsSubCloseToRepCloseData where
  close_of_abs_sub_const := by
    intro x y k hclose
    have hgap :
        PosEventually
          (subSeq (constSeq (eps k)) (absSeq (subSeq x y))) := by
      change PosEventually
        (subSeq (constSeq (eps k)) (absSeq (subSeq x y))) at hclose
      exact hclose
    exact gapData.gap_to_close x y k hgap

/-- Final conditional assembly after replacing the concrete quotient close core
by the representative gap-to-close core. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableOfRepGapAndDiagonal
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (gapData : CRealRepAbsGapToCloseData)
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithPositiveInverseDecidableOfConcreteCloseAndDiagonal
    A rep hdec ltDataOf
    (cRealQuotConcreteAbsSubCloseToRepCloseData_of_repAbsGap gapData)
    diagData

/-- Compact package for the frontier after quotient closeness has been unfolded
to the representative gap estimate. -/
structure CRealQuotPositiveInverseCOFOCRepGapPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  gapData : CRealRepAbsGapToCloseData
  diagData : CRealRepDiagonalLimitData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  concreteData : CRealQuotConcreteAbsSubCloseToRepCloseData
  closeData : CRealQuotCloseToRepCloseData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotPositiveInverseCOFOCRepGapPackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (gapData : CRealRepAbsGapToCloseData)
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    CRealQuotPositiveInverseCOFOCRepGapPackage A where
  rep := rep
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  gapData := gapData
  diagData := diagData
  concreteData :=
    cRealQuotConcreteAbsSubCloseToRepCloseData_of_repAbsGap gapData
  closeData :=
    cRealQuotCloseToRepCloseData_of_concreteAbsSubClose
      A rep hdec ltDataOf
      (cRealQuotConcreteAbsSubCloseToRepCloseData_of_repAbsGap gapData)
  cofoc :=
    cRealQuotCOFOCWithPositiveInverseDecidableOfRepGapAndDiagonal
      A rep hdec ltDataOf gapData diagData

/-- Exact frontier after this file: quotient packaging has been removed from
the local close bridge.  What remains is scalar tail arithmetic plus the
diagonal-limit construction. -/
structure CRealQuotAfterRepGapCloseFrontier : Type where
  representative_gap_to_close : Prop
  representative_diagonal_limit : Prop
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterRepGapCloseFrontier :
    CRealQuotAfterRepGapCloseFrontier where
  representative_gap_to_close := True
  representative_diagonal_limit := True
  remove_global_rep_witness := True
  remove_decidable_order_fork := True

end BishopCReal

