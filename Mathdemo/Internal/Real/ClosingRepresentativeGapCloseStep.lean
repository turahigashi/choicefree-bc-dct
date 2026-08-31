import Mathdemo.Internal.Real.FromConcreteQuotientClosenessRepresentativeGap

/-!
# Closing the representative gap-to-close step

`FromConcreteQuotientClosenessRepresentativeGap` isolated the scalar-tail core of the local close bridge:

```
PosEventually (const eps k - |x - y|) → RepCloseAtGauge k x y
```

This file proves that core.  The only index issue is definitional: `subSeq`
uses the additive `addIndex`, so the positivity witness at index `m` controls
the original representatives at index `m + 2`.  The modulus is therefore
shifted by two.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A positive gap below `e` gives the constructive non-strict bound `a ≤ e`. -/
theorem scalar_le_of_positive_gap {a e delta : Scalar}
    (hdelta : COF.lt 0 delta) (hgap : COF.lt delta (e - a)) :
    Le a e := by
  intro hea
  have hpos_sub : COF.lt 0 (e - a) :=
    scalarCOFOSeed.lt_trans hdelta hgap
  have hsub_neg : COF.lt (e - a) 0 := by
    have t := COF.lt_add_left (-a) hea
    rwa [show -a + e = e - a from by ring,
      show -a + a = (0 : Scalar) from by ring] at t
  exact COF.lt_irrefl (0 : Scalar)
    (scalarCOFOSeed.lt_trans hpos_sub hsub_neg)

/-- The representative gap estimate yields tail closeness at the same dyadic
gauge. -/
theorem repCloseAtGauge_of_absGap
    (x y : RegularSeq) (k : Nat)
    (hgap : PosEventually
      (subSeq (constSeq (eps k)) (absSeq (subSeq x y)))) :
    RepCloseAtGauge k x y := by
  rcases hgap with ⟨j, N, hN⟩
  refine ⟨N + 2, ?_⟩
  intro n hn
  let m : Nat := n - 2
  have hmN : N ≤ m := by
    unfold m
    omega
  have hm2 : m + 2 = n := by
    unfold m
    omega
  have hraw := hN m hmN
  have hpoint :
      COF.lt (eps j)
        (eps k - COF.abs (x.val (m + 2) - y.val (m + 2))) := by
    simpa [subSeq, subVal, constSeq, constVal, absSeq, absVal, addIndex]
      using hraw
  have hle :
      Le (COF.abs (x.val (m + 2) - y.val (m + 2))) (eps k) :=
    scalar_le_of_positive_gap (eps_pos j) hpoint
  simpa [hm2] using hle

/-- The local close bridge's scalar-tail core is now closed. -/
def cRealRepAbsGapToCloseData : CRealRepAbsGapToCloseData where
  gap_to_close := repCloseAtGauge_of_absGap

/-- Concrete quotient-order close to representative tail-close is now closed. -/
def cRealQuotConcreteAbsSubCloseToRepCloseData :
    CRealQuotConcreteAbsSubCloseToRepCloseData :=
  cRealQuotConcreteAbsSubCloseToRepCloseData_of_repAbsGap
    cRealRepAbsGapToCloseData

/-- Record-level local quotient-close extraction is now available for the
positive-inverse conditional branch. -/
def cRealQuotCloseToRepCloseDataWithPositiveInverseDecidable
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCloseToRepCloseData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf) :=
  cRealQuotCloseToRepCloseData_of_concreteAbsSubClose
    A rep hdec ltDataOf cRealQuotConcreteAbsSubCloseToRepCloseData

/-- The first completeness sub-obligation, quotient-Cauchy to
representative-Cauchy extraction, is closed for the positive-inverse conditional
branch. -/
def cRealQuotCauchyToRepSequenceDataWithPositiveInverseDecidable
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCauchyToRepSequenceData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf) :=
  cRealQuotCauchyToRepSequenceData_of_closeBridge
    (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
    (cRealQuotCloseToRepCloseDataWithPositiveInverseDecidable
      A rep hdec ltDataOf)

/-- Final conditional `COFOC` assembly now depends only on representative
diagonal-limit data. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableOfDiagonal
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithPositiveInverseDecidableOfCloseBridgeAndDiagonal
    A rep hdec ltDataOf
    (cRealQuotCloseToRepCloseDataWithPositiveInverseDecidable
      A rep hdec ltDataOf)
    diagData

/-- Exact frontier after this file: quotient-Cauchy extraction is closed for
the conditional branch; representative diagonal convergence remains. -/
structure CRealQuotAfterCloseExtractionClosedFrontier : Type where
  representative_diagonal_limit : Prop
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterCloseExtractionClosedFrontier :
    CRealQuotAfterCloseExtractionClosedFrontier where
  representative_diagonal_limit := True
  remove_global_rep_witness := True
  remove_decidable_order_fork := True

end BishopCReal

