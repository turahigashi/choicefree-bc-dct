import Mathdemo.Internal.Real.FinalCompletenessInterfaceConditionalQuotientBranch

/-!
# Completeness frontier split for the conditional quotient branch

`FinalCompletenessInterfaceConditionalQuotientBranch` identified the honest final input for `COFOC.complete`:
representation-carrying sequential completeness.  This file splits that input
into two source-faithful sub-obligations:

* extract a concrete representative-sequence Cauchy datum from a quotient
  Cauchy sequence whose terms carry explicit representatives;
* build a diagonal limit for such a representative sequence and prove quotient
  convergence back to the original sequence.

The file proves only the interface bridge between these two obligations and
the live `HasLim` field.  It does not claim that either sub-obligation has
been solved.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Tail closeness at one dyadic gauge for two representatives. -/
def RepCloseAtGauge (k : Nat) (x y : RegularSeq) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n →
    Le (COF.abs (x.val n - y.val n)) (eps k)

/-- A representative-level Cauchy datum for a sequence of regular
representatives.  The `close_eventually` field deliberately stays in the
existing representative vocabulary; the exact conversion from quotient Cauchy
data into this shape is recorded separately below. -/
structure CRealRepSequenceCauchyData (w : Nat → RegularSeq) : Type where
  cmod : Nat → Nat
  close_eventually :
    ∀ k m n : Nat, cmod k ≤ m → cmod k ≤ n →
      RepCloseAtGauge k (w m) (w n)

/-- First sub-obligation for completeness: from the live quotient Cauchy
predicate and explicit representatives for each term, produce a
representative-level Cauchy datum. -/
structure CRealQuotCauchyToRepSequenceData
    (cofo : BishopC.COFO CRealQuot) : Type 1 where
  rep_cauchy :
    letI : BishopC.COFO CRealQuot := cofo
    ∀ {v : Nat → CRealQuot},
      (vreps : ∀ n : Nat, CRealQuotRepWitness (v n)) →
      IsCauchy v →
        CRealRepSequenceCauchyData (fun n : Nat => (vreps n).rep)

/-- Second sub-obligation for completeness: construct a diagonal limit from a
representative-level Cauchy datum and prove quotient convergence.  The
convergence statement is phrased for `mkQuot (w n)`; the bridge below transports
it back along the explicit equality witnesses `v n = mkQuot ((vreps n).rep)`. -/
structure CRealRepDiagonalLimitData
    (cofo : BishopC.COFO CRealQuot) : Type 1 where
  limit : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → RegularSeq
  lmod : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → Nat → Nat
  tends :
    letI : BishopC.COFO CRealQuot := cofo
    ∀ (w : Nat → RegularSeq) (hc : CRealRepSequenceCauchyData w),
      ∀ k n : Nat, lmod w hc k ≤ n →
        COF.lt
          (COF.abs (mkQuot (w n) - mkQuot (limit w hc)))
          (COF.halfPow (R := CRealQuot) k)

/-- The checked bridge: quotient Cauchy extraction plus a diagonal-limit
theorem gives the representation-carrying completeness datum required by
`FinalCompletenessInterfaceConditionalQuotientBranch`. -/
def cRealQuotRepCarryingCompletenessData_of_repDiagonal
    (cofo : BishopC.COFO CRealQuot)
    (extractData : CRealQuotCauchyToRepSequenceData cofo)
    (diagData : CRealRepDiagonalLimitData cofo) :
    CRealQuotRepCarryingCompletenessData cofo where
  complete_with_reps := by
    intro v vreps hv
    let w : Nat → RegularSeq := fun n => (vreps n).rep
    let hc : CRealRepSequenceCauchyData w :=
      extractData.rep_cauchy vreps hv
    let limitRep : RegularSeq := diagData.limit w hc
    refine ⟨mkQuot limitRep, ?_⟩
    refine ⟨diagData.lmod w hc, ?_⟩
    intro k n hn
    have hmk :
        COF.lt
          (COF.abs (mkQuot (w n) - mkQuot limitRep))
          (COF.halfPow (R := CRealQuot) k) :=
      diagData.tends w hc k n hn
    have hvn : v n = mkQuot (w n) := (vreps n).eq_mk
    rw [hvn]
    exact hmk

/-- Direct `COFOC` field bridge using the split completeness frontier. -/
def cRealQuotCOFOCFieldData_of_repDiagonal
    (cofo : BishopC.COFO CRealQuot)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (extractData : CRealQuotCauchyToRepSequenceData cofo)
    (diagData : CRealRepDiagonalLimitData cofo) :
    CRealQuotCOFOCFieldData cofo :=
  cRealQuotCOFOCFieldData_of_repCarryingComplete cofo rep
    (cRealQuotRepCarryingCompletenessData_of_repDiagonal
      cofo extractData diagData)

/-- Final conditional assembly after the completeness frontier has been split
into quotient-Cauchy extraction and representative diagonal convergence. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableOfRepDiagonal
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (extractData : CRealQuotCauchyToRepSequenceData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf))
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCConditionalOfCOFO
    (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
    (cRealQuotCOFOCFieldData_of_repDiagonal
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
      rep extractData diagData)

/-- Compact package for the state after splitting the completeness frontier. -/
structure CRealQuotPositiveInverseCOFOCSplitCompletePackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  extractData : CRealQuotCauchyToRepSequenceData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  diagData : CRealRepDiagonalLimitData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  completeData : CRealQuotRepCarryingCompletenessData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotPositiveInverseCOFOCSplitCompletePackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (extractData : CRealQuotCauchyToRepSequenceData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf))
    (diagData : CRealRepDiagonalLimitData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    CRealQuotPositiveInverseCOFOCSplitCompletePackage A where
  rep := rep
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  extractData := extractData
  diagData := diagData
  completeData :=
    cRealQuotRepCarryingCompletenessData_of_repDiagonal
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
      extractData diagData
  cofo := cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf
  cofoc := cRealQuotCOFOCWithPositiveInverseDecidableOfRepDiagonal
    A rep hdec ltDataOf extractData diagData

/-- Exact next frontier after this file: the bridge is complete, but the two
mathematical inputs remain open. -/
structure CRealQuotAfterCompletenessSplitFrontier : Type where
  quotient_cauchy_to_rep_sequence : Prop
  representative_diagonal_limit : Prop
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterCompletenessSplitFrontier :
    CRealQuotAfterCompletenessSplitFrontier where
  quotient_cauchy_to_rep_sequence := True
  representative_diagonal_limit := True
  remove_global_rep_witness := True
  remove_decidable_order_fork := True

end BishopCReal

