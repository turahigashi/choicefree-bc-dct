import Mathdemo.Internal.Real.COFOCAssemblyCauchySequenceRepresentativeData

/-!
# Cauchy-sequence representatives imply global representatives

`COFOCAssemblyCauchySequenceRepresentativeData` isolated a seemingly weaker representative principle:
representatives only for the terms of a Cauchy quotient sequence.  This file
closes the audit of that principle.

Every constant sequence is Cauchy in any `COFO`.  Therefore a provider of
representatives for all Cauchy sequences already gives a representative for
every quotient element by applying it to the constant sequence at that element.
So the `COFOCAssemblyCauchySequenceRepresentativeData` principle is a precise interface, but not a genuine
weakening of the previous global representative selector.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Constant quotient-valued sequences are Cauchy for any chosen `COFO`
structure. -/
def cRealQuot_constSeq_isCauchy
    (cofo : BishopC.COFO CRealQuot)
    (x : CRealQuot) :
    letI : BishopC.COFO CRealQuot := cofo
    IsCauchy (fun _n : Nat => x) := by
  letI : BishopC.COFO CRealQuot := cofo
  refine ⟨fun _k => 0, ?_⟩
  intro k m n _hm _hn
  change COF.lt (COF.abs (x - x)) (COF.halfPow (R := CRealQuot) k)
  rw [show x - x = (0 : CRealQuot) from by ring, COFO.abs_zero]
  exact halfPow_pos (R := CRealQuot) k

/-- Cauchy-sequence representative data already implies a global representative
selector, by applying it to constant sequences. -/
def cRealQuotGlobalRep_of_cauchySequenceRepData
    (cofo : BishopC.COFO CRealQuot)
    (seqReps : CRealQuotCauchySequenceRepData cofo) :
    ∀ x : CRealQuot, CRealQuotRepWitness x := by
  intro x
  exact seqReps.reps
    (v := fun _n : Nat => x)
    (cRealQuot_constSeq_isCauchy cofo x)
    0

/-- The two representative principles are interderivable for any `COFO`
structure on quotient reals. -/
structure CRealQuotCauchySequenceRepDataEquivGlobal
    (cofo : BishopC.COFO CRealQuot) : Type 1 where
  to_global :
    CRealQuotCauchySequenceRepData cofo →
      ∀ x : CRealQuot, CRealQuotRepWitness x
  from_global :
    (∀ x : CRealQuot, CRealQuotRepWitness x) →
      CRealQuotCauchySequenceRepData cofo

def cRealQuotCauchySequenceRepDataEquivGlobal
    (cofo : BishopC.COFO CRealQuot) :
    CRealQuotCauchySequenceRepDataEquivGlobal cofo where
  to_global := cRealQuotGlobalRep_of_cauchySequenceRepData cofo
  from_global := cRealQuotCauchySequenceRepData_of_globalRep cofo

/-- For the rep-free decidable-order `COFO` from `RepresentativeFreeDecidableOrderCOFOAssembly`, the
Cauchy-sequence representative principle is exactly strong enough to recover
the previous global representative selector. -/
def cRealQuotGlobalRepOfDecidableLTCauchySequenceReps
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (seqReps : CRealQuotCauchySequenceRepData
      (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)) :
    ∀ x : CRealQuot, CRealQuotRepWitness x :=
  cRealQuotGlobalRep_of_cauchySequenceRepData
    (cRealQuotCOFOWithPositiveInverseDecidableLTData A hdec ltDataOf)
    seqReps

/-- Frontier after auditing the Cauchy-sequence representative principle. -/
structure CRealQuotAfterCauchyRepAuditFrontier : Type where
  cauchy_sequence_reps_equivalent_to_global_rep : Prop
  find_different_rep_free_complete_interface : Prop
  remove_ltDataOf_for_positive_inverse : Prop
  construct_or_remove_strict_order_decidability : Prop

def cRealQuotAfterCauchyRepAuditFrontier :
    CRealQuotAfterCauchyRepAuditFrontier where
  cauchy_sequence_reps_equivalent_to_global_rep := True
  find_different_rep_free_complete_interface := True
  remove_ltDataOf_for_positive_inverse := True
  construct_or_remove_strict_order_decidability := True

end BishopCReal

