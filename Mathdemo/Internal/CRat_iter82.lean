import Mathdemo.Internal.CRat_iter81

/-!
# Final completeness interface for the conditional quotient branch

`CRat_iter81` assembles the conditional quotient `COFO` record after the
positive-inverse block has been closed.  The only remaining `COFOC` field is
sequential completeness.

This file keeps the Phase 8 warning from `cofoc.txt` explicit.  The live
`COFOC.complete` target is a Cauchy sequence of opaque quotient elements:

```
∀ {v : Nat → CRealQuot}, IsCauchy v → HasLim v
```

The source-faithful route is therefore not to extract representatives from the
quotient silently.  Instead, this file records the representation-carrying
version as a separate datum and proves the small bridge: if such a theorem is
available, and if the conditional branch already supplies a representative
witness for each quotient element, then it gives the required `COFOC` field.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The live quotient completeness target for a chosen quotient `COFO` record.
This is intentionally the opaque quotient-sequence interface. -/
abbrev CRealQuotSequentialCompletenessTarget
    (cofo : BishopC.COFO CRealQuot) : Type :=
  letI : BishopC.COFO CRealQuot := cofo
  ∀ {v : Nat → CRealQuot}, IsCauchy v → HasLim v

/-- Representation-carrying sequential completeness.  The sequence still lives
in the quotient, but every term is accompanied by an explicit representative
witness.  This is the exact data shape needed to avoid hiding representative
extraction inside the proof. -/
structure CRealQuotRepCarryingCompletenessData
    (cofo : BishopC.COFO CRealQuot) : Type 1 where
  complete_with_reps :
    letI : BishopC.COFO CRealQuot := cofo
    ∀ {v : Nat → CRealQuot},
      (vreps : ∀ n : Nat, CRealQuotRepWitness (v n)) →
      IsCauchy v → HasLim v

/-- Bridge from representation-carrying completeness to the live quotient
`COFOC` field, using the explicit global representative branch already present
in the conditional development. -/
def cRealQuotCOFOCFieldData_of_repCarryingComplete
    (cofo : BishopC.COFO CRealQuot)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (completeData : CRealQuotRepCarryingCompletenessData cofo) :
    CRealQuotCOFOCFieldData cofo where
  complete := by
    intro v hv
    exact completeData.complete_with_reps (fun n => rep (v n)) hv

/-- The final conditional `COFOC` assembly for the positive-inverse branch,
provided a representation-carrying completeness theorem is supplied. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableOfRepCarryingComplete
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (completeData : CRealQuotRepCarryingCompletenessData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCConditionalOfCOFO
    (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
    (cRealQuotCOFOCFieldData_of_repCarryingComplete
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)
      rep completeData)

/-- Compact package for the exact state after the positive inverse block:
all quotient `COFO` fields are available in the conditional branch, and the
only mathematical input still needed for `COFOC` is representation-carrying
sequential completeness. -/
structure CRealQuotPositiveInverseCOFOCRepCompletePackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  strict_order_decidable : CRealQuotLTDecidable
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  completeData : CRealQuotRepCarryingCompletenessData
    (cRealQuotCOFOWithPositiveInverseDecidable A rep strict_order_decidable ltDataOf)
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotPositiveInverseCOFOCRepCompletePackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (completeData : CRealQuotRepCarryingCompletenessData
      (cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf)) :
    CRealQuotPositiveInverseCOFOCRepCompletePackage A where
  rep := rep
  strict_order_decidable := hdec
  ltDataOf := ltDataOf
  completeData := completeData
  cofo := cRealQuotCOFOWithPositiveInverseDecidable A rep hdec ltDataOf
  cofoc := cRealQuotCOFOCWithPositiveInverseDecidableOfRepCarryingComplete
    A rep hdec ltDataOf completeData

/-- Exact source route still to be proved: representation-carrying sequential
completeness for a chosen quotient `COFO` record. -/
abbrev CRealQuotRepCarryingCompletenessFrontier : Type 1 :=
  ∀ cofo : BishopC.COFO CRealQuot,
    CRealQuotRepCarryingCompletenessData cofo

/-- Exact live-interface target: opaque quotient sequential completeness. -/
abbrev CRealQuotOpaqueCompletenessFrontier : Type 1 :=
  ∀ cofo : BishopC.COFO CRealQuot,
    CRealQuotCOFOCFieldData cofo

/-- Honest marker after this file.  The exact types above are the real
frontiers; this record only keeps a compact status value for downstream logs. -/
structure CRealQuotAfterCompletenessBridgeFrontier : Type where
  rep_carrying_complete : Prop
  opaque_quotient_complete : Prop
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop

def cRealQuotAfterCompletenessBridgeFrontier :
    CRealQuotAfterCompletenessBridgeFrontier where
  rep_carrying_complete := True
  opaque_quotient_complete := True
  remove_global_rep_witness := True
  remove_decidable_order_fork := True

end BishopCReal

