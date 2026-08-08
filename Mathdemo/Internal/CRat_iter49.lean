import Mathdemo.Internal.CRat_iter48

/-!
# Conditional CReal quotient COFO/COFOC assembly

`CRat_iter46` and `CRat_iter48` give two conditional ways to obtain a live
`BishopC.COF CRealQuot` record.  This file does not pretend to solve the
remaining analytic obligations.  Instead, it turns the post-COF frontier into
explicit field data:

* `CRealQuotCOFOFieldData cof` is exactly the extra data needed to extend a
  chosen quotient `COF` record to `COFO`;
* `CRealQuotCOFOCFieldData cofo` is exactly the sequential completeness data
  needed to extend that `COFO` record to `COFOC`.

This keeps the proof state honest: the quotient COF forks are now separated
from the stronger order, inverse, Archimedean, and completeness obligations.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Extra field data required to extend a chosen quotient `COF` record to the
live `BishopC.COFO` interface.  The type is parameterized by the `COF` record so
that both the data-order fork and the decidable-order fork can share the same
assembly layer. -/
structure CRealQuotCOFOFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 where
  lt_trans :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b c : CRealQuot}, COF.lt a b → COF.lt b c → COF.lt a c
  abs_zero :
    letI : BishopC.COF CRealQuot := cof
    COF.abs (0 : CRealQuot) = 0
  abs_neg :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, COF.abs (-a) = COF.abs a
  neg_le_abs :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.abs a) (-a)
  le_abs_self :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.abs a) a
  abs_le_of :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b : CRealQuot},
      ¬ COF.lt b a → ¬ COF.lt b (-a) → ¬ COF.lt b (COF.abs a)
  one_pos :
    letI : BishopC.COF CRealQuot := cof
    COF.lt (0 : CRealQuot) 1
  half_pos :
    letI : BishopC.COF CRealQuot := cof
    COF.lt (0 : CRealQuot) COF.half
  mul_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b : CRealQuot}, COF.lt 0 a → COF.lt 0 b → COF.lt 0 (a * b)
  archimedean :
    letI : BishopC.COF CRealQuot := cof
    ∀ t : CRealQuot, COF.lt 0 t → ∃ k : Nat,
      COF.lt (COF.halfPow (R := CRealQuot) k) t
  archimedean_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ t : CRealQuot, COF.lt 0 t → { k : Nat //
      COF.lt (COF.halfPow (R := CRealQuot) k) t }
  abs_add_le :
    letI : BishopC.COF CRealQuot := cof
    ∀ a b : CRealQuot, ¬ COF.lt (COF.abs a + COF.abs b) (COF.abs (a + b))
  eq_of_small :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b : CRealQuot},
      (∀ k : Nat, ¬ COF.lt (COF.halfPow (R := CRealQuot) k)
        (COF.abs (a - b))) → a = b
  abs_of_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a : CRealQuot}, ¬ COF.lt a 0 → COF.abs a = a
  max_zero_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.max a 0) 0
  max_le_abs :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.abs a) (COF.max a 0)
  neg_min_zero_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (- COF.min a 0) 0
  neg_min_le_abs :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.abs a) (- COF.min a 0)
  lt_or_lt_of_abs_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ {c : CRealQuot}, COF.lt 0 (COF.abs c) → COF.lt 0 c ∨ COF.lt c 0
  abs_mul :
    letI : BishopC.COF CRealQuot := cof
    ∀ a b : CRealQuot, COF.abs (a * b) = COF.abs a * COF.abs b
  mul_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b : CRealQuot}, ¬ COF.lt a 0 → ¬ COF.lt b 0 → ¬ COF.lt (a * b) 0
  mul_archimedean :
    letI : BishopC.COF CRealQuot := cof
    ∀ x : CRealQuot,
      { m : Nat // ¬ COF.lt 1 (COF.abs x * COF.halfPow (R := CRealQuot) m) }
  inv : CRealQuot → CRealQuot
  mul_inv_cancel :
    letI : BishopC.COF CRealQuot := cof
    ∀ {x : CRealQuot}, COF.lt 0 x → x * inv x = 1
  inv_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ {x : CRealQuot}, COF.lt 0 x → COF.lt 0 (inv x)

/-- Generic assembly: a quotient `COF` record plus the remaining `COFO` field
data gives the live `BishopC.COFO CRealQuot` record. -/
@[reducible] def cRealQuotCOFOConditionalOfCOF
    (cof : BishopC.COF CRealQuot)
    (laws : CRealQuotCOFOFieldData cof) :
    BishopC.COFO CRealQuot where
  toCOF := cof
  lt_trans := laws.lt_trans
  abs_zero := laws.abs_zero
  abs_neg := laws.abs_neg
  neg_le_abs := laws.neg_le_abs
  le_abs_self := laws.le_abs_self
  abs_le_of := laws.abs_le_of
  one_pos := laws.one_pos
  half_pos := laws.half_pos
  mul_pos := laws.mul_pos
  archimedean := laws.archimedean
  archimedean_pos := laws.archimedean_pos
  abs_add_le := laws.abs_add_le
  eq_of_small := laws.eq_of_small
  abs_of_nonneg := laws.abs_of_nonneg
  max_zero_nonneg := laws.max_zero_nonneg
  max_le_abs := laws.max_le_abs
  neg_min_zero_nonneg := laws.neg_min_zero_nonneg
  neg_min_le_abs := laws.neg_min_le_abs
  lt_or_lt_of_abs_pos := laws.lt_or_lt_of_abs_pos
  abs_mul := laws.abs_mul
  mul_nonneg := laws.mul_nonneg
  mul_archimedean := laws.mul_archimedean
  inv := laws.inv
  mul_inv_cancel := laws.mul_inv_cancel
  inv_pos := laws.inv_pos

/-- The same `COFO` assembly specialized to the data-order/representative fork
from `CRat_iter46`. -/
@[reducible] def cRealQuotCOFOConditionalWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (laws : CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf)) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOConditionalOfCOF
    (cRealQuotCOFConditionalWith A rep ltDataOf) laws

/-- The same `COFO` assembly specialized to the decidable strict-order fork
from `CRat_iter48`. -/
@[reducible] def cRealQuotCOFOConditionalWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (laws : CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec)) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOConditionalOfCOF
    (cRealQuotCOFConditionalWithDecidableLT A hdec) laws

/-- Final sequential-completeness field data required to extend a chosen
quotient `COFO` record to `COFOC`. -/
structure CRealQuotCOFOCFieldData
    (cofo : BishopC.COFO CRealQuot) : Type 1 where
  complete :
    letI : BishopC.COFO CRealQuot := cofo
    ∀ {v : Nat → CRealQuot}, IsCauchy v → HasLim v

/-- Generic final assembly: a quotient `COFO` record plus sequential
completeness gives the live `BishopC.COFOC CRealQuot` record. -/
@[reducible] def cRealQuotCOFOCConditionalOfCOFO
    (cofo : BishopC.COFO CRealQuot)
    (completeData : CRealQuotCOFOCFieldData cofo) :
    BishopC.COFOC CRealQuot where
  toCOFO := cofo
  complete := completeData.complete

/-- Full conditional package for the data-order/representative branch. -/
structure CRealQuotConditionalCOFOCPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  rep : ∀ x : CRealQuot, CRealQuotRepWitness x
  ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b
  cofoLaws : CRealQuotCOFOFieldData
    (cRealQuotCOFConditionalWith A rep ltDataOf)
  completeData : CRealQuotCOFOCFieldData
    (cRealQuotCOFOConditionalWith A rep ltDataOf cofoLaws)
  cof : BishopC.COF CRealQuot
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotConditionalCOFOCPackageWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (cofoLaws : CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf))
    (completeData : CRealQuotCOFOCFieldData
      (cRealQuotCOFOConditionalWith A rep ltDataOf cofoLaws)) :
    CRealQuotConditionalCOFOCPackage A where
  rep := rep
  ltDataOf := ltDataOf
  cofoLaws := cofoLaws
  completeData := completeData
  cof := cRealQuotCOFConditionalWith A rep ltDataOf
  cofo := cRealQuotCOFOConditionalWith A rep ltDataOf cofoLaws
  cofoc := cRealQuotCOFOCConditionalOfCOFO
    (cRealQuotCOFOConditionalWith A rep ltDataOf cofoLaws) completeData

/-- Full conditional package for the decidable-order branch.  This branch is
logically useful for isolating obligations, but its strict-order decidability
assumption remains stronger than Bishop's intended constructive real order. -/
structure CRealQuotDecidableLTCOFOCPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  strict_order_decidable : CRealQuotLTDecidable
  cofoLaws : CRealQuotCOFOFieldData
    (cRealQuotCOFConditionalWithDecidableLT A strict_order_decidable)
  completeData : CRealQuotCOFOCFieldData
    (cRealQuotCOFOConditionalWithDecidableLT A strict_order_decidable cofoLaws)
  cof : BishopC.COF CRealQuot
  cofo : BishopC.COFO CRealQuot
  cofoc : BishopC.COFOC CRealQuot

def cRealQuotDecidableLTCOFOCPackageWith
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (cofoLaws : CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec))
    (completeData : CRealQuotCOFOCFieldData
      (cRealQuotCOFOConditionalWithDecidableLT A hdec cofoLaws)) :
    CRealQuotDecidableLTCOFOCPackage A where
  strict_order_decidable := hdec
  cofoLaws := cofoLaws
  completeData := completeData
  cof := cRealQuotCOFConditionalWithDecidableLT A hdec
  cofo := cRealQuotCOFOConditionalWithDecidableLT A hdec cofoLaws
  cofoc := cRealQuotCOFOCConditionalOfCOFO
    (cRealQuotCOFOConditionalWithDecidableLT A hdec cofoLaws) completeData

/-- Honest post-assembly frontier: after this file, the record plumbing no
longer hides anything.  What remains is the mathematical content of the
individual `COFO` fields and sequential completeness. -/
structure CRealQuotCOFOCAssemblyFrontier : Type where
  cof_fork : Prop
  cofo_order_abs_laws : Prop
  cofo_archimedean_laws : Prop
  cofo_positive_inverse : Prop
  cofoc_sequential_completeness : Prop

def cRealQuotCOFOCAssemblyFrontier : CRealQuotCOFOCAssemblyFrontier where
  cof_fork := True
  cofo_order_abs_laws := True
  cofo_archimedean_laws := True
  cofo_positive_inverse := True
  cofoc_sequential_completeness := True

end BishopCReal

