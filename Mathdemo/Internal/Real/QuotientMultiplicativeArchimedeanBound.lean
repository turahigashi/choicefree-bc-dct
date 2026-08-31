import Mathdemo.Internal.Real.QuotientMultiplicationPreservesNonnegativity

/-!
# Quotient multiplicative Archimedean bound

`QuotientMultiplicationPreservesNonnegativity` closed `mul_nonneg`.  This file closes the next `COFO` field:

* for every quotient real `x`, some dyadic gauge makes `|x| * halfPow m`
  not exceed `1`.

This is the first remaining field that genuinely uses the representative
witness carried by the conditional quotient branch.  Given `x = mk xr`, choose
`m = standardBoundWith A xr`.  The standard representative bound controls all
multiplication samples of `|xr| * eps m`, so an eventual positive tail above
`1` is impossible.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A representative's standard bound controls every sampled product
`|x_q| * eps m`. -/
theorem abs_sample_mul_standard_eps_le_one
    (A : ScalarMulArchimedeanData) (x : RegularSeq) (K n : Nat) :
    Le (COF.abs (x.val (mulIndexFromBound K n)) *
        eps (standardBoundWith A x)) 1 := by
  have hx : Le (COF.abs (x.val (mulIndexFromBound K n)))
      (COF.abs (x.val 1) + 1) :=
    regular_value_bound_from_one x K n
  have hmul : Le
      (COF.abs (x.val (mulIndexFromBound K n)) *
        eps (standardBoundWith A x))
      ((COF.abs (x.val 1) + 1) * eps (standardBoundWith A x)) :=
    scalar_mul_le_mul_right hx (eps_nonneg (standardBoundWith A x))
  exact BishopC.le_trans hmul (standardBoundWith_spec_base A x)

/-- Representative-level impossibility of `1 < |x| * eps m` when `m` is the
standard bound for `x`. -/
theorem not_posEventually_abs_mul_standard_sub_one_with
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    ¬ PosEventually
      (subSeq
        (mulSeqConcreteWith A (absSeq x)
          (constSeq (eps (standardBoundWith A x))))
        oneSeq) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  set m : Nat := standardBoundWith A x with hmdef
  set K : Nat := mulBoundWith A (absSeq x) (constSeq (eps m)) with hKdef
  set q : Nat := mulIndexFromBound K (N + 1) with hqdef
  have hpoint' : COF.lt (eps k)
      ((COF.abs (x.val q) * eps m) - 1) := by
    simpa [subSeq, subVal, oneSeq, constSeq, oneVal, constVal,
      mulSeqConcreteWith, mulSeqWith, boundedMulValWith, mulValWithBound,
      absSeq, absVal, hKdef, hqdef, hmdef] using hpoint
  have hzero : COF.lt (0 : Scalar)
      ((COF.abs (x.val q) * eps m) - 1) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint'
  have hbad : COF.lt (1 : Scalar) (COF.abs (x.val q) * eps m) := by
    have t := COF.lt_add_left (1 : Scalar) hzero
    rwa [show (1 : Scalar) + 0 = 1 from by ring,
      show (1 : Scalar) + ((COF.abs (x.val q) * eps m) - 1) =
          COF.abs (x.val q) * eps m from by ring] at t
  have hle : Le (COF.abs (x.val q) * eps m) 1 := by
    rw [hmdef, hqdef]
    exact abs_sample_mul_standard_eps_le_one A x K (N + 1)
  exact hle hbad

/-- Quotient-level multiplicative Archimedean bound against constant dyadic
gauges, using the supplied representative witness. -/
def mulArchimedeanQuot_const_with
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (x : CRealQuot) :
    { m : Nat //
      ¬ ltQuot oneQuot
        (mulQuotConcreteWith A (absQuot x) (constQuot (eps m))) } := by
  rcases rep x with ⟨xr, hx⟩
  refine ⟨standardBoundWith A xr, ?_⟩
  rw [hx]
  change ¬ PosEventually
    (subSeq
      (mulSeqConcreteWith A (absSeq xr)
        (constSeq (eps (standardBoundWith A xr))))
      oneSeq)
  exact not_posEventually_abs_mul_standard_sub_one_with A xr

/-- Basic quotient `COFO` fields through `mul_archimedean`. -/
structure CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegMulArchFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldData cof where
  mul_archimedean :
    letI : BishopC.COF CRealQuot := cof
    ∀ x : CRealQuot,
      { m : Nat // ¬ COF.lt 1 (COF.abs x * COF.halfPow (R := CRealQuot) m) }

/-- Data-order/representative branch package including `mul_archimedean`. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegMulArchFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegMulArchFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldDataWith
      A rep ltDataOf
  mul_archimedean := by
    intro x
    rcases mulArchimedeanQuot_const_with A rep x with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    change ¬ ltQuot oneQuot
      (mulQuotConcreteWith A (absQuot x)
        (@COF.halfPow CRealQuot
          (cRealQuotCOFConditionalWith A rep ltDataOf) m))
    rwa [halfPowQuot_eq_const_eps_with A rep ltDataOf m]

/-- Frontier after quotient `mul_archimedean` is closed. -/
structure CRealQuotCOFOAfterMulArchFrontier : Type where
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterMulArchFrontier :
    CRealQuotCOFOAfterMulArchFrontier where
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

