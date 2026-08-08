import Mathdemo.Internal.CRat_iter59

/-!
# Quotient absolute value of nonnegative elements

`CRat_iter59` closed the quotient Archimedean fields.  This file closes the
next order/absolute-value field:

* if a quotient real is not strictly negative, then `abs x = x`.

The proof avoids extracting pointwise nonnegativity from the quotient
assumption.  Instead, a late point where `||a| - a|` is dyadically large would
force a dyadic positive lower bound for `-a`; regularity then extends that
single late point to tail positivity of `-x`, contradicting the quotient
nonnegativity hypothesis.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar dyadic version of the raw rational calculation. -/
theorem scalar_eps_lt_abs_abs_sub_self_implies_neg
    {a : Scalar} {k : Nat}
    (h : COF.lt (eps k) (COF.abs (COF.abs a - a))) :
    COF.lt (eps (k + 1)) (-a) := by
  have hgap_nonneg : Le 0 (COF.abs a - a) :=
    scalar_abs_sub_self_nonneg a
  have hgap : COF.lt (eps k) (COF.abs a - a) := by
    change COF.lt (eps k) (BishopCRat.CRat.absF (COF.abs a - a)) at h
    rwa [scalarCOFOSeed.abs_of_nonneg hgap_nonneg] at h
  have hgap_pos : COF.lt (0 : Scalar) (COF.abs a - a) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hgap
  have ha_lt_abs : COF.lt a (COF.abs a) := by
    have t := COF.lt_add_left a hgap_pos
    rwa [show a + (0 : Scalar) = a from by ring,
      show a + (COF.abs a - a) = COF.abs a from by ring] at t
  have ha_neg : COF.lt a 0 := by
    rcases COF.lt_cotrans ha_lt_abs (0 : Scalar) with ha0 | h0abs
    · exact ha0
    · rcases scalarCOFOSeed.lt_or_lt_of_abs_pos h0abs with h0a | ha0
      · have hnotneg : ¬ COF.lt a 0 := by
          intro ha0
          exact COF.lt_irrefl (0 : Scalar)
            (scalarCOFOSeed.lt_trans h0a ha0)
        have habs_eq : COF.abs a = a :=
          scalarCOFOSeed.abs_of_nonneg hnotneg
        have hzero : COF.lt (eps k) (0 : Scalar) := by
          rwa [habs_eq, show a - a = (0 : Scalar) from by ring] at hgap
        exact False.elim
          (COF.lt_irrefl (0 : Scalar)
            (scalarCOFOSeed.lt_trans (eps_pos k) hzero))
      · exact ha0
  have hneg_nonneg : Le 0 (-a) := by
    intro hneg_lt_zero
    have hzero_lt_a : COF.lt (0 : Scalar) a := by
      have t := COF.lt_add_left a hneg_lt_zero
      rwa [show a + -a = (0 : Scalar) from by ring,
        show a + (0 : Scalar) = a from by ring] at t
    exact COF.lt_irrefl (0 : Scalar)
      (scalarCOFOSeed.lt_trans hzero_lt_a ha_neg)
  have habs_eq_neg : COF.abs a = -a := by
    have hneg_abs := scalarCOFOSeed.abs_of_nonneg hneg_nonneg
    rw [scalarCOFOSeed.abs_neg a] at hneg_abs
    exact hneg_abs
  have hgap_neg : COF.lt (eps k) (-a - a) := by
    rwa [habs_eq_neg] at hgap
  have hraw :
      COF.lt ((COF.half : Scalar) * eps k)
        ((COF.half : Scalar) * (-a - a)) :=
    scalar_mul_lt_mul_left hgap_neg scalarCOFOSeed.half_pos
  change COF.lt (eps (k + 1)) (-a)
  rwa [show (COF.half : Scalar) * eps k = eps (k + 1) from rfl,
    show (COF.half : Scalar) * (-a - a) = -a from by
      calc
        (COF.half : Scalar) * (-a - a)
            = (COF.half : Scalar) * (-a + -a) := by ring
        _ = ((COF.half : Scalar) + COF.half) * (-a) := by ring
        _ = (1 : Scalar) * (-a) := by rw [COF.half_add_half]
        _ = -a := by ring] at hraw

/-- Representative-level form of `¬ x < 0 -> |x| = x`.

The equality target is eventual Bishop equality.  If the target gauge failed at
a late index, the scalar lemma gives a dyadic lower bound for `-x` at the
previous `subSeq` index; regularity then extends that point to a positive tail.
-/
theorem relEventually_abs_of_not_pos_neg
    (x : RegularSeq)
    (hx : ¬ PosEventually (subSeq zeroSeq x)) :
    relEventually (absSeq x) x := by
  intro k
  refine ⟨k + 4, ?_⟩
  intro n hn
  change Le (COF.abs (COF.abs (x.val n) - x.val n)) (eps k)
  intro hbad
  let M : Nat := n - 1
  have hn_pos : 0 < n := by omega
  have hM_succ : M + 1 = n := by
    unfold M
    exact Nat.succ_pred_eq_of_pos hn_pos
  have hMlate : k + 3 ≤ M := by
    unfold M
    omega
  have hneg :
      COF.lt (eps (k + 1)) (-x.val n) :=
    scalar_eps_lt_abs_abs_sub_self_implies_neg hbad
  have hpoint : COF.lt (eps (k + 1)) ((subSeq zeroSeq x).val M) := by
    change COF.lt (eps (k + 1)) (0 - x.val (M + 1))
    rw [hM_succ]
    rwa [zero_sub]
  have htail : PosEventually (subSeq zeroSeq x) :=
    posEventually_of_late_point (subSeq zeroSeq x) hMlate hpoint
  exact hx htail

/-- Quotient-level absolute value of a nonnegative element. -/
theorem absQuot_of_nonneg (x : CRealQuot) :
    ¬ ltQuot x zeroQuot → absQuot x = x := by
  refine Quotient.inductionOn x ?_
  intro xr hx
  change ¬ PosEventually (subSeq zeroSeq xr) at hx
  change mkQuot (absSeq xr) = mkQuot xr
  exact Quotient.sound (relEventually_abs_of_not_pos_neg xr hx)

/-- Basic quotient `COFO` fields through Archimedean plus `abs_of_nonneg`. -/
structure CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsNonnegFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldData cof where
  abs_of_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a : CRealQuot}, ¬ COF.lt a 0 → COF.abs a = a

/-- Data-order/representative branch package including `abs_of_nonneg`. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsNonnegFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsNonnegFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldDataWith
      A rep ltDataOf
  abs_of_nonneg := by
    intro a ha
    change absQuot a = a
    exact absQuot_of_nonneg a ha

/-- Frontier after quotient `abs_of_nonneg` is closed. -/
structure CRealQuotCOFOAfterAbsNonnegFrontier : Type where
  abs_le_of : Prop
  mul_nonneg : Prop
  mul_archimedean : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterAbsNonnegFrontier :
    CRealQuotCOFOAfterAbsNonnegFrontier where
  abs_le_of := True
  mul_nonneg := True
  mul_archimedean := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

