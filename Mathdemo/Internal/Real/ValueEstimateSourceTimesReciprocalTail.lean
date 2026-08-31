import Mathdemo.Internal.Real.SourceQuotientRepresentedPositiveOrderData

/-!
# Value estimate for source times reciprocal tail

`SourceQuotientRepresentedPositiveOrderData` connects the positive source representative back to the quotient
element.  The next analytic ingredient for `mul_inv_cancel` is a value-level
estimate: multiplying a source sample by a reciprocal-tail sample is close to
one, with the error controlled by the distance between the two source samples.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- If the reciprocal sample is taken at the reindexed source point `q`, then
the product with any source sample `p` is close to one in proportion to
`|x_p - x_q|`. -/
theorem positiveTail_source_mul_invValWithBound_abs_sub_one_le
    (A : ScalarMulArchimedeanData)
    (x : RegularSeq) (h : PosEventuallyData x)
    (p m : Nat) :
    Le
      (COF.abs
        (x.val p * positiveTailInvValWithBound A x h m - 1))
      (COF.abs (scalarPositiveInverseSeed.inv (eps h.k)) *
        (eps p + eps (reciprocalTailIndexWith A x h m))) := by
  set q : Nat := reciprocalTailIndexWith A x h m
  set invm : Scalar := positiveTailInvValWithBound A x h m
  set L : Scalar := COF.abs (scalarPositiveInverseSeed.inv (eps h.k))
  have hcancel : x.val q * invm = 1 := by
    simpa [q, invm] using positiveTail_mul_invValWithBound_eq_one A x h m
  have hrewrite :
      x.val p * invm - 1 = (x.val p - x.val q) * invm := by
    rw [← hcancel]
    ring
  have hdist : Le (COF.abs (x.val p - x.val q)) (eps p + eps q) :=
    x.regular p q
  have hinv : Le (COF.abs invm) L := by
    simpa [invm, L] using positiveTailInvValWithBound_abs_le_lipschitzFactor A x h m
  have hstep1 :
      Le
        (COF.abs (x.val p - x.val q) * COF.abs invm)
        ((eps p + eps q) * COF.abs invm) :=
    scalar_mul_le_mul_right hdist (scalar_abs_nonneg invm)
  have hstep2 :
      Le
        ((eps p + eps q) * COF.abs invm)
        (L * (eps p + eps q)) := by
    have h := scalar_mul_le_mul_left hinv (eps_add_nonneg p q)
    rwa [show (eps p + eps q) * L = L * (eps p + eps q) from by ring] at h
  rw [hrewrite, scalar_abs_mul]
  exact BishopC.le_trans hstep1 hstep2

/-- The previous estimate can be absorbed into a dyadic budget once both source
sample indices are beyond the scalar bound for the reciprocal uniform bound. -/
theorem positiveTail_source_mul_invValWithBound_abs_sub_one_le_budget
    (A : ScalarMulArchimedeanData)
    (x : RegularSeq) (h : PosEventuallyData x)
    {p m r : Nat}
    (hp : scalarBoundWith A (COF.abs (scalarPositiveInverseSeed.inv (eps h.k))) + r ≤ p)
    (hq : scalarBoundWith A (COF.abs (scalarPositiveInverseSeed.inv (eps h.k))) + r ≤
      reciprocalTailIndexWith A x h m) :
    Le
      (COF.abs
        (x.val p * positiveTailInvValWithBound A x h m - 1))
      (eps r + eps r) := by
  set q : Nat := reciprocalTailIndexWith A x h m
  set L : Scalar := COF.abs (scalarPositiveInverseSeed.inv (eps h.k))
  have hbase :
      Le
        (COF.abs
          (x.val p * positiveTailInvValWithBound A x h m - 1))
        (L * (eps p + eps q)) := by
    simpa [L, q] using positiveTail_source_mul_invValWithBound_abs_sub_one_le A x h p m
  have hLnonneg : Le 0 L := by
    unfold L
    exact scalar_abs_nonneg (scalarPositiveInverseSeed.inv (eps h.k))
  have hLabs : COF.abs L = L :=
    scalarCOFOSeed.abs_of_nonneg hLnonneg
  have hpterm : Le (L * eps p) (eps r) := by
    have h := scalar_bound_eps_le_of_ge A L hp
    rwa [hLabs] at h
  have hqterm : Le (L * eps q) (eps r) := by
    have h := scalar_bound_eps_le_of_ge A L (by simpa [L, q] using hq)
    rwa [hLabs] at h
  have hterms : Le (L * (eps p + eps q)) (eps r + eps r) := by
    rw [show L * (eps p + eps q) = L * eps p + L * eps q from by ring]
    exact BishopC.le_add hpterm hqterm
  exact BishopC.le_trans hbase hterms

/-- Data package for the source-times-reciprocal value estimate. -/
structure PositiveTailSourceMulReciprocalEstimateSeed : Type where
  product_abs_sub_one_le :
    ∀ A : ScalarMulArchimedeanData,
      ∀ x : RegularSeq, ∀ h : PosEventuallyData x,
      ∀ p m : Nat,
        Le
          (COF.abs
            (x.val p * positiveTailInvValWithBound A x h m - 1))
          (COF.abs (scalarPositiveInverseSeed.inv (eps h.k)) *
            (eps p + eps (reciprocalTailIndexWith A x h m)))
  product_abs_sub_one_le_budget :
    ∀ A : ScalarMulArchimedeanData,
      ∀ x : RegularSeq, ∀ h : PosEventuallyData x,
      ∀ {p m r : Nat},
        scalarBoundWith A (COF.abs (scalarPositiveInverseSeed.inv (eps h.k))) + r ≤ p →
        scalarBoundWith A (COF.abs (scalarPositiveInverseSeed.inv (eps h.k))) + r ≤
          reciprocalTailIndexWith A x h m →
        Le
          (COF.abs
            (x.val p * positiveTailInvValWithBound A x h m - 1))
          (eps r + eps r)

def positiveTailSourceMulReciprocalEstimateSeed :
    PositiveTailSourceMulReciprocalEstimateSeed where
  product_abs_sub_one_le := positiveTail_source_mul_invValWithBound_abs_sub_one_le
  product_abs_sub_one_le_budget :=
    positiveTail_source_mul_invValWithBound_abs_sub_one_le_budget

/-- Frontier after the value-level cancellation estimate is available. -/
structure CRealQuotPositiveInverseProductEstimateFrontier : Type where
  quotient_product_eventual_cancel : Prop
  quotient_inv_pos_uniform_lower_bound : Prop
  cauchy_completeness : Prop

def cRealQuotPositiveInverseProductEstimateFrontier :
    CRealQuotPositiveInverseProductEstimateFrontier where
  quotient_product_eventual_cancel := True
  quotient_inv_pos_uniform_lower_bound := True
  cauchy_completeness := True

end BishopCReal

