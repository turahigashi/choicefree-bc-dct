import Mathdemo.Internal.Sec4_relIntegral_abs_continuous_iteration1

/-!
# Sec4 theorem 4.15: faithful split inequality

This file isolates the first displayed inequality in the source proof of
Bishop--Cheng theorem 4.15:

```text
chi_B = chi_{A and B} + chi_{-A and B} <= chi_{A and B} + chi_{-A}
```

and transports it through the direct measurable relative integral.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Full support for the theorem-4.15 split comparison
`I_B(u) <= I_{A and B}(u) + I_{-A}(u)`. -/
def thm_4_15_ib_split_support
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u) : Set X :=
  (((((genIB_rep_from_measurable B hB u hnn).domain ∩
      (genIB_rep_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn).domain) ∩
      (genIB_rep_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn).domain) ∩
      hA.rep.domain) ∩
      u.domain)


/-- The split-comparison support is full. -/
theorem thm_4_15_ib_split_support_full
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u) :
    IsFull S (thm_4_15_ib_split_support (S := S) A B hA hB u hnn) := by
  unfold thm_4_15_ib_split_support
  exact isFull_inter
    (isFull_inter
      (isFull_inter
        (isFull_inter
          (IntegrableRep.domain_isFull
            (genIB_rep_from_measurable B hB u hnn))
          (IntegrableRep.domain_isFull
            (genIB_rep_from_measurable (BSet.and A B)
              (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)))
        (IntegrableRep.domain_isFull
          (genIB_rep_from_measurable (BSet.neg A)
            (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)))
      (IntegrableRep.domain_isFull hA.rep))
    (IntegrableRep.domain_isFull u)


/-- Pointwise version of the source inequality
`chi_B u <= chi_{A and B} u + chi_{-A} u`, expressed through the direct
`genIB` value bridges. -/
theorem thm_4_15_genIB_split_le_on_support
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u)
    (VB : Sec4GenIBValueBridge (S := S) B hB u hnn)
    (VAB : Sec4GenIBValueBridge (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
    (VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn) :
    ∀ x ∈ thm_4_15_ib_split_support (S := S) A B hA hB u hnn,
      ∀ (hleft : RSeq.SeriesSum
        (fun n => ((genIB_rep_from_measurable B hB u hnn).fn n).toFun x))
        (hright : RSeq.SeriesSum
        (fun n =>
          (((genIB_rep_from_measurable (BSet.and A B)
              (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn).add
            (genIB_rep_from_measurable (BSet.neg A)
              (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)).fn n).toFun x)),
        Le hleft.sum hright.sum := by
  intro x hx hleft hright
  rcases hx with ⟨⟨⟨⟨hBDom, hABDom⟩, hNegDom⟩, hADom⟩, huDom⟩
  rcases hBDom.2 with ⟨hBabs⟩
  rcases hABDom.2 with ⟨hABabs⟩
  rcases hNegDom.2 with ⟨hNegabs⟩
  rcases hADom.2 with ⟨hAabs⟩
  rcases huDom.2 with ⟨huabs⟩
  let hBsum : RSeq.SeriesSum
      (fun n => ((genIB_rep_from_measurable B hB u hnn).fn n).toFun x) :=
    seriesSum_of_abs hBabs
  let hABsum : RSeq.SeriesSum
      (fun n => ((genIB_rep_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn).fn n).toFun x) :=
    seriesSum_of_abs hABabs
  let hNegsum : RSeq.SeriesSum
      (fun n => ((genIB_rep_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn).fn n).toFun x) :=
    seriesSum_of_abs hNegabs
  have hleft_eq : hleft.sum = hBsum.sum :=
    seriesSum_unique hleft hBsum
  have hright_eq : hright.sum = hABsum.sum + hNegsum.sum :=
    seriesSum_unique hright (add_seriesSum_value hABsum hNegsum)
  have hAB_nonneg : Nonneg hABsum.sum :=
    genIB_rep_from_measurable_repNonneg
      (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA))
      u hnn x hABabs hABsum
  have hNeg_nonneg : Nonneg hNegsum.sum :=
    genIB_rep_from_measurable_repNonneg
      (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA)
      u hnn x hNegabs hNegsum
  have hBcases := VB.domain x hBabs
  have hAcases := (hA.valid x hAabs).1
  cases hBcases with
  | inl hxB1 =>
      have hB_value : hBsum.sum = (seriesSum_of_abs huabs).sum :=
        VB.value_s1 x hxB1 hBabs huabs
      cases hAcases with
      | inl hxA1 =>
          have hAB_value : hABsum.sum = (seriesSum_of_abs huabs).sum :=
            VAB.value_s1 x ⟨hxA1, hxB1⟩ hABabs huabs
          rw [hleft_eq, hright_eq, hB_value, hAB_value]
          exact le_of_nonneg_sub (by
            rw [show ((seriesSum_of_abs huabs).sum + hNegsum.sum
                  - (seriesSum_of_abs huabs).sum) = hNegsum.sum from by ring]
            exact hNeg_nonneg)
      | inr hxA2 =>
          have hNeg_value : hNegsum.sum = (seriesSum_of_abs huabs).sum :=
            VnegA.value_s1 x hxA2 hNegabs huabs
          rw [hleft_eq, hright_eq, hB_value, hNeg_value]
          exact le_of_nonneg_sub (by
            rw [show (hABsum.sum + (seriesSum_of_abs huabs).sum
                  - (seriesSum_of_abs huabs).sum) = hABsum.sum from by ring]
            exact hAB_nonneg)
  | inr hxB2 =>
      have hB_value : hBsum.sum = 0 :=
        VB.value_s2 x hxB2 hBabs
      rw [hleft_eq, hright_eq, hB_value]
      exact le_of_nonneg_sub (by
        rw [sub_zero]
        exact nonneg_add hAB_nonneg hNeg_nonneg)


/-- Integral form of the first displayed inequality in theorem 4.15:
`I_B(u) <= I_{A and B}(u) + I_{-A}(u)`. -/
theorem thm_4_15_genIB_split_le
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u)
    (VB : Sec4GenIBValueBridge (S := S) B hB u hnn)
    (VAB : Sec4GenIBValueBridge (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
    (VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn) :
    Le
      (genRelIntegral_from_measurable B hB u hnn)
      (genRelIntegral_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn
        + genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn) := by
  unfold genRelIntegral_from_measurable
  rw [← IntegrableRep.integral_add]
  exact prop_1_11
    (thm_4_15_ib_split_support_full (S := S) A B hA hB u hnn)
    (genIB_rep_from_measurable B hB u hnn)
    ((genIB_rep_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn).add
      (genIB_rep_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn))
    (thm_4_15_genIB_split_le_on_support
      (S := S) A B hA hB u hnn VB VAB VnegA)


/-- Strict form of the source split estimate in theorem 4.15.

Once the two pieces on the right side are known to be small, the general
measurable relative integral over `B` is small.  This is the arithmetic part of
the source passage

`I_B(u) <= I_{A∧B}(u) + I_{-A}(u) < eps`.
-/
theorem thm_4_15_genIB_split_lt_of_piece_bounds
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u)
    (VB : Sec4GenIBValueBridge (S := S) B hB u hnn)
    (VAB : Sec4GenIBValueBridge (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
    (VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
    (epsAB epsNeg eps : R)
    (hAB : COF.lt
      (genRelIntegral_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
      epsAB)
    (hNeg : COF.lt
      (genRelIntegral_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
      epsNeg)
    (hsum : COF.lt (epsAB + epsNeg) eps) :
    COF.lt (genRelIntegral_from_measurable B hB u hnn) eps := by
  have hsplit :=
    thm_4_15_genIB_split_le
      (S := S) A B hA hB u hnn VB VAB VnegA
  have hpieces : COF.lt
      (genRelIntegral_from_measurable (BSet.and A B)
          (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn
        + genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
      (epsAB + epsNeg) :=
    lt_add hAB hNeg
  exact COFO.lt_trans (lt_of_le_of_lt hsplit hpieces) hsum


/-- Strict split estimate with explicit upper bounds for the two pieces.

This is the arithmetic form of the second displayed inequality in the source
proof of theorem 4.15:

`I_{A∧B}(u)+I_{-A}(u) <= upperAB + upperNeg < eps`.

In the intended DCT use, the two upper bounds are the corresponding relative
integrals of `2g`; this theorem deliberately keeps them abstract so the
domination comparison can be supplied by a later source-faithful bridge. -/
theorem thm_4_15_genIB_split_lt_of_piece_upper_bounds
    (A B : BSet X) (hA : IntegrableSet1 S A)
    (hB : IsMeasurableSet (S := S) B)
    (u : IntegrableRep S) (hnn : RepNonneg u)
    (VB : Sec4GenIBValueBridge (S := S) B hB u hnn)
    (VAB : Sec4GenIBValueBridge (S := S) (BSet.and A B)
      (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
    (VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
    (upperAB upperNeg epsAB epsNeg eps : R)
    (hAB_le : Le
      (genRelIntegral_from_measurable (BSet.and A B)
        (isMeasurableSet_of_integrable (S := S) (hB A hA)) u hnn)
      upperAB)
    (hNeg_le : Le
      (genRelIntegral_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA) u hnn)
      upperNeg)
    (hAB_lt : COF.lt upperAB epsAB)
    (hNeg_lt : COF.lt upperNeg epsNeg)
    (hsum : COF.lt (epsAB + epsNeg) eps) :
    COF.lt (genRelIntegral_from_measurable B hB u hnn) eps :=
  thm_4_15_genIB_split_lt_of_piece_bounds
    (S := S) A B hA hB u hnn VB VAB VnegA epsAB epsNeg eps
    (lt_of_le_of_lt hAB_le hAB_lt)
    (lt_of_le_of_lt hNeg_le hNeg_lt)
    hsum


end BishopC
