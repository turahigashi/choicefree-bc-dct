import Mathdemo.Internal.Real.FirstConcreteCRealQuotientCOFOFields

/-!
# CReal quotient strict-order transitivity

`FirstConcreteCRealQuotientCOFOFields` closed the first four quotient `COFO` fields.  This file closes
the next local order field: transitivity of the quotient strict order.

The proof is representative-level and tail-based.  If `b - a` and `c - b` are
eventually bounded below by dyadic gauges, then at a common late index we
weaken both gauges to the same finer dyadic gauge and add the inequalities to
obtain eventual positivity of `c - a`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar helper: a non-strict lower bound followed by a strict upper bound
gives a strict inequality.  This uses only cotransitivity of the scalar `COF`
order, not a global scalar `COFO` instance. -/
theorem scalar_lt_of_le_of_lt {a b c : Scalar}
    (hab : Le a b) (hbc : COF.lt b c) : COF.lt a c := by
  rcases COF.lt_cotrans hbc a with hba | hac
  · exact False.elim (hab hba)
  · exact hac

/-- Scalar helper: strict inequalities add.  The scalar transitivity used here
comes from the audited `scalarCOFOSeed`. -/
theorem scalar_lt_add {a b c d : Scalar}
    (h1 : COF.lt a b) (h2 : COF.lt c d) : COF.lt (a + c) (b + d) := by
  have e1 : COF.lt (a + c) (b + c) := by
    have t := COF.lt_add_left c h1
    rwa [show c + a = a + c from by ring,
      show c + b = b + c from by ring] at t
  have e2 : COF.lt (b + c) (b + d) := COF.lt_add_left b h2
  exact scalarCOFOSeed.lt_trans e1 e2

/-- Tail-stable positivity is transitive for representative differences. -/
theorem posEventually_sub_trans (a b c : RegularSeq) :
    PosEventually (subSeq b a) →
    PosEventually (subSeq c b) →
      PosEventually (subSeq c a) := by
  intro hab hbc
  rcases hab with ⟨ka, Na, hNa⟩
  rcases hbc with ⟨kb, Nb, hNb⟩
  let j : Nat := max ka kb
  refine ⟨j, Na + Nb, ?_⟩
  intro n hn
  have hnA : Na ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hnB : Nb ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have h1 := hNa n hnA
  have h2 := hNb n hnB
  change COF.lt (eps ka) (b.val (n + 1) - a.val (n + 1)) at h1
  change COF.lt (eps kb) (c.val (n + 1) - b.val (n + 1)) at h2
  have hle1 : Le (eps (j + 1)) (eps ka) := by
    exact eps_le_of_le (by unfold j; omega)
  have hle2 : Le (eps (j + 1)) (eps kb) := by
    exact eps_le_of_le (by unfold j; omega)
  have h1fine : COF.lt (eps (j + 1)) (b.val (n + 1) - a.val (n + 1)) :=
    scalar_lt_of_le_of_lt hle1 h1
  have h2fine : COF.lt (eps (j + 1)) (c.val (n + 1) - b.val (n + 1)) :=
    scalar_lt_of_le_of_lt hle2 h2
  have hsum := scalar_lt_add h1fine h2fine
  rw [eps_succ_add_self j] at hsum
  change COF.lt (eps j) ((subSeq c a).val n)
  change COF.lt (eps j) (c.val (n + 1) - a.val (n + 1))
  rwa [show
      (b.val (n + 1) - a.val (n + 1)) + (c.val (n + 1) - b.val (n + 1))
        = c.val (n + 1) - a.val (n + 1)
      from by ring] at hsum

/-- Representative-level transitivity of the quotient strict order. -/
theorem ltQuot_trans_mk (a b c : RegularSeq) :
    ltQuot (mkQuot a) (mkQuot b) →
    ltQuot (mkQuot b) (mkQuot c) →
      ltQuot (mkQuot a) (mkQuot c) := by
  change PosEventually (subSeq b a) →
    PosEventually (subSeq c b) →
      PosEventually (subSeq c a)
  exact posEventually_sub_trans a b c

/-- Quotient-level transitivity of the strict order. -/
theorem ltQuot_trans (a b c : CRealQuot) :
    ltQuot a b → ltQuot b c → ltQuot a c := by
  refine Quotient.inductionOn a ?_
  intro ar
  refine Quotient.inductionOn b ?_
  intro br
  refine Quotient.inductionOn c ?_
  intro cr
  exact ltQuot_trans_mk ar br cr

/-- The closed basic `COFO` fields plus strict-order transitivity. -/
structure CRealQuotCOFOBasicAndTransFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicFieldData cof where
  lt_trans :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b c : CRealQuot}, COF.lt a b → COF.lt b c → COF.lt a c

/-- Basic fields plus transitivity for the data-order/representative COF fork. -/
def cRealQuotCOFOBasicAndTransFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicAndTransFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicFieldData :=
    cRealQuotCOFOBasicFieldDataWith A rep ltDataOf
  lt_trans := by
    intro a b c hab hbc
    change ltQuot a c
    exact ltQuot_trans a b c hab hbc

/-- Basic fields plus transitivity for the decidable strict-order COF fork. -/
def cRealQuotCOFOBasicAndTransFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicAndTransFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicFieldData :=
    cRealQuotCOFOBasicFieldDataWithDecidableLT A hdec
  lt_trans := by
    intro a b c hab hbc
    change ltQuot a c
    exact ltQuot_trans a b c hab hbc

/-- Frontier after quotient strict-order transitivity is closed. -/
structure CRealQuotCOFOAfterLTTransFrontier : Type where
  abs_order_bounds : Prop
  abs_add_mul_laws : Prop
  archimedean_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterLTTransFrontier :
    CRealQuotCOFOAfterLTTransFrontier where
  abs_order_bounds := True
  abs_add_mul_laws := True
  archimedean_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

