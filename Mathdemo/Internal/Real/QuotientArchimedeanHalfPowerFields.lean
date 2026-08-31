import Mathdemo.Internal.Real.QuotientMaxMinAbsoluteBounds

/-!
# Quotient Archimedean half-power fields

`QuotientMaxMinAbsoluteBounds` closed the max/min order fields.  This file adds the two
Archimedean fields that only require the already-available tail-positivity
definition:

* `archimedean`;
* `archimedean_pos`.

The proof is intentionally modest.  A positive quotient has a representative
tail bounded below by `eps k`; subtracting one dyadic half gives a strict lower
bound by the constant sequence `eps (k+1)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Multiplying the quotient half by a dyadic constant gives the next dyadic
constant. -/
theorem mulQuotConcrete_half_const_eps_with
    (A : ScalarMulArchimedeanData) (m : Nat) :
    mulQuotConcreteWith A halfQuot (constQuot (eps m)) =
      constQuot (eps (m + 1)) := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (boundedMulValWith A halfSeq (constSeq (eps m)))
    (constVal (eps (m + 1)))
  intro n
  unfold boundedMulValWith mulValWithBound
  simp only [halfSeq, constSeq, constVal]
  rw [show (COF.half : Scalar) * eps m = eps (m + 1) from rfl,
    show eps (m + 1) - eps (m + 1) = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF (0 : Scalar)) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- In the data/representative COF fork, quotient half-powers are exactly the
constant dyadic gauges. -/
theorem halfPowQuot_eq_const_eps_with
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (m : Nat) :
    letI : BishopC.COF CRealQuot :=
      cRealQuotCOFConditionalWith A rep ltDataOf
    COF.halfPow (R := CRealQuot) m = constQuot (eps m) := by
  change @COF.halfPow CRealQuot (cRealQuotCOFConditionalWith A rep ltDataOf) m =
    constQuot (eps m)
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      change mulQuotConcreteWith A halfQuot
        (@COF.halfPow CRealQuot (cRealQuotCOFConditionalWith A rep ltDataOf) m) =
          constQuot (eps (m + 1))
      rw [ih]
      exact mulQuotConcrete_half_const_eps_with A m

/-- In the decidable-order COF fork, quotient half-powers are exactly the
constant dyadic gauges. -/
theorem halfPowQuot_eq_const_eps_with_decidable
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable)
    (m : Nat) :
    letI : BishopC.COF CRealQuot :=
      cRealQuotCOFConditionalWithDecidableLT A hdec
    COF.halfPow (R := CRealQuot) m = constQuot (eps m) := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      change mulQuotConcreteWith A halfQuot
        (@COF.halfPow CRealQuot (cRealQuotCOFConditionalWithDecidableLT A hdec) m) =
          constQuot (eps (m + 1))
      rw [ih]
      exact mulQuotConcrete_half_const_eps_with A m

/-- Existence-form quotient Archimedean law for constant dyadic gauges. -/
theorem archimedeanQuot_const (t : CRealQuot) :
    ltQuot zeroQuot t → ∃ k : Nat, ltQuot (constQuot (eps k)) t := by
  refine Quotient.inductionOn t ?_
  intro x h
  change PosEventually (subSeq x zeroSeq) at h
  rcases h with ⟨k, N, hN⟩
  refine ⟨k + 1, ?_⟩
  change PosEventually (subSeq x (constSeq (eps (k + 1))))
  refine ⟨k + 1, N, ?_⟩
  intro n hn
  have hx := hN n hn
  change COF.lt (eps k) (x.val (n + 1) - 0) at hx
  have hshift : COF.lt (eps (k + 1))
      ((x.val (n + 1) - 0) - eps (k + 1)) := by
    have t := COF.lt_add_left (-(eps (k + 1))) hx
    rwa [← eps_succ_add_self k,
      show -(eps (k + 1)) + (eps (k + 1) + eps (k + 1)) = eps (k + 1)
        from by ring,
      show -(eps (k + 1)) + (x.val (n + 1) - 0) =
          (x.val (n + 1) - 0) - eps (k + 1)
        from by ring] at t
  change COF.lt (eps (k + 1)) (x.val (n + 1) - eps (k + 1))
  rwa [show (x.val (n + 1) - 0) - eps (k + 1) =
      x.val (n + 1) - eps (k + 1) from by ring] at hshift

/-- Data-form quotient Archimedean law from a data strict-order witness.

The left representative may only be eventually equal to zero.  We therefore
spend two extra dyadic halvings: one to absorb that representative and one to
keep a strict positive tail after subtracting the constant gauge. -/
def archimedeanQuot_const_data_of_ltData {t : CRealQuot}
    (h : ltQuotData zeroQuot t) :
    { k : Nat // ltQuot (constQuot (eps k)) t } := by
  rcases h with ⟨zr, tr, hz, ht, hpos⟩
  rcases hpos with ⟨k, N, hN⟩
  have hzrel : relEventually zeroSeq zr := by
    change mkQuot zeroSeq = mkQuot zr at hz
    exact Quotient.exact hz
  refine ⟨k + 2, ?_⟩
  rcases hzrel (k + 2) with ⟨Nz, hzN⟩
  rw [ht]
  change PosEventually (subSeq tr (constSeq (eps (k + 2))))
  refine ⟨k + 1, N + Nz, ?_⟩
  intro n hn
  have hNn : N ≤ n := Nat.le_trans (Nat.le_add_right N Nz) hn
  have hZ : Nz ≤ n + 1 := by
    have hZn : Nz ≤ n := Nat.le_trans (Nat.le_add_left Nz N) hn
    exact Nat.le_trans hZn (Nat.le_succ n)
  set e2 : Scalar := eps (k + 2)
  set z : Scalar := zr.val (n + 1)
  set u : Scalar := tr.val (n + 1)
  have hraw := hN n hNn
  change COF.lt (eps k) (u - z) at hraw
  have hzclose := hzN (n + 1) hZ
  change Le (COF.abs ((0 : Scalar) - z)) e2 at hzclose
  have hzlower0 : Le ((0 : Scalar) - e2) z :=
    scalar_point_lower_of_abs_le hzclose
  have hzlower : Le (-e2) z := by
    rwa [show (0 : Scalar) - e2 = -e2 from by ring] at hzlower0
  have hzminus : Le (-(e2 + e2)) (z - e2) := by
    have hsum := BishopC.le_add hzlower (BishopC.le_refl (-e2))
    rwa [show -e2 + -e2 = -(e2 + e2) from by ring,
      show z + -e2 = z - e2 from by ring] at hsum
  have hbase : Le (eps k - (e2 + e2)) ((z - e2) + eps k) := by
    have hsum := BishopC.le_add hzminus (BishopC.le_refl (eps k))
    rwa [show -(e2 + e2) + eps k = eps k - (e2 + e2) from by ring] at hsum
  have hbase' : Le (eps (k + 1)) ((z - e2) + eps k) := by
    have heq : eps k - (e2 + e2) = eps (k + 1) := by
      unfold e2
      rw [← eps_succ_add_self k, eps_succ_add_self (k + 1)]
      ring
    rwa [heq] at hbase
  have hstrict0 := COF.lt_add_left (z - e2) hraw
  have hstrict : COF.lt ((z - e2) + eps k) (u - e2) := by
    rwa [show (z - e2) + (u - z) = u - e2 from by ring] at hstrict0
  have hfinal : COF.lt (eps (k + 1)) (u - e2) :=
    scalar_lt_of_le_of_lt hbase' hstrict
  change COF.lt (eps (k + 1)) (tr.val (n + 1) - eps (k + 2))
  rwa [show u - e2 = tr.val (n + 1) - eps (k + 2) from by
    unfold u e2
    rfl] at hfinal

/-- Basic quotient `COFO` fields through max/min and the two Archimedean
fields. -/
structure CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinFieldData cof where
  archimedean :
    letI : BishopC.COF CRealQuot := cof
    ∀ t : CRealQuot, COF.lt 0 t → ∃ k : Nat,
      COF.lt (COF.halfPow (R := CRealQuot) k) t
  archimedean_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ t : CRealQuot, COF.lt 0 t → { k : Nat //
      COF.lt (COF.halfPow (R := CRealQuot) k) t }

/-- Data-order/representative branch package including the Archimedean fields. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinFieldDataWith
      A rep ltDataOf
  archimedean := by
    intro t ht
    rcases archimedeanQuot_const_data_of_ltData (ltDataOf ht) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rwa [halfPowQuot_eq_const_eps_with A rep ltDataOf k]
  archimedean_pos := by
    intro t ht
    rcases archimedeanQuot_const_data_of_ltData (ltDataOf ht) with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rwa [halfPowQuot_eq_const_eps_with A rep ltDataOf k]

/-- Frontier after quotient Archimedean fields are closed. -/
structure CRealQuotCOFOAfterArchimedeanFrontier : Type where
  abs_le_of : Prop
  abs_of_nonneg : Prop
  mul_nonneg : Prop
  mul_archimedean : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterArchimedeanFrontier :
    CRealQuotCOFOAfterArchimedeanFrontier where
  abs_le_of := True
  abs_of_nonneg := True
  mul_nonneg := True
  mul_archimedean := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

