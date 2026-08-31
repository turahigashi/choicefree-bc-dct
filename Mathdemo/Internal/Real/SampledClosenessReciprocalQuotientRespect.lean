import Mathdemo.Internal.Real.MixedReciprocalEstimatesQuotientRespect

/-!
# Sampled closeness for reciprocal quotient respect

`MixedReciprocalEstimatesQuotientRespect` reduced reciprocal-tail respect to a sampled closeness
obligation.  This file closes that obligation from eventual Bishop equality of
the source representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Three copies of a two-step finer dyadic gauge fit under the original gauge. -/
theorem eps_three_two_steps_le (k : Nat) :
    Le ((eps (k + 2) + eps (k + 2)) + eps (k + 2)) (eps k) := by
  rw [eps_succ_add_self (k + 1)]
  have hsum : Le (eps (k + 1) + eps (k + 2)) (eps (k + 1) + eps (k + 1)) :=
    BishopC.le_add (BishopC.le_refl (eps (k + 1))) (eps_succ_le_eps (k + 1))
  rwa [eps_succ_add_self k] at hsum

/-- If a sample index is beyond a scalar Archimedean bound, multiplication by
the scalar is absorbed by the target dyadic gauge. -/
theorem scalar_bound_eps_le_of_ge
    (A : ScalarMulArchimedeanData) (B : Scalar) {p r : Nat}
    (hp : scalarBoundWith A B + r ≤ p) :
    Le (COF.abs B * eps p) (eps r) := by
  have heps : Le (eps p) (eps (scalarBoundWith A B + r)) :=
    eps_le_of_le hp
  have hmul :
      Le (COF.abs B * eps p)
        (COF.abs B * eps (scalarBoundWith A B + r)) :=
    scalar_mul_le_mul_left heps (scalar_abs_nonneg B)
  exact BishopC.le_trans hmul (scalar_bound_tail_eps_le A B r)

/-- Reciprocal-tail output indices are at least the original output index. -/
theorem reciprocalTailIndex_ge_self
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    n ≤ reciprocalTailIndexWith A x h n := by
  have hbase : n ≤ reciprocalTailBoundWith A x h + n := by
    omega
  exact Nat.le_trans hbase (reciprocalTailIndex_bound A x h n)

/-- A distance between independently sampled source representatives is
controlled by one source regularity estimate plus one eventual-equality
estimate. -/
theorem sampled_source_abs_le_regular_eventual
    (x y : RegularSeq) {j p q : Nat}
    (hxy_p : Le (COF.abs (x.val p - y.val p)) (eps j)) :
    Le (COF.abs (y.val q - x.val p)) ((eps q + eps p) + eps j) := by
  have hyreg : Le (COF.abs (y.val q - y.val p)) (eps q + eps p) :=
    y.regular q p
  have hmid : Le (COF.abs (y.val p - x.val p)) (eps j) := by
    rw [show y.val p - x.val p = -(x.val p - y.val p) from by ring]
    change Le (BishopCRat.CRat.absF (-(x.val p - y.val p))) (eps j)
    rw [BishopCRat.CRat.abs_neg (x.val p - y.val p)]
    exact hxy_p
  have htri :
      Le (COF.abs (y.val q - x.val p))
        (COF.abs (y.val q - y.val p) + COF.abs (y.val p - x.val p)) := by
    have h := scalar_abs_add_le (y.val q - y.val p) (y.val p - x.val p)
    rwa [show (y.val q - y.val p) + (y.val p - x.val p) =
        y.val q - x.val p from by ring] at h
  exact BishopC.le_trans htri (BishopC.le_add hyreg hmid)

/-- The sampled source representatives of eventually equal positive
representatives are close enough for the mixed reciprocal Lipschitz estimate. -/
theorem positiveTailReciprocalSampledClose_of_relEventually
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq)
    (hx : PosEventuallyData x) (hy : PosEventuallyData y)
    (hxy : relEventually x y) :
    positiveTailReciprocalSampledClose A x hx y hy := by
  intro k
  set L : Scalar := positiveReciprocalMixedLipschitzBound x hx y hy
  set B : Nat := scalarBoundWith A L
  set r : Nat := k + 2
  set j : Nat := B + r
  rcases hxy j with ⟨Nxy, hNxy⟩
  refine ⟨j + Nxy, ?_⟩
  intro n hn
  set p : Nat := reciprocalTailIndexWith A x hx n
  set q : Nat := reciprocalTailIndexWith A y hy n
  have hp_ge_n : n ≤ p := by
    simpa [p] using reciprocalTailIndex_ge_self A x hx n
  have hq_ge_n : n ≤ q := by
    simpa [q] using reciprocalTailIndex_ge_self A y hy n
  have hNxy_p : Nxy ≤ p := by
    omega
  have hB_p : B + r ≤ p := by
    omega
  have hB_q : B + r ≤ q := by
    omega
  have hxy_p : Le (COF.abs (x.val p - y.val p)) (eps j) :=
    hNxy p hNxy_p
  have hdist :
      Le (COF.abs (y.val q - x.val p)) ((eps q + eps p) + eps j) :=
    sampled_source_abs_le_regular_eventual x y hxy_p
  have hmul0 :
      Le
        (COF.abs L * COF.abs (y.val q - x.val p))
        (COF.abs L * ((eps q + eps p) + eps j)) :=
    scalar_mul_le_mul_left hdist (scalar_abs_nonneg L)
  have hqterm : Le (COF.abs L * eps q) (eps r) := by
    exact scalar_bound_eps_le_of_ge A L hB_q
  have hpterm : Le (COF.abs L * eps p) (eps r) := by
    exact scalar_bound_eps_le_of_ge A L hB_p
  have hjterm : Le (COF.abs L * eps j) (eps r) := by
    simpa [B, j] using scalar_bound_tail_eps_le A L r
  have hterms :
      Le (COF.abs L * ((eps q + eps p) + eps j))
        ((eps r + eps r) + eps r) := by
    rw [show COF.abs L * ((eps q + eps p) + eps j) =
        (COF.abs L * eps q + COF.abs L * eps p) + COF.abs L * eps j
      from by ring]
    exact BishopC.le_add (BishopC.le_add hqterm hpterm) hjterm
  have hbudget : Le ((eps r + eps r) + eps r) (eps k) := by
    simpa [r] using eps_three_two_steps_le k
  exact BishopC.le_trans hmul0 (BishopC.le_trans hterms hbudget)

/-- Consequently, reciprocal representatives respect eventual equality once
positive tail witnesses for both representatives are supplied. -/
theorem positiveTailInvSeqWithBound_respects_eventually
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq)
    (hx : PosEventuallyData x) (hy : PosEventuallyData y)
    (hxy : relEventually x y) :
    relEventually
      (positiveTailInvSeqWithBound A x hx)
      (positiveTailInvSeqWithBound A y hy) :=
  positiveTailInvSeqWithBound_respects_eventually_of_sampled_close
    A x hx y hy
    (positiveTailReciprocalSampledClose_of_relEventually A x y hx hy hxy)

/-- Data package for the representative-level reciprocal respect closure. -/
structure PositiveTailReciprocalRepresentativeRespectSeed : Type where
  sampledClose_of_rel :
    ∀ A : ScalarMulArchimedeanData,
      ∀ x y : RegularSeq,
      ∀ hx : PosEventuallyData x, ∀ hy : PosEventuallyData y,
        relEventually x y →
          positiveTailReciprocalSampledClose A x hx y hy
  recipSeq_respects :
    ∀ A : ScalarMulArchimedeanData,
      ∀ x y : RegularSeq,
      ∀ hx : PosEventuallyData x, ∀ hy : PosEventuallyData y,
        relEventually x y →
          relEventually
            (positiveTailInvSeqWithBound A x hx)
            (positiveTailInvSeqWithBound A y hy)

def positiveTailReciprocalRepresentativeRespectSeed :
    PositiveTailReciprocalRepresentativeRespectSeed where
  sampledClose_of_rel := positiveTailReciprocalSampledClose_of_relEventually
  recipSeq_respects := positiveTailInvSeqWithBound_respects_eventually

/-- Frontier after representative-level reciprocal respect is closed. -/
structure CRealQuotPositiveInverseRepresentativeRespectFrontier : Type where
  quotient_inv_definition : Prop
  quotient_positive_witness_transport : Prop
  quotient_inv_respects : Prop
  quotient_mul_inv_cancel : Prop
  quotient_inv_pos : Prop

def cRealQuotPositiveInverseRepresentativeRespectFrontier :
    CRealQuotPositiveInverseRepresentativeRespectFrontier where
  quotient_inv_definition := True
  quotient_positive_witness_transport := True
  quotient_inv_respects := True
  quotient_mul_inv_cancel := True
  quotient_inv_pos := True

end BishopCReal

