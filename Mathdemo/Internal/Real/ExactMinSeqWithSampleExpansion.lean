import Mathdemo.Internal.Real.SameSampleTransportScalarMinStrict

set_option linter.style.longLine false

/-!
# G124: exact `minSeqWith` sample expansion

G123 reduced line 735 to a same-sample half-sum expansion problem.  This file
unfolds the concrete `minSeqWith` representative exactly: each value is the
scalar half-sum formula at the bounded multiplication sample index.

The remaining line-735 work after this file is the alignment of the two
potentially different bounded multiplication samples for `min x c` and
`min y c`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The bounded multiplication sample index used by `minSeqWith A x c` at
outer index `n`. -/
def minSeqWithSampleIndex
    (A : ScalarMulArchimedeanData)
    (x c : RegularSeq) (n : Nat) : Nat :=
  mulIndexFromBound
    (mulBoundWith A halfSeq
      (subSeq (addSeq x c) (absSeq (subSeq x c))))
    n

/-- Exact value expansion of `minSeqWith` into the scalar half-sum expression
at its bounded multiplication sample. -/
theorem minSeqWith_val_eq_halfsum_sample
    (A : ScalarMulArchimedeanData)
    (x c : RegularSeq) (n : Nat) :
    (minSeqWith A x c).val n =
      ((COF.half : Scalar) *
        (x.val (minSeqWithSampleIndex A x c n + 1 + 1) +
          c.val (minSeqWithSampleIndex A x c n + 1 + 1) -
            COF.abs
              (x.val (minSeqWithSampleIndex A x c n + 1 + 1) -
                c.val (minSeqWithSampleIndex A x c n + 1 + 1)))) := by
  simp [minSeqWith, minSeqWithSampleIndex, mulSeqConcreteWith, mulSeqWith,
    boundedMulValWith, mulValWithBound, halfSeq, constSeq, constVal, subSeq,
    subVal, addSeq, addVal, addIndex, absSeq, absVal]

/-- The sample function naturally associated to `minSeqWith A x c` after one
outer `subSeq` step.  It is written so that `F n + 1` is exactly the scalar
sample used by `(minSeqWith A x c).val (n+1)`. -/
def minSeqWithOuterSample
    (A : ScalarMulArchimedeanData)
    (x c : RegularSeq) (n : Nat) : Nat :=
  minSeqWithSampleIndex A x c (n + 1) + 1

/-- The outer sample is cofinal. -/
theorem minSeqWithOuterSample_late
    (A : ScalarMulArchimedeanData)
    (x c : RegularSeq) :
    forall n : Nat, n <= minSeqWithOuterSample A x c n := by
  intro n
  unfold minSeqWithOuterSample minSeqWithSampleIndex
  have hlate :
      n + 1 <=
        mulIndexFromBound
          (mulBoundWith A halfSeq
            (subSeq (addSeq x c) (absSeq (subSeq x c))))
          (n + 1) :=
    le_mulIndexFromBound
      (mulBoundWith A halfSeq
        (subSeq (addSeq x c) (absSeq (subSeq x c))))
      (n + 1)
  omega

/-- Two-sample half-sum strictness obtained by direct expansion of the two
`minSeqWith` representatives. -/
def TwoSampleMinHalfsumLeftStrict
    (x y c : RegularSeq) (Fx Fy : Nat -> Nat) : Prop :=
  ∃ k N : Nat,
    ∀ n : Nat, N <= n ->
      COF.lt (eps k)
        (((COF.half : Scalar) *
            (x.val (Fx n + 1) + c.val (Fx n + 1) -
              COF.abs (x.val (Fx n + 1) - c.val (Fx n + 1)))) -
          ((COF.half : Scalar) *
            (y.val (Fy n + 1) + c.val (Fy n + 1) -
              COF.abs (y.val (Fy n + 1) - c.val (Fy n + 1)))))

/-- A strict `minSeqWith` counterexample expands to a two-sample half-sum
strict statement, with both sample functions cofinal. -/
theorem minSeqWith_strict_to_two_sample_halfsum
    (A : ScalarMulArchimedeanData)
    (x y c : RegularSeq)
    (hmin : regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c)) :
    ∃ Fx Fy : Nat -> Nat,
      (forall n : Nat, n <= Fx n) ∧
      (forall n : Nat, n <= Fy n) ∧
        TwoSampleMinHalfsumLeftStrict x y c Fx Fy := by
  refine ⟨minSeqWithOuterSample A x c, minSeqWithOuterSample A y c,
    minSeqWithOuterSample_late A x c,
    minSeqWithOuterSample_late A y c, ?_⟩
  rcases hmin with ⟨k, N, hN⟩
  refine ⟨k, N, ?_⟩
  intro n hn
  have hpoint := hN n hn
  change COF.lt (eps k)
    ((minSeqWith A x c).val (n + 1) -
      (minSeqWith A y c).val (n + 1)) at hpoint
  rw [minSeqWith_val_eq_halfsum_sample A x c (n + 1),
    minSeqWith_val_eq_halfsum_sample A y c (n + 1)] at hpoint
  simpa [minSeqWithOuterSample] using hpoint

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}





end BishopRegularSeqTheorem118





end BishopCReal
