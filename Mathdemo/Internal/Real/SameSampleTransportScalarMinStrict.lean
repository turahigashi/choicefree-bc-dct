import Mathdemo.Internal.Real.ScalarStrictBackwardKernelHalfSum

set_option linter.style.longLine false

/-!
# G123: same-sample transport for scalar min strict-backward

G122 closed the scalar strict-backward kernel for the half-sum minimum.  This
file transports that kernel to `RegularSeq` once the strict `minSeqWith`
counterexample has been expanded to a cofinal same-sample half-sum statement.

The remaining line-735 work is therefore the concrete expansion/alignment of
`minSeqWith`'s bounded multiplication samples, not any quotient representative
selection.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Same-sample half-sum strictness for the left min argument.  The sampled
index is written as `F n + 1` so it matches `(subSeq x y).val (F n)`. -/
def SameSampleMinHalfsumLeftStrict
    (x y c : RegularSeq) (F : Nat -> Nat) : Prop :=
  ∃ k N : Nat,
    ∀ n : Nat, N <= n ->
      COF.lt (eps k)
        (((COF.half : Scalar) *
            (x.val (F n + 1) + c.val (F n + 1) -
              COF.abs (x.val (F n + 1) - c.val (F n + 1)))) -
          ((COF.half : Scalar) *
            (y.val (F n + 1) + c.val (F n + 1) -
              COF.abs (y.val (F n + 1) - c.val (F n + 1)))))

/-- Same-sample scalar strict-backward transported to `PosEventually` for
regular representatives. -/
theorem posEventually_subSeq_of_late_same_sample_min_halfsum_strict
    (x y c : RegularSeq)
    (F : Nat -> Nat)
    (hF : forall n : Nat, n <= F n)
    (hstrict : SameSampleMinHalfsumLeftStrict x y c F) :
    PosEventually (subSeq x y) := by
  rcases hstrict with ⟨k, N, hN⟩
  apply posEventually_subSeq_of_late_sample_pos y x F hF
  refine ⟨k, N, ?_⟩
  intro n hn
  have hscalar :=
    scalar_min_halfsum_left_strict_backward
      (x.val (F n + 1))
      (y.val (F n + 1))
      (c.val (F n + 1))
      (hN n hn)
  change COF.lt (eps k) ((subSeq x y).val (F n))
  change COF.lt (eps k) (x.val (F n + 1) - y.val (F n + 1))
  exact hscalar

/-- If a `minSeqWith` strict counterexample can be expanded to a cofinal
same-sample half-sum strict statement, then the full RegularSeq
strict-backward comparison follows. -/
theorem minSeqWith_strict_backward_of_same_sample_expansion
    (A : ScalarMulArchimedeanData)
    (same_sample_expansion :
      forall x y c : RegularSeq,
        regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) ->
          ∃ F : Nat -> Nat,
            (forall n : Nat, n <= F n) ∧
              SameSampleMinHalfsumLeftStrict x y c F)
    (x y c : RegularSeq)
    (hmin : regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c)) :
    regularSeqLtProp y x := by
  rcases same_sample_expansion x y c hmin with ⟨F, hF, hsame⟩
  exact posEventually_subSeq_of_late_same_sample_min_halfsum_strict
    x y c F hF hsame

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
