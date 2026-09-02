import Mathdemo.Internal.Real.ExactMinSeqWithSampleExpansion

set_option linter.style.longLine false

/-!
# G125: bridge from two-sample expansion to the same-sample frontier

G124 expands a strict `minSeqWith` counterexample into two sampled scalar
half-sum expressions.  G123 already transports a same-sample half-sum strict
statement back to `RegularSeq` order.

This file connects those two closed pieces.  The only remaining mathematical
frontier is now the explicit alignment lemma that turns the two cofinal sample
functions into one cofinal sample function, using regularity budgets.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The exact remaining line-735 alignment problem: two cofinal sampled
half-sum strict inequalities can be aligned to a single cofinal sample. -/
def TwoSampleMinHalfsumAlignment
    (x y c : RegularSeq) : Prop :=
  forall Fx Fy : Nat -> Nat,
    (forall n : Nat, n <= Fx n) ->
    (forall n : Nat, n <= Fy n) ->
      TwoSampleMinHalfsumLeftStrict x y c Fx Fy ->
        ∃ F : Nat -> Nat,
          (forall n : Nat, n <= F n) ∧
            SameSampleMinHalfsumLeftStrict x y c F

/-- A closed two-sample alignment theorem immediately supplies G123's
same-sample expansion frontier. -/
theorem minSeqWith_same_sample_expansion_of_two_sample_alignment
    (A : ScalarMulArchimedeanData)
    (align : forall x y c : RegularSeq,
      TwoSampleMinHalfsumAlignment x y c)
    (x y c : RegularSeq)
    (hmin : regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c)) :
    ∃ F : Nat -> Nat,
      (forall n : Nat, n <= F n) ∧
        SameSampleMinHalfsumLeftStrict x y c F := by
  rcases minSeqWith_strict_to_two_sample_halfsum A x y c hmin with
    ⟨Fx, Fy, hFx, hFy, htwo⟩
  exact align x y c Fx Fy hFx hFy htwo

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
