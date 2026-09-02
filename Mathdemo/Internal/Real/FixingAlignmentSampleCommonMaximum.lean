import Mathdemo.Internal.Real.BridgeTwoSampleExpansionSameSample

set_option linter.style.longLine false

/-!
# G126: fixing the alignment sample to the common maximum

G125 left the residual line-735 alignment theorem in existential form:
two cofinal sample functions must be aligned to one cofinal sample function.

This file makes that residual theorem more concrete.  The aligned sample is
not chosen later from a quotient or a positivity proposition; it is the
computable common maximum `fun n => max (Fx n) (Fy n)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The canonical common sample for aligning two cofinal sample functions. -/
def commonMaxSample (Fx Fy : Nat -> Nat) (n : Nat) : Nat :=
  Nat.max (Fx n) (Fy n)

/-- If both input samples are cofinal, their common maximum is cofinal. -/
theorem commonMaxSample_late
    (Fx Fy : Nat -> Nat)
    (hFx : forall n : Nat, n <= Fx n)
    (_hFy : forall n : Nat, n <= Fy n) :
    forall n : Nat, n <= commonMaxSample Fx Fy n := by
  intro n
  exact Nat.le_trans (hFx n) (Nat.le_max_left (Fx n) (Fy n))

/-- The concrete remaining transport theorem: move a two-sample strict
half-sum gap to the common maximum sample. -/
def CommonMaxMinHalfsumTransport
    (x y c : RegularSeq) : Prop :=
  forall Fx Fy : Nat -> Nat,
    (forall n : Nat, n <= Fx n) ->
    (forall n : Nat, n <= Fy n) ->
      TwoSampleMinHalfsumLeftStrict x y c Fx Fy ->
        SameSampleMinHalfsumLeftStrict x y c (commonMaxSample Fx Fy)

/-- Common-max transport supplies the G125 existential alignment statement. -/
theorem twoSampleAlignment_of_commonMaxTransport
    (x y c : RegularSeq)
    (transport : CommonMaxMinHalfsumTransport x y c) :
    TwoSampleMinHalfsumAlignment x y c := by
  intro Fx Fy hFx hFy htwo
  refine ⟨commonMaxSample Fx Fy, ?_, ?_⟩
  · exact commonMaxSample_late Fx Fy hFx hFy
  · exact transport Fx Fy hFx hFy htwo

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
