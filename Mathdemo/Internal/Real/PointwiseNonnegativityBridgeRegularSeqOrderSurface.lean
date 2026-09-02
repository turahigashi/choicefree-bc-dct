import Mathdemo.Internal.Real.ClosingLine743AdditiveSumTranslation

set_option linter.style.longLine false

/-!
# G119: pointwise nonnegativity bridge for the RegularSeq order surface

G118 leaves property (4) with a single line-735 frontier: left monotonicity of
`minSeqWith` over `RegularSeqLe`.

This file adds the safe representative-side bridge needed for the direct
RegularSeq route.  It does not extract witnesses from `PosEventually`; it only
shows that pointwise scalar nonnegativity rules out a positive tail of the
negative sequence.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- If every displayed scalar sample is nonnegative, then the representative is
nonnegative in the `RegularSeqNonneg` surface.  This is a contradiction
principle, not a Prop-to-data witness selector. -/
theorem regularSeqNonneg_of_pointwise_nonneg
    (x : RegularSeq)
    (hpoint : forall n : Nat, Le 0 (x.val n)) :
    RegularSeqNonneg x := by
  intro hlt
  rcases hlt with ⟨k, N, hN⟩
  have htail := hN N (Nat.le_refl N)
  change COF.lt (eps k) (0 - x.val (N + 1)) at htail
  have hzero :
      COF.lt (0 : Scalar) (0 - x.val (N + 1)) :=
    scalarCOFOSeed.lt_trans (eps_pos k) htail
  have hbad :
      COF.lt (x.val (N + 1)) 0 := by
    have t := COF.lt_add_left (x.val (N + 1)) hzero
    rwa [show x.val (N + 1) + (0 : Scalar) = x.val (N + 1) from by ring,
      show x.val (N + 1) + (0 - x.val (N + 1)) = 0 from by ring] at t
  exact (hpoint (N + 1)) hbad

/-- Pointwise nonnegativity of the represented difference gives
`RegularSeqLe`. -/
theorem regularSeqLe_of_pointwise_sub_nonneg
    (x y : RegularSeq)
    (hpoint : forall n : Nat, Le 0 ((subSeq y x).val n)) :
    RegularSeqLe x y :=
  regularSeqNonneg_of_pointwise_nonneg (subSeq y x) hpoint

/-- A convenient indexed form: if the samples satisfy
`x.val (n+1) <= y.val (n+1)`, then `x <= y` as RegularSeq representatives. -/
theorem regularSeqLe_of_indexed_pointwise_le
    (x y : RegularSeq)
    (hpoint : forall n : Nat, Le (x.val (n + 1)) (y.val (n + 1))) :
    RegularSeqLe x y := by
  apply regularSeqLe_of_pointwise_sub_nonneg x y
  intro n
  change Le 0 (y.val (n + 1) - x.val (n + 1))
  exact BishopC.nonneg_sub_of_le (hpoint n)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}





end BishopRegularSeqTheorem118





end BishopCReal
