import Mathdemo.Internal.Real.ClosingBaseAbsoluteBound

set_option linter.style.longLine false

/-!
# G92: closing nonnegativity of `absSeq`

G91 left the primitive input `0 <= |x|`.  This file proves it at the
representative level from scalar absolute-value nonnegativity, then transports
it into the `RegularSeqLe zeroSeq (absSeq x)` surface used by the line-735 and
line-743 chains.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Absolute-value representatives are nonnegative in the `RegularSeqNonneg`
surface. -/
theorem absSeq_regularSeqNonneg
    (x : RegularSeq) :
    RegularSeqNonneg (absSeq x) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  change COF.lt (eps k) (0 - COF.abs (x.val (N + 1))) at hpoint
  have hzero :
      COF.lt (0 : Scalar) (0 - COF.abs (x.val (N + 1))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint
  have hbad :
      COF.lt (COF.abs (x.val (N + 1))) 0 := by
    have t := COF.lt_add_left (COF.abs (x.val (N + 1))) hzero
    rwa [show COF.abs (x.val (N + 1)) + (0 : Scalar) =
          COF.abs (x.val (N + 1)) from by ring,
      show COF.abs (x.val (N + 1)) +
            (0 - COF.abs (x.val (N + 1))) =
          0 from by ring] at t
  exact scalar_abs_nonneg (x.val (N + 1)) hbad

/-- Nonnegativity of `absSeq` in the `RegularSeqLe` surface. -/
theorem absSeq_nonnegative_regularSeqLe
    (x : RegularSeq) :
    RegularSeqLe zeroSeq (absSeq x) :=
  regularSeqNonneg_of_eventual
    (subSeq_zero_right_eventually (absSeq x))
    (absSeq_regularSeqNonneg x)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
