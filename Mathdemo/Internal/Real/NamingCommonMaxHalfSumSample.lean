import Mathdemo.Internal.Real.FixingAlignmentSampleCommonMaximum

set_option linter.style.longLine false

/-!
# G127: naming the common-max half-sum sample values

G126 fixed the remaining line-735 alignment sample to the computable common
maximum `fun n => max (Fx n) (Fy n)`.

This file prepares the actual regularity transport by naming the scalar
half-sum sample value and exposing the exact folds for the two-sample and
same-sample strictness statements.  No representative is extracted from a
quotient and no positivity witness is selected from a proposition.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Scalar half-sum expression for `min z c` at the raw sample `j`.  The
definition uses `j + 1`, matching the existing `subSeq`-based strictness
interfaces. -/
def minHalfsumSample (z c : RegularSeq) (j : Nat) : Scalar :=
  (COF.half : Scalar) *
    (z.val (j + 1) + c.val (j + 1) -
      COF.abs (z.val (j + 1) - c.val (j + 1)))




/-- Left input sample is contained in the common maximum. -/
theorem le_commonMaxSample_left
    (Fx Fy : Nat -> Nat) (n : Nat) :
    Fx n <= commonMaxSample Fx Fy n := by
  exact Nat.le_max_left (Fx n) (Fy n)

/-- Right input sample is contained in the common maximum. -/
theorem le_commonMaxSample_right
    (Fx Fy : Nat -> Nat) (n : Nat) :
    Fy n <= commonMaxSample Fx Fy n := by
  exact Nat.le_max_right (Fx n) (Fy n)

/-- Raw regularity estimate between two samples of a regular representative.
The later common-max proof will combine this with dyadic budget weakening. -/
theorem regularSeq_sample_close
    (x : RegularSeq) (i j : Nat) :
    Le (COF.abs (x.val (i + 1) - x.val (j + 1)))
      (eps (i + 1) + eps (j + 1)) := by
  exact x.regular (i + 1) (j + 1)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}



end BishopRegularSeqTheorem118





end BishopCReal
