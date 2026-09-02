import Mathdemo.Internal.Real.ClosingAbsoluteTailShiftBounds

set_option linter.style.longLine false

/-!
# G94: closing monotonicity under adding a common right term

G93 left `addSeq_monotone_left` as a primitive order input.  This file closes
it by reducing

`(y+z)-(x+z)`

to `y-x`.  The proof reuses the G90 identity
`(x'-r)-(x-r)=x'-x`, after rewriting `a+z` as `a-(-z)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Double negation over the RegularSeq implementation equality. -/
theorem negSeq_negSeq_eventually
    (x : RegularSeq) :
    relEventually (negSeq (negSeq x)) x := by
  apply rel_to_relEventually
  intro n
  unfold negSeq negVal
  rw [show -(-x.val n) - x.val n = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Adding `z` is the same as subtracting `-z` over `relEventually`. -/
theorem addSeq_eq_sub_neg_eventually
    (x z : RegularSeq) :
    relEventually (addSeq x z) (subSeq x (negSeq z)) := by
  have hsub :
      relEventually
        (subSeq x (negSeq z))
        (addSeq x (negSeq (negSeq z))) :=
    subSeq_eq_add_neg_eventually x (negSeq z)
  have hdn :
      relEventually
        (addSeq x (negSeq (negSeq z)))
        (addSeq x z) :=
    addSeq_respects_eventually
      x x
      (negSeq (negSeq z)) z
      (relEventually_refl x)
      (negSeq_negSeq_eventually z)
  exact
    relEventually_symm
      (subSeq x (negSeq z))
      (addSeq x z)
      (relEventually_trans
        (subSeq x (negSeq z))
        (addSeq x (negSeq (negSeq z)))
        (addSeq x z)
        hsub
        hdn)

/-- The represented difference is unchanged by adding the same right term:
`(y+z)-(x+z) = y-x`. -/
theorem addSeq_same_right_sub_eventually
    (x y z : RegularSeq) :
    relEventually
      (subSeq (addSeq y z) (addSeq x z))
      (subSeq y x) := by
  have hy :
      relEventually
        (addSeq y z)
        (subSeq y (negSeq z)) :=
    addSeq_eq_sub_neg_eventually y z
  have hx :
      relEventually
        (addSeq x z)
        (subSeq x (negSeq z)) :=
    addSeq_eq_sub_neg_eventually x z
  have h0 :
      relEventually
        (subSeq (addSeq y z) (addSeq x z))
        (subSeq (subSeq y (negSeq z)) (subSeq x (negSeq z))) :=
    subSeq_respects_eventually
      (addSeq y z) (subSeq y (negSeq z))
      (addSeq x z) (subSeq x (negSeq z))
      hy
      hx
  have hsame :
      relEventually
        (subSeq (subSeq y (negSeq z)) (subSeq x (negSeq z)))
        (subSeq y x) :=
    subSeq_same_right_diff_eventually x y (negSeq z)
  exact
    relEventually_trans
      (subSeq (addSeq y z) (addSeq x z))
      (subSeq (subSeq y (negSeq z)) (subSeq x (negSeq z)))
      (subSeq y x)
      h0
      hsame

/-- Non-strict order is monotone under adding a common right term. -/
theorem addSeq_monotone_left_regularSeqLe
    (x y z : RegularSeq)
    (hxy : RegularSeqLe x y) :
    RegularSeqLe (addSeq x z) (addSeq y z) :=
  regularSeqNonneg_of_eventual
    (addSeq_same_right_sub_eventually x y z)
    hxy

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
