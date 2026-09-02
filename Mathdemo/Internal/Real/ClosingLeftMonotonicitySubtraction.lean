import Mathdemo.Internal.Real.FactoringAddBoundSubtractionBoundTransport

set_option linter.style.longLine false

/-!
# G90: closing left monotonicity of subtraction

G89 reduced the add-bound-to-subtraction bridge to left monotonicity of
`subSeq · y` plus the cancellation `(y+z)-y = z`.  This file closes that left
monotonicity from:

* eventual transport of `RegularSeqNonneg`;
* the algebraic identity `(x'-y)-(x-y) = x'-x` over `relEventually`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Nonnegativity is stable under eventual equality on the represented
RegularSeq. -/
theorem regularSeqNonneg_of_eventual
    {x y : RegularSeq}
    (hxy : relEventually x y)
    (hy : RegularSeqNonneg y) :
    RegularSeqNonneg x := by
  intro hx
  have hsub :
      relEventually
        (subSeq zeroSeq x)
        (subSeq zeroSeq y) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      x y
      (relEventually_refl zeroSeq)
      hxy
  exact
    hy
      (posEventually_respects
        (subSeq zeroSeq x)
        (subSeq zeroSeq y)
        hsub
        hx)

/-- Subtracting the same right-hand representative preserves the represented
difference: `(x'-y)-(x-y) = x'-x` over `relEventually`. -/
theorem subSeq_same_right_diff_eventually
    (x x' y : RegularSeq) :
    relEventually
      (subSeq (subSeq x' y) (subSeq x y))
      (subSeq x' x) := by
  have h0 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq (subSeq x' y) (negSeq (subSeq x y))) :=
    subSeq_eq_add_neg_eventually (subSeq x' y) (subSeq x y)
  have hleft :
      relEventually
        (subSeq x' y)
        (addSeq x' (negSeq y)) :=
    subSeq_eq_add_neg_eventually x' y
  have hright :
      relEventually
        (negSeq (subSeq x y))
        (subSeq y x) :=
    relEventually_symm
      (subSeq y x)
      (negSeq (subSeq x y))
      (subSeq_comm_neg_eventually y x)
  have h1 :
      relEventually
        (addSeq (subSeq x' y) (negSeq (subSeq x y)))
        (addSeq (addSeq x' (negSeq y)) (subSeq y x)) :=
    addSeq_respects_eventually
      (subSeq x' y) (addSeq x' (negSeq y))
      (negSeq (subSeq x y)) (subSeq y x)
      hleft
      hright
  have hright_sub :
      relEventually
        (subSeq y x)
        (addSeq y (negSeq x)) :=
    subSeq_eq_add_neg_eventually y x
  have h2 :
      relEventually
        (addSeq (addSeq x' (negSeq y)) (subSeq y x))
        (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x))) :=
    addSeq_respects_eventually
      (addSeq x' (negSeq y)) (addSeq x' (negSeq y))
      (subSeq y x) (addSeq y (negSeq x))
      (relEventually_refl (addSeq x' (negSeq y)))
      hright_sub
  have h3 :
      relEventually
        (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x)))
        (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x)))) :=
    addSeq_assoc_eventually x' (negSeq y) (addSeq y (negSeq x))
  have hinner_assoc :
      relEventually
        (addSeq (negSeq y) (addSeq y (negSeq x)))
        (addSeq (addSeq (negSeq y) y) (negSeq x)) :=
    relEventually_symm
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (addSeq (negSeq y) (addSeq y (negSeq x)))
      (addSeq_assoc_eventually (negSeq y) y (negSeq x))
  have h4 :
      relEventually
        (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x))))
        (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x))) :=
    addSeq_respects_eventually
      x' x'
      (addSeq (negSeq y) (addSeq y (negSeq x)))
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (relEventually_refl x')
      hinner_assoc
  have hcancel :
      relEventually
        (addSeq (negSeq y) y)
        zeroSeq :=
    addSeq_neg_left_eventually y
  have hinner_cancel :
      relEventually
        (addSeq (addSeq (negSeq y) y) (negSeq x))
        (addSeq zeroSeq (negSeq x)) :=
    addSeq_respects_eventually
      (addSeq (negSeq y) y) zeroSeq
      (negSeq x) (negSeq x)
      hcancel
      (relEventually_refl (negSeq x))
  have hinner_zero :
      relEventually
        (addSeq zeroSeq (negSeq x))
        (negSeq x) :=
    addSeq_zero_left_eventually (negSeq x)
  have hinner :
      relEventually
        (addSeq (addSeq (negSeq y) y) (negSeq x))
        (negSeq x) :=
    relEventually_trans
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (addSeq zeroSeq (negSeq x))
      (negSeq x)
      hinner_cancel
      hinner_zero
  have h5 :
      relEventually
        (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x)))
        (addSeq x' (negSeq x)) :=
    addSeq_respects_eventually
      x' x'
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (negSeq x)
      (relEventually_refl x')
      hinner
  have h6 :
      relEventually
        (addSeq x' (negSeq x))
        (subSeq x' x) :=
    relEventually_symm
      (subSeq x' x)
      (addSeq x' (negSeq x))
      (subSeq_eq_add_neg_eventually x' x)
  have h01 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq (addSeq x' (negSeq y)) (subSeq y x)) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq (subSeq x' y) (negSeq (subSeq x y)))
      (addSeq (addSeq x' (negSeq y)) (subSeq y x))
      h0
      h1
  have h012 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x))) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq (addSeq x' (negSeq y)) (subSeq y x))
      (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x)))
      h01
      h2
  have h0123 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x)))) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x)))
      (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x))))
      h012
      h3
  have h01234 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x))) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x))))
      (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x)))
      h0123
      h4
  have h012345 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq x' (negSeq x)) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x)))
      (addSeq x' (negSeq x))
      h01234
      h5
  exact
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq x' (negSeq x))
      (subSeq x' x)
      h012345
      h6

/-- Left monotonicity of subtraction by a fixed right-hand representative. -/
theorem subSeq_monotone_left_regularSeqLe
    (x x' y : RegularSeq)
    (hxx : RegularSeqLe x x') :
    RegularSeqLe (subSeq x y) (subSeq x' y) :=
  regularSeqNonneg_of_eventual
    (subSeq_same_right_diff_eventually x x' y)
    hxx

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
