import Mathdemo.Internal.Real.ReducingShiftedMinTranslationOrderExact

set_option linter.style.longLine false

/-!
# G116: peeling off the half factor in the shifted-min translation identity

G115 reduced the last line-743 order input to the exact `relEventually`
identity

`min(x+d,c) ~ min(x,c-d)+d`.

This file separates the half-sum minimum into its pre-half body and proves the
representative half-arithmetic needed to move between

`half * (body + d + d)`

and

`half * body + d`.

The remaining translation frontier is thereby narrowed to the pre-half body
identity.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The pre-half body of the half-sum minimum. -/
def minSeqBody (x y : RegularSeq) : RegularSeq :=
  subSeq (addSeq x y) (absSeq (subSeq x y))

/-- Representative half satisfies `half + half = 1` over eventual equality. -/
theorem addSeq_half_half_eventually_one :
    relEventually (addSeq halfSeq halfSeq) oneSeq := by
  apply rel_to_relEventually
  change relVal (addVal halfVal halfVal) oneVal
  intro n
  unfold addVal addIndex halfVal oneVal constVal
  rw [COF.half_add_half]
  rw [show (1 : Scalar) - 1 = 0 from by ring]
  change Le (BishopCRat.CRat.absF (0 : Scalar)) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Adding two half-multiples of the same representative gives the
representative itself. -/
theorem addSeq_half_mul_self_eventually
    (A : ScalarMulArchimedeanData)
    (d : RegularSeq) :
    relEventually
      (addSeq
        (mulSeqConcreteWith A halfSeq d)
        (mulSeqConcreteWith A halfSeq d))
      d := by
  have hdist :
      relEventually
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (addSeq
          (mulSeqConcreteWith A halfSeq d)
          (mulSeqConcreteWith A halfSeq d)) :=
    mulSeqConcrete_right_distrib_eventually A halfSeq halfSeq d
  have hsum :
      relEventually (addSeq halfSeq halfSeq) oneSeq :=
    addSeq_half_half_eventually_one
  have hmul :
      relEventually
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (mulSeqConcreteWith A oneSeq d) :=
    mulSeqConcrete_respects_eventually
      A
      (addSeq halfSeq halfSeq) oneSeq
      d d
      hsum
      (relEventually_refl d)
  have hone :
      relEventually (mulSeqConcreteWith A oneSeq d) d :=
    mulSeqConcrete_one_left_eventually A d
  exact
    relEventually_trans
      (addSeq
        (mulSeqConcreteWith A halfSeq d)
        (mulSeqConcreteWith A halfSeq d))
      (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
      d
      (relEventually_symm
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (addSeq
          (mulSeqConcreteWith A halfSeq d)
          (mulSeqConcreteWith A halfSeq d))
        hdist)
      (relEventually_trans
        (mulSeqConcreteWith A (addSeq halfSeq halfSeq) d)
        (mulSeqConcreteWith A oneSeq d)
        d
        hmul
        hone)

/-- Multiplying a doubled representative by one half returns the original
representative. -/
theorem half_mul_double_eventually_self
    (A : ScalarMulArchimedeanData)
    (d : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A halfSeq (addSeq d d))
      d := by
  have hdist :
      relEventually
        (mulSeqConcreteWith A halfSeq (addSeq d d))
        (addSeq
          (mulSeqConcreteWith A halfSeq d)
          (mulSeqConcreteWith A halfSeq d)) :=
    mulSeqConcrete_left_distrib_eventually A halfSeq d d
  exact
    relEventually_trans
      (mulSeqConcreteWith A halfSeq (addSeq d d))
      (addSeq
        (mulSeqConcreteWith A halfSeq d)
        (mulSeqConcreteWith A halfSeq d))
      d
      hdist
      (addSeq_half_mul_self_eventually A d)

/-- If the pre-half bodies satisfy the translation identity with a doubled
shift, then the full half-sum `minSeqWith` translation identity follows. -/
theorem minSeqWith_translate_right_eventually_from_body
    (A : ScalarMulArchimedeanData)
    (x d c : RegularSeq)
    (hbody :
      relEventually
        (minSeqBody (addSeq x d) c)
        (addSeq (minSeqBody x (subSeq c d)) (addSeq d d))) :
    relEventually
      (minSeqWith A (addSeq x d) c)
      (addSeq (minSeqWith A x (subSeq c d)) d) := by
  change
    relEventually
      (mulSeqConcreteWith A halfSeq (minSeqBody (addSeq x d) c))
      (addSeq
        (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
        d)
  have hmul :
      relEventually
        (mulSeqConcreteWith A halfSeq (minSeqBody (addSeq x d) c))
        (mulSeqConcreteWith A halfSeq
          (addSeq (minSeqBody x (subSeq c d)) (addSeq d d))) :=
    mulSeqConcrete_respects_eventually
      A
      halfSeq halfSeq
      (minSeqBody (addSeq x d) c)
      (addSeq (minSeqBody x (subSeq c d)) (addSeq d d))
      (relEventually_refl halfSeq)
      hbody
  have hdist :
      relEventually
        (mulSeqConcreteWith A halfSeq
          (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          (mulSeqConcreteWith A halfSeq (addSeq d d))) :=
    mulSeqConcrete_left_distrib_eventually
      A halfSeq (minSeqBody x (subSeq c d)) (addSeq d d)
  have hdouble :
      relEventually
        (mulSeqConcreteWith A halfSeq (addSeq d d))
        d :=
    half_mul_double_eventually_self A d
  have hadd :
      relEventually
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          (mulSeqConcreteWith A halfSeq (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          d) :=
    addSeq_respects_eventually
      (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
      (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
      (mulSeqConcreteWith A halfSeq (addSeq d d))
      d
      (relEventually_refl
        (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d))))
      hdouble
  exact
    relEventually_trans
      (mulSeqConcreteWith A halfSeq (minSeqBody (addSeq x d) c))
      (mulSeqConcreteWith A halfSeq
        (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)))
      (addSeq
        (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
        d)
      hmul
      (relEventually_trans
        (mulSeqConcreteWith A halfSeq
          (addSeq (minSeqBody x (subSeq c d)) (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          (mulSeqConcreteWith A halfSeq (addSeq d d)))
        (addSeq
          (mulSeqConcreteWith A halfSeq (minSeqBody x (subSeq c d)))
          d)
        hdist
        hadd)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
