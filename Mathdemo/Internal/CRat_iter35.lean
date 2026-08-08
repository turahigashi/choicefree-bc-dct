import Mathdemo.Internal.CRat_iter34

/-!
# CReal concrete quotient multiplication and negation

This file adds the first Phase 11-B compatibility layer above concrete quotient
multiplication.  It proves that multiplication by a negated representative
agrees with negating the product.  The proof reuses the fixed-bound algebra
facts and absorbs pairwise bound changes with the Phase 10 estimate.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Standard multiplication bounds are unchanged by negating a representative. -/
theorem standardBoundWith_neg (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    standardBoundWith A (negSeq x) = standardBoundWith A x := by
  unfold standardBoundWith
  change (A.witness (BishopCRat.CRat.absF (-(x.val 1)) + 1)).val =
    (A.witness (BishopCRat.CRat.absF (x.val 1) + 1)).val
  rw [scalarCOFOSeed.abs_neg (x.val 1)]

/-- Bounded multiplication is compatible with negation on the left, at the
representative level. -/
theorem bounded_mul_neg_left_eventually_with (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A (negSeq x) y)
      (negSeq (mulSeqConcreteWith A x y)) := by
  intro k
  set Kneg : Nat := mulBoundWith A (negSeq x) y with hKneg
  set K : Nat := mulBoundWith A x y with hK
  have hxKneg : standardBoundWith A x ≤ Kneg := by
    rw [← standardBoundWith_neg A x]
    rw [hKneg]
    exact standardBoundWith_le_mulBound_left A (negSeq x) y
  have hyKneg : standardBoundWith A y ≤ Kneg := by
    rw [hKneg]
    exact standardBoundWith_le_mulBound_right A (negSeq x) y
  have hxK : standardBoundWith A x ≤ K := by
    rw [hK]
    exact standardBoundWith_le_mulBound_left A x y
  have hyK : standardBoundWith A y ≤ K := by
    rw [hK]
    exact standardBoundWith_le_mulBound_right A x y
  refine ⟨k + 2, ?_⟩
  intro n hn
  have htol : k + 1 + 1 ≤ n := by omega
  have hfixed0 : Le
      (COF.abs (mulValWithBound Kneg (negVal x.val) y.val n -
        negVal (mulValWithBound Kneg x.val y.val) n)) (tol n) := by
    exact mul_neg_left_raw_fixed Kneg x y n
  have hfixed : Le
      (COF.abs (mulValWithBound Kneg (negVal x.val) y.val n -
        negVal (mulValWithBound Kneg x.val y.val) n)) (eps (k + 1)) :=
    BishopC.le_trans hfixed0 (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
  have hchange0 : Le
      (COF.abs (mulValWithBound Kneg x.val y.val n -
        mulValWithBound K x.val y.val n)) (tol n) :=
    mulValWithBound_change_le_tol A x y (K := Kneg) (L := K) (n := n)
      hxKneg hxK hyKneg hyK
  have hchange0' : Le
      (COF.abs (negVal (mulValWithBound Kneg x.val y.val) n -
        negVal (mulValWithBound K x.val y.val) n)) (tol n) := by
    unfold negVal
    rw [show -(mulValWithBound Kneg x.val y.val n) -
          -(mulValWithBound K x.val y.val n) =
        -(mulValWithBound Kneg x.val y.val n -
          mulValWithBound K x.val y.val n) from by ring]
    change Le (BishopCRat.CRat.absF
        (-(mulValWithBound Kneg x.val y.val n -
          mulValWithBound K x.val y.val n))) (tol n)
    rw [scalarCOFOSeed.abs_neg
      (mulValWithBound Kneg x.val y.val n - mulValWithBound K x.val y.val n)]
    exact hchange0
  have hchange : Le
      (COF.abs (negVal (mulValWithBound Kneg x.val y.val) n -
        negVal (mulValWithBound K x.val y.val) n)) (eps (k + 1)) :=
    BishopC.le_trans hchange0' (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
  change Le (COF.abs ((mulSeqConcreteWith A (negSeq x) y).val n -
      (negSeq (mulSeqConcreteWith A x y)).val n)) (eps k)
  unfold mulSeqConcreteWith mulSeqWith boundedMulValWith negSeq
  change Le (COF.abs (mulValWithBound (mulBoundWith A (negSeq x) y)
      (negVal x.val) y.val n -
      negVal (mulValWithBound (mulBoundWith A x y) x.val y.val) n)) (eps k)
  rw [← hKneg, ← hK]
  have htri : Le
      (COF.abs (mulValWithBound Kneg (negVal x.val) y.val n -
        negVal (mulValWithBound K x.val y.val) n))
      (COF.abs (mulValWithBound Kneg (negVal x.val) y.val n -
        negVal (mulValWithBound Kneg x.val y.val) n) +
        COF.abs (negVal (mulValWithBound Kneg x.val y.val) n -
          negVal (mulValWithBound K x.val y.val) n)) := by
    have h := scalar_abs_add_le
      (mulValWithBound Kneg (negVal x.val) y.val n -
        negVal (mulValWithBound Kneg x.val y.val) n)
      (negVal (mulValWithBound Kneg x.val y.val) n -
        negVal (mulValWithBound K x.val y.val) n)
    rwa [show (mulValWithBound Kneg (negVal x.val) y.val n -
          negVal (mulValWithBound Kneg x.val y.val) n) +
        (negVal (mulValWithBound Kneg x.val y.val) n -
          negVal (mulValWithBound K x.val y.val) n) =
        mulValWithBound Kneg (negVal x.val) y.val n -
          negVal (mulValWithBound K x.val y.val) n from by ring] at h
  have hsum := BishopC.le_add hfixed hchange
  have hbudget : Le (eps (k + 1) + eps (k + 1)) (eps k) := by
    rw [eps_succ_add_self k]
    exact BishopC.le_refl (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

/-- Bounded multiplication is compatible with negation on the right, at the
representative level. -/
theorem bounded_mul_neg_right_eventually_with (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A x (negSeq y))
      (negSeq (mulSeqConcreteWith A x y)) := by
  intro k
  set Kneg : Nat := mulBoundWith A x (negSeq y) with hKneg
  set K : Nat := mulBoundWith A x y with hK
  have hxKneg : standardBoundWith A x ≤ Kneg := by
    rw [hKneg]
    exact standardBoundWith_le_mulBound_left A x (negSeq y)
  have hyKneg : standardBoundWith A y ≤ Kneg := by
    rw [← standardBoundWith_neg A y]
    rw [hKneg]
    exact standardBoundWith_le_mulBound_right A x (negSeq y)
  have hxK : standardBoundWith A x ≤ K := by
    rw [hK]
    exact standardBoundWith_le_mulBound_left A x y
  have hyK : standardBoundWith A y ≤ K := by
    rw [hK]
    exact standardBoundWith_le_mulBound_right A x y
  refine ⟨k + 2, ?_⟩
  intro n hn
  have htol : k + 1 + 1 ≤ n := by omega
  have hfixed0 : Le
      (COF.abs (mulValWithBound Kneg x.val (negVal y.val) n -
        negVal (mulValWithBound Kneg x.val y.val) n)) (tol n) := by
    exact mul_neg_right_raw_fixed Kneg x y n
  have hfixed : Le
      (COF.abs (mulValWithBound Kneg x.val (negVal y.val) n -
        negVal (mulValWithBound Kneg x.val y.val) n)) (eps (k + 1)) :=
    BishopC.le_trans hfixed0 (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
  have hchange0 : Le
      (COF.abs (mulValWithBound Kneg x.val y.val n -
        mulValWithBound K x.val y.val n)) (tol n) :=
    mulValWithBound_change_le_tol A x y (K := Kneg) (L := K) (n := n)
      hxKneg hxK hyKneg hyK
  have hchange0' : Le
      (COF.abs (negVal (mulValWithBound Kneg x.val y.val) n -
        negVal (mulValWithBound K x.val y.val) n)) (tol n) := by
    unfold negVal
    rw [show -(mulValWithBound Kneg x.val y.val n) -
          -(mulValWithBound K x.val y.val n) =
        -(mulValWithBound Kneg x.val y.val n -
          mulValWithBound K x.val y.val n) from by ring]
    change Le (BishopCRat.CRat.absF
        (-(mulValWithBound Kneg x.val y.val n -
          mulValWithBound K x.val y.val n))) (tol n)
    rw [scalarCOFOSeed.abs_neg
      (mulValWithBound Kneg x.val y.val n - mulValWithBound K x.val y.val n)]
    exact hchange0
  have hchange : Le
      (COF.abs (negVal (mulValWithBound Kneg x.val y.val) n -
        negVal (mulValWithBound K x.val y.val) n)) (eps (k + 1)) :=
    BishopC.le_trans hchange0' (tol_le_eps_of_succ_le (k := k + 1) (n := n) htol)
  change Le (COF.abs ((mulSeqConcreteWith A x (negSeq y)).val n -
      (negSeq (mulSeqConcreteWith A x y)).val n)) (eps k)
  unfold mulSeqConcreteWith mulSeqWith boundedMulValWith negSeq
  change Le (COF.abs (mulValWithBound (mulBoundWith A x (negSeq y))
      x.val (negVal y.val) n -
      negVal (mulValWithBound (mulBoundWith A x y) x.val y.val) n)) (eps k)
  rw [← hKneg, ← hK]
  have htri : Le
      (COF.abs (mulValWithBound Kneg x.val (negVal y.val) n -
        negVal (mulValWithBound K x.val y.val) n))
      (COF.abs (mulValWithBound Kneg x.val (negVal y.val) n -
        negVal (mulValWithBound Kneg x.val y.val) n) +
        COF.abs (negVal (mulValWithBound Kneg x.val y.val) n -
          negVal (mulValWithBound K x.val y.val) n)) := by
    have h := scalar_abs_add_le
      (mulValWithBound Kneg x.val (negVal y.val) n -
        negVal (mulValWithBound Kneg x.val y.val) n)
      (negVal (mulValWithBound Kneg x.val y.val) n -
        negVal (mulValWithBound K x.val y.val) n)
    rwa [show (mulValWithBound Kneg x.val (negVal y.val) n -
          negVal (mulValWithBound Kneg x.val y.val) n) +
        (negVal (mulValWithBound Kneg x.val y.val) n -
          negVal (mulValWithBound K x.val y.val) n) =
        mulValWithBound Kneg x.val (negVal y.val) n -
          negVal (mulValWithBound K x.val y.val) n from by ring] at h
  have hsum := BishopC.le_add hfixed hchange
  have hbudget : Le (eps (k + 1) + eps (k + 1)) (eps k) := by
    rw [eps_succ_add_self k]
    exact BishopC.le_refl (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

theorem mulQuotConcrete_neg_left (A : ScalarMulArchimedeanData)
    (x y : CRealQuot) :
    mulQuotConcreteWith A (negQuot x) y = negQuot (mulQuotConcreteWith A x y) := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  apply Quotient.sound
  exact bounded_mul_neg_left_eventually_with A x' y'

theorem mulQuotConcrete_neg_right (A : ScalarMulArchimedeanData)
    (x y : CRealQuot) :
    mulQuotConcreteWith A x (negQuot y) = negQuot (mulQuotConcreteWith A x y) := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  apply Quotient.sound
  exact bounded_mul_neg_right_eventually_with A x' y'

/-- Concrete quotient multiplication compatibility with additive negation. -/
structure CRealQuotMulNegConcreteSeed (A : ScalarMulArchimedeanData) : Type where
  standard_bound_neg : ∀ x : RegularSeq,
    standardBoundWith A (negSeq x) = standardBoundWith A x
  neg_left : ∀ x y : CRealQuot,
    mulQuotConcreteWith A (negQuot x) y = negQuot (mulQuotConcreteWith A x y)
  neg_right : ∀ x y : CRealQuot,
    mulQuotConcreteWith A x (negQuot y) = negQuot (mulQuotConcreteWith A x y)

def cRealQuotMulNegConcreteSeedWith
    (A : ScalarMulArchimedeanData) : CRealQuotMulNegConcreteSeed A where
  standard_bound_neg := standardBoundWith_neg A
  neg_left := mulQuotConcrete_neg_left A
  neg_right := mulQuotConcrete_neg_right A

end BishopCReal

