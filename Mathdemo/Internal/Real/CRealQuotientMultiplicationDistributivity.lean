import Mathdemo.Internal.Real.CRealCommonBoundDistributivityEstimates

/-!
# CReal quotient multiplication distributivity

This file connects the common-bound estimates from `CRealCommonBoundDistributivityEstimates` to concrete
quotient multiplication.  Pair-specific multiplication bounds are transported
to one shared bound, the common-bound distributivity estimate is applied there,
and the result descends to quotient-level left and right distributivity.
-/

namespace BishopCReal
open BishopC
open BishopCRat

/-- Concrete bounded multiplication is left-distributive over representative
addition, up to eventual equality. -/
theorem boundedMul_left_distrib_eventually_with
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A x (addSeq y z))
      (addSeq (mulSeqConcreteWith A x y) (mulSeqConcreteWith A x z)) := by
  intro k
  set Ksum : Nat := mulBoundWith A x (addSeq y z) with hKsum
  set Kxy : Nat := mulBoundWith A x y with hKxy
  set Kxz : Nat := mulBoundWith A x z with hKxz
  set C : Nat := Nat.max Ksum (Nat.max Kxy Kxz) with hC
  have hKsumC : Ksum <= C := by
    rw [hC]
    exact Nat.le_max_left Ksum (Nat.max Kxy Kxz)
  have hKxyC : Kxy <= C := by
    rw [hC]
    exact Nat.le_trans (Nat.le_max_left Kxy Kxz)
      (Nat.le_max_right Ksum (Nat.max Kxy Kxz))
  have hKxzC : Kxz <= C := by
    rw [hC]
    exact Nat.le_trans (Nat.le_max_right Kxy Kxz)
      (Nat.le_max_right Ksum (Nat.max Kxy Kxz))
  have hxKsum : standardBoundWith A x <= Ksum := by
    rw [hKsum]
    exact standardBoundWith_le_mulBound_left A x (addSeq y z)
  have hyzKsum : standardBoundWith A (addSeq y z) <= Ksum := by
    rw [hKsum]
    exact standardBoundWith_le_mulBound_right A x (addSeq y z)
  have hxKxy : standardBoundWith A x <= Kxy := by
    rw [hKxy]
    exact standardBoundWith_le_mulBound_left A x y
  have hyKxy : standardBoundWith A y <= Kxy := by
    rw [hKxy]
    exact standardBoundWith_le_mulBound_right A x y
  have hxKxz : standardBoundWith A x <= Kxz := by
    rw [hKxz]
    exact standardBoundWith_le_mulBound_left A x z
  have hzKxz : standardBoundWith A z <= Kxz := by
    rw [hKxz]
    exact standardBoundWith_le_mulBound_right A x z
  have hxC : standardBoundWith A x <= C := Nat.le_trans hxKsum hKsumC
  have hyzC : standardBoundWith A (addSeq y z) <= C :=
    Nat.le_trans hyzKsum hKsumC
  have hyC : standardBoundWith A y <= C := Nat.le_trans hyKxy hKxyC
  have hzC : standardBoundWith A z <= C := Nat.le_trans hzKxz hKxzC
  rcases mulValWithBound_common_left_distrib_eventually_with
      A x y z hxC hyC hzC (k + 1) with ⟨Nmid, hNmid⟩
  refine ⟨Nmid + (k + 3), ?_⟩
  intro n hn
  have hnMid : Nmid <= n := by omega
  have hleft0 : Le (COF.abs (mulValWithBound Ksum x.val (addVal y.val z.val) n -
      mulValWithBound C x.val (addVal y.val z.val) n)) (tol n) := by
    simpa using
      (mulValWithBound_change_le_tol A x (addSeq y z)
        (K := Ksum) (L := C) (n := n) hxKsum hxC hyzKsum hyzC)
  have hleft : Le (COF.abs (mulValWithBound Ksum x.val (addVal y.val z.val) n -
      mulValWithBound C x.val (addVal y.val z.val) n)) (eps (k + 2)) :=
    BishopC.le_trans hleft0
      (tol_le_eps_of_succ_le (k := k + 2) (n := n) (by omega))
  have hmid : Le
      (COF.abs (mulValWithBound C x.val (addVal y.val z.val) n -
        addVal (mulValWithBound C x.val y.val) (mulValWithBound C x.val z.val) n))
      (eps (k + 1)) :=
    hNmid n hnMid
  have hxy0 : Le (COF.abs (mulValWithBound C x.val y.val (n + 1) -
      mulValWithBound Kxy x.val y.val (n + 1))) (tol (n + 1)) :=
    mulValWithBound_change_le_tol A x y
      (K := C) (L := Kxy) (n := n + 1) hxC hxKxy hyC hyKxy
  have hxy : Le (COF.abs (mulValWithBound C x.val y.val (n + 1) -
      mulValWithBound Kxy x.val y.val (n + 1))) (eps (k + 3)) :=
    BishopC.le_trans hxy0
      (tol_le_eps_of_succ_le (k := k + 3) (n := n + 1) (by omega))
  have hxz0 : Le (COF.abs (mulValWithBound C x.val z.val (n + 1) -
      mulValWithBound Kxz x.val z.val (n + 1))) (tol (n + 1)) :=
    mulValWithBound_change_le_tol A x z
      (K := C) (L := Kxz) (n := n + 1) hxC hxKxz hzC hzKxz
  have hxz : Le (COF.abs (mulValWithBound C x.val z.val (n + 1) -
      mulValWithBound Kxz x.val z.val (n + 1))) (eps (k + 3)) :=
    BishopC.le_trans hxz0
      (tol_le_eps_of_succ_le (k := k + 3) (n := n + 1) (by omega))
  have hright : Le
      (COF.abs (addVal (mulValWithBound C x.val y.val)
        (mulValWithBound C x.val z.val) n -
        addVal (mulValWithBound Kxy x.val y.val)
          (mulValWithBound Kxz x.val z.val) n)) (eps (k + 2)) := by
    unfold addVal addIndex
    have htri := scalar_abs_add_le
      (mulValWithBound C x.val y.val (n + 1) -
        mulValWithBound Kxy x.val y.val (n + 1))
      (mulValWithBound C x.val z.val (n + 1) -
        mulValWithBound Kxz x.val z.val (n + 1))
    have hsum := BishopC.le_add hxy hxz
    have hbudget : Le (eps (k + 3) + eps (k + 3)) (eps (k + 2)) := by
      rw [show k + 3 = k + 2 + 1 from by omega, eps_succ_add_self (k + 2)]
      exact BishopC.le_refl (eps (k + 2))
    have htri' : Le
        (COF.abs ((mulValWithBound C x.val y.val (n + 1) +
              mulValWithBound C x.val z.val (n + 1)) -
            (mulValWithBound Kxy x.val y.val (n + 1) +
              mulValWithBound Kxz x.val z.val (n + 1))))
        (COF.abs (mulValWithBound C x.val y.val (n + 1) -
            mulValWithBound Kxy x.val y.val (n + 1)) +
          COF.abs (mulValWithBound C x.val z.val (n + 1) -
            mulValWithBound Kxz x.val z.val (n + 1))) := by
      rwa [show
          (mulValWithBound C x.val y.val (n + 1) -
              mulValWithBound Kxy x.val y.val (n + 1)) +
            (mulValWithBound C x.val z.val (n + 1) -
              mulValWithBound Kxz x.val z.val (n + 1)) =
          (mulValWithBound C x.val y.val (n + 1) +
              mulValWithBound C x.val z.val (n + 1)) -
            (mulValWithBound Kxy x.val y.val (n + 1) +
              mulValWithBound Kxz x.val z.val (n + 1)) from by ring] at htri
    exact BishopC.le_trans htri' (BishopC.le_trans hsum hbudget)
  change Le (COF.abs (boundedMulValWith A x (addSeq y z) n -
      addVal (boundedMulValWith A x y) (boundedMulValWith A x z) n)) (eps k)
  unfold boundedMulValWith
  rw [← hKsum, ← hKxy, ← hKxz]
  change Le (COF.abs (mulValWithBound Ksum x.val (addVal y.val z.val) n -
      addVal (mulValWithBound Kxy x.val y.val)
        (mulValWithBound Kxz x.val z.val) n)) (eps k)
  have htri := scalar_abs_sub_le_three
    (mulValWithBound Ksum x.val (addVal y.val z.val) n)
    (mulValWithBound C x.val (addVal y.val z.val) n)
    (addVal (mulValWithBound C x.val y.val) (mulValWithBound C x.val z.val) n)
    (addVal (mulValWithBound Kxy x.val y.val) (mulValWithBound Kxz x.val z.val) n)
  have htail := BishopC.le_add hmid hright
  have hsum := BishopC.le_add hleft htail
  have hbudget : Le (eps (k + 2) + (eps (k + 1) + eps (k + 2))) (eps k) := by
    rw [show eps (k + 2) + (eps (k + 1) + eps (k + 2)) =
        (eps (k + 2) + eps (k + 2)) + eps (k + 1) from by ring]
    rw [show k + 2 = k + 1 + 1 from by omega]
    rw [eps_succ_add_self (k + 1), eps_succ_add_self k]
    exact BishopC.le_refl (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

/-- Concrete bounded multiplication is right-distributive over representative
addition, up to eventual equality. -/
theorem boundedMul_right_distrib_eventually_with
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A (addSeq x y) z)
      (addSeq (mulSeqConcreteWith A x z) (mulSeqConcreteWith A y z)) := by
  intro k
  set Ksum : Nat := mulBoundWith A (addSeq x y) z with hKsum
  set Kxz : Nat := mulBoundWith A x z with hKxz
  set Kyz : Nat := mulBoundWith A y z with hKyz
  set C : Nat := Nat.max Ksum (Nat.max Kxz Kyz) with hC
  have hKsumC : Ksum <= C := by
    rw [hC]
    exact Nat.le_max_left Ksum (Nat.max Kxz Kyz)
  have hKxzC : Kxz <= C := by
    rw [hC]
    exact Nat.le_trans (Nat.le_max_left Kxz Kyz)
      (Nat.le_max_right Ksum (Nat.max Kxz Kyz))
  have hKyzC : Kyz <= C := by
    rw [hC]
    exact Nat.le_trans (Nat.le_max_right Kxz Kyz)
      (Nat.le_max_right Ksum (Nat.max Kxz Kyz))
  have hxyKsum : standardBoundWith A (addSeq x y) <= Ksum := by
    rw [hKsum]
    exact standardBoundWith_le_mulBound_left A (addSeq x y) z
  have hzKsum : standardBoundWith A z <= Ksum := by
    rw [hKsum]
    exact standardBoundWith_le_mulBound_right A (addSeq x y) z
  have hxKxz : standardBoundWith A x <= Kxz := by
    rw [hKxz]
    exact standardBoundWith_le_mulBound_left A x z
  have hzKxz : standardBoundWith A z <= Kxz := by
    rw [hKxz]
    exact standardBoundWith_le_mulBound_right A x z
  have hyKyz : standardBoundWith A y <= Kyz := by
    rw [hKyz]
    exact standardBoundWith_le_mulBound_left A y z
  have hzKyz : standardBoundWith A z <= Kyz := by
    rw [hKyz]
    exact standardBoundWith_le_mulBound_right A y z
  have hxyC : standardBoundWith A (addSeq x y) <= C :=
    Nat.le_trans hxyKsum hKsumC
  have hxC : standardBoundWith A x <= C := Nat.le_trans hxKxz hKxzC
  have hyC : standardBoundWith A y <= C := Nat.le_trans hyKyz hKyzC
  have hzC : standardBoundWith A z <= C := Nat.le_trans hzKsum hKsumC
  rcases mulValWithBound_common_right_distrib_eventually_with
      A x y z hxC hyC hzC (k + 1) with ⟨Nmid, hNmid⟩
  refine ⟨Nmid + (k + 3), ?_⟩
  intro n hn
  have hnMid : Nmid <= n := by omega
  have hleft0 : Le (COF.abs (mulValWithBound Ksum (addVal x.val y.val) z.val n -
      mulValWithBound C (addVal x.val y.val) z.val n)) (tol n) := by
    simpa using
      (mulValWithBound_change_le_tol A (addSeq x y) z
        (K := Ksum) (L := C) (n := n) hxyKsum hxyC hzKsum hzC)
  have hleft : Le (COF.abs (mulValWithBound Ksum (addVal x.val y.val) z.val n -
      mulValWithBound C (addVal x.val y.val) z.val n)) (eps (k + 2)) :=
    BishopC.le_trans hleft0
      (tol_le_eps_of_succ_le (k := k + 2) (n := n) (by omega))
  have hmid : Le
      (COF.abs (mulValWithBound C (addVal x.val y.val) z.val n -
        addVal (mulValWithBound C x.val z.val) (mulValWithBound C y.val z.val) n))
      (eps (k + 1)) :=
    hNmid n hnMid
  have hxz0 : Le (COF.abs (mulValWithBound C x.val z.val (n + 1) -
      mulValWithBound Kxz x.val z.val (n + 1))) (tol (n + 1)) :=
    mulValWithBound_change_le_tol A x z
      (K := C) (L := Kxz) (n := n + 1) hxC hxKxz hzC hzKxz
  have hxz : Le (COF.abs (mulValWithBound C x.val z.val (n + 1) -
      mulValWithBound Kxz x.val z.val (n + 1))) (eps (k + 3)) :=
    BishopC.le_trans hxz0
      (tol_le_eps_of_succ_le (k := k + 3) (n := n + 1) (by omega))
  have hyz0 : Le (COF.abs (mulValWithBound C y.val z.val (n + 1) -
      mulValWithBound Kyz y.val z.val (n + 1))) (tol (n + 1)) :=
    mulValWithBound_change_le_tol A y z
      (K := C) (L := Kyz) (n := n + 1) hyC hyKyz hzC hzKyz
  have hyz : Le (COF.abs (mulValWithBound C y.val z.val (n + 1) -
      mulValWithBound Kyz y.val z.val (n + 1))) (eps (k + 3)) :=
    BishopC.le_trans hyz0
      (tol_le_eps_of_succ_le (k := k + 3) (n := n + 1) (by omega))
  have hright : Le
      (COF.abs (addVal (mulValWithBound C x.val z.val)
        (mulValWithBound C y.val z.val) n -
        addVal (mulValWithBound Kxz x.val z.val)
          (mulValWithBound Kyz y.val z.val) n)) (eps (k + 2)) := by
    unfold addVal addIndex
    have htri := scalar_abs_add_le
      (mulValWithBound C x.val z.val (n + 1) -
        mulValWithBound Kxz x.val z.val (n + 1))
      (mulValWithBound C y.val z.val (n + 1) -
        mulValWithBound Kyz y.val z.val (n + 1))
    have hsum := BishopC.le_add hxz hyz
    have hbudget : Le (eps (k + 3) + eps (k + 3)) (eps (k + 2)) := by
      rw [show k + 3 = k + 2 + 1 from by omega, eps_succ_add_self (k + 2)]
      exact BishopC.le_refl (eps (k + 2))
    have htri' : Le
        (COF.abs ((mulValWithBound C x.val z.val (n + 1) +
              mulValWithBound C y.val z.val (n + 1)) -
            (mulValWithBound Kxz x.val z.val (n + 1) +
              mulValWithBound Kyz y.val z.val (n + 1))))
        (COF.abs (mulValWithBound C x.val z.val (n + 1) -
            mulValWithBound Kxz x.val z.val (n + 1)) +
          COF.abs (mulValWithBound C y.val z.val (n + 1) -
            mulValWithBound Kyz y.val z.val (n + 1))) := by
      rwa [show
          (mulValWithBound C x.val z.val (n + 1) -
              mulValWithBound Kxz x.val z.val (n + 1)) +
            (mulValWithBound C y.val z.val (n + 1) -
              mulValWithBound Kyz y.val z.val (n + 1)) =
          (mulValWithBound C x.val z.val (n + 1) +
              mulValWithBound C y.val z.val (n + 1)) -
            (mulValWithBound Kxz x.val z.val (n + 1) +
              mulValWithBound Kyz y.val z.val (n + 1)) from by ring] at htri
    exact BishopC.le_trans htri' (BishopC.le_trans hsum hbudget)
  change Le (COF.abs (boundedMulValWith A (addSeq x y) z n -
      addVal (boundedMulValWith A x z) (boundedMulValWith A y z) n)) (eps k)
  unfold boundedMulValWith
  rw [← hKsum, ← hKxz, ← hKyz]
  change Le (COF.abs (mulValWithBound Ksum (addVal x.val y.val) z.val n -
      addVal (mulValWithBound Kxz x.val z.val)
        (mulValWithBound Kyz y.val z.val) n)) (eps k)
  have htri := scalar_abs_sub_le_three
    (mulValWithBound Ksum (addVal x.val y.val) z.val n)
    (mulValWithBound C (addVal x.val y.val) z.val n)
    (addVal (mulValWithBound C x.val z.val) (mulValWithBound C y.val z.val) n)
    (addVal (mulValWithBound Kxz x.val z.val) (mulValWithBound Kyz y.val z.val) n)
  have htail := BishopC.le_add hmid hright
  have hsum := BishopC.le_add hleft htail
  have hbudget : Le (eps (k + 2) + (eps (k + 1) + eps (k + 2))) (eps k) := by
    rw [show eps (k + 2) + (eps (k + 1) + eps (k + 2)) =
        (eps (k + 2) + eps (k + 2)) + eps (k + 1) from by ring]
    rw [show k + 2 = k + 1 + 1 from by omega]
    rw [eps_succ_add_self (k + 1), eps_succ_add_self k]
    exact BishopC.le_refl (eps k)
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

theorem mulQuotConcrete_left_distrib_mk
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    mulQuotConcreteWith A (mkQuot x) (addQuot (mkQuot y) (mkQuot z)) =
      addQuot (mulQuotConcreteWith A (mkQuot x) (mkQuot y))
        (mulQuotConcreteWith A (mkQuot x) (mkQuot z)) := by
  apply Quotient.sound
  change relEventually
    (mulSeqConcreteWith A x (addSeq y z))
    (addSeq (mulSeqConcreteWith A x y) (mulSeqConcreteWith A x z))
  exact boundedMul_left_distrib_eventually_with A x y z

theorem mulQuotConcrete_right_distrib_mk
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    mulQuotConcreteWith A (addQuot (mkQuot x) (mkQuot y)) (mkQuot z) =
      addQuot (mulQuotConcreteWith A (mkQuot x) (mkQuot z))
        (mulQuotConcreteWith A (mkQuot y) (mkQuot z)) := by
  apply Quotient.sound
  change relEventually
    (mulSeqConcreteWith A (addSeq x y) z)
    (addSeq (mulSeqConcreteWith A x z) (mulSeqConcreteWith A y z))
  exact boundedMul_right_distrib_eventually_with A x y z

theorem mulQuotConcrete_left_distrib
    (A : ScalarMulArchimedeanData) (x y z : CRealQuot) :
    mulQuotConcreteWith A x (addQuot y z) =
      addQuot (mulQuotConcreteWith A x y) (mulQuotConcreteWith A x z) := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  refine Quotient.inductionOn z ?_
  intro z'
  exact mulQuotConcrete_left_distrib_mk A x' y' z'

theorem mulQuotConcrete_right_distrib
    (A : ScalarMulArchimedeanData) (x y z : CRealQuot) :
    mulQuotConcreteWith A (addQuot x y) z =
      addQuot (mulQuotConcreteWith A x z) (mulQuotConcreteWith A y z) := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  refine Quotient.inductionOn z ?_
  intro z'
  exact mulQuotConcrete_right_distrib_mk A x' y' z'

/-- Audited concrete quotient multiplication distributivity seed. -/
structure CRealQuotMulDistribConcreteSeed (A : ScalarMulArchimedeanData) : Type where
  left_distrib : ∀ x y z : CRealQuot,
    mulQuotConcreteWith A x (addQuot y z) =
      addQuot (mulQuotConcreteWith A x y) (mulQuotConcreteWith A x z)
  right_distrib : ∀ x y z : CRealQuot,
    mulQuotConcreteWith A (addQuot x y) z =
      addQuot (mulQuotConcreteWith A x z) (mulQuotConcreteWith A y z)

def cRealQuotMulDistribConcreteSeed
    (A : ScalarMulArchimedeanData) : CRealQuotMulDistribConcreteSeed A where
  left_distrib := mulQuotConcrete_left_distrib A
  right_distrib := mulQuotConcrete_right_distrib A

end BishopCReal

