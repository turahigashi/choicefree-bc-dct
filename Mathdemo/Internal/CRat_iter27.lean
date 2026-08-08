import Mathdemo.Internal.CRat_iter26

/-!
# CReal multiplication bound seed

The current `CRat.COFOSeed` intentionally does not expose the full
`COFO.mul_archimedean` data.  This file therefore records the exact scalar data
needed by the global multiplication construction and proves the bound-shaped
facts conditionally from that data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar data needed for CReal multiplication bounds.  This is the missing
piece before a fully unconditional multiplication construction can be emitted. -/
structure ScalarMulArchimedeanData : Type where
  witness : ∀ x : Scalar, {m : Nat // Le (COF.abs x * eps m) 1}

/-- Standard representative bound, computed from a fixed nonzero approximation
once scalar multiplicative Archimedean data is supplied. -/
def standardBoundWith (A : ScalarMulArchimedeanData) (x : RegularSeq) : Nat :=
  (A.witness (COF.abs (x.val 1) + 1)).val

/-- The scalar certificate carried by `standardBoundWith`. -/
theorem standardBoundWith_spec (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    Le (COF.abs (COF.abs (x.val 1) + 1) * eps (standardBoundWith A x)) 1 := by
  unfold standardBoundWith
  exact (A.witness (COF.abs (x.val 1) + 1)).property

/-- Multiplication uses a common bound for both representatives. -/
def mulBoundWith (A : ScalarMulArchimedeanData) (x y : RegularSeq) : Nat :=
  Nat.max (standardBoundWith A x) (standardBoundWith A y)

theorem standardBoundWith_le_mulBound_left (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) : standardBoundWith A x ≤ mulBoundWith A x y := by
  unfold mulBoundWith
  exact Nat.le_max_left _ _

theorem standardBoundWith_le_mulBound_right (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) : standardBoundWith A y ≤ mulBoundWith A x y := by
  unfold mulBoundWith
  exact Nat.le_max_right _ _

theorem mulBoundWith_comm (A : ScalarMulArchimedeanData) (x y : RegularSeq) :
    mulBoundWith A x y = mulBoundWith A y x := by
  unfold mulBoundWith
  exact Nat.max_comm _ _

/-- Bounded multiplication values using the supplied common bound. -/
def boundedMulValWith (A : ScalarMulArchimedeanData) (x y : RegularSeq) : Nat → Scalar :=
  mulValWithBound (mulBoundWith A x y) x.val y.val

/-- Bounded multiplication by zero on the left is raw-equal to zero. -/
theorem bounded_mul_zero_left_raw_with (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relVal (boundedMulValWith A zeroSeq x) zeroVal := by
  change relVal (mulValWithBound (mulBoundWith A zeroSeq x) zeroVal x.val) zeroVal
  exact mul_zero_left_raw_fixed (mulBoundWith A zeroSeq x) x

/-- Bounded multiplication by zero on the right is raw-equal to zero. -/
theorem bounded_mul_zero_right_raw_with (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relVal (boundedMulValWith A x zeroSeq) zeroVal := by
  change relVal (mulValWithBound (mulBoundWith A x zeroSeq) x.val zeroVal) zeroVal
  exact mul_zero_right_raw_fixed (mulBoundWith A x zeroSeq) x

/-- Bounded multiplication by one on the left is raw-equal to the representative. -/
theorem bounded_mul_one_left_raw_with (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relVal (boundedMulValWith A oneSeq x) x.val := by
  change relVal (mulValWithBound (mulBoundWith A oneSeq x) oneVal x.val) x.val
  exact mul_one_left_raw_fixed (mulBoundWith A oneSeq x) x

/-- Bounded multiplication by one on the right is raw-equal to the representative. -/
theorem bounded_mul_one_right_raw_with (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    relVal (boundedMulValWith A x oneSeq) x.val := by
  change relVal (mulValWithBound (mulBoundWith A x oneSeq) x.val oneVal) x.val
  exact mul_one_right_raw_fixed (mulBoundWith A x oneSeq) x

/-- Bounded multiplication is raw-commutative. -/
theorem bounded_mul_comm_raw_with (A : ScalarMulArchimedeanData) (x y : RegularSeq) :
    relVal (boundedMulValWith A x y) (boundedMulValWith A y x) := by
  unfold boundedMulValWith
  rw [mulBoundWith_comm A x y]
  exact mul_comm_raw_fixed (mulBoundWith A y x) x y

/-- Audited conditional seed for global multiplication bounds. -/
structure CRealMulBoundSeed : Type where
  scalarData : ScalarMulArchimedeanData
  standardBound : RegularSeq → Nat
  standardBound_spec : ∀ x : RegularSeq,
    Le (COF.abs (COF.abs (x.val 1) + 1) * eps (standardBound x)) 1
  mulBound : RegularSeq → RegularSeq → Nat
  mulBound_left : ∀ x y : RegularSeq, standardBound x ≤ mulBound x y
  mulBound_right : ∀ x y : RegularSeq, standardBound y ≤ mulBound x y
  mulBound_comm : ∀ x y : RegularSeq, mulBound x y = mulBound y x
  boundedMulVal : RegularSeq → RegularSeq → Nat → Scalar
  zero_left : ∀ x : RegularSeq, relVal (boundedMulVal zeroSeq x) zeroVal
  zero_right : ∀ x : RegularSeq, relVal (boundedMulVal x zeroSeq) zeroVal
  one_left : ∀ x : RegularSeq, relVal (boundedMulVal oneSeq x) x.val
  one_right : ∀ x : RegularSeq, relVal (boundedMulVal x oneSeq) x.val
  comm_raw : ∀ x y : RegularSeq, relVal (boundedMulVal x y) (boundedMulVal y x)

def cRealMulBoundSeedWith (A : ScalarMulArchimedeanData) : CRealMulBoundSeed where
  scalarData := A
  standardBound := standardBoundWith A
  standardBound_spec := standardBoundWith_spec A
  mulBound := mulBoundWith A
  mulBound_left := standardBoundWith_le_mulBound_left A
  mulBound_right := standardBoundWith_le_mulBound_right A
  mulBound_comm := mulBoundWith_comm A
  boundedMulVal := boundedMulValWith A
  zero_left := bounded_mul_zero_left_raw_with A
  zero_right := bounded_mul_zero_right_raw_with A
  one_left := bounded_mul_one_left_raw_with A
  one_right := bounded_mul_one_right_raw_with A
  comm_raw := bounded_mul_comm_raw_with A

end BishopCReal

