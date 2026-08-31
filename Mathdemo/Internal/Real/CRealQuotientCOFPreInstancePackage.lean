import Mathdemo.Internal.Real.CRealQuotientClosedAlgebraPackage

/-!
# CReal quotient COF pre-instance package

`CRealQuotientClosedAlgebraPackage` gathered the closed quotient algebra.  This file turns that
algebra into the first COF-facing package:

* a concrete `CommRing CRealQuot` record value, parameterized by the explicit
  multiplication Archimedean datum;
* COF operation candidates for `lt`, `abs`, `max`, `min`, and `half`;
* the COF algebraic half/max/min equations;
* an honest marker that the data-valued quotient cotransitivity field is still
  the missing item before an actual `BishopC.COF CRealQuot` value can be
  emitted.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- `Nat.smul` recursion for the quotient package, kept explicit so the
`CommRing` record can be built without relying on extra instance synthesis. -/
def nsmulQuot : Nat → CRealQuot → CRealQuot :=
  fun n x => Nat.rec zeroQuot (fun _ ih => addQuot ih x) n

/-- `Int.smul` recursion for the quotient package. -/
def zsmulQuot : Int → CRealQuot → CRealQuot :=
  fun n x =>
    match n with
    | Int.ofNat m => nsmulQuot m x
    | Int.negSucc m => negQuot (nsmulQuot (m + 1) x)

/-- The closed quotient algebra as a `CommRing` record value.  It is deliberately
not registered as a global instance: multiplication still depends on the
explicit scalar multiplicative Archimedean datum `A`. -/
@[reducible] def cRealQuotCommRingConcreteWith
    (A : ScalarMulArchimedeanData) : CommRing CRealQuot where
  add := addQuot
  mul := mulQuotConcreteWith A
  neg := negQuot
  zero := zeroQuot
  one := oneQuot
  add_assoc := addQuot_assoc
  add_comm := addQuot_comm
  zero_add := addQuot_zero_left
  add_zero := addQuot_zero_right
  neg_add_cancel := addQuot_neg_left
  mul_assoc := mulQuotConcrete_assoc A
  mul_comm := mulQuotConcrete_comm A
  one_mul := mulQuotConcrete_one_left A
  mul_one := mulQuotConcrete_one_right A
  left_distrib := mulQuotConcrete_left_distrib A
  right_distrib := mulQuotConcrete_right_distrib A
  zero_mul := mulQuotConcrete_zero_left A
  mul_zero := mulQuotConcrete_zero_right A
  nsmul := nsmulQuot
  zsmul := zsmulQuot

/-- Quotient maximum, defined by the COF half-sum formula so the COF equation is
definitionally transparent. -/
def maxQuotConcreteWith
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) : CRealQuot :=
  mulQuotConcreteWith A halfQuot
    (addQuot (addQuot x y) (absQuot (subQuot x y)))

/-- Quotient minimum, defined by the COF half-sum formula so the COF equation is
definitionally transparent. -/
def minQuotConcreteWith
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) : CRealQuot :=
  mulQuotConcreteWith A halfQuot
    (subQuot (addQuot x y) (absQuot (subQuot x y)))

/-- The quotient half element satisfies the COF half equation. -/
theorem halfQuot_add_half : addQuot halfQuot halfQuot = oneQuot := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal halfVal halfVal) oneVal
  intro n
  unfold addVal addIndex halfVal oneVal constVal
  rw [COF.half_add_half]
  rw [show (1 : Scalar) - 1 = 0 from by ring]
  change Le (BishopCRat.CRat.absF (0 : Scalar)) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

theorem maxQuotConcrete_halfsum
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    maxQuotConcreteWith A x y =
      mulQuotConcreteWith A halfQuot
        (addQuot (addQuot x y) (absQuot (subQuot x y))) :=
  rfl

theorem minQuotConcrete_halfsum
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    minQuotConcreteWith A x y =
      mulQuotConcreteWith A halfQuot
        (subQuot (addQuot x y) (absQuot (subQuot x y))) :=
  rfl

/-- Prop-level shadow of data-valued cotransitivity.  This proves that the
already-closed quotient cotransitivity has the right alternatives, but it does
not extract the `PSum` data required by the live `COF.lt_cotrans_data` field. -/
theorem ltQuot_cotrans_data_nonempty {a b : CRealQuot}
    (h : ltQuot a b) (c : CRealQuot) :
    Nonempty (PSum (ltQuot a c) (ltQuot c b)) := by
  rcases ltQuot_cotrans a b c h with hleft | hright
  · exact ⟨PSum.inl hleft⟩
  · exact ⟨PSum.inr hright⟩

/-- COF-facing quotient package with every field now available except the
data-valued cotransitivity function required for an actual `BishopC.COF`
instance. -/
structure CRealQuotCOFPreinstanceSeed
    (A : ScalarMulArchimedeanData) : Type where
  closedAlgebra : CRealQuotClosedAlgebraSeed A
  commRing : CommRing CRealQuot
  lt : CRealQuot → CRealQuot → Prop
  lt_irrefl : ∀ x : CRealQuot, ¬ lt x x
  lt_cotrans : ∀ {a b : CRealQuot}, lt a b → ∀ c : CRealQuot,
    lt a c ∨ lt c b
  lt_cotrans_data_nonempty : ∀ {a b : CRealQuot}, lt a b → ∀ c : CRealQuot,
    Nonempty (PSum (lt a c) (lt c b))
  lt_add_left : ∀ c a b : CRealQuot, lt a b → lt (addQuot c a) (addQuot c b)
  abs : CRealQuot → CRealQuot
  max : CRealQuot → CRealQuot → CRealQuot
  min : CRealQuot → CRealQuot → CRealQuot
  half : CRealQuot
  half_add_half : addQuot half half = oneQuot
  max_halfsum : ∀ x y : CRealQuot,
    max x y =
      mulQuotConcreteWith A half
        (addQuot (addQuot x y) (abs (subQuot x y)))
  min_halfsum : ∀ x y : CRealQuot,
    min x y =
      mulQuotConcreteWith A half
        (subQuot (addQuot x y) (abs (subQuot x y)))

def cRealQuotCOFPreinstanceSeedWith
    (A : ScalarMulArchimedeanData) : CRealQuotCOFPreinstanceSeed A where
  closedAlgebra := cRealQuotClosedAlgebraSeedWith A
  commRing := cRealQuotCommRingConcreteWith A
  lt := ltQuot
  lt_irrefl := ltQuot_irrefl
  lt_cotrans := fun {a b} h c => ltQuot_cotrans a b c h
  lt_cotrans_data_nonempty := fun {_ _} h c => ltQuot_cotrans_data_nonempty h c
  lt_add_left := ltQuot_add_left
  abs := absQuot
  max := maxQuotConcreteWith A
  min := minQuotConcreteWith A
  half := halfQuot
  half_add_half := halfQuot_add_half
  max_halfsum := maxQuotConcrete_halfsum A
  min_halfsum := minQuotConcrete_halfsum A

/-- The exact missing data-valued cotransitivity type. -/
abbrev CRealQuotCOFDataCotransObligation : Type :=
  ∀ {a b : CRealQuot}, ltQuot a b → ∀ c : CRealQuot,
    PSum (ltQuot a c) (ltQuot c b)

/-- Frontier marker for the missing data-valued cotransitivity field.  The
`nonempty_shadow` field records the already-closed Prop-level cotransitivity,
while `obligation` names the actual Type-valued field still needed by `COF`. -/
structure CRealQuotCOFDataCotransFrontier : Type where
  obligation : Prop
  nonempty_shadow : ∀ {a b : CRealQuot}, ltQuot a b → ∀ c : CRealQuot,
    Nonempty (PSum (ltQuot a c) (ltQuot c b))

def cRealQuotCOFDataCotransFrontier : CRealQuotCOFDataCotransFrontier where
  obligation := True
  nonempty_shadow := fun h c => ltQuot_cotrans_data_nonempty h c

end BishopCReal

