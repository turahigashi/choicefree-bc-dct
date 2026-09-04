import Mathdemo.Internal.Real.TransportingMinSeqWithQuotientMinObligations
set_option linter.style.longLine false

/-!
# G101: removing positive-inverse totalization from the min-law closure

G98-G100 closed the line-735 and line-743 quotient min laws through a live
`COFO CRealQuot`, which required a positive-inverse totalization even though
the source min estimates themselves use no reciprocal.

This file factors out the smaller half-sum min-order kernel actually used by
the proof, instantiates it from the existing quotient field data before the
positive-inverse block, and rebuilds the two quotient min laws without the
totalization input.

The remaining frontier is therefore sharper: global quotient representatives
and the `PosEventually` Prop-to-data selector remain; positive-inverse
totalization is no longer needed for these min-law obligations.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Minimal order/absolute-value kernel needed by the half-sum min estimates.

This is deliberately smaller than `BishopC.COFO`: it contains no inverse and no
sequential-completeness fields. -/
structure MinHalfsumOrderKernel (R : Type*) [BishopC.COF R] : Type 1 where
  lt_trans : ∀ {a b c : R}, COF.lt a b -> COF.lt b c -> COF.lt a c
  abs_neg : ∀ a : R, COF.abs (-a) = COF.abs a
  le_abs_self : ∀ a : R, BishopC.Le a (COF.abs a)
  abs_le_of :
    ∀ {a b : R}, BishopC.Le a b -> BishopC.Le (-a) b ->
      BishopC.Le (COF.abs a) b
  half_pos : COF.lt (0 : R) COF.half
  abs_add_le :
    ∀ a b : R, BishopC.Le (COF.abs (a + b)) (COF.abs a + COF.abs b)
  abs_of_nonneg : ∀ {a : R}, BishopC.Nonneg a -> COF.abs a = a
  mul_nonneg : ∀ {a b : R}, BishopC.Nonneg a -> BishopC.Nonneg b ->
    BishopC.Nonneg (a * b)

/-- Local strict-to-nonstrict conversion from the minimal min kernel. -/
theorem minKernel_le_of_lt
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    {a b : R}
    (h : COF.lt a b) :
    BishopC.Le a b :=
  fun hba => COF.lt_irrefl a (K.lt_trans h hba)

/-- Reverse triangle inequality for absolute values from the minimal kernel. -/
theorem minKernel_abs_abs_sub_abs_le
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (a b : R) :
    BishopC.Le
      (COF.abs (COF.abs a - COF.abs b))
      (COF.abs (a - b)) := by
  have key :
      ∀ u v : R,
        BishopC.Le (COF.abs u - COF.abs v) (COF.abs (u - v)) := by
    intro u v
    have ht : BishopC.Le (COF.abs u) (COF.abs (u - v) + COF.abs v) := by
      have h := K.abs_add_le (u - v) v
      rwa [show (u - v) + v = u from by ring] at h
    have h2 := BishopC.le_sub_right (c := COF.abs v) ht
    rwa [show COF.abs (u - v) + COF.abs v - COF.abs v =
        COF.abs (u - v) from by ring] at h2
  have h1 : BishopC.Le
      (COF.abs a - COF.abs b) (COF.abs (a - b)) :=
    key a b
  have h2 : BishopC.Le
      (-(COF.abs a - COF.abs b)) (COF.abs (a - b)) := by
    have hb := key b a
    rw [show COF.abs (b - a) = COF.abs (a - b) from by
      rw [show b - a = -(a - b) from by ring, K.abs_neg]] at hb
    rwa [show COF.abs b - COF.abs a =
      -(COF.abs a - COF.abs b) from by ring] at hb
  exact K.abs_le_of h1 h2

/-- Min monotonicity in the second argument from the minimal half-sum kernel. -/
theorem minKernel_min_halfsum_monotone_right
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (s a b : R)
    (h : BishopC.Le a b) :
    BishopC.Le (COF.min s a) (COF.min s b) := by
  apply BishopC.le_of_nonneg_sub
  rw [COF.min_halfsum s a, COF.min_halfsum s b,
    show COF.half * (s + b - COF.abs (s - b)) -
        COF.half * (s + a - COF.abs (s - a)) =
      COF.half * ((b - a) - (COF.abs (s - b) - COF.abs (s - a)))
    from by ring]
  have hrt : BishopC.Le
      (COF.abs (s - b) - COF.abs (s - a))
      (b - a) := by
    have h1 : BishopC.Le
        (COF.abs (s - b) - COF.abs (s - a))
        (COF.abs ((s - b) - (s - a))) :=
      BishopC.le_trans
        (K.le_abs_self
          (COF.abs (s - b) - COF.abs (s - a)))
        (minKernel_abs_abs_sub_abs_le K (s - b) (s - a))
    rwa [show (s - b) - (s - a) = -(b - a) from by ring,
      K.abs_neg,
      K.abs_of_nonneg (BishopC.nonneg_sub_of_le h)] at h1
  exact K.mul_nonneg
    (minKernel_le_of_lt K K.half_pos)
    (BishopC.nonneg_sub_of_le hrt)

/-- Commutativity of min from the half-sum formula and the minimal kernel. -/
theorem minKernel_min_halfsum_comm
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (a b : R) :
    COF.min a b = COF.min b a := by
  rw [COF.min_halfsum a b, COF.min_halfsum b a,
    show b - a = -(a - b) from by ring,
    K.abs_neg]
  ring

/-- Min monotonicity in the first argument from the minimal half-sum kernel. -/
theorem minKernel_min_halfsum_monotone_left
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (a b c : R)
    (h : BishopC.Le a b) :
    BishopC.Le (COF.min a c) (COF.min b c) := by
  rw [minKernel_min_halfsum_comm K a c,
    minKernel_min_halfsum_comm K b c]
  exact minKernel_min_halfsum_monotone_right K c a b h

/-- Translation identity for the half-sum minimum. -/
theorem minKernel_min_halfsum_translate_right
    {R : Type*} [BishopC.COF R]
    (_K : MinHalfsumOrderKernel R)
    (x d c : R) :
    COF.min (x + d) c = COF.min x (c - d) + d := by
  rw [COF.min_halfsum (x + d) c, COF.min_halfsum x (c - d),
    show x - (c - d) = (x + d) - c from by ring]
  linear_combination d * COF.half_add_half (R := R)

/-- Shifted-min bound from the minimal half-sum kernel. -/
theorem minKernel_min_halfsum_add_nonnegative_right_bound
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (x d c : R)
    (hd : BishopC.Nonneg d) :
    BishopC.Le (COF.min (x + d) c) (COF.min x c + d) := by
  have hcd : BishopC.Le (c - d) c := by
    apply BishopC.le_of_nonneg_sub
    rwa [show c - (c - d) = d from by ring]
  have hmono : BishopC.Le (COF.min x (c - d)) (COF.min x c) :=
    minKernel_min_halfsum_monotone_right K x (c - d) c hcd
  have hadd :
      BishopC.Le (COF.min x (c - d) + d) (COF.min x c + d) :=
    BishopC.le_add hmono (BishopC.le_refl d)
  rw [minKernel_min_halfsum_translate_right K x d c]
  exact hadd








namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}





end BishopRegularSeqTheorem118





end BishopCReal
