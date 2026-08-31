import Mathdemo.Internal.Real.CRealMultiplicationPhase10SupportLemmas

/-!
# CRat absolute value of products

Phase 10 product estimates need the scalar fact `|a*b| = |a|*|b|`.  The current
`CRat.COFOSeed` intentionally remains a partial seed, so this file proves the
missing fact as a standalone audited theorem instead of pretending that a full
`COFO CRat` instance is available.
-/

namespace BishopCRat
open Q

namespace Q

/-- Absolute value distributes over multiplication at the raw rational layer. -/
theorem abs_mul (a b : Q) : rel (abs (mul a b)) (mul (abs a) (abs b)) := by
  unfold abs
  by_cases ha : 0 ≤ a.num
  · by_cases hb : 0 ≤ b.num
    · have hp : 0 ≤ (mul a b).num := by
        change 0 ≤ a.num * b.num
        exact Int.mul_nonneg ha hb
      simp only [hp, ha, hb, if_true]
      exact rel_refl (mul a b)
    · have hbneg : b.num < 0 := by omega
      by_cases haz : a.num = 0
      · have hp : 0 ≤ (mul a b).num := by
          change 0 ≤ a.num * b.num
          rw [haz]
          omega
        simp only [hp, ha, hb, if_true, if_false]
        unfold rel mul neg
        rw [haz]
        ring
      · have hapos : 0 < a.num := by omega
        have hp : ¬ 0 ≤ (mul a b).num := by
          change ¬ 0 ≤ a.num * b.num
          have hprod : a.num * b.num < 0 := Int.mul_neg_of_pos_of_neg hapos hbneg
          omega
        simp only [hp, ha, hb, if_true, if_false]
        unfold rel neg mul
        ring
  · have haneg : a.num < 0 := by omega
    by_cases hb : 0 ≤ b.num
    · by_cases hbz : b.num = 0
      · have hp : 0 ≤ (mul a b).num := by
          change 0 ≤ a.num * b.num
          rw [hbz]
          omega
        simp only [hp, ha, hb, if_true, if_false]
        unfold rel mul neg
        rw [hbz]
        ring
      · have hbpos : 0 < b.num := by omega
        have hp : ¬ 0 ≤ (mul a b).num := by
          change ¬ 0 ≤ a.num * b.num
          have hprod : a.num * b.num < 0 := Int.mul_neg_of_neg_of_pos haneg hbpos
          omega
        simp only [hp, ha, hb, if_true, if_false]
        unfold rel neg mul
        ring
    · have hbneg : b.num < 0 := by omega
      have hp : 0 ≤ (mul a b).num := by
        change 0 ≤ a.num * b.num
        exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      simp only [hp, ha, hb, if_true, if_false]
      unfold rel neg mul
      ring

end Q

namespace CRat

/-- Absolute value distributes over multiplication on the CRat quotient. -/
theorem abs_mul (a b : CRat) : absF (a * b) = absF a * absF b := by
  induction a using Quotient.inductionOn with | _ qa =>
  induction b using Quotient.inductionOn with | _ qb =>
  exact Quotient.sound (Q.abs_mul qa qb)

end CRat
end BishopCRat

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar absolute value of products for the audited CRat scalar. -/
theorem scalar_abs_mul (a b : Scalar) : COF.abs (a * b) = COF.abs a * COF.abs b :=
  BishopCRat.CRat.abs_mul a b




end BishopCReal

