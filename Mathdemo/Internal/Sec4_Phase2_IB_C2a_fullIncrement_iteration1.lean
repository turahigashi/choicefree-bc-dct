import Mathdemo.Internal.Sec4_Phase2_IB_C1_tailData_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2a: full-cover telescope and comparison interface

C1 reduced the tail datum for the direct `I_B` construction to two facts:
`hcmp` and `hsumInc`.

This file avoids the insufficient route "monotone bounded `I_{A_k∧B}` alone".
Instead it follows the original comparison route: dominate the `B`-increments
by the full-cover increments, and sum the full-cover increments using
`coverSet_tendsto`.

The remaining geometric/Boolean set algebra is packaged in
`Sec4IBIncrementBridge`; the next kernel-loop chunk should build that bridge
from `relIntegral_complement_additive` or `relIntegral_or_add_and`.
-/

#check coverSet_tendsto
#check relIntegral_le_integral
#check relIntegral_mono_set
#check relIntegral_mono_le
#check relIntegral_complement_additive
#check relIntegral_or_add_and
#check seriesSum_comparison
#check tendstoHalf_add
#check tendstoHalf_const
#check RSeq.partialSum

/-! ## 1. Full-cover increments, without the measurable set `B` -/

/-- `Ψ_k = I_{A_k}(f)`, the full-cover relative integral. -/
noncomputable def sec4FullCoverIntegral
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : R :=
  relIntegral (coverSet f k) (coverSet_int f k) f hnn


/-- Full-cover increment `Ψ_{k+1}-Ψ_k`. -/
noncomputable def sec4FullCoverIncrement
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : R :=
  sec4FullCoverIntegral f hnn (k + 1) -
    sec4FullCoverIntegral f hnn k


/-- The Phase 1a convergence theorem in the `sec4FullCoverIntegral` notation. -/
noncomputable def sec4FullCoverIntegral_tendsto
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    RSeq.TendstoHalf (fun k => sec4FullCoverIntegral f hnn k) f.integral := by
  change RSeq.TendstoHalf
    (fun k => relIntegral (coverSet f k) (coverSet_int f k) f hnn)
    f.integral
  exact coverSet_tendsto f hnn


/-- Shift a convergent sequence by one index. -/
def sec4_tendstoHalf_succ {u : Nat → R} {l : R}
    (h : RSeq.TendstoHalf u l) :
    RSeq.TendstoHalf (fun n => u (n + 1)) l where
  mod := h.mod
  close := by
    intro k n hn
    exact h.close k (n + 1) (Nat.le_trans hn (Nat.le_succ n))


/-- Subtract a constant from a convergent sequence. -/
def sec4_tendstoHalf_sub_const {u : Nat → R} {l : R}
    (h : RSeq.TendstoHalf u l) (c : R) :
    RSeq.TendstoHalf (fun n => u n - c) (l - c) := by
  -- Technical note.
  simp only [sub_eq_add_neg]
  exact tendstoHalf_add h (tendstoHalf_const (-c))


/-- Telescoping finite sums for the full-cover increments. -/
theorem sec4FullCoverIncrement_partialSum
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    ∀ N : Nat,
      RSeq.partialSum (fun k => sec4FullCoverIncrement f hnn k) N =
        sec4FullCoverIntegral f hnn (N + 1) -
          sec4FullCoverIntegral f hnn 0 := by
  intro N
  induction N with
  | zero =>
      rfl
  | succ N ih =>
      change
        RSeq.partialSum (fun k => sec4FullCoverIncrement f hnn k) N +
            sec4FullCoverIncrement f hnn (N + 1) =
          sec4FullCoverIntegral f hnn (N + 1 + 1) -
            sec4FullCoverIntegral f hnn 0
      rw [ih]
      unfold sec4FullCoverIncrement
      ring


/--
The full-cover increments form a convergent series.  Its sum is
`I(f) - Ψ_0`.
-/
noncomputable def sec4FullCoverIncrement_sum
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    RSeq.SeriesSum (fun k => sec4FullCoverIncrement f hnn k) := by
  let ψ : Nat → R := fun k => sec4FullCoverIntegral f hnn k
  let ht0 : RSeq.TendstoHalf ψ f.integral := by
    change RSeq.TendstoHalf
      (fun k => sec4FullCoverIntegral f hnn k) f.integral
    exact sec4FullCoverIntegral_tendsto f hnn
  let ht1 : RSeq.TendstoHalf (fun n => ψ (n + 1) - ψ 0)
      (f.integral - ψ 0) :=
    sec4_tendstoHalf_sub_const (sec4_tendstoHalf_succ ht0) (ψ 0)
  exact {
    sum := f.integral - ψ 0
    tends := {
      mod := ht1.mod
      close := by
        intro k n hn
        have hc := ht1.close k n hn
        change COF.Close k
          (RSeq.partialSum (fun k => sec4FullCoverIncrement f hnn k) n)
          (f.integral - ψ 0)
        rw [sec4FullCoverIncrement_partialSum f hnn n]
        exact hc
    }
  }


/-! ## 2. Comparison interface for the measurable-set increments -/

/--
The two facts still needed after C2a.

`hcmp` is the C1 assumption
`I_{D_k} ≤ I_{A_{k+1}∧B}-I_{A_k∧B}`.  The second field compares the
`B`-increment to the full-cover increment.  Together with
`sec4FullCoverIncrement_sum`, this yields the desired `hsumInc`.
-/
structure Sec4IBIncrementBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop where
  hcmp : ∀ k : Nat,
    Le (sec4IB_diffRelIntegral B hB f hnn k)
      (sec4IB_coverIncrement B hB f hnn k)
  cover_le_full : ∀ k : Nat,
    Le (sec4IB_coverIncrement B hB f hnn k)
      (sec4FullCoverIncrement f hnn k)


/--
The `B`-cover increments are summable once they are dominated by the
full-cover increments.
-/
noncomputable def sec4IB_coverIncrement_sum_of_bridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementBridge (S := S) B hB f hnn) :
    RSeq.SeriesSum (fun k => sec4IB_coverIncrement B hB f hnn k) :=
  seriesSum_comparison
    (fun k => sec4IB_coverIncrement_nonneg B hB f hnn k)
    G.cover_le_full
    (sec4FullCoverIncrement_sum f hnn)


/-- Tail data for the direct `I_B` candidate from the C2 bridge. -/
noncomputable def sec4IBTailData_of_incrementBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementBridge (S := S) B hB f hnn) :
    Sec4IBTailData (S := S) B hB f hnn :=
  sec4IBTailData_of_coverIncrement B hB f hnn
    G.hcmp
    (sec4IB_coverIncrement_sum_of_bridge B hB f hnn G)


/-- Direct `χ_B·f` candidate from the C2 bridge. -/
noncomputable def genIB_rep_from_incrementBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementBridge (S := S) B hB f hnn) :
    IntegrableRep S :=
  genIB_rep_from_tailData B hB f hnn
    (sec4IBTailData_of_incrementBridge B hB f hnn G)


/-- General relative integral candidate from the C2 bridge. -/
noncomputable def genRelIntegral_from_incrementBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementBridge (S := S) B hB f hnn) : R :=
  (genIB_rep_from_incrementBridge B hB f hnn G).integral


/-- Non-negativity of the direct candidate from the C2 bridge. -/
noncomputable def genIB_rep_from_incrementBridge_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementBridge (S := S) B hB f hnn) :
    RepNonneg (genIB_rep_from_incrementBridge B hB f hnn G) := by
  unfold genIB_rep_from_incrementBridge
  exact genIB_rep_from_tailData_repNonneg B hB f hnn
    (sec4IBTailData_of_incrementBridge B hB f hnn G)


end BishopC
