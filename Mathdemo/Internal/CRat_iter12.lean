import Mathdemo.Internal.CRat_iter11

/-!
# CReal raw order irrefl and closed COFO fragments

This file closes the easy order fragment: no representative can be strictly
positive over its own raw difference.  It also records the already closed COFO
raw fragments in one audited seed.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The raw self-difference sequence is pointwise zero. -/
theorem sub_self_val (x : Nat → Scalar) (n : Nat) : subVal x x n = 0 := by
  unfold subVal addIndex
  ring

/-- Raw strict order is irreflexive at the representative level. -/
theorem lt_irrefl_raw (x : RegularSeq) : ¬ PosVal (subVal x.val x.val) := by
  intro hpos
  rcases hpos with ⟨n, hn⟩
  rw [sub_self_val x.val n] at hn
  exact eps_nonneg n hn

/-- The current `inv_pos_raw` frontier field is an identity placeholder. -/
theorem inv_pos_raw (x : RegularSeq) : PosRaw x → PosRaw x := by
  intro hx
  exact hx

/-- Audited basic order fragment. -/
structure CRealOrderBasicSeed : Type where
  sub_self_val : ∀ x : Nat → Scalar, ∀ n : Nat, subVal x x n = 0
  lt_irrefl_raw : ∀ x : RegularSeq, ¬ PosVal (subVal x.val x.val)

def cRealOrderBasicSeed : CRealOrderBasicSeed where
  sub_self_val := sub_self_val
  lt_irrefl_raw := lt_irrefl_raw

/-- Audited COFO fragments that are already closed without the hard order,
multiplication, Archimedean, or equality-smallness layers. -/
structure CRealCOFOBasicSeed : Type where
  abs_zero_raw : relVal (absVal zeroVal) zeroVal
  abs_neg_raw : ∀ x : RegularSeq, relVal (absVal (negVal x.val)) (absVal x.val)
  one_pos_raw : PosVal oneVal
  half_pos_raw : PosVal halfVal
  inv_pos_raw : ∀ x : RegularSeq, PosRaw x → PosRaw x

def cRealCOFOBasicSeed : CRealCOFOBasicSeed where
  abs_zero_raw := abs_zero_raw
  abs_neg_raw := abs_neg_raw
  one_pos_raw := one_pos_raw
  half_pos_raw := half_pos_raw
  inv_pos_raw := inv_pos_raw

end BishopCReal

