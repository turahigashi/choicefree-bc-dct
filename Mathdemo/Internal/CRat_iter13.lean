import Mathdemo.Internal.CRat_iter12

/-!
# CReal raw additive algebra laws

These laws are not yet enough to emit a quotient `CommRing`, but they close the
representative-level additive identities that the eventual quotient algebra
will need.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Strict scalar inequality induces the constructive non-strict order. -/
theorem scalar_le_of_lt {a b : Scalar} (h : COF.lt a b) : Le a b := by
  intro hba
  exact COF.lt_irrefl a (scalarCOFOSeed.lt_trans h hba)

/-- The next dyadic gauge is non-strictly below the previous one. -/
theorem eps_succ_le_eps (n : Nat) : Le (eps (n + 1)) (eps n) :=
  scalar_le_of_lt (eps_succ_lt_eps n)

/-- Regularity budget for shifting one step forward. -/
theorem eps_succ_add_le_tol (n : Nat) : Le (eps (n + 1) + eps n) (tol n) := by
  unfold tol
  exact BishopC.le_add (eps_succ_le_eps n) (BishopC.le_refl (eps n))

/-- Budget for associativity of the reindexed addition operation. -/
theorem eps_assoc_budget (n : Nat) :
    Le ((eps (n + 2) + eps (n + 1)) + (eps (n + 1) + eps (n + 2))) (tol n) := by
  have heq :
      (eps (n + 2) + eps (n + 1)) + (eps (n + 1) + eps (n + 2))
        = eps n + eps (n + 1) := by
    rw [show (eps (n + 2) + eps (n + 1)) + (eps (n + 1) + eps (n + 2))
        = (eps (n + 1) + eps (n + 1)) + (eps (n + 2) + eps (n + 2))
        from by ring, eps_succ_add_self n, eps_succ_add_self (n + 1)]
  rw [heq]
  unfold tol
  exact BishopC.le_add (BishopC.le_refl (eps n)) (eps_succ_le_eps n)

/-- Raw right additive identity. -/
theorem add_zero_raw (x : RegularSeq) : relVal (addVal x.val zeroVal) x.val := by
  intro n
  unfold addVal addIndex zeroVal constVal
  rw [show x.val (n + 1) + 0 - x.val n = x.val (n + 1) - x.val n from by ring]
  exact BishopC.le_trans (x.regular (n + 1) n) (eps_succ_add_le_tol n)

/-- Raw left additive identity. -/
theorem zero_add_raw (x : RegularSeq) : relVal (addVal zeroVal x.val) x.val := by
  intro n
  unfold addVal addIndex zeroVal constVal
  rw [show 0 + x.val (n + 1) - x.val n = x.val (n + 1) - x.val n from by ring]
  exact BishopC.le_trans (x.regular (n + 1) n) (eps_succ_add_le_tol n)

/-- Raw commutativity of addition. -/
theorem add_comm_raw (x y : RegularSeq) :
    relVal (addVal x.val y.val) (addVal y.val x.val) := by
  intro n
  unfold addVal addIndex
  rw [show (x.val (n + 1) + y.val (n + 1)) - (y.val (n + 1) + x.val (n + 1))
      = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Raw associativity of reindexed addition. -/
theorem add_assoc_raw (x y z : RegularSeq) :
    relVal (addVal (addVal x.val y.val) z.val) (addVal x.val (addVal y.val z.val)) := by
  intro n
  unfold addVal addIndex
  have htri : Le
      (COF.abs (((x.val (n + 2) + y.val (n + 2)) + z.val (n + 1))
        - (x.val (n + 1) + (y.val (n + 2) + z.val (n + 2)))))
      (COF.abs (x.val (n + 2) - x.val (n + 1))
        + COF.abs (z.val (n + 1) - z.val (n + 2))) := by
    have h := scalar_abs_add_le
      (x.val (n + 2) - x.val (n + 1))
      (z.val (n + 1) - z.val (n + 2))
    rwa [show (x.val (n + 2) - x.val (n + 1))
        + (z.val (n + 1) - z.val (n + 2))
        = ((x.val (n + 2) + y.val (n + 2)) + z.val (n + 1))
          - (x.val (n + 1) + (y.val (n + 2) + z.val (n + 2)))
        from by ring] at h
  have hx := x.regular (n + 2) (n + 1)
  have hz := z.regular (n + 1) (n + 2)
  have hsum := BishopC.le_add hx hz
  exact BishopC.le_trans htri (BishopC.le_trans hsum (eps_assoc_budget n))

/-- Raw left additive inverse. -/
theorem neg_add_cancel_raw (x : RegularSeq) :
    relVal (addVal (negVal x.val) x.val) zeroVal := by
  intro n
  unfold addVal addIndex negVal zeroVal constVal
  rw [show (-x.val (n + 1) + x.val (n + 1)) - 0 = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Raw right additive inverse. -/
theorem add_neg_cancel_raw (x : RegularSeq) :
    relVal (addVal x.val (negVal x.val)) zeroVal := by
  intro n
  unfold addVal addIndex negVal zeroVal constVal
  rw [show (x.val (n + 1) + -x.val (n + 1)) - 0 = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Audited raw additive algebra seed. -/
structure CRealAdditiveAlgebraSeed : Type where
  add_zero_raw : ∀ x : RegularSeq, relVal (addVal x.val zeroVal) x.val
  zero_add_raw : ∀ x : RegularSeq, relVal (addVal zeroVal x.val) x.val
  add_comm_raw : ∀ x y : RegularSeq, relVal (addVal x.val y.val) (addVal y.val x.val)
  add_assoc_raw : ∀ x y z : RegularSeq,
    relVal (addVal (addVal x.val y.val) z.val) (addVal x.val (addVal y.val z.val))
  neg_add_cancel_raw : ∀ x : RegularSeq, relVal (addVal (negVal x.val) x.val) zeroVal
  add_neg_cancel_raw : ∀ x : RegularSeq, relVal (addVal x.val (negVal x.val)) zeroVal

def cRealAdditiveAlgebraSeed : CRealAdditiveAlgebraSeed where
  add_zero_raw := add_zero_raw
  zero_add_raw := zero_add_raw
  add_comm_raw := add_comm_raw
  add_assoc_raw := add_assoc_raw
  neg_add_cancel_raw := neg_add_cancel_raw
  add_neg_cancel_raw := add_neg_cancel_raw

end BishopCReal

