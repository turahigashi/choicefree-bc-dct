import Mathdemo.Internal.Sec4.FullIncrement

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bα: from increment algebra to `Sec4IBIncrementBridge`

C2a reduced the direct construction to `Sec4IBIncrementBridge`.
The C2a kernel response identified the remaining hard part as finite
BSet algebra:

* `I_{(A_{k+1}∧B)\(A_k∧B)} = I_{A_{k+1}∧B} - I_{A_k∧B}`;
* the analogous full-cover identity;
* `(A_{k+1}∧B)\(A_k∧B) ⊆ A_{k+1}\A_k`.

This file isolates those exact algebraic facts in `Sec4IBIncrementAlgebra`
and proves that they imply the C2a bridge and therefore the concrete direct
candidate.  The next kernel-loop chunk can focus only on constructing
`Sec4IBIncrementAlgebra` from `relIntegral_or_add_and`,
`relIntegral_complement_additive`, and raw `BSet` subset algebra.
-/

#check Sec4IBIncrementBridge
#check sec4IB_diffRelIntegral
#check sec4IB_coverIncrement
#check sec4FullCoverIncrement
#check relIntegral_mono_set
#check IntegrableSet1_sub
#check coverSet_int
#check BSet.sub
#check BSet.Subset

/-! ## 1. Full-cover difference layer -/

/--
The full-cover layer `A_{k+1} \ A_k`.

This is the ambient version of `sec4CoverDiff`, without the measurable set
`B`.
-/
noncomputable def sec4FullCoverDiff
    (f : IntegrableRep S) (k : Nat) : BSet X :=
  BSet.sub (coverSet f (k + 1)) (coverSet f k)


/-- Integrability of the full-cover layer. -/
noncomputable def sec4FullCoverDiff_int
    (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (sec4FullCoverDiff f k) :=
  IntegrableSet1_sub (coverSet_int f (k + 1)) (coverSet_int f k)


/-- Relative integral over the full-cover layer. -/
noncomputable def sec4FullDiffRelIntegral
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : R :=
  relIntegral (sec4FullCoverDiff f k) (sec4FullCoverDiff_int f k) f hnn


/-! ## 2. Algebraic package for the bridge -/

/--
The exact finite-set algebra still required for C2b.

`diff_eq_cover` and `full_diff_eq_increment` are the two telescoping
increment identities; `diff_subset_full` is the raw inclusion of the
`B`-restricted layer into the full layer.
-/
structure Sec4IBIncrementAlgebra
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop where
  diff_eq_cover :
    ∀ k : Nat,
      sec4IB_diffRelIntegral B hB f hnn k =
        sec4IB_coverIncrement B hB f hnn k
  full_diff_eq_increment :
    ∀ k : Nat,
      sec4FullDiffRelIntegral f hnn k =
        sec4FullCoverIncrement f hnn k
  diff_subset_full :
    ∀ k : Nat,
      BSet.Subset (sec4CoverDiff B f k) (sec4FullCoverDiff f k)


/-- The C1 comparison `I_{D_k^B} ≤ ψ_{k+1}-ψ_k` from the first identity. -/
theorem sec4IB_hcmp_of_incrementAlgebra
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementAlgebra (S := S) B hB f hnn) :
    ∀ k : Nat,
      Le (sec4IB_diffRelIntegral B hB f hnn k)
        (sec4IB_coverIncrement B hB f hnn k) := by
  intro k
  rw [← G.diff_eq_cover k]
  exact BishopC.le_refl (sec4IB_diffRelIntegral B hB f hnn k)


/--
`B`-restricted cover increments are bounded by full-cover increments.

After both increment identities are rewritten, this is just
`relIntegral_mono_set` applied to the inclusion of difference layers.
-/
theorem sec4IB_cover_le_full_of_incrementAlgebra
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementAlgebra (S := S) B hB f hnn) :
    ∀ k : Nat,
      Le (sec4IB_coverIncrement B hB f hnn k)
        (sec4FullCoverIncrement f hnn k) := by
  intro k
  rw [← G.diff_eq_cover k, ← G.full_diff_eq_increment k]
  exact relIntegral_mono_set
    (sec4CoverDiff B f k)
    (sec4FullCoverDiff f k)
    (sec4CoverDiff_int B hB f k)
    (sec4FullCoverDiff_int f k)
    (G.diff_subset_full k)
    f hnn


/--
Construct the C2a bridge from the algebra package.
-/
noncomputable def sec4IBIncrementBridge_of_algebra
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementAlgebra (S := S) B hB f hnn) :
    Sec4IBIncrementBridge (S := S) B hB f hnn := {
  hcmp := sec4IB_hcmp_of_incrementAlgebra B hB f hnn G
  cover_le_full := sec4IB_cover_le_full_of_incrementAlgebra B hB f hnn G
}


/-! ## 3. Direct construction from increment algebra -/

/-- Tail data obtained from the finite-set algebra package. -/
noncomputable def sec4IBTailData_of_incrementAlgebra
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementAlgebra (S := S) B hB f hnn) :
    Sec4IBTailData (S := S) B hB f hnn :=
  sec4IBTailData_of_incrementBridge B hB f hnn
    (sec4IBIncrementBridge_of_algebra B hB f hnn G)


/-- Direct `χ_B·f` candidate from the finite-set algebra package. -/
noncomputable def genIB_rep_from_incrementAlgebra
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBIncrementAlgebra (S := S) B hB f hnn) :
    IntegrableRep S :=
  genIB_rep_from_tailData B hB f hnn
    (sec4IBTailData_of_incrementAlgebra B hB f hnn G)






end BishopC
