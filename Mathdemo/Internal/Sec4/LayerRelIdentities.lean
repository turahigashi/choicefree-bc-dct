import Mathdemo.Internal.Sec4.IncrementAlgebra

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bβ1: increment identities from value-level layer algebra

C2bα reduced the construction to `Sec4IBIncrementAlgebra`.
The kernel response explains that the equalities cannot be obtained by a
missing `relIntegral_congr`; they must be proved by the same value-computation
pattern used internally by `relIntegral_or_add_and`.

This file packages exactly the four value-level relIntegral identities needed
around `relIntegral_or_add_and`, and proves that they imply
`Sec4IBIncrementAlgebra`.

The next chunk should construct `Sec4IBLayerRelIdentities` by `cor_1_12` and
`prop_4_2_chi_f_rep_value`:
* `(V∧B)∨((U∧B)\(V∧B))` has the same characteristic value as `U∧B`;
* `(V∧B)∧((U∧B)\(V∧B))` has characteristic value zero;
* `V∨(U\V)` has the same characteristic value as `U`;
* `V∧(U\V)` has characteristic value zero;
* and the raw subset field needed by C2bα.
-/

#check relIntegral_or_add_and
#check IntegrableSet1_or
#check IntegrableSet1_and
#check cor_1_12
#check prop_4_2_chi_f_rep_value
#check Sec4IBIncrementAlgebra
#check sec4IBIncrementBridge_of_algebra
#check genIB_rep_from_incrementAlgebra

/-! ## 1. The four local layer sets used by `relIntegral_or_add_and` -/

/-- `(A_k∧B) ∨ ((A_{k+1}∧B)\(A_k∧B))`. -/
noncomputable def sec4CoverOrDiff
    (B : BSet X) (f : IntegrableRep S) (k : Nat) : BSet X :=
  BSet.or (sec4CoverAnd B f k) (sec4CoverDiff B f k)


/-- `(A_k∧B) ∧ ((A_{k+1}∧B)\(A_k∧B))`. -/
noncomputable def sec4CoverAndDiff
    (B : BSet X) (f : IntegrableRep S) (k : Nat) : BSet X :=
  BSet.and (sec4CoverAnd B f k) (sec4CoverDiff B f k)


/-- `A_k ∨ (A_{k+1}\A_k)`. -/
noncomputable def sec4FullCoverOrDiff
    (f : IntegrableRep S) (k : Nat) : BSet X :=
  BSet.or (coverSet f k) (sec4FullCoverDiff f k)


/-- `A_k ∧ (A_{k+1}\A_k)`. -/
noncomputable def sec4FullCoverAndDiff
    (f : IntegrableRep S) (k : Nat) : BSet X :=
  BSet.and (coverSet f k) (sec4FullCoverDiff f k)


/-- Integrability of `sec4CoverOrDiff`. -/
noncomputable def sec4CoverOrDiff_int
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (sec4CoverOrDiff B f k) :=
  IntegrableSet1_or
    (sec4CoverAnd_int B hB f k)
    (sec4CoverDiff_int B hB f k)


/-- Integrability of `sec4CoverAndDiff`. -/
noncomputable def sec4CoverAndDiff_int
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (sec4CoverAndDiff B f k) :=
  IntegrableSet1_and
    (sec4CoverAnd_int B hB f k)
    (sec4CoverDiff_int B hB f k)


/-- Integrability of `sec4FullCoverOrDiff`. -/
noncomputable def sec4FullCoverOrDiff_int
    (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (sec4FullCoverOrDiff f k) :=
  IntegrableSet1_or
    (coverSet_int f k)
    (sec4FullCoverDiff_int f k)


/-- Integrability of `sec4FullCoverAndDiff`. -/
noncomputable def sec4FullCoverAndDiff_int
    (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (sec4FullCoverAndDiff f k) :=
  IntegrableSet1_and
    (coverSet_int f k)
    (sec4FullCoverDiff_int f k)


/-! ## 2. The layer relIntegral identities still supplied by value computation -/

/--
The relIntegral identities around one restricted layer and one full layer.

The four equalities are intended to be proved by `cor_1_12` plus
`prop_4_2_chi_f_rep_value`, not by a nonexistent relIntegral congruence lemma.
-/
structure Sec4IBLayerRelIdentities
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop where
  cover_or_eq :
    ∀ k : Nat,
      relIntegral (sec4CoverOrDiff B f k)
        (sec4CoverOrDiff_int B hB f k) f hnn =
      sec4IB_coverIntegral B hB f hnn (k + 1)
  cover_and_zero :
    ∀ k : Nat,
      relIntegral (sec4CoverAndDiff B f k)
        (sec4CoverAndDiff_int B hB f k) f hnn = 0
  full_or_eq :
    ∀ k : Nat,
      relIntegral (sec4FullCoverOrDiff f k)
        (sec4FullCoverOrDiff_int f k) f hnn =
      sec4FullCoverIntegral f hnn (k + 1)
  full_and_zero :
    ∀ k : Nat,
      relIntegral (sec4FullCoverAndDiff f k)
        (sec4FullCoverAndDiff_int f k) f hnn = 0
  diff_subset_full :
    ∀ k : Nat,
      BSet.Subset (sec4CoverDiff B f k) (sec4FullCoverDiff f k)


/-! ## 3. Algebraic extraction of the increment identities -/

/--
`I_{(A_{k+1}∧B)\(A_k∧B)} = I_{A_{k+1}∧B} - I_{A_k∧B}`.

This is just `relIntegral_or_add_and`, plus the two value-level identities
for the union and empty-intersection terms.
-/
theorem sec4IB_diff_eq_cover_of_layerRelIdentities
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelIdentities (S := S) B hB f hnn) :
    ∀ k : Nat,
      sec4IB_diffRelIntegral B hB f hnn k =
        sec4IB_coverIncrement B hB f hnn k := by
  intro k
  let D := sec4CoverAnd B f k
  let E := sec4CoverDiff B f k
  let hD := sec4CoverAnd_int B hB f k
  let hE := sec4CoverDiff_int B hB f k
  let Ior : R :=
    relIntegral (BSet.or D E) (IntegrableSet1_or hD hE) f hnn
  let Iand : R :=
    relIntegral (BSet.and D E) (IntegrableSet1_and hD hE) f hnn
  let ID : R := relIntegral D hD f hnn
  let IE : R := relIntegral E hE f hnn
  let IU : R := sec4IB_coverIntegral B hB f hnn (k + 1)
  have hadd : Ior + Iand = ID + IE := by
    dsimp [Ior, Iand, ID, IE, D, E, hD, hE]
    exact relIntegral_or_add_and
      (sec4CoverAnd_int B hB f k)
      (sec4CoverDiff_int B hB f k) f hnn
  have hor : Ior = IU := by
    dsimp [Ior, IU, D, E, hD, hE, sec4CoverOrDiff, sec4IB_coverIntegral]
    exact G.cover_or_eq k
  have hand : Iand = 0 := by
    dsimp [Iand, D, E, hD, hE, sec4CoverAndDiff]
    exact G.cover_and_zero k
  calc
    sec4IB_diffRelIntegral B hB f hnn k
        = IE := by rfl
    _ = (ID + IE) - ID := by ring
    _ = (Ior + Iand) - ID := by rw [hadd]
    _ = (IU + 0) - ID := by rw [hor, hand]
    _ = IU - ID := by ring
    _ = sec4IB_coverIncrement B hB f hnn k := by rfl


/--
`I_{A_{k+1}\A_k} = Ψ_{k+1} - Ψ_k`.

The proof is the full-cover analogue of
`sec4IB_diff_eq_cover_of_layerRelIdentities`.
-/
theorem sec4Full_diff_eq_increment_of_layerRelIdentities
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelIdentities (S := S) B hB f hnn) :
    ∀ k : Nat,
      sec4FullDiffRelIntegral f hnn k =
        sec4FullCoverIncrement f hnn k := by
  intro k
  let D := coverSet f k
  let E := sec4FullCoverDiff f k
  let hD := coverSet_int f k
  let hE := sec4FullCoverDiff_int f k
  let Ior : R :=
    relIntegral (BSet.or D E) (IntegrableSet1_or hD hE) f hnn
  let Iand : R :=
    relIntegral (BSet.and D E) (IntegrableSet1_and hD hE) f hnn
  let ID : R := relIntegral D hD f hnn
  let IE : R := relIntegral E hE f hnn
  let IU : R := sec4FullCoverIntegral f hnn (k + 1)
  have hadd : Ior + Iand = ID + IE := by
    dsimp [Ior, Iand, ID, IE, D, E, hD, hE]
    exact relIntegral_or_add_and
      (coverSet_int f k)
      (sec4FullCoverDiff_int f k) f hnn
  have hor : Ior = IU := by
    dsimp [Ior, IU, D, E, hD, hE, sec4FullCoverOrDiff, sec4FullCoverIntegral]
    exact G.full_or_eq k
  have hand : Iand = 0 := by
    dsimp [Iand, D, E, hD, hE, sec4FullCoverAndDiff]
    exact G.full_and_zero k
  calc
    sec4FullDiffRelIntegral f hnn k
        = IE := by rfl
    _ = (ID + IE) - ID := by ring
    _ = (Ior + Iand) - ID := by rw [hadd]
    _ = (IU + 0) - ID := by rw [hor, hand]
    _ = IU - ID := by ring
    _ = sec4FullCoverIncrement f hnn k := by rfl




/-! ## 4. Direct construction from layer identities -/









end BishopC
