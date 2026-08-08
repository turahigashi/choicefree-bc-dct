import Mathdemo.Internal.Sec4_Phase2_IB_C2b_beta1_layerRelIdentities_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bβ2a: bridge without global `BSet.Subset`

C2bβ1 passed.  The next mathematical task is to build the four value-level
relative-integral identities.  The kernel response also warns that the
`BSet.Subset` second component for
`(A_{k+1}∧B)\(A_k∧B) ⊆ A_{k+1}\A_k` may be too strong constructively.

This file therefore provides a safer interface: instead of asking for a global
`BSet.Subset`, it asks directly for the relIntegral comparison

`I_{(A_{k+1}∧B)\(A_k∧B)} ≤ I_{A_{k+1}\A_k}`,

which is the statement actually needed by C2a.  This comparison can later be
proved by `relIntegral_mono_le` on a full set supplied by measurability of `B`.

The four equalities are still extracted from `relIntegral_or_add_and` exactly
as in C2bβ1.
-/

#check Sec4IBIncrementBridge
#check Sec4IBLayerRelIdentities
#check sec4IB_diff_eq_cover_of_layerRelIdentities
#check sec4Full_diff_eq_increment_of_layerRelIdentities
#check sec4IBTailData_of_incrementBridge
#check genIB_rep_from_incrementBridge
#check relIntegral_mono_le
#check relIntegral_or_add_and

/--
Layer relative-integral data sufficient for the direct `I_B` construction.

Compared with `Sec4IBLayerRelIdentities`, the final field is the exact
relIntegral comparison needed downstream, rather than a global complemented-set
subset.
-/
structure Sec4IBLayerRelData
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
  diff_le_full :
    ∀ k : Nat,
      Le (sec4IB_diffRelIntegral B hB f hnn k)
        (sec4FullDiffRelIntegral f hnn k)


/--
Restricted increment identity from the four value-level identities.
-/
theorem sec4IB_diff_eq_cover_of_layerRelData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelData (S := S) B hB f hnn) :
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
Full-cover increment identity from the full-cover value-level identities.
-/
theorem sec4Full_diff_eq_increment_of_layerRelData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelData (S := S) B hB f hnn) :
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


/--
Construct the C2a increment bridge from the value-level layer data.
-/
noncomputable def sec4IBIncrementBridge_of_layerRelData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelData (S := S) B hB f hnn) :
    Sec4IBIncrementBridge (S := S) B hB f hnn := {
  hcmp := by
    intro k
    rw [← sec4IB_diff_eq_cover_of_layerRelData B hB f hnn G k]
    exact BishopC.le_refl (sec4IB_diffRelIntegral B hB f hnn k)
  cover_le_full := by
    intro k
    rw [← sec4IB_diff_eq_cover_of_layerRelData B hB f hnn G k,
        ← sec4Full_diff_eq_increment_of_layerRelData B hB f hnn G k]
    exact G.diff_le_full k
}


/-- Tail data from the safer value-level layer data. -/
noncomputable def sec4IBTailData_of_layerRelData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelData (S := S) B hB f hnn) :
    Sec4IBTailData (S := S) B hB f hnn :=
  sec4IBTailData_of_incrementBridge B hB f hnn
    (sec4IBIncrementBridge_of_layerRelData B hB f hnn G)


/-- Direct representative from the safer value-level layer data. -/
noncomputable def genIB_rep_from_layerRelData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelData (S := S) B hB f hnn) :
    IntegrableRep S :=
  genIB_rep_from_tailData B hB f hnn
    (sec4IBTailData_of_layerRelData B hB f hnn G)


/-- General relative integral from the safer value-level layer data. -/
noncomputable def genRelIntegral_from_layerRelData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelData (S := S) B hB f hnn) : R :=
  (genIB_rep_from_layerRelData B hB f hnn G).integral


/-- Non-negativity of the direct representative from the safer layer data. -/
noncomputable def genIB_rep_from_layerRelData_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerRelData (S := S) B hB f hnn) :
    RepNonneg (genIB_rep_from_layerRelData B hB f hnn G) := by
  unfold genIB_rep_from_layerRelData
  exact genIB_rep_from_tailData_repNonneg B hB f hnn
    (sec4IBTailData_of_layerRelData B hB f hnn G)


end BishopC
