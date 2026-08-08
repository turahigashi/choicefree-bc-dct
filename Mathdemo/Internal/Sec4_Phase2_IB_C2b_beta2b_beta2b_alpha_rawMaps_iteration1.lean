import Mathdemo.Internal.Sec4_Phase2_IB_C2b_beta2b_beta2a_setMap_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C2bβ2bβ2bα: raw BSet maps for the layer construction

The previous chunk reduced the direct `I_B` candidate to
`Sec4IBLayerSetMapData`.

This file proves the raw set-theoretic part:
* `(V ∧ B) ∨ ((U ∧ B) - (V ∧ B)) → U ∧ B`;
* `V ∨ (U - V) → U`;
* the two empty-S1 facts for the intersections;
* the S1 direction `(U ∧ B) - (V ∧ B) → U - V`.

The remaining analytic conversion from the empty-S1/S1-map facts to
`cover_and_zero`, `full_and_zero`, and `diff_le_full_value` is isolated in
`Sec4IBLayerResidualData`.
-/

#check Sec4IBLayerSetMapData
#check Sec4IBLayerSetMapData.mk
#check Sec4BSetValueMap
#check sec4CoverAnd
#check sec4CoverDiff
#check sec4CoverOrDiff
#check sec4CoverAndDiff
#check sec4FullCoverDiff
#check sec4FullCoverOrDiff
#check sec4FullCoverAndDiff
#check coverSet_mono
#check BSet.and
#check BSet.or
#check BSet.sub
#check BSet.neg

/-! ## 1. Raw maps for the two union identities -/

/-- Technical lemma used in the public import closure. -/
theorem sec4_coverOr_valueMap_raw
    (B : BSet X) (f : IntegrableRep S) (k : Nat) :
    Sec4BSetValueMap
      (sec4CoverOrDiff B f k)
      (sec4CoverAnd B f (k + 1)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold sec4CoverOrDiff at hx
    rcases hx with (⟨⟨hV, hB⟩, _⟩ | ⟨⟨hV, hB⟩, _⟩) | ⟨_, hUB1, _⟩
    · exact ⟨coverSet_mono f k hV, hB⟩
    · exact ⟨coverSet_mono f k hV, hB⟩
    · exact hUB1
  · intro x hx
    unfold sec4CoverOrDiff at hx
    rcases hx with ⟨hA2, (hbad | hgood) | hgood⟩
    · exact ((sec4CoverAnd B f k).disj x hbad.2 x hA2 rfl).elim
    · exact hgood.1
    · exact hgood.1


/-- Technical lemma used in the public import closure. -/
theorem sec4_fullOr_valueMap_raw
    (f : IntegrableRep S) (k : Nat) :
    Sec4BSetValueMap
      (sec4FullCoverOrDiff f k)
      (coverSet f (k + 1)) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold sec4FullCoverOrDiff at hx
    rcases hx with (⟨hV, _⟩ | ⟨hV, _⟩) | ⟨_, hU1, _⟩
    · exact coverSet_mono f k hV
    · exact coverSet_mono f k hV
    · exact hU1
  · intro x hx
    unfold sec4FullCoverOrDiff at hx
    rcases hx with ⟨hV2, (hbad | hgood) | hgood⟩
    · exact ((coverSet f k).disj x hbad.2 x hV2 rfl).elim
    · exact hgood.1
    · exact hgood.1


/-! ## 2. Empty-S1 and S1-map raw facts -/

/-- The restricted intersection `(V∧B)∧((U∧B)\(V∧B))` has empty S1. -/
theorem sec4_coverAndDiff_s1_empty_raw
    (B : BSet X) (f : IntegrableRep S) (k : Nat) :
    ∀ x : X, x ∈ (sec4CoverAndDiff B f k).S1 → False := by
  intro x hx
  unfold sec4CoverAndDiff at hx
  change x ∈ (sec4CoverAnd B f k).S1 ∧
      x ∈ (sec4CoverDiff B f k).S1 at hx
  rcases hx with ⟨hOld1, hD1⟩
  unfold sec4CoverDiff at hD1
  change x ∈ (sec4CoverAnd B f (k + 1)).S1 ∧
      x ∈ (sec4CoverAnd B f k).S2 at hD1
  exact (sec4CoverAnd B f k).disj x hOld1 x hD1.2 rfl


/-- The full-cover intersection `V∧(U\V)` has empty S1. -/
theorem sec4_fullCoverAndDiff_s1_empty_raw
    (f : IntegrableRep S) (k : Nat) :
    ∀ x : X, x ∈ (sec4FullCoverAndDiff f k).S1 → False := by
  intro x hx
  unfold sec4FullCoverAndDiff at hx
  change x ∈ (coverSet f k).S1 ∧
      x ∈ (sec4FullCoverDiff f k).S1 at hx
  rcases hx with ⟨hV1, hD1⟩
  unfold sec4FullCoverDiff at hD1
  change x ∈ (coverSet f (k + 1)).S1 ∧ x ∈ (coverSet f k).S2 at hD1
  exact (coverSet f k).disj x hV1 x hD1.2 rfl


/--
S1 direction for the difference comparison:
`((U∧B)\(V∧B)).S1 → (U\V).S1`.
-/
theorem sec4_coverDiff_s1_to_full_raw
    (B : BSet X) (f : IntegrableRep S) (k : Nat) :
    ∀ x : X, x ∈ (sec4CoverDiff B f k).S1 →
      x ∈ (sec4FullCoverDiff f k).S1 := by
  intro x hx
  unfold sec4CoverDiff at hx
  unfold sec4FullCoverDiff
  rcases hx with ⟨⟨hU1, hB1⟩, (hbad | hgood) | hgood⟩
  · exact absurd hbad.2 (fun h => B.disj x hB1 x h rfl)
  · exact ⟨hU1, hgood.1⟩
  · exact ⟨hU1, hgood.1⟩


/-! ## 3. Residual analytic data and assembly -/

/--
The remaining analytic conversion data after the raw set maps are known.

`cover_and_zero` and `full_and_zero` should be obtained from the empty-S1
facts above.  `diff_le_full_value` should be obtained from
`sec4_coverDiff_s1_to_full_raw` and the characteristic validness of the two
integrable difference sets.
-/
def Sec4IBLayerResidualData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4PD_coverAndZero (S := S) B hB f hnn)
    (PProd (Sec4PD_fullAndZero (S := S) f hnn)
      (Sec4PD_diffLeFull (S := S) B hB f hnn))


namespace Sec4IBLayerResidualData

/-- Constructor with stable named arguments. -/
def mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (cover_and_zero : Sec4PD_coverAndZero (S := S) B hB f hnn)
    (full_and_zero : Sec4PD_fullAndZero (S := S) f hnn)
    (diff_le_full_value : Sec4PD_diffLeFull (S := S) B hB f hnn) :
    Sec4IBLayerResidualData (S := S) B hB f hnn :=
  ⟨cover_and_zero, full_and_zero, diff_le_full_value⟩


def cover_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerResidualData (S := S) B hB f hnn) :
    Sec4PD_coverAndZero (S := S) B hB f hnn :=
  G.1


def full_and_zero
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerResidualData (S := S) B hB f hnn) :
    Sec4PD_fullAndZero (S := S) f hnn :=
  G.2.1


def diff_le_full_value
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (G : Sec4IBLayerResidualData (S := S) B hB f hnn) :
    Sec4PD_diffLeFull (S := S) B hB f hnn :=
  G.2.2


end Sec4IBLayerResidualData

/--
Build the set-map data once the residual analytic conversions have been
supplied.
-/
noncomputable def sec4IBLayerSetMapData_of_residualData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerResidualData (S := S) B hB f hnn) :
    Sec4IBLayerSetMapData (S := S) B hB f hnn :=
  Sec4IBLayerSetMapData.mk
    (cover_or_map := fun k => sec4_coverOr_valueMap_raw B f k)
    (cover_and_zero := G.cover_and_zero)
    (full_or_map := fun k => sec4_fullOr_valueMap_raw f k)
    (full_and_zero := G.full_and_zero)
    (diff_le_full_value := G.diff_le_full_value)


/-- Direct representative from the residual analytic data and the raw maps. -/
noncomputable def genIB_rep_from_residualData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerResidualData (S := S) B hB f hnn) :
    IntegrableRep S :=
  genIB_rep_from_setMapData B hB f hnn
    (sec4IBLayerSetMapData_of_residualData B hB f hnn G)


/-- General relative integral from residual analytic data and the raw maps. -/
noncomputable def genRelIntegral_from_residualData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerResidualData (S := S) B hB f hnn) : R :=
  (genIB_rep_from_residualData B hB f hnn G).integral


/-- Non-negativity from residual analytic data and the raw maps. -/
noncomputable def genIB_rep_from_residualData_repNonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (G : Sec4IBLayerResidualData (S := S) B hB f hnn) :
    RepNonneg (genIB_rep_from_residualData B hB f hnn G) := by
  unfold genIB_rep_from_residualData
  exact genIB_rep_from_setMapData_repNonneg B hB f hnn
    (sec4IBLayerSetMapData_of_residualData B hB f hnn G)


end BishopC
