import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b4_succLayerTelescope_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b5: point χ-step telescope

The b2b4 kernel response confirms that the successor-index layer interface
passed.  The remaining six fields of `Sec4CanonicalCoverLayerTelescopeDataSucc`
contain one genuinely algebraic part: the pointwise characteristic telescope.

This file proves that algebraic part from validness of the three characteristic
representatives.  It uses no equality/congruence theorem for integrals and no
arbitrary signed-witness χ reading.  Everything is read from abs witnesses via
`IntegrableSet1.valid`.

The remaining data after this file are only the characteristic abs witnesses
and the zero branches on `B.S2`.
-/

#check Sec4CanonicalCoverLayerTelescopeDataSucc
#check sec4_genIBValueBridge_of_succLayerData
#check sec4_genRelIntegral_eq_relIntegral_of_succLayerData
#check sec4_genIBConsistencyBridge_of_succLayerData
#check sec4CoverAnd
#check sec4CoverDiff
#check sec4CoverAnd_int
#check sec4CoverDiff_int
#check coverSet_mono

/-! ## 1. Raw membership facts for `coverAnd` and `coverDiff` -/

/-- `coverSet` monotonicity, lifted to `coverSet ∧ B`. -/
theorem sec4_coverAnd_s1_mono
    (B : BSet X) (f : IntegrableRep S) (k : Nat) (x : X)
    (h : x ∈ (sec4CoverAnd B f k).S1) :
    x ∈ (sec4CoverAnd B f (k + 1)).S1 := by
  unfold sec4CoverAnd at h
  unfold sec4CoverAnd
  exact ⟨coverSet_mono f k h.1, h.2⟩


/-- S1 membership for the difference layer `(A_{k+1}∧B) - (A_k∧B)`. -/
theorem sec4_coverDiff_s1_of_succ_s1_curr_s2
    (B : BSet X) (f : IntegrableRep S) (k : Nat) (x : X)
    (hU : x ∈ (sec4CoverAnd B f (k + 1)).S1)
    (hV : x ∈ (sec4CoverAnd B f k).S2) :
    x ∈ (sec4CoverDiff B f k).S1 := by
  unfold sec4CoverDiff
  change x ∈ (sec4CoverAnd B f (k + 1)).S1 ∧
      x ∈ (sec4CoverAnd B f k).S2
  exact ⟨hU, hV⟩


/-- S2 membership for the difference layer from `A_{k+1}∧B` and `A_k∧B` both positive. -/
theorem sec4_coverDiff_s2_of_succ_s1_curr_s1
    (B : BSet X) (f : IntegrableRep S) (k : Nat) (x : X)
    (hU : x ∈ (sec4CoverAnd B f (k + 1)).S1)
    (hV : x ∈ (sec4CoverAnd B f k).S1) :
    x ∈ (sec4CoverDiff B f k).S2 := by
  unfold sec4CoverDiff
  exact Or.inl (Or.inl ⟨hU, hV⟩)


/-- S2 membership for the difference layer from `A_{k+1}∧B` and `A_k∧B` both negative. -/
theorem sec4_coverDiff_s2_of_succ_s2_curr_s2
    (B : BSet X) (f : IntegrableRep S) (k : Nat) (x : X)
    (hU : x ∈ (sec4CoverAnd B f (k + 1)).S2)
    (hV : x ∈ (sec4CoverAnd B f k).S2) :
    x ∈ (sec4CoverDiff B f k).S2 := by
  unfold sec4CoverDiff
  exact Or.inl (Or.inr ⟨hU, hV⟩)


/-! ## 2. One-step characteristic identity -/

/--
Pointwise characteristic identity for one layer:
`χ_(A_k∧B) + χ_D_k = χ_(A_{k+1}∧B)`.

The proof uses only the `valid` fields of the three integrable sets, fed with
abs witnesses.
-/
theorem sec4_chiStep_coverDiff
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (k : Nat) (x : X)
    (hVDom : (sec4CoverAnd_int B hB f k).rep.MemAt x)
    (hV : RSeq.SeriesSum
      (fun m => COF.abs
        ((sec4CoverAnd_int B hB f k).rep.valueAt x hVDom m)))
    (hDDom : (sec4CoverDiff_int B hB f k).rep.MemAt x)
    (hD : RSeq.SeriesSum
      (fun m => COF.abs
        ((sec4CoverDiff_int B hB f k).rep.valueAt x hDDom m)))
    (hUDom : (sec4CoverAnd_int B hB f (k + 1)).rep.MemAt x)
    (hU : RSeq.SeriesSum
      (fun m => COF.abs
        ((sec4CoverAnd_int B hB f (k + 1)).rep.valueAt x hUDom m))) :
    (seriesSum_of_abs hV).sum + (seriesSum_of_abs hD).sum =
      (seriesSum_of_abs hU).sum := by
  have vV := (sec4CoverAnd_int B hB f k).valid x hVDom hV
  have vD := (sec4CoverDiff_int B hB f k).valid x hDDom hD
  have vU := (sec4CoverAnd_int B hB f (k + 1)).valid x hUDom hU
  cases vV.1 with
  | inl hV1 =>
      have hU1 : x ∈ (sec4CoverAnd B f (k + 1)).S1 :=
        sec4_coverAnd_s1_mono B f k x hV1
      have hD2 : x ∈ (sec4CoverDiff B f k).S2 :=
        sec4_coverDiff_s2_of_succ_s1_curr_s1 B f k x hU1 hV1
      have hv : (seriesSum_of_abs hV).sum = 1 :=
        vV.2.1 hV1 (seriesSum_of_abs hV)
      have hd : (seriesSum_of_abs hD).sum = 0 :=
        vD.2.2 hD2 (seriesSum_of_abs hD)
      have hu : (seriesSum_of_abs hU).sum = 1 :=
        vU.2.1 hU1 (seriesSum_of_abs hU)
      rw [hv, hd, hu]
      ring
  | inr hV2 =>
      cases vU.1 with
      | inl hU1 =>
          have hD1 : x ∈ (sec4CoverDiff B f k).S1 :=
            sec4_coverDiff_s1_of_succ_s1_curr_s2 B f k x hU1 hV2
          have hv : (seriesSum_of_abs hV).sum = 0 :=
            vV.2.2 hV2 (seriesSum_of_abs hV)
          have hd : (seriesSum_of_abs hD).sum = 1 :=
            vD.2.1 hD1 (seriesSum_of_abs hD)
          have hu : (seriesSum_of_abs hU).sum = 1 :=
            vU.2.1 hU1 (seriesSum_of_abs hU)
          rw [hv, hd, hu]
          ring
      | inr hU2 =>
          have hD2 : x ∈ (sec4CoverDiff B f k).S2 :=
            sec4_coverDiff_s2_of_succ_s2_curr_s2 B f k x hU2 hV2
          have hv : (seriesSum_of_abs hV).sum = 0 :=
            vV.2.2 hV2 (seriesSum_of_abs hV)
          have hd : (seriesSum_of_abs hD).sum = 0 :=
            vD.2.2 hD2 (seriesSum_of_abs hD)
          have hu : (seriesSum_of_abs hU).sum = 0 :=
            vU.2.2 hU2 (seriesSum_of_abs hU)
          rw [hv, hd, hu]
          ring


/-! ## 3. Generic successor-index finite telescope -/

/--
Generic finite telescope compatible with `RSeq.partialSum u 0 = u 0`.

If `base + term 0 = coverSucc 0` and
`coverSucc k + term (k+1) = coverSucc (k+1)`, then
`base + partialSum term n = coverSucc n`.
-/
theorem sec4_successor_telescope
    (base : R) (term coverSucc : Nat → R)
    (h0 : base + term 0 = coverSucc 0)
    (hstep : ∀ k : Nat, coverSucc k + term (k + 1) = coverSucc (k + 1)) :
    ∀ n : Nat, base + RSeq.partialSum term n = coverSucc n := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      change base + (RSeq.partialSum term n + term (n + 1)) = coverSucc (n + 1)
      calc
        base + (RSeq.partialSum term n + term (n + 1))
            = (base + RSeq.partialSum term n) + term (n + 1) := by ring
        _ = coverSucc n + term (n + 1) := by rw [ih]
        _ = coverSucc (n + 1) := hstep n


/-! ## 4. Atom data: everything except the χ-step telescope -/

/--
Atomic data sufficient for the corrected successor-index layer telescope.

Compared with `Sec4CanonicalCoverLayerTelescopeDataSucc`, this omits
`chi_telescope_s1`; it is derived below from `sec4_chiStep_coverDiff`.
-/
structure Sec4CanonicalCoverLayerAtomDataSucc
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) where
  cover_chi_dom_succ :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        (sec4CoverAnd_int B hB f (n + 1)).rep.MemAt x
  cover_chi_abs_succ :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        RSeq.SeriesSum
          (fun m => COF.abs
            ((sec4CoverAnd_int B hB f (n + 1)).rep.valueAt x
              (cover_chi_dom_succ x hgenDom hgenabs n) m))
  base_chi_dom :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        (sec4CoverAnd_int B hB f 0).rep.MemAt x
  base_chi_abs :
    ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        RSeq.SeriesSum
          (fun m => COF.abs
            ((sec4CoverAnd_int B hB f 0).rep.valueAt x
              (base_chi_dom x hgenDom hgenabs) m))
  term_chi_dom :
    ∀ k : Nat, ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        (sec4CoverDiff_int B hB f k).rep.MemAt x
  term_chi_abs :
    ∀ k : Nat, ∀ x : X,
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        RSeq.SeriesSum
          (fun m => COF.abs
            ((sec4CoverDiff_int B hB f k).rep.valueAt x
              (term_chi_dom k x hgenDom hgenabs) m))
  base_value_s2 :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        sec4_genIB_baseValue B hB f hnn x hgenDom hgenabs = 0
  row_value_s2 :
    ∀ k : Nat, ∀ x : X, x ∈ B.S2 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
        sec4_genIB_tailRowSeq B hB f hnn x hgenDom hgenabs k = 0


/--
The successor-index characteristic telescope derived from atom data.
-/
theorem sec4_chi_telescope_s1_of_atomData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerAtomDataSucc (S := S) B hB f hnn) :
    ∀ x : X, x ∈ B.S1 →
      ∀ hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs
            ((genIB_rep_from_measurable B hB f hnn).valueAt x hgenDom m)),
      ∀ n : Nat,
        (seriesSum_of_abs (T.base_chi_abs x hgenDom hgenabs)).sum +
          RSeq.partialSum
            (fun k =>
              (seriesSum_of_abs
                (T.term_chi_abs k x hgenDom hgenabs)).sum) n =
        (seriesSum_of_abs
          (T.cover_chi_abs_succ x hgenDom hgenabs n)).sum := by
  intro x hxB hgenDom hgenabs
  let base : R :=
    (seriesSum_of_abs (T.base_chi_abs x hgenDom hgenabs)).sum
  let term : Nat → R := fun k =>
    (seriesSum_of_abs (T.term_chi_abs k x hgenDom hgenabs)).sum
  let coverSucc : Nat → R := fun n =>
    (seriesSum_of_abs
      (T.cover_chi_abs_succ x hgenDom hgenabs n)).sum
  apply sec4_successor_telescope base term coverSucc
  · exact sec4_chiStep_coverDiff B hB f 0 x
      (T.base_chi_dom x hgenDom hgenabs)
      (T.base_chi_abs x hgenDom hgenabs)
      (T.term_chi_dom 0 x hgenDom hgenabs)
      (T.term_chi_abs 0 x hgenDom hgenabs)
      (T.cover_chi_dom_succ x hgenDom hgenabs 0)
      (T.cover_chi_abs_succ x hgenDom hgenabs 0)
  · intro k
    exact sec4_chiStep_coverDiff B hB f (k + 1) x
      (T.cover_chi_dom_succ x hgenDom hgenabs k)
      (T.cover_chi_abs_succ x hgenDom hgenabs k)
      (T.term_chi_dom (k + 1) x hgenDom hgenabs)
      (T.term_chi_abs (k + 1) x hgenDom hgenabs)
      (T.cover_chi_dom_succ x hgenDom hgenabs (k + 1))
      (T.cover_chi_abs_succ x hgenDom hgenabs (k + 1))


/--
Build the corrected successor-index layer data from atom data.
-/
noncomputable def sec4_succLayerData_of_atomData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerAtomDataSucc (S := S) B hB f hnn) :
    Sec4CanonicalCoverLayerTelescopeDataSucc (S := S) B hB f hnn := {
  cover_chi_dom_succ := T.cover_chi_dom_succ
  cover_chi_abs_succ := T.cover_chi_abs_succ
  base_chi_dom := T.base_chi_dom
  base_chi_abs := T.base_chi_abs
  term_chi_dom := T.term_chi_dom
  term_chi_abs := T.term_chi_abs
  chi_telescope_s1 := sec4_chi_telescope_s1_of_atomData B hB f hnn T
  base_value_s2 := T.base_value_s2
  row_value_s2 := T.row_value_s2
}


/-! ## 5. Final bridges from atom data -/

/-- Full value bridge from atom data. -/
noncomputable def sec4_genIBValueBridge_of_atomData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerAtomDataSucc (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_succLayerData B hB f hnn
    (sec4_succLayerData_of_atomData B hB f hnn T)


/-- Consistency theorem from atom data. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_atomData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerAtomDataSucc
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_succLayerData C hC f hnn
    (sec4_succLayerData_of_atomData
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from atom data. -/
noncomputable def sec4_genIBConsistencyBridge_of_atomData
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4CanonicalCoverLayerAtomDataSucc
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_succLayerData C hC f hnn
    (sec4_succLayerData_of_atomData
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
