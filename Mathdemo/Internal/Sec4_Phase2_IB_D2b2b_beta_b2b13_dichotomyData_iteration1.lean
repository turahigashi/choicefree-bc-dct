import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b12_dataCases_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b13: construct the data-valued dichotomy package

The b2b12 kernel response confirms that the `PSum` assembly is complete and
that only two data packages remain:

* `Sec4ChiFCaseToolsData f hnn`;
* `Sec4CoverDichotomyData B hB f`.

This file constructs the second package.  In fact, it proves a more general
lemma: every `IntegrableSet1` has a choice-free data-valued S1/S2 dichotomy at
points where its characteristic representative has an absolute convergence
witness.

The construction does not eliminate `valid.1 : S1 ∨ S2` into data.  It first
uses the data-valued cotransitivity

```
COF.lt_cotrans_data COFO.half_pos χ(x)
```

to choose a Type-level branch, and then uses `valid` only inside a Prop goal
to prove the corresponding membership.  This is exactly the `propRecLargeElim`
avoidance pattern from b2b12.
-/

#check Sec4ChiFCaseToolsData
#check Sec4CoverDichotomyData
#check Sec4IntegrableSetDichotomy
#check sec4_prop42FinalTools_of_dataCases
#check sec4_genIBValueBridge_of_dataCases
#check sec4_genRelIntegral_eq_relIntegral_of_dataCases
#check sec4_genIBConsistencyBridge_of_dataCases
#check COF.lt_cotrans_data
#check COFO.half_pos
#check COF.half_add_half

/-! ## 1. Numeric split helpers -/

/-- `1/2 < 1`, in the abstract constructive ordered field. -/
theorem sec4_half_lt_one : COF.lt COF.half (1 : R) := by
  -- Technical note.
  -- Technical note.
  have h : COF.lt (COF.half + (0 : R)) (COF.half + COF.half) :=
    COF.lt_add_left COF.half COFO.half_pos
  rw [add_zero, COF.half_add_half] at h
  exact h


/--
If a characteristic value is positive, it cannot be the zero branch.
-/
theorem sec4_valid_s1_of_half_lt_value
    (A : BSet X) (hA : IntegrableSet1 S A) (x : X)
    (hχDom : hA.rep.MemAt x)
    (hχabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hχDom m)))
    (hpos : COF.lt 0 (seriesSum_of_abs hχabs).sum) :
    x ∈ A.S1 := by
  -- Technical note.
  -- Technical note.
  let hχ := seriesSum_of_abs hχabs
  have hvalid := hA.valid x hχDom hχabs
  cases hvalid.1 with
  | inl h1 =>
      exact h1
  | inr h2 =>
      have hzero : hχ.sum = 0 :=
        hvalid.2.2 h2 hχ
      have hpos0 : COF.lt (0 : R) (0 : R) := by
        simpa [hχ] using hzero ▸ hpos
      exact False.elim ((COF.lt_irrefl (0 : R)) hpos0)


/--
If a characteristic value is smaller than `1/2`, it cannot be the one branch.
-/
theorem sec4_valid_s2_of_value_lt_half
    (A : BSet X) (hA : IntegrableSet1 S A) (x : X)
    (hχDom : hA.rep.MemAt x)
    (hχabs : RSeq.SeriesSum
      (fun m => COF.abs (hA.rep.valueAt x hχDom m)))
    (hlt : COF.lt (seriesSum_of_abs hχabs).sum COF.half) :
    x ∈ A.S2 := by
  let hχ := seriesSum_of_abs hχabs
  have hvalid := hA.valid x hχDom hχabs
  cases hvalid.1 with
  | inl h1 =>
      have hone : hχ.sum = 1 :=
        hvalid.2.1 h1 hχ
      have hone_half : COF.lt (1 : R) COF.half := by
        simpa [hχ] using hone ▸ hlt
      exact False.elim
        ((COF.lt_irrefl (1 : R))
          (COFO.lt_trans hone_half (sec4_half_lt_one (R := R))))
  | inr h2 =>
      exact h2


/-! ## 2. A generic data-valued dichotomy for `IntegrableSet1` -/

/--
Choice-free data-valued S1/S2 dichotomy for every integrable complemented set.

The only data split is `COF.lt_cotrans_data COFO.half_pos χ(x)`.
The use of `hA.valid` occurs only in Prop-valued subgoals, so it does not
trigger large elimination.
-/
noncomputable def sec4_integrableSetDichotomy_from_valid
    (A : BSet X) (hA : IntegrableSet1 S A) :
    Sec4IntegrableSetDichotomy (S := S) A hA := by
  intro x hχAt
  let hχDom := hχAt.fst
  let hχabs := hχAt.snd
  let hχ := seriesSum_of_abs hχabs
  cases COF.lt_cotrans_data COFO.half_pos hχ.sum with
  | inl hhalf =>
      exact PSum.inl
        (sec4_valid_s1_of_half_lt_value A hA x hχDom hχabs hhalf)
  | inr hlt =>
      exact PSum.inr
        (sec4_valid_s2_of_value_lt_half A hA x hχDom hχabs hlt)


/--
The remaining cover/difference data-valued dichotomy package.

This is the full `Sec4CoverDichotomyData` requested by b2b12.
It is generic in `B`: no decidability of membership in `B` is used.
-/
noncomputable def sec4_coverDichotomyData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) :
    Sec4CoverDichotomyData (S := S) B hB f :=
  Sec4CoverDichotomyData.mk
    (coverAnd_case := fun k =>
      sec4_integrableSetDichotomy_from_valid
        (sec4CoverAnd B f k)
        (sec4CoverAnd_int B hB f k))
    (coverDiff_case := fun k =>
      sec4_integrableSetDichotomy_from_valid
        (sec4CoverDiff B f k)
        (sec4CoverDiff_int B hB f k))


/-! ## 3. Final bridge assuming only the internal `χ_A·f` case tools -/

/--
The final-tools package from the internal `χ_A·f` case tools alone.

The cover/difference dichotomy package is now constructed unconditionally by
`sec4_coverDichotomyData`.
-/
noncomputable def sec4_prop42FinalTools_of_chiFCaseTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  sec4_prop42FinalTools_of_dataCases B hB f hnn T
    (sec4_coverDichotomyData B hB f)


/-- Full value bridge from the internal `χ_A·f` case tools alone. -/
noncomputable def sec4_genIBValueBridge_of_chiFCaseTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_dataCases B hB f hnn T
    (sec4_coverDichotomyData B hB f)


/--
Consistency theorem from the internal `χ_A·f` case tools alone.
-/
theorem sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_dataCases C hC f hnn T
    (sec4_coverDichotomyData C (isMeasurableSet_of_integrable hC) f)


/--
Packaged consistency bridge from the internal `χ_A·f` case tools alone.
-/
noncomputable def sec4_genIBConsistencyBridge_of_chiFCaseTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseToolsData (S := S) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_dataCases C hC f hnn T
    (sec4_coverDichotomyData C (isMeasurableSet_of_integrable hC) f)


end BishopC
