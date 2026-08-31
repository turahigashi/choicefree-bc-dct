import Mathdemo.Internal.Sec4.Row1Switch

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b10: reduce the last primitive to a one-step finite cover assembly

The b2b9 kernel response confirms that `n0_pos` is gone and that the only
remaining primitive is

`Sec4CoverChiFAbsSucc B hB f hnn`.

The response also explains that this primitive is not available as an existing
point-abs lemma for `prop_4_2_chi_f_rep (coverAnd (n+1))`.  This file takes
the most local remaining step: it reduces that last primitive to a single
one-step finite-cover assembly lemma.

The one-step assembly says:

if the point belongs to the domains of
  * `χ_(A_k∧B) · f`, and
  * `χ_((A_{k+1}∧B)\(A_k∧B)) · f`,

then it belongs to the domain of
  * `χ_(A_{k+1}∧B) · f`.

Base and layer point-abs witnesses are supplied by already verified D2a data:
`sec4_genIB_baseAbs_of_abs` and `(sec4_genIB_tailPointBridge ...).rowAbs`.

Thus, after this file, the final unresolved object is a single local
`Sec4CoverChiFStepAbs` construction.
-/

#check Sec4Prop42FinalTools
#check Sec4CoverChiFAbsSucc
#check sec4_genIBValueBridge_of_finalTools
#check sec4_genRelIntegral_eq_relIntegral_of_finalTools
#check sec4_genIBConsistencyBridge_of_finalTools
#check sec4_genIB_baseAbs_of_abs
#check sec4_genIB_tailPointBridge
#check sec4CoverAnd
#check sec4CoverAnd_int
#check sec4CoverDiff
#check sec4CoverDiff_int
#check prop_4_2_chi_f_rep

/-! ## 1. Base and layer abs witnesses already contained in `genIB` -/

/--
The base component of `genIB` is definitionally the `χ_(A₀∧B)·f`
representative.
-/
noncomputable def sec4_coverChiFBaseAbs_from_genIB
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun m => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt
          x hgenDom m))) :
    Sec4RepAbsAt
      (prop_4_2_chi_f_rep
        (sec4CoverAnd B f 0)
        (sec4CoverAnd_int B hB f 0)
        f hnn) x :=
  ⟨sec4_genIB_baseMemAt B hB f hnn hgenDom,
    sec4_genIB_baseAbs_of_abs B hB f hnn x hgenDom hgenabs⟩


/--
The `k`-th tail row of `genIB` is definitionally the
`χ_((A_{k+1}∧B)\(A_k∧B))·f` representative.
-/
noncomputable def sec4_coverChiFTermAbs_from_genIB
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (k : Nat) (x : X)
    (hgenDom : (genIB_rep_from_measurable B hB f hnn).MemAt x)
    (hgenabs : RSeq.SeriesSum
      (fun m => COF.abs
        ((genIB_rep_from_measurable B hB f hnn).valueAt
          x hgenDom m))) :
    Sec4RepAbsAt
      (prop_4_2_chi_f_rep
        (sec4CoverDiff B f k)
        (sec4CoverDiff_int B hB f k)
        f hnn) x :=
  let PB := sec4_genIB_tailPointBridge B hB f hnn x hgenDom hgenabs
  ⟨PB.rowDom k, PB.rowAbs k⟩


/-! ## 2. The single remaining local assembly lemma -/

/--
One-step finite-cover domain assembly.

This is the precise local form of the final `cover_chiF_abs_succ` problem:
from the current finite cover and the next difference layer, assemble the
successor finite cover.

Mathematically this is the point-abs/domain version of
`χ_(A_{k+1}∧B)·f = χ_(A_k∧B)·f + χ_Dk·f`.
-/
def Sec4CoverChiFStepAbs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ k : Nat, ∀ x : X,
    Sec4RepAbsAt
      (prop_4_2_chi_f_rep
        (sec4CoverAnd B f k)
        (sec4CoverAnd_int B hB f k)
        f hnn) x →
    Sec4RepAbsAt
      (prop_4_2_chi_f_rep
        (sec4CoverDiff B f k)
        (sec4CoverDiff_int B hB f k)
        f hnn) x →
    Sec4RepAbsAt
      (prop_4_2_chi_f_rep
        (sec4CoverAnd B f (k + 1))
        (sec4CoverAnd_int B hB f (k + 1))
        f hnn) x


/-! ## 3. Iterating the one-step assembly gives the final primitive -/

/--
The final primitive `Sec4CoverChiFAbsSucc`, assuming the one-step finite cover
assembly.
-/
noncomputable def sec4_coverChiFAbsSucc_of_stepAbs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Step : Sec4CoverChiFStepAbs (S := S) B hB f hnn) :
    Sec4CoverChiFAbsSucc (S := S) B hB f hnn := by
  intro x hgenDom hgenabs n
  induction n with
  | zero =>
      exact Step 0 x
        (sec4_coverChiFBaseAbs_from_genIB
          B hB f hnn x hgenDom hgenabs)
        (sec4_coverChiFTermAbs_from_genIB
          B hB f hnn 0 x hgenDom hgenabs)
  | succ n ih =>
      exact Step (n + 1) x ih
        (sec4_coverChiFTermAbs_from_genIB
          B hB f hnn (n + 1) x hgenDom hgenabs)


/-! ## 4. Final bridges from the one-step assembly -/

/-- The b2b9 final-tools package from the one-step finite-cover assembly. -/
noncomputable def sec4_prop42FinalTools_of_stepAbs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Step : Sec4CoverChiFStepAbs (S := S) B hB f hnn) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  Sec4Prop42FinalTools.mk
    (cover_chiF_abs_succ :=
      sec4_coverChiFAbsSucc_of_stepAbs B hB f hnn Step)


/-- Full value bridge from the one-step finite-cover assembly. -/
noncomputable def sec4_genIBValueBridge_of_stepAbs
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Step : Sec4CoverChiFStepAbs (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_finalTools B hB f hnn
    (sec4_prop42FinalTools_of_stepAbs B hB f hnn Step)


/-- Consistency theorem from the one-step finite-cover assembly. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_stepAbs
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Step : Sec4CoverChiFStepAbs
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_finalTools C hC f hnn
    (sec4_prop42FinalTools_of_stepAbs
      C (isMeasurableSet_of_integrable hC) f hnn Step)


/-- Packaged consistency bridge from the one-step finite-cover assembly. -/
noncomputable def sec4_genIBConsistencyBridge_of_stepAbs
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Step : Sec4CoverChiFStepAbs
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_finalTools C hC f hnn
    (sec4_prop42FinalTools_of_stepAbs
      C (isMeasurableSet_of_integrable hC) f hnn Step)


end BishopC
