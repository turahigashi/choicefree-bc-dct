import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b33_s2StandardOuterAbsErrorFrontier_iteration1

/-!
# Sec4 Phase2-D2b2b_beta-b2b34: chapter-4 source completion bridge

The printed chapter 4 proceeds in one line after Definition 4.8:
if `B` is measurable and `f` is integrable, then the formal relative integral
`I_B(f)` is represented by the characteristic-function construction, and for
already integrable sets it agrees with the previous `I_A(f)`.

The existing files already contain the representative construction
`genIB_rep_from_measurable` and the theorem-4.15 dominated convergence endpoint.
This file ties the two sides together through the current source-shaped
Proposition 4.2 residual:

* standard rows on `A.S1` and `A.S2`;
* corrected outer convergence of the absolute row sums for those same rows.

No new analytic claim is introduced here.  The only frontier is the shared
`Sec4GeneralIBSourceS2StandardOuterProvider`, which is the chapter-4 residual
left by the formalization.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Chapter-4 `I_B` value and consistency entries -/

/-- Source-shaped value bridge for the direct general measurable `I_B`.

This is the chapter-4 name for the existing bridge supplied by the refined
standard-row outer provider. -/
noncomputable def sec4_chapter4_genIBValueBridge_of_sourceS2StandardOuterProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_sourceS2StandardOuterProvider
    (S := S) P B hB f hnn


/-- On an already integrable set, the general measurable `I_C` agrees with the
older relative integral `I_C`. -/
theorem sec4_chapter4_genRelIntegral_eq_relIntegral_of_sourceS2StandardOuterProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_sourceS2StandardOuterProvider
    (S := S) P C hC f hnn


/-- Packaged consistency bridge for the already integrable-set specialization
of the general measurable `I_B`. -/
noncomputable def sec4_chapter4_genIBConsistencyBridge_of_sourceS2StandardOuterProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_sourceS2StandardOuterProvider
    (S := S) P C hC f hnn


/-! ## 2. Theorem-4.15 abs-error frontier derived from the same provider -/

/-- The general measurable-`I_B` source provider supplies the theorem-4.15
abs-error `A.S2` standard rows and corrected standard-row outer convergence. -/
noncomputable def Lemma415AbsErrorS2StandardOuterFrontier.of_generalIBSourceS2StandardOuterProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S)) :
    Lemma415AbsErrorS2StandardOuterFrontier (S := S) fn f where
  rows_on_s2 := fun n =>
    P.rows_on_s2
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  standard_outer_on_s2 := fun n =>
    P.standard_outer_on_s2
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-! ## 3. Theorem 4.15 through the chapter-4 provider -/

/-- Dominated convergence from the theorem-specific `A.S1` seed frontier and
the chapter-4 source-shaped general measurable-`I_B` provider.

This endpoint makes explicit that the `A.S2` part of theorem 4.15 is not a
separate theorem-specific assumption once the chapter-4 provider is available. -/
noncomputable def thm_4_15_source_tail_budget_abs_error_s1_seed_chapter4_provider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_seed_s2_standard_outer
    (S := S) fn f g g_nonneg hfn_dom hf_dom T
    (Lemma415AbsErrorS2StandardOuterFrontier.of_generalIBSourceS2StandardOuterProvider
      (S := S) fn f P)
    gSeeds hBudget hconv


/-- Default-budget version of the preceding chapter-4 provider endpoint. -/
noncomputable def thm_4_15_source_default_budget_abs_error_s1_seed_chapter4_provider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_tail_budget_abs_error_s1_seed_chapter4_provider
    (S := S) fn f g g_nonneg hfn_dom hf_dom T P gSeeds
    (fun eps heps => lemma_4_15_default_tail_budget (R := R) eps heps)
    hconv


end BishopC
