import Mathdemo.Internal.Sec4.S2StandardOuterBridge

/-!
# Sec4 Phase2-D2b2b_beta-b2b33: theorem-4.15 abs-error S2 standard-outer frontier

`b2b31` introduced the source-shaped `A.S2` target: the standard Proposition 4.2
rows, together with the corrected outer series of the absolute row sums for
those same rows.

This file specializes that target to the theorem-4.15 abs-error sequence
`u_n = |f_n - f|`.  The resulting frontier is weaker than the older split
frontier in the source-complete file: it does not ask for a corrected outer
witness for every separately supplied row witness, only for the standard rows
chosen by the frontier itself.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Abs-error-specific standard `A.S2` frontier -/

/-- The theorem-4.15-specific `A.S2` standard-row frontier.

For each abs-error term `u_n = |f_n - f|`, this provides the standard
Proposition 4.2 rows on `A.S2` and the corrected abs-outer convergence attached
to those same rows. -/
structure Lemma415AbsErrorS2StandardOuterFrontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  rows_on_s2 : forall n,
    Sec4Prop42RowsOnS2 (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  standard_outer_on_s2 : forall n,
    Sec4LambdaRowsAbsOuterOnS2ForRows (S := S) (rows_on_s2 n)


/-! ## 2. Bridges back to the existing theorem-4.15 endpoints -/

/-- Bundle the abs-error-specific standard `A.S2` rows and corrected standard
outer convergence into the existing theorem-4.15 `A.S2` package frontier. -/
noncomputable def Lemma415AbsErrorPackOnS2Frontier.of_s2StandardOuter
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (F : Lemma415AbsErrorS2StandardOuterFrontier (S := S) fn f) :
    Lemma415AbsErrorPackOnS2Frontier (S := S) fn f where
  pack_on_s2 := fun n =>
    sec4_packOnS2_of_rowsAbsOuter
      (S := S)
      (Lemma415AbsErrorS2StandardOuterFrontier.rows_on_s2 F n)
      (Lemma415AbsErrorS2StandardOuterFrontier.standard_outer_on_s2 F n)


/-- Reassemble the remaining-atom frontier from the abs-error-specific `A.S1`
seed frontier and the source-shaped `A.S2` standard-outer frontier. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_absErrorPackS1SeedAndS2StandardOuter
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (F : Lemma415AbsErrorS2StandardOuterFrontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_absErrorPackS1SeedAndS2
    (S := S) fn f T
    (Lemma415AbsErrorPackOnS2Frontier.of_s2StandardOuter
      (S := S) fn f F)


/-- The concrete `coverSet` tail endpoint with the abs-error-specific `A.S1`
seed frontier and the source-shaped `A.S2` standard-outer frontier. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_seed_s2_standard_outer
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (F : Lemma415AbsErrorS2StandardOuterFrontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_seed_and_s2
    (S := S) fn f g g_nonneg hfn_dom hf_dom T
    (Lemma415AbsErrorPackOnS2Frontier.of_s2StandardOuter
      (S := S) fn f F)
    gSeeds hBudget hconv


end BishopC
