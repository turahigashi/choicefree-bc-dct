import Mathdemo.Internal.Sec4.DominatedConvergence415SourceComplete

/-!
# Sec4 Phase2-D2b2b_beta-b2b32: bridges into the S2 standard-outer provider

`b2b31` exposed the source-shaped negative-side residual:

* the standard Proposition 4.2 rows on `A.S2`;
* the corrected outer series of the absolute row sums for those same rows.

This file adds only compatibility bridges.  It does not claim to prove the
printed Proposition 4.2 `A.S2` construction from first principles.  Instead it
shows how the new `b2b31` provider is obtained from older, stronger interfaces:
the bundled corrected `pack_on_s2` package, or the generic `Rows + Outer` tools
already present in the theorem-4.15 source-complete layer.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Split an existing corrected `A.S2` package -/

/-- Extract the row component of an existing corrected `A.S2` package. -/
noncomputable def sec4_rowsOnS2_of_packOnS2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Pack : Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn) :
    Sec4Prop42RowsOnS2 (S := S) f hnn := by
  intro A hA x hxA
  exact Sec4LambdaRowsAbsPackAt.rows (Pack A hA x hxA)


/-- Extract the corrected abs-outer component of an existing `A.S2` package,
attached to the row component extracted above. -/
noncomputable def sec4_absOuterOnS2ForRows_of_packOnS2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Pack : Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn) :
    Sec4LambdaRowsAbsOuterOnS2ForRows (S := S)
      (sec4_rowsOnS2_of_packOnS2 (S := S) Pack) := by
  intro A hA x hxA
  simpa [sec4_rowsOnS2_of_packOnS2] using
    (Sec4LambdaRowsAbsPackAt.outer (Pack A hA x hxA))


/-- The stronger generic `A.S2` outer tool implies the source-shaped
standard-row outer frontier used by `b2b31`. -/
noncomputable def sec4_absOuterOnS2ForRows_of_prop42AbsOuterOnS2OfRows
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Rows : Sec4Prop42RowsOnS2 (S := S) f hnn)
    (Outer : Sec4Prop42AbsOuterOnS2OfRows (S := S) f hnn) :
    Sec4LambdaRowsAbsOuterOnS2ForRows (S := S) Rows := by
  intro A hA x hxA
  exact Outer A hA x hxA (Rows A hA x hxA)


/-! ## 2. Provider-level bridges -/

namespace Sec4GeneralIBSourceS2StandardOuterProvider

/-- Backward-compatibility bridge from the bundled source abs-pack provider.

This is not the preferred source frontier, but it confirms that `b2b31` is a
true refinement of the previous `b2b29` interface. -/
noncomputable def ofSourceAbsPackProvider
    (P : Sec4GeneralIBSourceAbsPackProvider (S := S)) :
    Sec4GeneralIBSourceS2StandardOuterProvider (S := S) where
  rowToFlat := P.rowToFlat
  charDomain := P.charDomain
  standard_outer_on_s1 := P.standard_outer_on_s1
  rows_on_s2 := fun f hnn =>
    sec4_rowsOnS2_of_packOnS2 (S := S) (P.pack_on_s2 f hnn)
  standard_outer_on_s2 := fun f hnn =>
    sec4_absOuterOnS2ForRows_of_packOnS2 (S := S) (P.pack_on_s2 f hnn)


/-- Build the `b2b31` source-shaped provider from generic `A.S2` rows and the
older generic corrected `A.S2` abs-outer tool. -/
noncomputable def ofGenericS2Tools
    (rowToFlat : Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S))
    (charDomain : Sec4Prop42CharacteristicDomainWitness (S := S))
    (standard_outer_on_s1 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
      Sec4Prop42StandardAbsOuterOnS1OfFAbs (S := S) charDomain f hnn)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415Prop42AbsOuterOnS2Tool (S := S)) :
    Sec4GeneralIBSourceS2StandardOuterProvider (S := S) where
  rowToFlat := rowToFlat
  charDomain := charDomain
  standard_outer_on_s1 := standard_outer_on_s1
  rows_on_s2 := Rows.rows_on_s2
  standard_outer_on_s2 := fun f hnn =>
    sec4_absOuterOnS2ForRows_of_prop42AbsOuterOnS2OfRows
      (S := S)
      (Rows.rows_on_s2 f hnn)
      (Outer.abs_outer_on_s2_of_rows f hnn)


end Sec4GeneralIBSourceS2StandardOuterProvider

/-! ## 3. Theorem 4.15 endpoint through the generic S2 tools -/

/-- The concrete `coverSet` tail endpoint using the `b2b31` provider assembled
from generic `A.S2` rows plus the older generic corrected `A.S2` outer tool. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_genericS2ToolsProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (rowToFlat : Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S))
    (charDomain : Sec4Prop42CharacteristicDomainWitness (S := S))
    (standard_outer_on_s1 : forall (u : IntegrableRep S) (unn : RepNonneg u),
      Sec4Prop42StandardAbsOuterOnS1OfFAbs (S := S) charDomain u unn)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415Prop42AbsOuterOnS2Tool (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_generalIBSourceS2StandardOuterProvider
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Sec4GeneralIBSourceS2StandardOuterProvider.ofGenericS2Tools
      (S := S) rowToFlat charDomain standard_outer_on_s1 Rows Outer)
    gSeeds hBudget hconv


end BishopC
