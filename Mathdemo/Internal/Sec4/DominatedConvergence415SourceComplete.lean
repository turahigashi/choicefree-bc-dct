import Mathdemo.Internal.Sec4.DominatedConvergence415FaithfulSplit
import Mathdemo.Internal.Sec4.DominatedConvergence415
import Mathdemo.Internal.Sec4.RowSeedProvider
import Mathdemo.Internal.Sec4.RowSeedResidual
import Mathdemo.Internal.Sec4.SourceDomainWitness
import Mathdemo.Internal.Sec4.SourceAbsPackProvider
import Mathdemo.Internal.Sec4.S2AbsZeroProvider
import Mathdemo.Internal.Sec4.S2StandardOuterProvider
import Mathdemo.Internal.Sec4.Preservation
import Mathdemo.Internal.Sec4GenIB

/-!
# Bishop--Cheng §4, theorem 4.15: source route through lemma 4.14

The source proof of theorem 4.15 proceeds in this order:

1. reduce the theorem to `I(|f_n - f|) -> 0`;
2. choose the set `A` and the small-measure threshold `δ` as in theorem 4.13;
3. prove the displayed split estimate for `I_B(|f_n - f|)`;
4. apply lemma 4.14 to `u_n = |f_n - f|`;
5. return from the error estimate to `I(f_n) -> I(f)`.

The split estimate is proved in
`DominatedConvergence415FaithfulSplit`.
This file closes steps 4 and 5 against the source-complete lemma-4.14 entry
point.  The quantitative domination-to-uniform-`I_B` construction in steps
2--3 is deliberately kept as source-shaped data rather than hidden in a
wrapper: it is exactly the remaining theorem-4.15 frontier if one wants to
derive the data from only `|f_n| <= g` and `f_n -> f` in measure.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Source-level data needed after the first line of the source proof has
formed the nonnegative error sequence `u_n = |f_n - f|`.

The fields match the hypotheses of the source-complete lemma 4.14, specialized
to `u_n`.  In the printed proof these fields are supplied by:

* convergence in measure of `f_n` to `f`, giving `u_n -> 0` in measure;
* the displayed domination/splitting argument with `g`, giving uniform `I_B`;
* the existing row-seed bridge for the general measurable relative integral.

This is not a PFunR compatibility wrapper. -/
structure Lemma415AbsErrorSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  rowSeeds : forall n,
    Sec4Prop42RowSeedTools (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  uniform : forall eps, COF.lt 0 eps ->
    Lemma414UniformIBSourceData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (thm_4_15_abs_error_ib_from_rowSeeds (S := S) fn f rowSeeds)
      eps
  converge :
    Lemma414ConvergeInMeasureToZeroData (S := S)
      (thm_4_15_abs_error (S := S) fn f)


/-- Source-level abs-error data using the lower `remainingAtoms` interface
instead of `Sec4Prop42RowSeedTools`.

This is a strictly lower 4.14 entry point: `remainingAtoms` is the exact
three-atom package consumed by the completed general-measurable `I_B`
construction. -/
structure Lemma415AbsErrorAtomSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  atoms : forall n,
    Sec4Prop42RemainingAtomTools (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  uniform : forall eps, COF.lt 0 eps ->
    Lemma414UniformIBSourceData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (lemma_4_14_ib_interface_from_genIB_remainingAtoms
        (S := S)
        (thm_4_15_abs_error (S := S) fn f)
        (thm_4_15_abs_error_nonneg (S := S) fn f)
        atoms)
      eps
  converge :
    Lemma414ConvergeInMeasureToZeroData (S := S)
      (thm_4_15_abs_error (S := S) fn f)


/-- The exact Prop. 4.2 atom frontier for theorem 4.15's error sequence.

For `u_n = |f_n - f|`, the completed general-measurable `I_B` construction
needs precisely these three internal Prop. 4.2 witnesses.  Keeping them
separate records the remaining source obligation without collapsing it into a
single bundled assumption. -/
structure Lemma415AbsErrorRemainingAtomFrontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  fabs_of_rows_s1 : forall n,
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  pack_on_s1_of_fabs : forall n,
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  pack_on_s2 : forall n,
    Sec4LambdaRowsAbsPackOnS2 (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Reassemble the three named theorem-4.15 atom frontiers into the lower
`Sec4Prop42RemainingAtomTools` interface consumed by lemma 4.14. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.toAtoms
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (F : Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f) :
    forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n =>
    Sec4Prop42RemainingAtomTools.mk
      (S := S)
      (F.fabs_of_rows_s1 n)
      (F.pack_on_s1_of_fabs n)
      (F.pack_on_s2 n)


/-- Step 2b-i frontier for theorem 4.15: reconstruct absolute convergence of
`u_n = |f_n - f|` from the Proposition 4.2 lambda-row witnesses on `A.S1`. -/
structure Lemma415AbsErrorFAbsRowsS1Frontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  fabs_of_rows_s1 : forall n,
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Generic Proposition 4.2 obligation behind Step 2b-i.

It says that, for every nonnegative integrable representative `u`, the
absolute convergence of the Proposition 4.2 lambda rows on `A.S1` reconstructs
the absolute convergence of `u` itself there.  The theorem-4.15 specialization
is then just `u = |f_n - f|`. -/
structure Lemma415Prop42FAbsRowsS1Tool : Type _ where
  fabs_of_rows_s1 : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) u unn


/-- Step 2b-i, closed from the row-0 right component.

For row 0,
`prop_4_2_lambda_k A hA u (prop_4_2_n_k u) 0` is a `min2` whose right
component is `u.sub (prop_4_2_min_f_n u 0)`.  Absolute convergence of the row
therefore gives absolute convergence of that right component, and the left
interleaved half of the subtraction is exactly the original representative
`u`. -/
noncomputable def sec4_fabsOfLambdaAbsRowsOnS1_of_row0Right
    (u : IntegrableRep S) (unn : RepNonneg u) :
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) u unn := by
  intro A hA x _hxA hrows
  let hrow0 : Sec4RepAbsAt
      (prop_4_2_lambda_k A hA u (prop_4_2_n_k u) 0) x := hrows 0
  dsimp [prop_4_2_lambda_k] at hrow0
  let hrightDom := min2_dom_right hrow0.fst
  have hright :
      RSeq.SeriesSum
        (fun m => COF.abs
          ((u.sub (prop_4_2_min_f_n u 0)).valueAt x hrightDom m)) :=
    min2_absSeriesSum_right hrow0.fst hrow0.snd
  exact ⟨add_dom_left hrightDom, add_absSeriesSum_left hrightDom hright⟩


/-- The generic Proposition 4.2 Step 2b-i tool, now discharged. -/
noncomputable def Lemma415Prop42FAbsRowsS1Tool.of_row0Right :
    Lemma415Prop42FAbsRowsS1Tool (S := S) where
  fabs_of_rows_s1 := sec4_fabsOfLambdaAbsRowsOnS1_of_row0Right


/-- Generic row-seed provider for Proposition 4.2.

This is stronger than Step 2b-i: row seeds contain the row-to-function
absolute-convergence atom as their first component, together with the two
abs-outer package ingredients used later. -/
structure Lemma415Prop42RowSeedToolsProvider : Type _ where
  rowSeeds : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4Prop42RowSeedTools (S := S) u unn


/-- Specialize the general measurable-`I_B` row-seed provider to the theorem
4.15 source route. -/
noncomputable def Lemma415Prop42RowSeedToolsProvider.of_generalIBProvider
    (P : Sec4GeneralIBRowSeedToolsProvider (S := S)) :
    Lemma415Prop42RowSeedToolsProvider (S := S) where
  rowSeeds := P.rowSeeds


/-- Specialize the narrowed general measurable-`I_B` row-seed provider to the
theorem 4.15 source route.  The row-to-function field is supplied by the
generic row-0-right construction, so only the residual three fields remain. -/
noncomputable def Lemma415Prop42RowSeedToolsProvider.of_generalIBResidualProvider
    (P : Sec4GeneralIBRowSeedResidualProvider (S := S)) :
    Lemma415Prop42RowSeedToolsProvider (S := S) where
  rowSeeds := fun u unn =>
    sec4_rowSeedTools_of_residualTools u unn (P.residual u unn)


/-- Specialize the source-faithful domain-residual provider to the theorem
4.15 source route.  The characteristic-domain witness supplies the `χ_A`
absolute-convergence residual field; the abs-outer and `A.S2` package fields
remain explicit. -/
noncomputable def Lemma415Prop42RowSeedToolsProvider.of_generalIBDomainResidualProvider
    (P : Sec4GeneralIBDomainResidualProvider (S := S)) :
    Lemma415Prop42RowSeedToolsProvider (S := S) :=
  Lemma415Prop42RowSeedToolsProvider.of_generalIBResidualProvider
    (S := S)
    (Sec4GeneralIBDomainResidualProvider.toResidualProvider P)


/-- Generic provider for the corrected Proposition 4.2 abs-pack tools.

This mirrors `Sec4ChiFCaseAbsPackTools`: row-to-flat, row-to-function on
`A.S1`, the corrected `A.S1` package, and the corrected bundled `A.S2`
package are kept together for each nonnegative representative. -/
structure Lemma415Prop42AbsPackToolsProvider : Type _ where
  absPackTools : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4ChiFCaseAbsPackTools (S := S) u unn


/-- Specialize the source-shaped general measurable-`I_B` abs-pack provider
to theorem 4.15's generic Proposition 4.2 abs-pack provider interface.

This route avoids the older arbitrary-row `A.S1` abs-outer residual: the
provider already supplies the corrected package for the standard Proposition
4.2 rows. -/
noncomputable def Lemma415Prop42AbsPackToolsProvider.of_generalIBSourceAbsPackProvider
    (P : Sec4GeneralIBSourceAbsPackProvider (S := S)) :
    Lemma415Prop42AbsPackToolsProvider (S := S) where
  absPackTools := fun u unn =>
    Sec4GeneralIBSourceAbsPackProvider.absPackTools (S := S) P u unn


/-- Specialize the refined source-shaped general measurable-`I_B` provider,
where the corrected `A.S2` package is split into standard rows plus corrected
absolute row-zero, to theorem 4.15's generic Proposition 4.2 abs-pack provider
interface. -/
noncomputable def Lemma415Prop42AbsPackToolsProvider.of_generalIBSourceS2AbsZeroProvider
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S)) :
    Lemma415Prop42AbsPackToolsProvider (S := S) where
  absPackTools := fun u unn =>
    Sec4GeneralIBSourceS2AbsZeroProvider.absPackTools (S := S) P u unn


/-- Specialize the refined source-shaped general measurable-`I_B` provider,
where both `A.S1` and `A.S2` corrected abs-outer obligations are attached to
the standard Proposition 4.2 rows, to theorem 4.15's generic Proposition 4.2
abs-pack provider interface. -/
noncomputable def Lemma415Prop42AbsPackToolsProvider.of_generalIBSourceS2StandardOuterProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S)) :
    Lemma415Prop42AbsPackToolsProvider (S := S) where
  absPackTools := fun u unn =>
    Sec4GeneralIBSourceS2StandardOuterProvider.absPackTools (S := S) P u unn


/-- The theorem-4.15-specific corrected abs-pack frontier for the error
sequence `u_n = |f_n - f|`.

This is weaker than `Lemma415Prop42AbsPackToolsProvider`: it asks for the
corrected Proposition 4.2 abs-pack tools only for the abs-error sequence. -/
structure Lemma415AbsErrorAbsPackToolsFrontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  absPackTools : forall n,
    Sec4ChiFCaseAbsPackTools (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Specialize a generic corrected abs-pack provider to the theorem-4.15
abs-error sequence. -/
noncomputable def Lemma415AbsErrorAbsPackToolsFrontier.of_provider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (P : Lemma415Prop42AbsPackToolsProvider (S := S)) :
    Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f where
  absPackTools := fun n =>
    P.absPackTools
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Extract the Step 2b-i generic tool from a generic Proposition 4.2 row-seed
provider. -/
noncomputable def Lemma415Prop42FAbsRowsS1Tool.of_rowSeedToolsProvider
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415Prop42FAbsRowsS1Tool (S := S) where
  fabs_of_rows_s1 := fun u unn =>
    Sec4Prop42RowSeedTools.fabs_of_rows_s1 (P.rowSeeds u unn)


/-- Extract the Step 2b-i generic tool from the corrected abs-pack tools. -/
noncomputable def Lemma415Prop42FAbsRowsS1Tool.of_absPackToolsProvider
    (P : Lemma415Prop42AbsPackToolsProvider (S := S)) :
    Lemma415Prop42FAbsRowsS1Tool (S := S) where
  fabs_of_rows_s1 := fun u unn =>
    Sec4ChiFCaseAbsPackTools.fabs_of_rows_s1 (P.absPackTools u unn)


/-- Specialize the generic Proposition 4.2 Step 2b-i tool to the theorem-4.15
error sequence `u_n = |f_n - f|`. -/
noncomputable def Lemma415AbsErrorFAbsRowsS1Frontier.of_prop42Tool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42FAbsRowsS1Tool (S := S)) :
    Lemma415AbsErrorFAbsRowsS1Frontier (S := S) fn f where
  fabs_of_rows_s1 := fun n =>
    T.fabs_of_rows_s1
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Extract theorem-4.15 Step 2b-i from row seeds for the abs-error sequence. -/
noncomputable def Lemma415AbsErrorFAbsRowsS1Frontier.of_rowSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)) :
    Lemma415AbsErrorFAbsRowsS1Frontier (S := S) fn f where
  fabs_of_rows_s1 := fun n =>
    Sec4Prop42RowSeedTools.fabs_of_rows_s1 (hSeeds n)


/-- Extract theorem-4.15 Step 2b-i from corrected abs-pack tools for the
abs-error sequence. -/
noncomputable def Lemma415AbsErrorFAbsRowsS1Frontier.of_absPackTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f) :
    Lemma415AbsErrorFAbsRowsS1Frontier (S := S) fn f where
  fabs_of_rows_s1 := fun n =>
    Sec4ChiFCaseAbsPackTools.fabs_of_rows_s1
      (Lemma415AbsErrorAbsPackToolsFrontier.absPackTools T n)


/-- Step 2b-ii frontier for theorem 4.15: on `A.S1`, build the corrected
abs-outer lambda-row package from an absolute-convergence witness for
`u_n = |f_n - f|`. -/
structure Lemma415AbsErrorPackOnS1Frontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  pack_on_s1_of_fabs : forall n,
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Local seeds for theorem-4.15 Step 2b-ii on `A.S1`.

This keeps the Bishop-Cheng route explicit: the absolute convergence of the
characteristic representative `χ_A` is a separate local datum, and only after
that datum is available do we assemble the lambda-row package. -/
structure Lemma415Prop42PackOnS1SeedTools : Type _ where
  chi_abs_on_s1_of_fabs : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4Prop42ChiAbsOnS1OfFAbs (S := S) u unn
  abs_outer_on_s1_of_rows : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4Prop42AbsOuterOnS1OfRows (S := S) u unn


/-- Generic source-shaped tool for constructing flat absolute convergence of
`χ_A * u` on `A.S1` from absolute convergence of `u`. -/
structure Lemma415Prop42ChiFAbsOnS1Tool : Type _ where
  chiF_abs_on_s1_of_fabs : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4ChiFAbsOnS1Data (S := S) u unn


/-- Generic corrected `A.S1` abs-outer tool. -/
structure Lemma415Prop42AbsOuterOnS1Tool : Type _ where
  abs_outer_on_s1_of_rows : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4Prop42AbsOuterOnS1OfRows (S := S) u unn


/-- Generic corrected `A.S1` package tool.

This is the package-shaped counterpart of the two seed tools above: it keeps
the row witnesses and their corrected abs-outer witness bundled. -/
structure Lemma415Prop42PackOnS1Tool : Type _ where
  pack_on_s1_of_fabs : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) u unn


/-- Generic row-to-flat tool for corrected absolute row packages. -/
structure Lemma415Prop42RowToFlatTool : Type _ where
  rowToFlat : Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S)


/-- Build the corrected Proposition 4.2 abs-pack provider from a global
row-to-flat bridge and the row-seed provider.

The row seeds supply `A.S1` row-to-function, the `A.S1` corrected package, and
the bundled `A.S2` package; the extra row-to-flat bridge supplies the first
component required by `Sec4ChiFCaseAbsPackTools`. -/
noncomputable def Lemma415Prop42AbsPackToolsProvider.of_rowToFlatAndRowSeedToolsProvider
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415Prop42AbsPackToolsProvider (S := S) where
  absPackTools := fun u unn =>
    Sec4ChiFCaseAbsPackTools.mk
      (S := S) (f := u) (hnn := unn)
      (Lemma415Prop42RowToFlatTool.rowToFlat Rtf)
      (Sec4Prop42RowSeedTools.fabs_of_rows_s1 (P.rowSeeds u unn))
      (sec4_packOnS1_of_rowSeedTools u unn (P.rowSeeds u unn))
      (Sec4Prop42RowSeedTools.pack_on_s2 (P.rowSeeds u unn))


/-- Build theorem-4.15-specific corrected abs-pack tools from a global
row-to-flat bridge and row seeds only for the abs-error sequence. -/
noncomputable def Lemma415AbsErrorAbsPackToolsFrontier.of_rowToFlatAndRowSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)) :
    Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f where
  absPackTools := fun n =>
    Sec4ChiFCaseAbsPackTools.mk
      (S := S)
      (f := thm_4_15_abs_error (S := S) fn f n)
      (hnn := thm_4_15_abs_error_nonneg (S := S) fn f n)
      (Lemma415Prop42RowToFlatTool.rowToFlat Rtf)
      (Sec4Prop42RowSeedTools.fabs_of_rows_s1 (hSeeds n))
      (sec4_packOnS1_of_rowSeedTools
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)
        (hSeeds n))
      (Sec4Prop42RowSeedTools.pack_on_s2 (hSeeds n))


/-- Specialize the row-to-flat plus row-seed-provider route to the theorem-4.15
abs-error sequence. -/
noncomputable def Lemma415AbsErrorAbsPackToolsFrontier.of_rowToFlatAndRowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f :=
  Lemma415AbsErrorAbsPackToolsFrontier.of_provider
    (S := S) fn f
    (Lemma415Prop42AbsPackToolsProvider.of_rowToFlatAndRowSeedToolsProvider
      (S := S) Rtf P)


/-- Build flat absolute convergence of `chi_A * u` on `A.S1` from a corrected
`A.S1` row package plus the generic row-to-flat bridge. -/
noncomputable def Lemma415Prop42ChiFAbsOnS1Tool.of_rowToFlatAndPackOnS1Tool
    (R : Lemma415Prop42RowToFlatTool (S := S))
    (P : Lemma415Prop42PackOnS1Tool (S := S)) :
    Lemma415Prop42ChiFAbsOnS1Tool (S := S) where
  chiF_abs_on_s1_of_fabs := by
    intro u unn A hA x hxA hfabs
    exact sec4_prop42FlatAbs_of_absPack u unn
      (Lemma415Prop42RowToFlatTool.rowToFlat R)
      A hA x
      (Lemma415Prop42PackOnS1Tool.pack_on_s1_of_fabs
        P u unn A hA x hxA hfabs)


/-- Extract the flat `chi_A * u` abs-convergence tool on `A.S1` directly from
the corrected abs-pack tools. -/
noncomputable def Lemma415Prop42ChiFAbsOnS1Tool.of_absPackToolsProvider
    (P : Lemma415Prop42AbsPackToolsProvider (S := S)) :
    Lemma415Prop42ChiFAbsOnS1Tool (S := S) where
  chiF_abs_on_s1_of_fabs := fun u unn =>
    sec4_absOnS1Data_of_absPackTools u unn (P.absPackTools u unn)


/-- Extract the corrected generic `A.S1` package tool from the corrected
abs-pack provider. -/
noncomputable def Lemma415Prop42PackOnS1Tool.of_absPackToolsProvider
    (P : Lemma415Prop42AbsPackToolsProvider (S := S)) :
    Lemma415Prop42PackOnS1Tool (S := S) where
  pack_on_s1_of_fabs := fun u unn =>
    Sec4ChiFCaseAbsPackTools.pack_on_s1_of_fabs (P.absPackTools u unn)


/-- Recover the characteristic absolute-convergence seed on `A.S1` from flat
absolute convergence of the completed `χ_A * u` representative.

This is the row-1 extraction already proved for Proposition 4.2. -/
noncomputable def sec4_chiAbsOnS1_of_chiFAbsOnS1
    (u : IntegrableRep S) (unn : RepNonneg u)
    (H : Sec4ChiFAbsOnS1Data (S := S) u unn) :
    Sec4Prop42ChiAbsOnS1OfFAbs (S := S) u unn := by
  intro A hA x hxA hfabs
  let hflat := H A hA x hxA hfabs
  exact sec4_setChiAbsOfChiFAbs_of_row1 (S := S) u unn A hA x
    hflat.fst hflat.snd


/-- Assemble the exact generic `A.S1` seed tools from the row-1 `χ_A`
extraction route plus the corrected `A.S1` abs-outer tool. -/
noncomputable def Lemma415Prop42PackOnS1SeedTools.of_chiFAbsToolAndAbsOuterTool
    (H : Lemma415Prop42ChiFAbsOnS1Tool (S := S))
    (Outer : Lemma415Prop42AbsOuterOnS1Tool (S := S)) :
    Lemma415Prop42PackOnS1SeedTools (S := S) where
  chi_abs_on_s1_of_fabs := fun u unn =>
    sec4_chiAbsOnS1_of_chiFAbsOnS1
      (S := S) u unn
      (H.chiF_abs_on_s1_of_fabs u unn)
  abs_outer_on_s1_of_rows := fun u unn =>
    Outer.abs_outer_on_s1_of_rows u unn


/-- Extract the exact generic `A.S1` seed tools from a generic Proposition 4.2
row-seed provider.  This discharges the `A.S1` chi and corrected abs-outer
frontiers only relative to the stronger row-seed interface. -/
noncomputable def Lemma415Prop42PackOnS1SeedTools.of_rowSeedToolsProvider
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415Prop42PackOnS1SeedTools (S := S) where
  chi_abs_on_s1_of_fabs := fun u unn =>
    Sec4Prop42RowSeedTools.chi_abs_on_s1_of_fabs (P.rowSeeds u unn)
  abs_outer_on_s1_of_rows := fun u unn =>
    Sec4Prop42RowSeedTools.abs_outer_on_s1_of_rows (P.rowSeeds u unn)


/-- Assemble the corrected `A.S1` abs-row package from the exact local seeds:
`χ_A` absolute convergence plus the abs-outer summation package. -/
noncomputable def sec4_packOnS1_of_seedTools
    (u : IntegrableRep S) (unn : RepNonneg u)
    (T : Lemma415Prop42PackOnS1SeedTools (S := S)) :
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) u unn := by
  intro A hA x hxA hfabs
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA u x :=
    sec4_lambdaRowAbs_of_chiF_fabs A hA u (prop_4_2_n_k u) x
      (Lemma415Prop42PackOnS1SeedTools.chi_abs_on_s1_of_fabs
        T u unn A hA x hxA hfabs)
      hfabs
  let houter : Sec4LambdaRowsAbsOuterSumAt (S := S) A hA u x hrows :=
    Lemma415Prop42PackOnS1SeedTools.abs_outer_on_s1_of_rows
      T u unn A hA x hxA hfabs hrows
  exact ⟨hrows, houter⟩


/-- Package the exact local `A.S1` seeds as the corrected generic `A.S1`
row package tool. -/
noncomputable def Lemma415Prop42PackOnS1Tool.of_seedTools
    (T : Lemma415Prop42PackOnS1SeedTools (S := S)) :
    Lemma415Prop42PackOnS1Tool (S := S) where
  pack_on_s1_of_fabs := fun u unn =>
    sec4_packOnS1_of_seedTools (S := S) u unn T


/-- Build the flat `chi_A * u` abs-convergence tool from row-to-flat plus the
exact `A.S1` local seeds. -/
noncomputable def Lemma415Prop42ChiFAbsOnS1Tool.of_rowToFlatAndSeedTools
    (R : Lemma415Prop42RowToFlatTool (S := S))
    (T : Lemma415Prop42PackOnS1SeedTools (S := S)) :
    Lemma415Prop42ChiFAbsOnS1Tool (S := S) :=
  Lemma415Prop42ChiFAbsOnS1Tool.of_rowToFlatAndPackOnS1Tool
    (S := S) R
    (Lemma415Prop42PackOnS1Tool.of_seedTools (S := S) T)


/-- Specialize the generic corrected `A.S1` package tool to the theorem-4.15
abs-error sequence. -/
noncomputable def Lemma415AbsErrorPackOnS1Frontier.of_prop42PackOnS1Tool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42PackOnS1Tool (S := S)) :
    Lemma415AbsErrorPackOnS1Frontier (S := S) fn f where
  pack_on_s1_of_fabs := fun n =>
    Lemma415Prop42PackOnS1Tool.pack_on_s1_of_fabs
      T
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Theorem-4.15 Step 2b-ii frontier obtained from the exact local `A.S1`
seeds for each abs-error representative. -/
noncomputable def Lemma415AbsErrorPackOnS1Frontier.of_seedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42PackOnS1SeedTools (S := S)) :
    Lemma415AbsErrorPackOnS1Frontier (S := S) fn f where
  pack_on_s1_of_fabs := fun n =>
    sec4_packOnS1_of_seedTools
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
      T


/-- Extract theorem-4.15 Step 2b-ii from corrected abs-pack tools for the
abs-error sequence. -/
noncomputable def Lemma415AbsErrorPackOnS1Frontier.of_absPackTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f) :
    Lemma415AbsErrorPackOnS1Frontier (S := S) fn f where
  pack_on_s1_of_fabs := fun n =>
    Sec4ChiFCaseAbsPackTools.pack_on_s1_of_fabs
      (Lemma415AbsErrorAbsPackToolsFrontier.absPackTools T n)


/-- The theorem-4.15-specific `A.S1` seed frontier for the abs-error sequence.

This is weaker than `Lemma415Prop42PackOnS1SeedTools`: it asks for the two
local `A.S1` seeds only for `u_n = |f_n - f|`. -/
structure Lemma415AbsErrorPackOnS1SeedFrontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  chi_abs_on_s1_of_fabs : forall n,
    Sec4Prop42ChiAbsOnS1OfFAbs (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_outer_on_s1_of_rows : forall n,
    Sec4Prop42AbsOuterOnS1OfRows (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Specialize the generic Proposition 4.2 `A.S1` seed tools to the theorem-4.15
abs-error sequence. -/
noncomputable def Lemma415AbsErrorPackOnS1SeedFrontier.of_genericSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42PackOnS1SeedTools (S := S)) :
    Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f where
  chi_abs_on_s1_of_fabs := fun n =>
    Lemma415Prop42PackOnS1SeedTools.chi_abs_on_s1_of_fabs
      T
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_outer_on_s1_of_rows := fun n =>
    Lemma415Prop42PackOnS1SeedTools.abs_outer_on_s1_of_rows
      T
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Build the theorem-4.15 `A.S1` packing frontier from the abs-error-specific
seed frontier. -/
noncomputable def Lemma415AbsErrorPackOnS1Frontier.of_seedFrontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f) :
    Lemma415AbsErrorPackOnS1Frontier (S := S) fn f where
  pack_on_s1_of_fabs := by
    intro n A hA x hxA hfabs
    let u : IntegrableRep S := thm_4_15_abs_error (S := S) fn f n
    let unn : RepNonneg u := thm_4_15_abs_error_nonneg (S := S) fn f n
    let hrows : Sec4LambdaRowsAbsAt (S := S) A hA u x :=
      sec4_lambdaRowAbs_of_chiF_fabs A hA u (prop_4_2_n_k u) x
        (Lemma415AbsErrorPackOnS1SeedFrontier.chi_abs_on_s1_of_fabs
          T n A hA x hxA hfabs)
        hfabs
    let houter : Sec4LambdaRowsAbsOuterSumAt (S := S) A hA u x hrows :=
      Lemma415AbsErrorPackOnS1SeedFrontier.abs_outer_on_s1_of_rows
        T n A hA x hxA hfabs hrows
    exact ⟨hrows, houter⟩


/-- Step 2b-iii frontier for theorem 4.15: on `A.S2`, build the corrected
abs-outer lambda-row package for `u_n = |f_n - f|`. -/
structure Lemma415AbsErrorPackOnS2Frontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  pack_on_s2 : forall n,
    Sec4LambdaRowsAbsPackOnS2 (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Generic Proposition 4.2 corrected `A.S2` package tool.

Unlike `Lemma415Prop42AbsOuterOnS2Tool`, this keeps rows and the corrected
outer witness bundled together.  This matches what the row-seed interface
actually provides: an outer witness for the package's own row witnesses, not
for an arbitrary separately supplied `hrows`. -/
structure Lemma415Prop42PackOnS2Tool : Type _ where
  pack_on_s2 : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4LambdaRowsAbsPackOnS2 (S := S) u unn


/-- Extract the generic corrected `A.S2` package tool from a generic row-seed
provider. -/
noncomputable def Lemma415Prop42PackOnS2Tool.of_rowSeedToolsProvider
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415Prop42PackOnS2Tool (S := S) where
  pack_on_s2 := fun u unn =>
    Sec4Prop42RowSeedTools.pack_on_s2 (P.rowSeeds u unn)


/-- Extract the generic corrected `A.S2` package tool from the corrected
abs-pack provider. -/
noncomputable def Lemma415Prop42PackOnS2Tool.of_absPackToolsProvider
    (P : Lemma415Prop42AbsPackToolsProvider (S := S)) :
    Lemma415Prop42PackOnS2Tool (S := S) where
  pack_on_s2 := fun u unn =>
    Sec4ChiFCaseAbsPackTools.pack_on_s2 (P.absPackTools u unn)


/-- Specialize the generic corrected `A.S2` package tool to the theorem-4.15
abs-error sequence. -/
noncomputable def Lemma415AbsErrorPackOnS2Frontier.of_prop42PackTool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42PackOnS2Tool (S := S)) :
    Lemma415AbsErrorPackOnS2Frontier (S := S) fn f where
  pack_on_s2 := fun n =>
    T.pack_on_s2
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Extract theorem-4.15 Step 2b-iii from corrected abs-pack tools for the
abs-error sequence. -/
noncomputable def Lemma415AbsErrorPackOnS2Frontier.of_absPackTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f) :
    Lemma415AbsErrorPackOnS2Frontier (S := S) fn f where
  pack_on_s2 := fun n =>
    Sec4ChiFCaseAbsPackTools.pack_on_s2
      (Lemma415AbsErrorAbsPackToolsFrontier.absPackTools T n)


/-- Corrected abs-outer witness on `A.S2`, once per-row abs witnesses are
known.  This is separate from the older signed outer zero result: the corrected
target is the series of row absolute sums. -/
def Sec4Prop42AbsOuterOnS2OfRows
    (u : IntegrableRep S) (_unn : RepNonneg u) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S2 →
    ∀ hrows : Sec4LambdaRowsAbsAt (S := S) A hA u x,
      Sec4LambdaRowsAbsOuterSumAt (S := S) A hA u x hrows


/-- Generic Proposition 4.2 corrected `A.S2` abs-outer tool.

This is kept separate from `Sec4LambdaRowZeroOnS2`: the latter turns a row abs
witness into the signed row value `0`, while the corrected target here is the
outer series of row absolute sums.  No cancellation shortcut is hidden here. -/
structure Lemma415Prop42AbsOuterOnS2Tool : Type _ where
  abs_outer_on_s2_of_rows : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4Prop42AbsOuterOnS2OfRows (S := S) u unn


/-- The theorem-4.15-specific `A.S2` row frontier for the abs-error sequence. -/
structure Lemma415AbsErrorRowsOnS2Frontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  rows_on_s2 : forall n,
    Sec4Prop42RowsOnS2 (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Generic Proposition 4.2 S2 row tool.

This is still an honest frontier: it supplies only the per-row absolute
convergence witnesses on `A.S2`; it does not assert the corrected abs-outer
row-sum convergence. -/
structure Lemma415Prop42RowsOnS2Tool : Type _ where
  rows_on_s2 : forall (u : IntegrableRep S) (unn : RepNonneg u),
    Sec4Prop42RowsOnS2 (S := S) u unn


/-- Specialize the generic Proposition 4.2 S2 row tool to the theorem-4.15
abs-error sequence. -/
noncomputable def Lemma415AbsErrorRowsOnS2Frontier.of_prop42Tool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42RowsOnS2Tool (S := S)) :
    Lemma415AbsErrorRowsOnS2Frontier (S := S) fn f where
  rows_on_s2 := fun n =>
    T.rows_on_s2
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Extract the generic S2 row tool from a generic Proposition 4.2 row-seed
provider.  The extraction uses only the row component of the corrected `A.S2`
package and does not reuse its corrected outer witness. -/
noncomputable def Lemma415Prop42RowsOnS2Tool.of_rowSeedToolsProvider
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415Prop42RowsOnS2Tool (S := S) where
  rows_on_s2 := by
    intro u unn A hA x hxA
    let Q : Sec4LambdaRowsAbsPackAt (S := S) A hA u x :=
      Sec4Prop42RowSeedTools.pack_on_s2 (P.rowSeeds u unn) A hA x hxA
    exact Sec4LambdaRowsAbsPackAt.rows Q


/-- Extract theorem-4.15 S2 rows from row seeds for the abs-error sequence.
Only the row component of each corrected `A.S2` package is used. -/
noncomputable def Lemma415AbsErrorRowsOnS2Frontier.of_rowSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)) :
    Lemma415AbsErrorRowsOnS2Frontier (S := S) fn f where
  rows_on_s2 := by
    intro n A hA x hxA
    let u : IntegrableRep S := thm_4_15_abs_error (S := S) fn f n
    let unn : RepNonneg u := thm_4_15_abs_error_nonneg (S := S) fn f n
    let Q : Sec4LambdaRowsAbsPackAt (S := S) A hA u x :=
      Sec4Prop42RowSeedTools.pack_on_s2 (hSeeds n) A hA x hxA
    exact Sec4LambdaRowsAbsPackAt.rows Q


/-- The theorem-4.15-specific corrected abs-outer `A.S2` frontier for the
abs-error sequence. -/
structure Lemma415AbsErrorAbsOuterOnS2Frontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  abs_outer_on_s2_of_rows : forall n,
    Sec4Prop42AbsOuterOnS2OfRows (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Specialize the generic corrected `A.S2` abs-outer tool to the theorem-4.15
abs-error sequence. -/
noncomputable def Lemma415AbsErrorAbsOuterOnS2Frontier.of_prop42Tool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42AbsOuterOnS2Tool (S := S)) :
    Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f where
  abs_outer_on_s2_of_rows := fun n =>
    T.abs_outer_on_s2_of_rows
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)


/-- Build the corrected `A.S2` abs-row package from its row and corrected
abs-outer components. -/
noncomputable def sec4_absPackOnS2_of_rowsAndAbsOuter
    (u : IntegrableRep S) (unn : RepNonneg u)
    (Rows : Sec4Prop42RowsOnS2 (S := S) u unn)
    (Outer : Sec4Prop42AbsOuterOnS2OfRows (S := S) u unn) :
    Sec4LambdaRowsAbsPackOnS2 (S := S) u unn := by
  intro A hA x hxA
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA u x :=
    Rows A hA x hxA
  let houter : Sec4LambdaRowsAbsOuterSumAt (S := S) A hA u x hrows :=
    Outer A hA x hxA hrows
  exact ⟨hrows, houter⟩


/-- Build theorem-4.15 Step 2b-iii from the two smaller `A.S2` frontiers. -/
noncomputable def Lemma415AbsErrorPackOnS2Frontier.of_rowsAndAbsOuter
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Rows : Lemma415AbsErrorRowsOnS2Frontier (S := S) fn f)
    (Outer : Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorPackOnS2Frontier (S := S) fn f where
  pack_on_s2 := fun n =>
    sec4_absPackOnS2_of_rowsAndAbsOuter
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
      (Lemma415AbsErrorRowsOnS2Frontier.rows_on_s2 Rows n)
      (Lemma415AbsErrorAbsOuterOnS2Frontier.abs_outer_on_s2_of_rows Outer n)


/-- Reassemble the three Step 2b frontiers into the existing theorem-4.15
remaining-atom frontier. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_splitFrontiers
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Fabs : Lemma415AbsErrorFAbsRowsS1Frontier (S := S) fn f)
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f where
  fabs_of_rows_s1 := Fabs.fabs_of_rows_s1
  pack_on_s1_of_fabs := Ps1.pack_on_s1_of_fabs
  pack_on_s2 := Ps2.pack_on_s2


/-- Reassemble the remaining-atom frontier when Step 2b-i is supplied by the
generic Proposition 4.2 row-to-function absolute-convergence tool. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_prop42FAbsTool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42FAbsRowsS1Tool (S := S))
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_splitFrontiers
    (S := S) fn f
    (Lemma415AbsErrorFAbsRowsS1Frontier.of_prop42Tool (S := S) fn f T)
    Ps1 Ps2


/-- Reassemble the remaining-atom frontier after the generic Proposition 4.2
Step 2b-i extraction has been closed.  The only remaining local frontiers are
the two packing steps on `A.S1` and `A.S2`. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_packFrontiers
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_prop42FAbsTool
    (S := S) fn f
    (Lemma415Prop42FAbsRowsS1Tool.of_row0Right (S := S))
    Ps1 Ps2


/-- Reassemble the remaining-atom frontier from the exact `A.S1` seed tools
and the separate `A.S2` packing frontier. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_packS1SeedAndS2
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42PackOnS1SeedTools (S := S))
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_packFrontiers
    (S := S) fn f
    (Lemma415AbsErrorPackOnS1Frontier.of_seedTools (S := S) fn f T)
    Ps2


/-- Reassemble the remaining-atom frontier from generic Proposition 4.2 tools:
exact `A.S1` local seeds plus the corrected bundled `A.S2` package. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_genericPackS1AndPackS2Tools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T1 : Lemma415Prop42PackOnS1SeedTools (S := S))
    (T2 : Lemma415Prop42PackOnS2Tool (S := S)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_packS1SeedAndS2
    (S := S) fn f T1
    (Lemma415AbsErrorPackOnS2Frontier.of_prop42PackTool
      (S := S) fn f T2)


/-- Reassemble the remaining-atom frontier from corrected package-shaped
Proposition 4.2 tools on both `A.S1` and `A.S2`. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_genericPackS1ToolAndPackS2Tool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T1 : Lemma415Prop42PackOnS1Tool (S := S))
    (T2 : Lemma415Prop42PackOnS2Tool (S := S)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_packFrontiers
    (S := S) fn f
    (Lemma415AbsErrorPackOnS1Frontier.of_prop42PackOnS1Tool
      (S := S) fn f T1)
    (Lemma415AbsErrorPackOnS2Frontier.of_prop42PackTool
      (S := S) fn f T2)


/-- Reassemble the remaining-atom frontier from the corrected abs-pack
provider for Proposition 4.2. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_absPackToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (P : Lemma415Prop42AbsPackToolsProvider (S := S)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_genericPackS1ToolAndPackS2Tool
    (S := S) fn f
    (Lemma415Prop42PackOnS1Tool.of_absPackToolsProvider (S := S) P)
    (Lemma415Prop42PackOnS2Tool.of_absPackToolsProvider (S := S) P)


/-- Reassemble the remaining-atom frontier from corrected abs-pack tools
available only for the theorem-4.15 abs-error sequence. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_absErrorAbsPackTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_splitFrontiers
    (S := S) fn f
    (Lemma415AbsErrorFAbsRowsS1Frontier.of_absPackTools
      (S := S) fn f T)
    (Lemma415AbsErrorPackOnS1Frontier.of_absPackTools
      (S := S) fn f T)
    (Lemma415AbsErrorPackOnS2Frontier.of_absPackTools
      (S := S) fn f T)


/-- Reassemble the remaining-atom frontier from a row-to-flat bridge plus row
seeds available only for the theorem-4.15 abs-error sequence. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_rowToFlatAndRowSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_absErrorAbsPackTools
    (S := S) fn f
    (Lemma415AbsErrorAbsPackToolsFrontier.of_rowToFlatAndRowSeedTools
      (S := S) fn f Rtf hSeeds)


/-- Reassemble the remaining-atom frontier from a row-to-flat bridge and a
generic Proposition 4.2 row-seed provider. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_rowToFlatAndRowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_absPackToolsProvider
    (S := S) fn f
    (Lemma415Prop42AbsPackToolsProvider.of_rowToFlatAndRowSeedToolsProvider
      (S := S) Rtf P)


/-- Reassemble the remaining-atom frontier from a generic Proposition 4.2
row-seed provider.  This route uses only projections of the row-seed package;
it does not turn an `A.S2` package outer witness into an arbitrary-row outer
witness. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_rowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (P : Lemma415Prop42RowSeedToolsProvider (S := S)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_genericPackS1AndPackS2Tools
    (S := S) fn f
    (Lemma415Prop42PackOnS1SeedTools.of_rowSeedToolsProvider (S := S) P)
    (Lemma415Prop42PackOnS2Tool.of_rowSeedToolsProvider (S := S) P)


/-- Reassemble the remaining-atom frontier from the abs-error-specific `A.S1`
seed frontier and the separate `A.S2` packing frontier. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_absErrorPackS1SeedAndS2
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_packFrontiers
    (S := S) fn f
    (Lemma415AbsErrorPackOnS1Frontier.of_seedFrontier (S := S) fn f T)
    Ps2


/-- Reassemble the remaining-atom frontier from the abs-error-specific `A.S1`
seed frontier and the two split `A.S2` ingredients: rows plus corrected
abs-outer row-sum convergence. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_absErrorS1SeedAndS2Split
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415AbsErrorRowsOnS2Frontier (S := S) fn f)
    (Outer : Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_absErrorPackS1SeedAndS2
    (S := S) fn f T
    (Lemma415AbsErrorPackOnS2Frontier.of_rowsAndAbsOuter
      (S := S) fn f Rows Outer)


/-- Reassemble the remaining-atom frontier with theorem-4.15-specific `A.S1`
seeds, a generic Proposition 4.2 S2 row tool, and the theorem-4.15-specific
corrected `A.S2` abs-outer frontier. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_absErrorS1SeedAndGenericRowsS2Outer
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_absErrorS1SeedAndS2Split
    (S := S) fn f T
    (Lemma415AbsErrorRowsOnS2Frontier.of_prop42Tool
      (S := S) fn f Rows)
    Outer


/-- Reassemble the remaining-atom frontier with theorem-4.15-specific `A.S1`
seeds and generic Proposition 4.2 tools for both `A.S2` rows and corrected
`A.S2` abs-outer convergence. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_absErrorS1SeedAndGenericS2Tools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415Prop42AbsOuterOnS2Tool (S := S)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f :=
  Lemma415AbsErrorRemainingAtomFrontier.of_absErrorS1SeedAndGenericRowsS2Outer
    (S := S) fn f T Rows
    (Lemma415AbsErrorAbsOuterOnS2Frontier.of_prop42Tool
      (S := S) fn f Outer)


/-- Build the theorem-4.15 remaining-atom frontier from row seeds for the
abs-error sequence. -/
noncomputable def Lemma415AbsErrorRemainingAtomFrontier.of_rowSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)) :
    Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f where
  fabs_of_rows_s1 := fun n =>
    Sec4Prop42RowSeedTools.fabs_of_rows_s1 (hSeeds n)
  pack_on_s1_of_fabs := fun n =>
    sec4_packOnS1_of_rowSeedTools
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
      (hSeeds n)
  pack_on_s2 := fun n =>
    Sec4Prop42RowSeedTools.pack_on_s2 (hSeeds n)


/-- Monotonicity of the relative integral in its integrand.

This is the source-faithful comparison used in theorem 4.15 when replacing
`|f_n-f|` by the dominating majorant. -/
theorem relIntegral_mono_integrand
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (hvu : RepNonneg (v.sub u)) :
    Le (relIntegral C hC u hnn_u) (relIntegral C hC v hnn_v) := by
  change Le (prop_4_2_chi_f_rep C hC u hnn_u).integral
    (prop_4_2_chi_f_rep C hC v hnn_v).integral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep C hC u hnn_u).domain_isFull
      (prop_4_2_chi_f_rep C hC v hnn_v).domain_isFull)
      u.domain_isFull) v.domain_isFull) hC.rep.domain_isFull)
    (prop_4_2_chi_f_rep C hC u hnn_u)
    (prop_4_2_chi_f_rep C hC v hnn_v) ?_
  intro x hx _hrArgDom _hr'ArgDom hr hr'
  obtain ⟨⟨⟨⟨hxrepU, hxrepV⟩, hxu⟩, hxv⟩, hxχ⟩ := hx
  obtain ⟨hflatUDom, ⟨hflatU⟩⟩ := hxrepU
  obtain ⟨hflatVDom, ⟨hflatV⟩⟩ := hxrepV
  obtain ⟨huDom, ⟨huabs⟩⟩ := hxu
  obtain ⟨hvDom, ⟨hvabs⟩⟩ := hxv
  obtain ⟨hχDom, ⟨hχabs⟩⟩ := hxχ
  let hu : RSeq.SeriesSum (fun n => u.valueAt x huDom n) :=
    seriesSum_of_abs huabs
  let hv : RSeq.SeriesSum (fun n => v.valueAt x hvDom n) :=
    seriesSum_of_abs hvabs
  have hvalU :=
    prop_4_2_chi_f_rep_value C hC u hnn_u
      hflatUDom hχDom huDom hflatU hχabs huabs
  have hvalV :=
    prop_4_2_chi_f_rep_value C hC v hnn_v
      hflatVDom hχDom hvDom hflatV hχabs hvabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatU),
      seriesSum_unique hr' (seriesSum_of_abs hflatV), hvalU, hvalV]
  have huv_le : Le hu.sum hv.sum := by
    let hsubAbs : Sec4RepAbsAt (v.sub u) x :=
      sec4_sub_absSeriesSum_fwd ⟨hvDom, hvabs⟩ ⟨huDom, huabs⟩
    have hnonneg : Nonneg (hv.sum + -hu.sum) := by
      let hsub : RSeq.SeriesSum
          (fun n => (v.sub u).valueAt x hsubAbs.fst n) :=
        add_seriesSum_value hvDom (IntegrableRep.neg_memAt huDom)
          hv (neg_seriesSum_value huDom hu)
      have h := hvu x hsubAbs.fst hsubAbs.snd hsub
      change Nonneg (hv.sum + -hu.sum) at h
      exact h
    exact le_of_nonneg_sub (by
      rw [show hv.sum - hu.sum = hv.sum + -hu.sum from by ring]
      exact hnonneg)
  rcases (hC.valid x hχDom hχabs).1 with hxC1 | hxC2
  · have hχ1 : (seriesSum_of_abs hχabs).sum = 1 :=
      (hC.valid x hχDom hχabs).2.1 hxC1 (seriesSum_of_abs hχabs)
    rw [hχ1, one_mul, one_mul]
    exact huv_le
  · have hχ0 : (seriesSum_of_abs hχabs).sum = 0 :=
      (hC.valid x hχDom hχabs).2.2 hxC2 (seriesSum_of_abs hχabs)
    rw [hχ0, zero_mul, zero_mul]
    exact le_refl _


/-- Integrand monotonicity transported to the direct `genIB` construction on
already integrable sets, using row-seed consistency. -/
theorem genRelIntegral_mono_integrand_of_rowSeeds
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u)
    (Tv : Sec4Prop42RowSeedTools (S := S) v hnn_v)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable C
        (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
      (genRelIntegral_from_measurable C
        (isMeasurableSet_of_integrable (S := S) hC) v hnn_v) := by
  rw [sec4_genRelIntegral_eq_relIntegral_of_rowSeedTools C hC u hnn_u Tu,
      sec4_genRelIntegral_eq_relIntegral_of_rowSeedTools C hC v hnn_v Tv]
  exact relIntegral_mono_integrand C hC u v hnn_u hnn_v hvu


/-- Monotonicity of the direct general-measurable relative integral in its
integrand.

This version works for merely measurable `B`, including the source proof's
complement `-A`.  The two value bridges identify both direct representatives
with the same characteristic function, so the proof is the pointwise
comparison `χ_B u <= χ_B v`. -/
theorem genRelIntegral_from_measurable_mono_integrand_of_bridges
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Vu : Sec4GenIBValueBridge (S := S) B hB u hnn_u)
    (Vv : Sec4GenIBValueBridge (S := S) B hB v hnn_v)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable B hB u hnn_u)
      (genRelIntegral_from_measurable B hB v hnn_v) := by
  unfold genRelIntegral_from_measurable
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull (genIB_rep_from_measurable B hB u hnn_u))
      (IntegrableRep.domain_isFull (genIB_rep_from_measurable B hB v hnn_v)))
      u.domain_isFull) v.domain_isFull)
    (genIB_rep_from_measurable B hB u hnn_u)
    (genIB_rep_from_measurable B hB v hnn_v) ?_
  intro x hx _hrArgDom _hr'ArgDom hr hr'
  obtain ⟨⟨⟨hxgenU, hxgenV⟩, hxu⟩, hxv⟩ := hx
  obtain ⟨hgenUDom, ⟨hgenUabs⟩⟩ := hxgenU
  obtain ⟨hgenVDom, ⟨hgenVabs⟩⟩ := hxgenV
  obtain ⟨huDom, ⟨huabs⟩⟩ := hxu
  obtain ⟨hvDom, ⟨hvabs⟩⟩ := hxv
  let hu : RSeq.SeriesSum (fun n => u.valueAt x huDom n) :=
    seriesSum_of_abs huabs
  let hv : RSeq.SeriesSum (fun n => v.valueAt x hvDom n) :=
    seriesSum_of_abs hvabs
  have hgenU_sum :
      hr.sum = (seriesSum_of_abs hgenUabs).sum :=
    seriesSum_unique hr (seriesSum_of_abs hgenUabs)
  have hgenV_sum :
      hr'.sum = (seriesSum_of_abs hgenVabs).sum :=
    seriesSum_unique hr' (seriesSum_of_abs hgenVabs)
  have huv_le : Le hu.sum hv.sum := by
    let hsubAbs : Sec4RepAbsAt (v.sub u) x :=
      sec4_sub_absSeriesSum_fwd ⟨hvDom, hvabs⟩ ⟨huDom, huabs⟩
    have hnonneg : Nonneg (hv.sum + -hu.sum) := by
      let hsub : RSeq.SeriesSum
          (fun n => (v.sub u).valueAt x hsubAbs.fst n) :=
        add_seriesSum_value hvDom (IntegrableRep.neg_memAt huDom)
          hv (neg_seriesSum_value huDom hu)
      have h := hvu x hsubAbs.fst hsubAbs.snd hsub
      change Nonneg (hv.sum + -hu.sum) at h
      exact h
    exact le_of_nonneg_sub (by
      rw [show hv.sum - hu.sum = hv.sum + -hu.sum from by ring]
      exact hnonneg)
  rcases Vu.domain x hgenUDom hgenUabs with hxB1 | hxB2
  · have hU : (seriesSum_of_abs hgenUabs).sum = hu.sum :=
      Vu.value_s1 x hxB1 hgenUDom hgenUabs huDom huabs
    have hV : (seriesSum_of_abs hgenVabs).sum = hv.sum :=
      Vv.value_s1 x hxB1 hgenVDom hgenVabs hvDom hvabs
    rw [hgenU_sum, hgenV_sum, hU, hV]
    exact huv_le
  · have hU : (seriesSum_of_abs hgenUabs).sum = 0 :=
      Vu.value_s2 x hxB2 hgenUDom hgenUabs
    have hV : (seriesSum_of_abs hgenVabs).sum = 0 :=
      Vv.value_s2 x hxB2 hgenVDom hgenVabs
    rw [hgenU_sum, hgenV_sum, hU, hV]
    exact le_refl _


/-- Row-seed version of direct measurable integrand monotonicity. -/
theorem genRelIntegral_from_measurable_mono_integrand_of_rowSeeds
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u)
    (Tv : Sec4Prop42RowSeedTools (S := S) v hnn_v)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable B hB u hnn_u)
      (genRelIntegral_from_measurable B hB v hnn_v) :=
  genRelIntegral_from_measurable_mono_integrand_of_bridges
    (S := S) B hB u v hnn_u hnn_v
    (sec4_genIBValueBridge_of_rowSeedTools B hB u hnn_u Tu)
    (sec4_genIBValueBridge_of_rowSeedTools B hB v hnn_v Tv)
    hvu


/-- Remaining-atoms version of direct measurable integrand monotonicity. -/
theorem genRelIntegral_from_measurable_mono_integrand_of_remainingAtoms
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Tu : Sec4Prop42RemainingAtomTools (S := S) u hnn_u)
    (Tv : Sec4Prop42RemainingAtomTools (S := S) v hnn_v)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable B hB u hnn_u)
      (genRelIntegral_from_measurable B hB v hnn_v) :=
  genRelIntegral_from_measurable_mono_integrand_of_bridges
    (S := S) B hB u v hnn_u hnn_v
    (sec4_genIBValueBridge_of_remainingAtoms B hB u hnn_u Tu)
    (sec4_genIBValueBridge_of_remainingAtoms B hB v hnn_v Tv)
    hvu


/-- Additivity of the direct general-measurable relative integral in its
integrand, assuming value bridges for all three integrands. -/
theorem genRelIntegral_from_measurable_add_integrand_of_bridges
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (u v : IntegrableRep S)
    (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (hnn_add : RepNonneg (u.add v))
    (Vu : Sec4GenIBValueBridge (S := S) B hB u hnn_u)
    (Vv : Sec4GenIBValueBridge (S := S) B hB v hnn_v)
    (Vadd : Sec4GenIBValueBridge (S := S) B hB (u.add v) hnn_add) :
    genRelIntegral_from_measurable B hB (u.add v) hnn_add =
      genRelIntegral_from_measurable B hB u hnn_u +
        genRelIntegral_from_measurable B hB v hnn_v := by
  unfold genRelIntegral_from_measurable
  rw [← IntegrableRep.integral_add]
  refine cor_1_12
    (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull
        (genIB_rep_from_measurable B hB (u.add v) hnn_add))
      (IntegrableRep.domain_isFull
        ((genIB_rep_from_measurable B hB u hnn_u).add
          (genIB_rep_from_measurable B hB v hnn_v))))
      (IntegrableRep.domain_isFull (u.add v)))
    (genIB_rep_from_measurable B hB (u.add v) hnn_add)
    ((genIB_rep_from_measurable B hB u hnn_u).add
      (genIB_rep_from_measurable B hB v hnn_v)) ?_
  intro x hx _hgenAddArgDom _hgenSumArgDom hgenAdd hgenSum
  obtain ⟨⟨hxgenAdd, hxgenSum⟩, hxuv⟩ := hx
  obtain ⟨hgenAddDom, ⟨hgenAddAbs⟩⟩ := hxgenAdd
  obtain ⟨hgenSumDom, ⟨hgenSumAbs⟩⟩ := hxgenSum
  obtain ⟨huvDom, ⟨huvAbs⟩⟩ := hxuv
  let huDom : u.MemAt x := add_dom_left huvDom
  let hvDom : v.MemAt x := add_dom_right huvDom
  let hgenUDom : (genIB_rep_from_measurable B hB u hnn_u).MemAt x :=
    add_dom_left hgenSumDom
  let hgenVDom : (genIB_rep_from_measurable B hB v hnn_v).MemAt x :=
    add_dom_right hgenSumDom
  have huAbs : RSeq.SeriesSum
      (fun k => COF.abs (u.valueAt x huDom k)) :=
    add_absSeriesSum_left huvDom huvAbs
  have hvAbs : RSeq.SeriesSum
      (fun k => COF.abs (v.valueAt x hvDom k)) :=
    add_absSeriesSum_right huvDom huvAbs
  have hgenUAbs : RSeq.SeriesSum
      (fun k => COF.abs ((genIB_rep_from_measurable B hB u hnn_u).valueAt
        x hgenUDom k)) :=
    add_absSeriesSum_left hgenSumDom hgenSumAbs
  have hgenVAbs : RSeq.SeriesSum
      (fun k => COF.abs ((genIB_rep_from_measurable B hB v hnn_v).valueAt
        x hgenVDom k)) :=
    add_absSeriesSum_right hgenSumDom hgenSumAbs
  let huSum : RSeq.SeriesSum (fun k => u.valueAt x huDom k) :=
    seriesSum_of_abs huAbs
  let hvSum : RSeq.SeriesSum (fun k => v.valueAt x hvDom k) :=
    seriesSum_of_abs hvAbs
  let hgenUSum : RSeq.SeriesSum
      (fun k => (genIB_rep_from_measurable B hB u hnn_u).valueAt
        x hgenUDom k) :=
    seriesSum_of_abs hgenUAbs
  let hgenVSum : RSeq.SeriesSum
      (fun k => (genIB_rep_from_measurable B hB v hnn_v).valueAt
        x hgenVDom k) :=
    seriesSum_of_abs hgenVAbs
  have hgenSum_eq :
      hgenSum.sum = hgenUSum.sum + hgenVSum.sum :=
    seriesSum_unique hgenSum
      (add_seriesSum_value hgenUDom hgenVDom hgenUSum hgenVSum)
  rcases Vadd.domain x hgenAddDom hgenAddAbs with hxB1 | hxB2
  · have hAddVal :
        (seriesSum_of_abs hgenAddAbs).sum =
          (seriesSum_of_abs huvAbs).sum :=
      Vadd.value_s1 x hxB1 hgenAddDom hgenAddAbs huvDom huvAbs
    have hUVal : hgenUSum.sum = huSum.sum :=
      Vu.value_s1 x hxB1 hgenUDom hgenUAbs huDom huAbs
    have hVVal : hgenVSum.sum = hvSum.sum :=
      Vv.value_s1 x hxB1 hgenVDom hgenVAbs hvDom hvAbs
    have huv_eq : (seriesSum_of_abs huvAbs).sum = huSum.sum + hvSum.sum :=
      seriesSum_unique (seriesSum_of_abs huvAbs)
        (add_seriesSum_value huDom hvDom huSum hvSum)
    calc
      hgenAdd.sum = (seriesSum_of_abs hgenAddAbs).sum :=
        seriesSum_unique hgenAdd (seriesSum_of_abs hgenAddAbs)
      _ = (seriesSum_of_abs huvAbs).sum := hAddVal
      _ = huSum.sum + hvSum.sum := huv_eq
      _ = hgenUSum.sum + hgenVSum.sum := by rw [hUVal, hVVal]
      _ = hgenSum.sum := hgenSum_eq.symm
  · have hAddVal : (seriesSum_of_abs hgenAddAbs).sum = 0 :=
      Vadd.value_s2 x hxB2 hgenAddDom hgenAddAbs
    have hUVal : hgenUSum.sum = 0 :=
      Vu.value_s2 x hxB2 hgenUDom hgenUAbs
    have hVVal : hgenVSum.sum = 0 :=
      Vv.value_s2 x hxB2 hgenVDom hgenVAbs
    calc
      hgenAdd.sum = (seriesSum_of_abs hgenAddAbs).sum :=
        seriesSum_unique hgenAdd (seriesSum_of_abs hgenAddAbs)
      _ = 0 := hAddVal
      _ = 0 + 0 := by ring
      _ = hgenUSum.sum + hgenVSum.sum := by rw [hUVal, hVVal]
      _ = hgenSum.sum := hgenSum_eq.symm


/-- Row-seed version of additivity for the direct general-measurable relative
integral. -/
theorem genRelIntegral_from_measurable_add_integrand_of_rowSeeds
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (u v : IntegrableRep S)
    (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (hnn_add : RepNonneg (u.add v))
    (Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u)
    (Tv : Sec4Prop42RowSeedTools (S := S) v hnn_v)
    (Tadd : Sec4Prop42RowSeedTools (S := S) (u.add v) hnn_add) :
    genRelIntegral_from_measurable B hB (u.add v) hnn_add =
      genRelIntegral_from_measurable B hB u hnn_u +
        genRelIntegral_from_measurable B hB v hnn_v :=
  genRelIntegral_from_measurable_add_integrand_of_bridges
    (S := S) B hB u v hnn_u hnn_v hnn_add
    (sec4_genIBValueBridge_of_rowSeedTools B hB u hnn_u Tu)
    (sec4_genIBValueBridge_of_rowSeedTools B hB v hnn_v Tv)
    (sec4_genIBValueBridge_of_rowSeedTools B hB (u.add v) hnn_add Tadd)


/-- Compare a direct measurable relative integral with the previous relative
integral on an already integrable set.

This is the mixed form needed in theorem 4.15: the error term is handled by the
direct `genIB` construction, while the dominating majorant on `A∧B` is the
ordinary `relIntegral` because `A∧B` is integrable. -/
theorem genRelIntegral_from_measurable_le_relIntegral_of_valueBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Vu : Sec4GenIBValueBridge (S := S) C
      (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable C
        (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
      (relIntegral C hC v hnn_v) := by
  unfold genRelIntegral_from_measurable relIntegral
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull
        (genIB_rep_from_measurable C
          (isMeasurableSet_of_integrable (S := S) hC) u hnn_u))
      (IntegrableRep.domain_isFull (prop_4_2_chi_f_rep C hC v hnn_v)))
      u.domain_isFull) v.domain_isFull) hC.rep.domain_isFull)
    (genIB_rep_from_measurable C
      (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
    (prop_4_2_chi_f_rep C hC v hnn_v) ?_
  intro x hx _hgenArgDom _hrelArgDom hgen hrel
  obtain ⟨⟨⟨⟨hxgen, hxrel⟩, hxu⟩, hxv⟩, hxχ⟩ := hx
  obtain ⟨hgenDom, ⟨hgenabs⟩⟩ := hxgen
  obtain ⟨hrelDom, ⟨hrelabs⟩⟩ := hxrel
  obtain ⟨huDom, ⟨huabs⟩⟩ := hxu
  obtain ⟨hvDom, ⟨hvabs⟩⟩ := hxv
  obtain ⟨hχDom, ⟨hχabs⟩⟩ := hxχ
  let hu : RSeq.SeriesSum (fun n => u.valueAt x huDom n) :=
    seriesSum_of_abs huabs
  let hv : RSeq.SeriesSum (fun n => v.valueAt x hvDom n) :=
    seriesSum_of_abs hvabs
  have hgen_sum :
      hgen.sum = (seriesSum_of_abs hgenabs).sum :=
    seriesSum_unique hgen (seriesSum_of_abs hgenabs)
  have hrel_sum :
      hrel.sum = (seriesSum_of_abs hrelabs).sum :=
    seriesSum_unique hrel (seriesSum_of_abs hrelabs)
  have hrel_value :
      (seriesSum_of_abs hrelabs).sum =
        (seriesSum_of_abs hχabs).sum * hv.sum :=
    prop_4_2_chi_f_rep_value C hC v hnn_v
      hrelDom hχDom hvDom hrelabs hχabs hvabs
  have huv_le : Le hu.sum hv.sum := by
    let hsubAbs : Sec4RepAbsAt (v.sub u) x :=
      sec4_sub_absSeriesSum_fwd ⟨hvDom, hvabs⟩ ⟨huDom, huabs⟩
    have hnonneg : Nonneg (hv.sum + -hu.sum) := by
      let hsub : RSeq.SeriesSum
          (fun n => (v.sub u).valueAt x hsubAbs.fst n) :=
        add_seriesSum_value hvDom (IntegrableRep.neg_memAt huDom)
          hv (neg_seriesSum_value huDom hu)
      have h := hvu x hsubAbs.fst hsubAbs.snd hsub
      change Nonneg (hv.sum + -hu.sum) at h
      exact h
    exact le_of_nonneg_sub (by
      rw [show hv.sum - hu.sum = hv.sum + -hu.sum from by ring]
      exact hnonneg)
  rcases Vu.domain x hgenDom hgenabs with hxC1 | hxC2
  · have hgen_value :
        (seriesSum_of_abs hgenabs).sum = hu.sum :=
      Vu.value_s1 x hxC1 hgenDom hgenabs huDom huabs
    have hχ_one :
        (seriesSum_of_abs hχabs).sum = 1 :=
      (hC.valid x hχDom hχabs).2.1 hxC1 (seriesSum_of_abs hχabs)
    rw [hgen_sum, hrel_sum, hgen_value, hrel_value, hχ_one, one_mul]
    exact huv_le
  · have hgen_value :
        (seriesSum_of_abs hgenabs).sum = 0 :=
      Vu.value_s2 x hxC2 hgenDom hgenabs
    have hχ_zero :
        (seriesSum_of_abs hχabs).sum = 0 :=
      (hC.valid x hχDom hχabs).2.2 hxC2 (seriesSum_of_abs hχabs)
    rw [hgen_sum, hrel_sum, hgen_value, hrel_value, hχ_zero, zero_mul]
    exact le_refl _


/-- Row-seed version of the mixed comparison with ordinary `relIntegral`. -/
theorem genRelIntegral_from_measurable_le_relIntegral_of_rowSeeds
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable C
        (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
      (relIntegral C hC v hnn_v) :=
  genRelIntegral_from_measurable_le_relIntegral_of_valueBridge
    (S := S) C hC u v hnn_u hnn_v
    (sec4_genIBValueBridge_of_rowSeedTools C
      (isMeasurableSet_of_integrable (S := S) hC) u hnn_u Tu)
    hvu


/-- Remaining-atoms version of the mixed comparison with ordinary
`relIntegral`. -/
theorem genRelIntegral_from_measurable_le_relIntegral_of_remainingAtoms
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Tu : Sec4Prop42RemainingAtomTools (S := S) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable C
        (isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
      (relIntegral C hC v hnn_v) :=
  genRelIntegral_from_measurable_le_relIntegral_of_valueBridge
    (S := S) C hC u v hnn_u hnn_v
    (sec4_genIBValueBridge_of_remainingAtoms C
      (isMeasurableSet_of_integrable (S := S) hC) u hnn_u Tu)
    hvu


/-- Additivity of ordinary relative integration in the integrand. -/
theorem relIntegral_add_integrand
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S)
    (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (hnn_add : RepNonneg (u.add v)) :
    relIntegral C hC (u.add v) hnn_add =
      relIntegral C hC u hnn_u + relIntegral C hC v hnn_v := by
  unfold relIntegral
  rw [← IntegrableRep.integral_add]
  refine cor_1_12
    (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull (prop_4_2_chi_f_rep C hC (u.add v) hnn_add))
      (IntegrableRep.domain_isFull
        ((prop_4_2_chi_f_rep C hC u hnn_u).add
          (prop_4_2_chi_f_rep C hC v hnn_v))))
      (IntegrableRep.domain_isFull (u.add v)))
      (IntegrableRep.domain_isFull u))
      (isFull_inter (IntegrableRep.domain_isFull v)
        (IntegrableRep.domain_isFull hC.rep)))
    (prop_4_2_chi_f_rep C hC (u.add v) hnn_add)
    ((prop_4_2_chi_f_rep C hC u hnn_u).add
      (prop_4_2_chi_f_rep C hC v hnn_v)) ?_
  intro x hx _hrelAddArgDom _hrelSumArgDom hrelAdd hrelSum
  obtain ⟨⟨⟨⟨hxrelAdd, hxrelSum⟩, hxuv⟩, hxu⟩, hxvχ⟩ := hx
  obtain ⟨hxv, hxχ⟩ := hxvχ
  obtain ⟨hrelAddDom, ⟨hrelAddAbs⟩⟩ := hxrelAdd
  obtain ⟨hrelSumDom, ⟨hrelSumAbs⟩⟩ := hxrelSum
  obtain ⟨huvDom, ⟨huvAbs⟩⟩ := hxuv
  obtain ⟨huDom, ⟨huAbs⟩⟩ := hxu
  obtain ⟨hvDom, ⟨hvAbs⟩⟩ := hxv
  obtain ⟨hχDom, ⟨hχAbs⟩⟩ := hxχ
  let hrelUDom : (prop_4_2_chi_f_rep C hC u hnn_u).MemAt x :=
    add_dom_left hrelSumDom
  let hrelVDom : (prop_4_2_chi_f_rep C hC v hnn_v).MemAt x :=
    add_dom_right hrelSumDom
  have hrelUAbs : RSeq.SeriesSum
      (fun k => COF.abs ((prop_4_2_chi_f_rep C hC u hnn_u).valueAt
        x hrelUDom k)) :=
    add_absSeriesSum_left hrelSumDom hrelSumAbs
  have hrelVAbs : RSeq.SeriesSum
      (fun k => COF.abs ((prop_4_2_chi_f_rep C hC v hnn_v).valueAt
        x hrelVDom k)) :=
    add_absSeriesSum_right hrelSumDom hrelSumAbs
  let huSum : RSeq.SeriesSum (fun k => u.valueAt x huDom k) :=
    seriesSum_of_abs huAbs
  let hvSum : RSeq.SeriesSum (fun k => v.valueAt x hvDom k) :=
    seriesSum_of_abs hvAbs
  let hrelUSum : RSeq.SeriesSum
      (fun k => (prop_4_2_chi_f_rep C hC u hnn_u).valueAt
        x hrelUDom k) :=
    seriesSum_of_abs hrelUAbs
  let hrelVSum : RSeq.SeriesSum
      (fun k => (prop_4_2_chi_f_rep C hC v hnn_v).valueAt
        x hrelVDom k) :=
    seriesSum_of_abs hrelVAbs
  have hrelSum_eq :
      hrelSum.sum = hrelUSum.sum + hrelVSum.sum :=
    seriesSum_unique hrelSum
      (add_seriesSum_value hrelUDom hrelVDom hrelUSum hrelVSum)
  have hrelAdd_value :
      (seriesSum_of_abs hrelAddAbs).sum =
        (seriesSum_of_abs hχAbs).sum * (seriesSum_of_abs huvAbs).sum :=
    prop_4_2_chi_f_rep_value C hC (u.add v) hnn_add
      hrelAddDom hχDom huvDom hrelAddAbs hχAbs huvAbs
  have hrelU_value :
      hrelUSum.sum = (seriesSum_of_abs hχAbs).sum * huSum.sum :=
    prop_4_2_chi_f_rep_value C hC u hnn_u
      hrelUDom hχDom huDom hrelUAbs hχAbs huAbs
  have hrelV_value :
      hrelVSum.sum = (seriesSum_of_abs hχAbs).sum * hvSum.sum :=
    prop_4_2_chi_f_rep_value C hC v hnn_v
      hrelVDom hχDom hvDom hrelVAbs hχAbs hvAbs
  have huv_value :
      (seriesSum_of_abs huvAbs).sum = huSum.sum + hvSum.sum :=
    seriesSum_unique (seriesSum_of_abs huvAbs)
      (add_seriesSum_value huDom hvDom huSum hvSum)
  calc
    hrelAdd.sum = (seriesSum_of_abs hrelAddAbs).sum :=
      seriesSum_unique hrelAdd (seriesSum_of_abs hrelAddAbs)
    _ = (seriesSum_of_abs hχAbs).sum * (seriesSum_of_abs huvAbs).sum :=
      hrelAdd_value
    _ = (seriesSum_of_abs hχAbs).sum * (huSum.sum + hvSum.sum) := by
      rw [huv_value]
    _ = (seriesSum_of_abs hχAbs).sum * huSum.sum +
        (seriesSum_of_abs hχAbs).sum * hvSum.sum := by ring
    _ = hrelUSum.sum + hrelVSum.sum := by rw [hrelU_value, hrelV_value]
    _ = hrelSum.sum := hrelSum_eq.symm


/-- Additivity of the complement expression `I_{-C}` in the integrand. -/
theorem complementIntegral_add_integrand
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S)
    (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (hnn_add : RepNonneg (u.add v)) :
    ((u.add v).sub (prop_4_2_chi_f_rep C hC (u.add v) hnn_add)).integral =
      (u.sub (prop_4_2_chi_f_rep C hC u hnn_u)).integral +
        (v.sub (prop_4_2_chi_f_rep C hC v hnn_v)).integral := by
  have hrel := relIntegral_add_integrand
    (S := S) C hC u v hnn_u hnn_v hnn_add
  unfold relIntegral at hrel
  rw [IntegrableRep.integral_sub, IntegrableRep.integral_add, hrel,
      IntegrableRep.integral_sub, IntegrableRep.integral_sub]
  ring


/-- Compare direct measurable `I_{-C}` of an error integrand with the old
complement expression for a dominating majorant. -/
theorem genRelIntegral_neg_le_complementIntegral_of_valueBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Vu : Sec4GenIBValueBridge (S := S) (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
      ((v.sub (prop_4_2_chi_f_rep C hC v hnn_v)).integral) := by
  unfold genRelIntegral_from_measurable
  refine prop_1_11 (isFull_inter (isFull_inter (isFull_inter (isFull_inter
      (IntegrableRep.domain_isFull
        (genIB_rep_from_measurable (BSet.neg C)
          (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u))
      (IntegrableRep.domain_isFull
        (v.sub (prop_4_2_chi_f_rep C hC v hnn_v))))
      (IntegrableRep.domain_isFull (prop_4_2_chi_f_rep C hC v hnn_v)))
      (IntegrableRep.domain_isFull hC.rep))
      (isFull_inter (IntegrableRep.domain_isFull u)
        (IntegrableRep.domain_isFull v)))
    (genIB_rep_from_measurable (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
    (v.sub (prop_4_2_chi_f_rep C hC v hnn_v)) ?_
  intro x hx _hgenArgDom _hcompArgDom hgen hcomp
  obtain ⟨⟨⟨⟨hxgen, hxcomp⟩, hxchiF⟩, hxχ⟩, hxuv⟩ := hx
  obtain ⟨hxu, hxv⟩ := hxuv
  obtain ⟨hgenDom, ⟨hgenabs⟩⟩ := hxgen
  obtain ⟨_hcompSupportDom, ⟨_hcompabs⟩⟩ := hxcomp
  obtain ⟨hchiFDom, ⟨hchiFabs⟩⟩ := hxchiF
  obtain ⟨hχDom, ⟨hχabs⟩⟩ := hxχ
  obtain ⟨huDom, ⟨huabs⟩⟩ := hxu
  obtain ⟨hvDom, ⟨hvabs⟩⟩ := hxv
  let hu : RSeq.SeriesSum (fun n => u.valueAt x huDom n) :=
    seriesSum_of_abs huabs
  let hv : RSeq.SeriesSum (fun n => v.valueAt x hvDom n) :=
    seriesSum_of_abs hvabs
  let hcompValue :=
    add_seriesSum_value hvDom (IntegrableRep.neg_memAt hchiFDom)
      hv (neg_seriesSum_value hchiFDom (seriesSum_of_abs hchiFabs))
  have hcomp_value :
      hcompValue.sum =
        (1 - (seriesSum_of_abs hχabs).sum) * hv.sum :=
    prop_4_2_complement_value C hC v hnn_v
      hchiFDom hχDom hvDom hchiFabs hχabs hvabs
  have hgen_sum :
      hgen.sum = (seriesSum_of_abs hgenabs).sum :=
    seriesSum_unique hgen (seriesSum_of_abs hgenabs)
  have hcomp_sum :
      hcomp.sum = hcompValue.sum :=
    seriesSum_unique hcomp hcompValue
  have huv_le : Le hu.sum hv.sum := by
    let hsubAbs : Sec4RepAbsAt (v.sub u) x :=
      sec4_sub_absSeriesSum_fwd ⟨hvDom, hvabs⟩ ⟨huDom, huabs⟩
    have hnonneg : Nonneg (hv.sum + -hu.sum) := by
      let hsub : RSeq.SeriesSum
          (fun n => (v.sub u).valueAt x hsubAbs.fst n) :=
        add_seriesSum_value hvDom (IntegrableRep.neg_memAt huDom)
          hv (neg_seriesSum_value huDom hu)
      have h := hvu x hsubAbs.fst hsubAbs.snd hsub
      change Nonneg (hv.sum + -hu.sum) at h
      exact h
    exact le_of_nonneg_sub (by
      rw [show hv.sum - hu.sum = hv.sum + -hu.sum from by ring]
      exact hnonneg)
  rcases (hC.valid x hχDom hχabs).1 with hxC1 | hxC2
  · have hχ_one :
        (seriesSum_of_abs hχabs).sum = 1 :=
      (hC.valid x hχDom hχabs).2.1 hxC1 (seriesSum_of_abs hχabs)
    have hgen_value :
        (seriesSum_of_abs hgenabs).sum = 0 :=
      Vu.value_s2 x (by simpa [BSet.neg] using hxC1) hgenDom hgenabs
    rw [hgen_sum, hcomp_sum, hgen_value, hcomp_value, hχ_one]
    ring_nf
    exact le_refl _
  · have hχ_zero :
        (seriesSum_of_abs hχabs).sum = 0 :=
      (hC.valid x hχDom hχabs).2.2 hxC2 (seriesSum_of_abs hχabs)
    have hgen_value :
        (seriesSum_of_abs hgenabs).sum = hu.sum :=
      Vu.value_s1 x (by simpa [BSet.neg] using hxC2)
        hgenDom hgenabs huDom huabs
    rw [hgen_sum, hcomp_sum, hgen_value, hcomp_value, hχ_zero]
    ring_nf
    exact huv_le


/-- Row-seed version of the complement comparison. -/
theorem genRelIntegral_neg_le_complementIntegral_of_rowSeeds
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
      ((v.sub (prop_4_2_chi_f_rep C hC v hnn_v)).integral) :=
  genRelIntegral_neg_le_complementIntegral_of_valueBridge
    (S := S) C hC u v hnn_u hnn_v
    (sec4_genIBValueBridge_of_rowSeedTools
      (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC)
      u hnn_u Tu)
    hvu


/-- Remaining-atoms version of the complement comparison. -/
theorem genRelIntegral_neg_le_complementIntegral_of_remainingAtoms
    (C : BSet X) (hC : IntegrableSet1 S C)
    (u v : IntegrableRep S) (hnn_u : RepNonneg u) (hnn_v : RepNonneg v)
    (Tu : Sec4Prop42RemainingAtomTools (S := S) u hnn_u)
    (hvu : RepNonneg (v.sub u)) :
    Le
      (genRelIntegral_from_measurable (BSet.neg C)
        (isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
      ((v.sub (prop_4_2_chi_f_rep C hC v hnn_v)).integral) :=
  genRelIntegral_neg_le_complementIntegral_of_valueBridge
    (S := S) C hC u v hnn_u hnn_v
    (sec4_genIBValueBridge_of_remainingAtoms
      (BSet.neg C)
      (isMeasurableSet_neg_of_integrable (S := S) hC)
      u hnn_u Tu)
    hvu


/-- Source-shaped split data for theorem 4.15's uniform-`I_B` hypothesis.

For a fixed `eps`, this records exactly the post-choice part of the source
proof:

* choose `A`, `N`, and `delta`;
* for every measurable `B` with small `A and B`, prove both right-hand pieces
  of the displayed split estimate are small;
* keep the direct `genIB` value bridges explicit.

The domination-by-`2g` work that supplies the two piece bounds is not hidden in
this structure.  This structure only turns those two bounds into the uniform
`I_B` datum required by lemma 4.14. -/
structure Lemma415SplitUniformSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) (eps : R) :
    Type _ where
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  delta : R
  delta_pos : COF.lt 0 delta
  epsAB : R
  epsNeg : R
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  pieceBounds : forall (n : Nat), N <= n ->
    forall (B : BSet X) (hB : IsMeasurableSet (S := S) B),
      COF.lt (measure1 S (hB A hA)) delta ->
        Exists (fun _VB : Sec4GenIBValueBridge (S := S) B hB
            (thm_4_15_abs_error (S := S) fn f n)
            (thm_4_15_abs_error_nonneg (S := S) fn f n) =>
          Exists (fun _VAB : Sec4GenIBValueBridge (S := S) (BSet.and A B)
              (isMeasurableSet_of_integrable (S := S) (hB A hA))
              (thm_4_15_abs_error (S := S) fn f n)
              (thm_4_15_abs_error_nonneg (S := S) fn f n) =>
            Exists (fun _VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg A)
                (isMeasurableSet_neg_of_integrable (S := S) hA)
                (thm_4_15_abs_error (S := S) fn f n)
                (thm_4_15_abs_error_nonneg (S := S) fn f n) =>
              And
                (COF.lt
                  (genRelIntegral_from_measurable (BSet.and A B)
                    (isMeasurableSet_of_integrable (S := S) (hB A hA))
                    (thm_4_15_abs_error (S := S) fn f n)
                    (thm_4_15_abs_error_nonneg (S := S) fn f n))
                  epsAB)
                (COF.lt
                  (genRelIntegral_from_measurable (BSet.neg A)
                    (isMeasurableSet_neg_of_integrable (S := S) hA)
                    (thm_4_15_abs_error (S := S) fn f n)
                    (thm_4_15_abs_error_nonneg (S := S) fn f n))
                  epsNeg))))


/-- Source-shaped majorant data for theorem 4.15's displayed estimate.

The intended majorant is the source proof's `2g`.  The fields say exactly what
the printed proof uses after choosing `A` and `delta`:

* `|f_n - f|` is pointwise bounded by the majorant;
* the majorant integral over `A∧B` is small when `μ(A∧B)<delta`;
* the majorant integral over `-A` is small.

The construction below turns these three facts into the already completed
split-uniform data.  It does not silently derive `|f| <= g` or the choice of
`A`; those are still explicit frontier data. -/
structure Lemma415MajorantSplitUniformSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R) : Type _ where
  majorantSeeds :
    Sec4Prop42RowSeedTools (S := S) majorant majorant_nonneg
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  delta : R
  delta_pos : COF.lt 0 delta
  epsAB : R
  epsNeg : R
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  dominatesError : forall n,
    RepNonneg (majorant.sub (thm_4_15_abs_error (S := S) fn f n))
  majorantABSmall : forall (B : BSet X) (hB : IsMeasurableSet (S := S) B),
    COF.lt (measure1 S (hB A hA)) delta ->
      COF.lt
        (genRelIntegral_from_measurable (BSet.and A B)
          (isMeasurableSet_of_integrable (S := S) (hB A hA))
          majorant majorant_nonneg)
        epsAB
  majorantNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          majorant majorant_nonneg)
        epsNeg


/-- Source-shaped data one step closer to the printed proof.

Here the `A∧B` estimate is not supplied directly.  It is obtained below from
the absolute continuity theorem for the relative integral of the majorant.
The only small-piece estimate still supplied as data is the source proof's
choice of `A` with small tail over `-A`. -/
structure Lemma415MajorantChoiceSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R) : Type _ where
  majorantSeeds :
    Sec4Prop42RowSeedTools (S := S) majorant majorant_nonneg
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  dominatesError : forall n,
    RepNonneg (majorant.sub (thm_4_15_abs_error (S := S) fn f n))
  majorantNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          majorant majorant_nonneg)
        epsNeg


/-- Source-shaped majorant choice data that keeps the majorant on the
ordinary `relIntegral`/complement side.

This avoids asking for row-seed data for the majorant.  In theorem 4.15 this
is closer to the displayed proof: only the error term needs the direct
measurable `I_B` bridge, while the two majorant pieces live on `A∧B` and
`-A` as ordinary relative/complement integrals. -/
structure Lemma415MajorantRelChoiceSourceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R) : Type _ where
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  dominatesError : forall n,
    RepNonneg (majorant.sub (thm_4_15_abs_error (S := S) fn f n))
  majorantNegSmall :
      COF.lt
        ((majorant.sub
          (prop_4_2_chi_f_rep A hA majorant majorant_nonneg)).integral)
        epsNeg


/-- The source proof's explicit majorant `2g`, represented constructively as
`g + g`. -/
noncomputable def thm_4_15_two_g_majorant_nonneg
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) :
    RepNonneg (g.add g) :=
  sec4_add_repNonneg (S := S) g g g_nonneg g_nonneg


/-- The source tail estimate transported from `g` to `2g = g + g`.

The source text chooses `A` so that the tail of `g` is small.  This theorem
formalizes the additive step needed to use the already specialized `2g`
majorant interface. -/
theorem thm_4_15_two_g_neg_small_from_g_neg_small
    (A : BSet X) (hA : IntegrableSet1 S A)
    (g : IntegrableRep S) (g_nonneg : RepNonneg g)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (twoGSeeds :
      Sec4Prop42RowSeedTools (S := S) (g.add g)
        (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg))
    (epsG epsNeg : R)
    (gNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          g g_nonneg)
        epsG)
    (gTailBudget : COF.lt (epsG + epsG) epsNeg) :
    COF.lt
      (genRelIntegral_from_measurable (BSet.neg A)
        (isMeasurableSet_neg_of_integrable (S := S) hA)
        (g.add g)
        (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg))
      epsNeg := by
  have hAdd :=
    genRelIntegral_from_measurable_add_integrand_of_rowSeeds
      (S := S)
      (BSet.neg A)
      (isMeasurableSet_neg_of_integrable (S := S) hA)
      g g g_nonneg g_nonneg
      (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
      gSeeds gSeeds twoGSeeds
  rw [hAdd]
  exact COFO.lt_trans (lt_add gNegSmall gNegSmall) gTailBudget


/-- The source tail estimate transported from `g` to the complement expression
for `2g = g + g`, without row-seed data for `2g`.

The direct `I_{-A}(g)` datum is first identified with the previous complement
expression using row seeds for `g`; additivity of the complement expression
then gives the `2g` tail estimate. -/
theorem thm_4_15_two_g_complement_small_from_g_neg_small
    (A : BSet X) (hA : IntegrableSet1 S A)
    (g : IntegrableRep S) (g_nonneg : RepNonneg g)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (epsG epsNeg : R)
    (gNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          g g_nonneg)
        epsG)
    (gTailBudget : COF.lt (epsG + epsG) epsNeg) :
    COF.lt
      (((g.add g).sub
        (prop_4_2_chi_f_rep A hA (g.add g)
          (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg))).integral)
      epsNeg := by
  have hgEq :
      genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          g g_nonneg =
        (g.sub (prop_4_2_chi_f_rep A hA g g_nonneg)).integral :=
    sec4_genRelIntegral_eq_complement_of_rowSeedTools
      (S := S) A hA g g_nonneg gSeeds
  have hgSmall :
      COF.lt
        ((g.sub (prop_4_2_chi_f_rep A hA g g_nonneg)).integral)
        epsG := by
    rw [← hgEq]
    exact gNegSmall
  have hAdd :=
    complementIntegral_add_integrand
      (S := S) A hA g g g_nonneg g_nonneg
      (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
  rw [hAdd]
  exact COFO.lt_trans (lt_add hgSmall hgSmall) gTailBudget


/-- The printed pointwise estimate `|f_n - f| <= 2g`.

This is the algebraic heart of theorem 4.15's displayed domination step.  The
source assumes `|f_n| <= g`; the same bound for the limit `f` is supplied here
as an explicit pointwise domination datum.  The proof is the triangle
inequality

`|f_n - f| <= |f_n| + |f| <= g + g`.
-/
theorem thm_4_15_abs_error_dominated_by_two_g
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal)) :
    forall n,
      RepNonneg
        ((g.add g).sub (thm_4_15_abs_error (S := S) fn f n)) := by
  intro n x htotalDom habs hx
  let err : IntegrableRep S := thm_4_15_abs_error (S := S) fn f n
  let subRep : IntegrableRep S := (fn n).sub f
  let htwoGDom : (g.add g).MemAt x := add_dom_left htotalDom
  let herrNegDom : err.neg.MemAt x := add_dom_right htotalDom
  let herrDom : err.MemAt x := neg_dom herrNegDom
  have htwoG_abs :
      RSeq.SeriesSum (fun k => COF.abs ((g.add g).valueAt x htwoGDom k)) :=
    add_absSeriesSum_left htotalDom habs
  have herr_neg_abs :
      RSeq.SeriesSum (fun k => COF.abs (err.neg.valueAt x herrNegDom k)) :=
    add_absSeriesSum_right htotalDom habs
  have herr_abs :
      RSeq.SeriesSum (fun k => COF.abs (err.valueAt x herrDom k)) :=
    neg_absSeriesSum herrNegDom herr_neg_abs
  let hg1Dom : g.MemAt x := add_dom_left htwoGDom
  let hg2Dom : g.MemAt x := add_dom_right htwoGDom
  have hg1_abs : RSeq.SeriesSum
      (fun k => COF.abs (g.valueAt x hg1Dom k)) :=
    add_absSeriesSum_left htwoGDom htwoG_abs
  have hg2_abs : RSeq.SeriesSum
      (fun k => COF.abs (g.valueAt x hg2Dom k)) :=
    add_absSeriesSum_right htwoGDom htwoG_abs
  let hg1_sum : RSeq.SeriesSum (fun k => g.valueAt x hg1Dom k) :=
    seriesSum_of_abs hg1_abs
  let hg2_sum : RSeq.SeriesSum (fun k => g.valueAt x hg2Dom k) :=
    seriesSum_of_abs hg2_abs
  let herr_sum : RSeq.SeriesSum (fun k => err.valueAt x herrDom k) :=
    seriesSum_of_abs herr_abs
  let htwoG_sum : RSeq.SeriesSum
      (fun k => (g.add g).valueAt x htwoGDom k) :=
    add_seriesSum_value hg1Dom hg2Dom hg1_sum hg2_sum
  let htotal : RSeq.SeriesSum
      (fun k => ((g.add g).sub err).valueAt x htotalDom k) :=
    add_seriesSum_value htwoGDom herrNegDom htwoG_sum
      (neg_seriesSum_value herrDom herr_sum)
  have hx_eq : hx.sum = htotal.sum := seriesSum_unique hx htotal
  let hsubDom : subRep.MemAt x := fun k => by
    have hk := herrDom (3 * k + 1)
    change x ∈ (subRep.absVal.fn (3 * k + 1)).dom at hk
    simpa only [IntegrableRep.absVal, seqMerge3_one] using hk
  let u : Nat -> R := fun j =>
    COF.abs ((subRep.absDiffFn j).toFun x
      (subRep.absDiffFn_memAt hsubDom j))
  let v : Nat -> R := fun k => COF.abs (subRep.valueAt x hsubDom k)
  let w : Nat -> R := fun k =>
    COF.abs ((BFunR.smul (-1) (subRep.fn k)).toFun x (hsubDom k))
  have hmerge : RSeq.SeriesSum (seqMerge3 u v w) := by
    refine seriesSum_congr (fun m => ?_) herr_abs
    dsimp [u, v, w, err, subRep, thm_4_15_abs_error]
    rcases natMod3 m with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_zero]
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_one]
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_two]
  have hsub_abs :
      RSeq.SeriesSum (fun k => COF.abs (subRep.valueAt x hsubDom k)) := by
    dsimp [v] at hmerge ⊢
    exact seriesSum_merge3_second_of_nonneg
      (u := u) (v := v) (w := w)
      (fun _ => abs_nonneg _)
      (fun _ => abs_nonneg _)
      (fun _ => abs_nonneg _)
      hmerge
  let hfnDom : (fn n).MemAt x := add_dom_left hsubDom
  let hnegFDom : f.neg.MemAt x := add_dom_right hsubDom
  let hfDom : f.MemAt x := neg_dom hnegFDom
  have hfn_abs :
      RSeq.SeriesSum (fun k => COF.abs ((fn n).valueAt x hfnDom k)) :=
    add_absSeriesSum_left hsubDom hsub_abs
  have hf_abs :
      RSeq.SeriesSum (fun k => COF.abs (f.valueAt x hfDom k)) :=
    neg_absSeriesSum hnegFDom (add_absSeriesSum_right hsubDom hsub_abs)
  let hfn_sum : RSeq.SeriesSum (fun k => (fn n).valueAt x hfnDom k) :=
    seriesSum_of_abs hfn_abs
  let hf_sum : RSeq.SeriesSum (fun k => f.valueAt x hfDom k) :=
    seriesSum_of_abs hf_abs
  let hsub_sum : RSeq.SeriesSum (fun k => subRep.valueAt x hsubDom k) :=
    seriesSum_of_abs hsub_abs
  have hsub_eq : hsub_sum.sum = hfn_sum.sum - hf_sum.sum := by
    have heq :=
      seriesSum_unique hsub_sum
        (add_seriesSum_value hfnDom hnegFDom hfn_sum
          (neg_seriesSum_value hfDom hf_sum))
    change hsub_sum.sum = hfn_sum.sum + -hf_sum.sum at heq
    rwa [sub_eq_add_neg]
  obtain ⟨herr_alt, herr_alt_eq⟩ :=
    subRep.absVal_signed_value x hsubDom hsub_sum
  have herr_eq :
      herr_sum.sum = COF.abs (hfn_sum.sum - hf_sum.sum) := by
    have heq : herr_sum.sum = herr_alt.sum :=
      seriesSum_unique herr_sum herr_alt
    rw [heq, herr_alt_eq, hsub_eq]
  let hfnAbsValDom : (fn n).absVal.MemAt x :=
    (fn n).mem_absVal_dom hfnDom
  have hfn_absVal_abs : RSeq.SeriesSum
      (fun k => COF.abs ((fn n).absVal.valueAt x hfnAbsValDom k)) := by
    simpa only [IntegrableRep.valueAt] using
      (fn n).absVal_absSeries hfnDom hfn_abs
  let hfn_absVal_sum :
      RSeq.SeriesSum (fun k => (fn n).absVal.valueAt x hfnAbsValDom k) :=
    seriesSum_of_abs hfn_absVal_abs
  obtain ⟨hfn_absVal_alt, hfn_absVal_alt_eq⟩ :=
    (fn n).absVal_signed_value x hfnDom hfn_sum
  have hfn_absVal_sum_eq :
      hfn_absVal_sum.sum = COF.abs hfn_sum.sum := by
    rw [seriesSum_unique hfn_absVal_sum hfn_absVal_alt,
      hfn_absVal_alt_eq]
  let hfn_sub_abs : Sec4RepAbsAt (g.sub (fn n).absVal) x :=
    sec4_sub_absSeriesSum_fwd
      ⟨hg1Dom, hg1_abs⟩ ⟨hfnAbsValDom, hfn_absVal_abs⟩
  let hfn_sub_sum : RSeq.SeriesSum
      (fun k => (g.sub (fn n).absVal).valueAt x hfn_sub_abs.fst k) :=
    add_seriesSum_value hg1Dom (IntegrableRep.neg_memAt hfnAbsValDom)
      hg1_sum (neg_seriesSum_value hfnAbsValDom hfn_absVal_sum)
  have hfn_nonneg :=
    hfn_dom n x hfn_sub_abs.fst hfn_sub_abs.snd hfn_sub_sum
  have hfn_abs_le_g : Le (COF.abs hfn_sum.sum) hg1_sum.sum := by
    have hle_absVal : Le hfn_absVal_sum.sum hg1_sum.sum :=
      le_of_nonneg_sub (by
        rw [show hg1_sum.sum - hfn_absVal_sum.sum =
            hg1_sum.sum + -hfn_absVal_sum.sum from by ring]
        exact hfn_nonneg)
    rwa [← hfn_absVal_sum_eq]
  let hfAbsValDom : f.absVal.MemAt x := f.mem_absVal_dom hfDom
  have hf_absVal_abs : RSeq.SeriesSum
      (fun k => COF.abs (f.absVal.valueAt x hfAbsValDom k)) := by
    simpa only [IntegrableRep.valueAt] using f.absVal_absSeries hfDom hf_abs
  let hf_absVal_sum :
      RSeq.SeriesSum (fun k => f.absVal.valueAt x hfAbsValDom k) :=
    seriesSum_of_abs hf_absVal_abs
  obtain ⟨hf_absVal_alt, hf_absVal_alt_eq⟩ :=
    f.absVal_signed_value x hfDom hf_sum
  have hf_absVal_sum_eq :
      hf_absVal_sum.sum = COF.abs hf_sum.sum := by
    rw [seriesSum_unique hf_absVal_sum hf_absVal_alt,
      hf_absVal_alt_eq]
  let hf_sub_abs : Sec4RepAbsAt (g.sub f.absVal) x :=
    sec4_sub_absSeriesSum_fwd
      ⟨hg2Dom, hg2_abs⟩ ⟨hfAbsValDom, hf_absVal_abs⟩
  let hf_sub_sum : RSeq.SeriesSum
      (fun k => (g.sub f.absVal).valueAt x hf_sub_abs.fst k) :=
    add_seriesSum_value hg2Dom (IntegrableRep.neg_memAt hfAbsValDom)
      hg2_sum (neg_seriesSum_value hfAbsValDom hf_absVal_sum)
  have hf_nonneg := hf_dom x hf_sub_abs.fst hf_sub_abs.snd hf_sub_sum
  have hf_abs_le_g : Le (COF.abs hf_sum.sum) hg2_sum.sum := by
    have hle_absVal : Le hf_absVal_sum.sum hg2_sum.sum :=
      le_of_nonneg_sub (by
        rw [show hg2_sum.sum - hf_absVal_sum.sum =
            hg2_sum.sum + -hf_absVal_sum.sum from by ring]
        exact hf_nonneg)
    rwa [← hf_absVal_sum_eq]
  have herr_le_abs_sum :
      Le herr_sum.sum (COF.abs hfn_sum.sum + COF.abs hf_sum.sum) := by
    rw [herr_eq]
    exact abs_sub_le hfn_sum.sum hf_sum.sum
  have herr_le_twoG :
      Le herr_sum.sum (hg1_sum.sum + hg2_sum.sum) :=
    le_trans herr_le_abs_sum (le_add hfn_abs_le_g hf_abs_le_g)
  rw [hx_eq]
  change Nonneg ((hg1_sum.sum + hg2_sum.sum) + -herr_sum.sum)
  rw [show (hg1_sum.sum + hg2_sum.sum) + -herr_sum.sum =
      (hg1_sum.sum + hg2_sum.sum) - herr_sum.sum from by ring]
  exact nonneg_sub_of_le herr_le_twoG


/-- Source-shaped choice data with the printed proof's actual majorant `2g`.

This is the closest current interface to Bishop--Cheng's displayed argument:
the majorant is no longer an arbitrary `majorant`, but exactly `g.add g`.
The remaining explicit frontiers are precisely the facts that the printed text
uses without expanding:

* `|f_n - f| <= 2g`;
* the chosen tail satisfies `I_{-A}(2g) < epsNeg`;
* the row-seed bridge exists for the `2g` relative integral.
-/
structure Lemma415TwoGChoiceSourceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g) (eps : R) : Type _ where
  twoGSeeds :
    Sec4Prop42RowSeedTools (S := S) (g.add g)
      (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  dominatesErrorByTwoG : forall n,
    RepNonneg
      ((g.add g).sub (thm_4_15_abs_error (S := S) fn f n))
  twoGNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          (g.add g)
          (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg))
        epsNeg


/-- The same source-shaped choice/tail data after the printed domination
`|f_n-f| <= 2g` has been discharged separately from `|f_n| <= g` and
`|f| <= g`. -/
structure Lemma415TwoGTailChoiceSourceData
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R) :
    Type _ where
  twoGSeeds :
    Sec4Prop42RowSeedTools (S := S) (g.add g)
      (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  twoGNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          (g.add g)
          (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg))
        epsNeg


/-- Source-shaped choice data one step closer to the printed proof's wording:
the small tail is supplied for `g`, then transported to `2g = g + g`. -/
structure Lemma415GSingleTailChoiceSourceData
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R) :
    Type _ where
  gSeeds :
    Sec4Prop42RowSeedTools (S := S) g g_nonneg
  twoGSeeds :
    Sec4Prop42RowSeedTools (S := S) (g.add g)
      (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsG : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  gTailBudget : COF.lt (epsG + epsG) epsNeg
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  gNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          g g_nonneg)
        epsG


/-- Source-shaped single-`g` tail data with no row-seed requirement for `2g`.

This keeps exactly the source choice `I_{-A}(g)` small.  The conversion below
uses the complement expression and additivity to obtain the `2g` tail estimate
without constructing `Sec4Prop42RowSeedTools` for `g.add g`. -/
structure Lemma415GSingleTailRelChoiceSourceData
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R) :
    Type _ where
  gSeeds :
    Sec4Prop42RowSeedTools (S := S) g g_nonneg
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsG : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  gTailBudget : COF.lt (epsG + epsG) epsNeg
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  gNegSmall :
      COF.lt
        (genRelIntegral_from_measurable (BSet.neg A)
          (isMeasurableSet_neg_of_integrable (S := S) hA)
          g g_nonneg)
        epsG


/-- Source-shaped single-`g` tail data when the tail smallness is supplied in
the previous complement-expression form.

This is the form closest to the preceding source machinery: theorem 4.13 and
lemma 4.3 naturally produce tails as `g - chi_A*g`.  The conversion below
identifies that expression with the direct measurable `I_{-A}(g)` used by the
current 4.15 assembly. -/
structure Lemma415GComplementTailRelChoiceSourceData
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R) :
    Type _ where
  gSeeds :
    Sec4Prop42RowSeedTools (S := S) g g_nonneg
  A : BSet X
  hA : IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsG : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  gTailBudget : COF.lt (epsG + epsG) epsNeg
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  gComplementSmall :
      COF.lt
        ((g.sub (prop_4_2_chi_f_rep A hA g g_nonneg)).integral)
        epsG


/-- The epsilon bookkeeping used by the source proof of theorem 4.15 after
the set `A` has been chosen.

The analytic choice of `A` is handled separately; this record keeps only the
source's later budget inequalities. -/
structure Lemma415TailBudgetSourceData (eps : R) : Type _ where
  N : Nat
  N_ge_one : 1 <= N
  epsAB : R
  epsG : R
  epsNeg : R
  epsAB_pos : COF.lt 0 epsAB
  epsG_pos : COF.lt 0 epsG
  gTailBudget : COF.lt (epsG + epsG) epsNeg
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps


/-- Canonical epsilon bookkeeping for theorem 4.15.

This is the source proof's `1/4`-style budget written with the existing
`halfPow` scale: `epsAB = epsNeg = 2^{-2} eps` and `epsG = 2^{-4} eps`.
It removes a purely numeric frontier from the later `coverSet` endpoints. -/
noncomputable def lemma_4_15_default_tail_budget
    (eps : R) (heps : COF.lt 0 eps) :
    Lemma415TailBudgetSourceData (R := R) eps where
  N := 1
  N_ge_one := Nat.le_refl 1
  epsAB := COF.halfPow (R := R) 2 * eps
  epsG := COF.halfPow (R := R) 4 * eps
  epsNeg := COF.halfPow (R := R) 2 * eps
  epsAB_pos := COFO.mul_pos (halfPow_pos (R := R) 2) heps
  epsG_pos := COFO.mul_pos (halfPow_pos (R := R) 4) heps
  gTailBudget := by
    have hscale :
        COF.lt (COF.halfPow (R := R) 3 * eps)
          (COF.halfPow (R := R) 2 * eps) :=
      lemma33_mul_lt_mul_right (halfPow_lt_succ (R := R) 2) heps
    have hdouble :
        COF.halfPow (R := R) 4 * eps + COF.halfPow (R := R) 4 * eps =
          COF.halfPow (R := R) 3 * eps := by
      calc
        COF.halfPow (R := R) 4 * eps + COF.halfPow (R := R) 4 * eps
            = (COF.halfPow (R := R) 4 + COF.halfPow (R := R) 4) * eps := by
              ring
        _ = COF.halfPow (R := R) 3 * eps := by
              rw [show COF.halfPow (R := R) 4 + COF.halfPow (R := R) 4 =
                COF.halfPow (R := R) 3 from by
                  simpa using (halfPow_succ_add (R := R) 3)]
    rwa [hdouble]
  pieces_sum_lt := by
    have hscale :
        COF.lt (COF.halfPow (R := R) 1 * eps)
          (COF.halfPow (R := R) 0 * eps) :=
      lemma33_mul_lt_mul_right (halfPow_lt_succ (R := R) 0) heps
    have hscale' : COF.lt (COF.halfPow (R := R) 1 * eps) eps := by
      rw [show COF.halfPow (R := R) 0 = (1 : R) from rfl, one_mul] at hscale
      exact hscale
    have hdouble :
        COF.halfPow (R := R) 2 * eps + COF.halfPow (R := R) 2 * eps =
          COF.halfPow (R := R) 1 * eps := by
      calc
        COF.halfPow (R := R) 2 * eps + COF.halfPow (R := R) 2 * eps
            = (COF.halfPow (R := R) 2 + COF.halfPow (R := R) 2) * eps := by
              ring
        _ = COF.halfPow (R := R) 1 * eps := by
              rw [show COF.halfPow (R := R) 2 + COF.halfPow (R := R) 2 =
                COF.halfPow (R := R) 1 from by
                  simpa using (halfPow_succ_add (R := R) 1)]
    rwa [hdouble]


/-- The previous complement-expression tail value `I(g - chi_A*g)`. -/
noncomputable def lemma_4_15_g_complement_tail_value
    (g : IntegrableRep S) (g_nonneg : RepNonneg g)
    (A : BSet X) (hA : IntegrableSet1 S A) : R :=
  ((g.sub (prop_4_2_chi_f_rep A hA g g_nonneg)).integral)


/-- Choose one set from a complement-tail sequence.

This is the exact modulus step hidden in the source phrase "as in the proof of
theorem 4.13": once a sequence of complement tails tends to zero, choose an
index whose tail is below the requested `epsG`.  The remaining budget fields
belong to theorem 4.15's later split estimate, so they stay explicit. -/
noncomputable def
    lemma_4_15_g_complement_tail_rel_choice_data_from_tail_sequence
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (Aseq : Nat -> BSet X)
    (hAseq : forall n, IntegrableSet1 S (Aseq n))
    (tailTendsto :
      RSeq.TendstoHalf
        (fun n =>
          lemma_4_15_g_complement_tail_value
            (S := S) g g_nonneg (Aseq n) (hAseq n))
        0)
    (N : Nat) (N_ge_one : 1 <= N)
    (epsAB epsG epsNeg : R)
    (epsAB_pos : COF.lt 0 epsAB)
    (epsG_pos : COF.lt 0 epsG)
    (gTailBudget : COF.lt (epsG + epsG) epsNeg)
    (pieces_sum_lt : COF.lt (epsAB + epsNeg) eps) :
    Lemma415GComplementTailRelChoiceSourceData (S := S) g g_nonneg eps where
  gSeeds := gSeeds
  A :=
    Aseq
      (tailTendsto.mod
        (COFO.archimedean_pos epsG epsG_pos).1)
  hA :=
    hAseq
      (tailTendsto.mod
        (COFO.archimedean_pos epsG epsG_pos).1)
  N := N
  N_ge_one := N_ge_one
  epsAB := epsAB
  epsG := epsG
  epsNeg := epsNeg
  epsAB_pos := epsAB_pos
  gTailBudget := gTailBudget
  pieces_sum_lt := pieces_sum_lt
  gComplementSmall := by
    let k : Nat := (COFO.archimedean_pos epsG epsG_pos).1
    let m : Nat := tailTendsto.mod k
    have hk : COF.lt (COF.halfPow (R := R) k) epsG :=
      (COFO.archimedean_pos epsG epsG_pos).2
    have hclose :
        COF.lt
          (COF.abs
            (lemma_4_15_g_complement_tail_value
              (S := S) g g_nonneg (Aseq m) (hAseq m) - 0))
          (COF.halfPow (R := R) k) :=
      tailTendsto.close k m (Nat.le_refl m)
    have htail_le_abs :
        Le
          (lemma_4_15_g_complement_tail_value
            (S := S) g g_nonneg (Aseq m) (hAseq m))
          (COF.abs
            (lemma_4_15_g_complement_tail_value
              (S := S) g g_nonneg (Aseq m) (hAseq m) - 0)) := by
      rw [sub_zero]
      exact COFO.le_abs_self
        (lemma_4_15_g_complement_tail_value
          (S := S) g g_nonneg (Aseq m) (hAseq m))
    have hsmall :
        COF.lt
          (lemma_4_15_g_complement_tail_value
            (S := S) g g_nonneg (Aseq m) (hAseq m))
          epsG :=
      COFO.lt_trans (lt_of_le_of_lt htail_le_abs hclose) hk
    simpa [lemma_4_15_g_complement_tail_value] using hsmall


/-- The concrete theorem-4.13/lemma-4.3 style cover sets give complement
tails tending to zero.

`coverSet_tendsto` says `I_{A_n}(g) -> I(g)`.  The complement identity
`I_A(g) + I(g - chi_A*g) = I(g)` rewrites this as
`I(g - chi_A*g) -> 0`, which is the previous complement-expression form used by
the source proof of theorem 4.15. -/
noncomputable def lemma_4_15_g_complement_tail_sequence_from_coverSet
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) :
    RSeq.TendstoHalf
      (fun n =>
        lemma_4_15_g_complement_tail_value
          (S := S) g g_nonneg (coverSet g n) (coverSet_int g n))
      0 := by
  have hcover := coverSet_tendsto (S := S) g g_nonneg
  exact {
    mod := hcover.mod
    close := by
      intro k n hn
      have hclose := hcover.close k n hn
      have hadd :
          relIntegral (coverSet g n) (coverSet_int g n) g g_nonneg
            + (g.sub
                (prop_4_2_chi_f_rep
                  (coverSet g n) (coverSet_int g n) g g_nonneg)).integral
            = g.integral :=
        relIntegral_complement_additive
          (coverSet g n) (coverSet_int g n) g g_nonneg
      have htail_eq :
          lemma_4_15_g_complement_tail_value
              (S := S) g g_nonneg (coverSet g n) (coverSet_int g n)
            = g.integral
                - relIntegral (coverSet g n) (coverSet_int g n) g g_nonneg := by
        unfold lemma_4_15_g_complement_tail_value
        rw [← hadd]
        ring
      change COF.lt
        (COF.abs
          (lemma_4_15_g_complement_tail_value
            (S := S) g g_nonneg (coverSet g n) (coverSet_int g n) - 0))
        (COF.halfPow (R := R) k)
      rw [htail_eq]
      have habs :
          COF.abs
              ((g.integral
                    - relIntegral (coverSet g n) (coverSet_int g n) g g_nonneg)
                - 0)
            =
          COF.abs
              (relIntegral (coverSet g n) (coverSet_int g n) g g_nonneg
                - g.integral) := by
        have e :
            (g.integral
                - relIntegral (coverSet g n) (coverSet_int g n) g g_nonneg)
              - 0
            =
            - (relIntegral (coverSet g n) (coverSet_int g n) g g_nonneg
                - g.integral) := by
          ring
        rw [e, COFO.abs_neg]
      rw [habs]
      exact hclose
  }


/-- Fully concrete source bridge for the set-selection line of theorem 4.15:
use the `coverSet` sequence of §4 and choose one member whose complement
`g`-tail is below the requested budget. -/
noncomputable def
    lemma_4_15_g_complement_tail_rel_choice_data_from_coverSet
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (N : Nat) (N_ge_one : 1 <= N)
    (epsAB epsG epsNeg : R)
    (epsAB_pos : COF.lt 0 epsAB)
    (epsG_pos : COF.lt 0 epsG)
    (gTailBudget : COF.lt (epsG + epsG) epsNeg)
    (pieces_sum_lt : COF.lt (epsAB + epsNeg) eps) :
    Lemma415GComplementTailRelChoiceSourceData (S := S) g g_nonneg eps :=
  lemma_4_15_g_complement_tail_rel_choice_data_from_tail_sequence
    (S := S) g g_nonneg eps gSeeds
    (fun n => coverSet g n)
    (fun n => coverSet_int g n)
    (lemma_4_15_g_complement_tail_sequence_from_coverSet
      (S := S) g g_nonneg)
    N N_ge_one epsAB epsG epsNeg epsAB_pos epsG_pos
    gTailBudget pieces_sum_lt


/-- The same concrete cover-set bridge, with theorem-4.15 epsilon
bookkeeping packaged as source budget data. -/
noncomputable def
    lemma_4_15_g_complement_tail_rel_choice_data_from_coverSetBudget
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (B : Lemma415TailBudgetSourceData (R := R) eps) :
    Lemma415GComplementTailRelChoiceSourceData (S := S) g g_nonneg eps :=
  lemma_4_15_g_complement_tail_rel_choice_data_from_coverSet
    (S := S) g g_nonneg eps gSeeds
    B.N B.N_ge_one B.epsAB B.epsG B.epsNeg
    B.epsAB_pos B.epsG_pos B.gTailBudget B.pieces_sum_lt


/-- Convert complement-expression `g`-tail data into the direct measurable
`I_{-A}(g)` tail data consumed by the current 4.15 source assembly. -/
noncomputable def
    lemma_4_15_g_single_tail_rel_choice_source_data_from_g_complement_tail_data
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R)
    (D : Lemma415GComplementTailRelChoiceSourceData (S := S) g g_nonneg eps) :
    Lemma415GSingleTailRelChoiceSourceData (S := S) g g_nonneg eps where
  gSeeds := D.gSeeds
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  epsAB := D.epsAB
  epsG := D.epsG
  epsNeg := D.epsNeg
  epsAB_pos := D.epsAB_pos
  gTailBudget := D.gTailBudget
  pieces_sum_lt := D.pieces_sum_lt
  gNegSmall := by
    rw [sec4_genRelIntegral_eq_complement_of_rowSeedTools
      (S := S) D.A D.hA g g_nonneg D.gSeeds]
    exact D.gComplementSmall


/-- Convert a source `g`-tail choice into the `2g` tail-choice interface. -/
noncomputable def
    lemma_4_15_two_g_tail_choice_source_data_from_g_single_tail_choice_data
    (g : IntegrableRep S) (g_nonneg : RepNonneg g) (eps : R)
    (D : Lemma415GSingleTailChoiceSourceData (S := S) g g_nonneg eps) :
    Lemma415TwoGTailChoiceSourceData (S := S) g g_nonneg eps where
  twoGSeeds := D.twoGSeeds
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  epsAB_pos := D.epsAB_pos
  pieces_sum_lt := D.pieces_sum_lt
  twoGNegSmall :=
    thm_4_15_two_g_neg_small_from_g_neg_small
      (S := S) D.A D.hA g g_nonneg
      D.gSeeds D.twoGSeeds D.epsG D.epsNeg
      D.gNegSmall D.gTailBudget


/-- Fill the `|f_n-f| <= 2g` field in the source `2g` choice data from the
two domination hypotheses `|f_n| <= g` and `|f| <= g`. -/
noncomputable def lemma_4_15_two_g_choice_source_data_from_tail_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (eps : R)
    (D : Lemma415TwoGTailChoiceSourceData (S := S) g g_nonneg eps) :
    Lemma415TwoGChoiceSourceData (S := S) fn f g g_nonneg eps where
  twoGSeeds := D.twoGSeeds
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  epsAB_pos := D.epsAB_pos
  pieces_sum_lt := D.pieces_sum_lt
  dominatesErrorByTwoG :=
    thm_4_15_abs_error_dominated_by_two_g
      (S := S) fn f g hfn_dom hf_dom
  twoGNegSmall := D.twoGNegSmall


/-- Forget that the source majorant is specifically `2g`, yielding the general
majorant-choice interface used by the completed split proof. -/
noncomputable def lemma_4_15_majorant_choice_source_data_from_two_g_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g) (eps : R)
    (D : Lemma415TwoGChoiceSourceData
      (S := S) fn f g g_nonneg eps) :
    Lemma415MajorantChoiceSourceData
      (S := S) fn f (g.add g)
      (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg) eps where
  majorantSeeds := D.twoGSeeds
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  epsAB_pos := D.epsAB_pos
  pieces_sum_lt := D.pieces_sum_lt
  dominatesError := D.dominatesErrorByTwoG
  majorantNegSmall := D.twoGNegSmall


/-- Use absolute continuity of the majorant integral to generate the
`A∧B` part of the source split estimate. -/
noncomputable def
    lemma_4_15_majorant_split_uniform_source_data_from_choice_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R)
    (D : Lemma415MajorantChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps) :
    Lemma415MajorantSplitUniformSourceData
      (S := S) fn f majorant majorant_nonneg eps where
  majorantSeeds := D.majorantSeeds
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := (relIntegral_abs_continuous_delta
    (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos).1
  delta_pos := (relIntegral_abs_continuous_delta
    (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos).2.1
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  pieces_sum_lt := D.pieces_sum_lt
  dominatesError := D.dominatesError
  majorantABSmall := by
    intro B hB hmu
    let H := relIntegral_abs_continuous_delta
      (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos
    have hsmallRel : COF.lt
        (relIntegral (BSet.and D.A B) (hB D.A D.hA)
          majorant majorant_nonneg)
        D.epsAB :=
      H.2.2 (BSet.and D.A B) (hB D.A D.hA) hmu
    rw [sec4_genRelIntegral_eq_relIntegral_of_rowSeedTools
      (BSet.and D.A B) (hB D.A D.hA)
      majorant majorant_nonneg D.majorantSeeds]
    exact hsmallRel
  majorantNegSmall := D.majorantNegSmall


/-- Convert the source proof's majorant estimate into the explicit split data.

This formalizes the source chain

`I_{A∧B}(|f_n-f|)+I_{-A}(|f_n-f|)
  <= I_{A∧B}(majorant)+I_{-A}(majorant)`.

For theorem 4.15, `majorant` is `2g`. -/
noncomputable def lemma_4_15_split_uniform_source_data_from_majorant_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R)
    (D : Lemma415MajorantSplitUniformSourceData
      (S := S) fn f majorant majorant_nonneg eps) :
    Lemma415SplitUniformSourceData (S := S) fn f eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := D.delta
  delta_pos := D.delta_pos
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  pieces_sum_lt := D.pieces_sum_lt
  pieceBounds := by
    intro n _hn B hB hmu
    let u : IntegrableRep S := thm_4_15_abs_error (S := S) fn f n
    let hnn_u : RepNonneg u :=
      thm_4_15_abs_error_nonneg (S := S) fn f n
    let Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u := hSeeds n
    let VB : Sec4GenIBValueBridge (S := S) B hB u hnn_u :=
      sec4_genIBValueBridge_of_rowSeedTools B hB u hnn_u Tu
    let VAB : Sec4GenIBValueBridge (S := S) (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA)) u hnn_u :=
      sec4_genIBValueBridge_of_rowSeedTools
        (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        u hnn_u Tu
    let VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA) u hnn_u :=
      sec4_genIBValueBridge_of_rowSeedTools
        (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        u hnn_u Tu
    have hAB_le : Le
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          majorant majorant_nonneg) :=
      genRelIntegral_from_measurable_mono_integrand_of_rowSeeds
        (S := S)
        (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        u majorant hnn_u majorant_nonneg Tu D.majorantSeeds
        (D.dominatesError n)
    have hNeg_le : Le
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          majorant majorant_nonneg) :=
      genRelIntegral_from_measurable_mono_integrand_of_rowSeeds
        (S := S)
        (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        u majorant hnn_u majorant_nonneg Tu D.majorantSeeds
        (D.dominatesError n)
    have hAB_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        D.epsAB :=
      lt_of_le_of_lt hAB_le (D.majorantABSmall B hB hmu)
    have hNeg_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        D.epsNeg :=
      lt_of_le_of_lt hNeg_le D.majorantNegSmall
    exact ⟨VB, VAB, VnegA, hAB_lt, hNeg_lt⟩


/-- Convert the source choice/tail data into the explicit split data, with
absolute continuity supplying the `A∧B` majorant estimate. -/
noncomputable def lemma_4_15_split_uniform_source_data_from_majorant_choice_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R)
    (D : Lemma415MajorantChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps) :
    Lemma415SplitUniformSourceData (S := S) fn f eps :=
  lemma_4_15_split_uniform_source_data_from_majorant_data
    (S := S) fn f hSeeds majorant majorant_nonneg eps
    (lemma_4_15_majorant_split_uniform_source_data_from_choice_data
      (S := S) fn f majorant majorant_nonneg eps D)


/-- Convert the source proof's majorant estimate into split data without
row-seed data for the majorant.

The error side still uses direct `genIB` value bridges, supplied by `hSeeds`.
The majorant side is kept on ordinary `relIntegral` for `A∧B` and on the old
complement expression for `-A`. -/
noncomputable def
    lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R)
    (D : Lemma415MajorantRelChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps) :
    Lemma415SplitUniformSourceData (S := S) fn f eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := (relIntegral_abs_continuous_delta
    (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos).1
  delta_pos := (relIntegral_abs_continuous_delta
    (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos).2.1
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  pieces_sum_lt := D.pieces_sum_lt
  pieceBounds := by
    intro n _hn B hB hmu
    let u : IntegrableRep S := thm_4_15_abs_error (S := S) fn f n
    let hnn_u : RepNonneg u :=
      thm_4_15_abs_error_nonneg (S := S) fn f n
    let Tu : Sec4Prop42RowSeedTools (S := S) u hnn_u := hSeeds n
    let VB : Sec4GenIBValueBridge (S := S) B hB u hnn_u :=
      sec4_genIBValueBridge_of_rowSeedTools B hB u hnn_u Tu
    let VAB : Sec4GenIBValueBridge (S := S) (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA)) u hnn_u :=
      sec4_genIBValueBridge_of_rowSeedTools
        (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        u hnn_u Tu
    let VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA) u hnn_u :=
      sec4_genIBValueBridge_of_rowSeedTools
        (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        u hnn_u Tu
    let H := relIntegral_abs_continuous_delta
      (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos
    have hAB_majorant_small : COF.lt
        (relIntegral (BSet.and D.A B) (hB D.A D.hA)
          majorant majorant_nonneg)
        D.epsAB :=
      H.2.2 (BSet.and D.A B) (hB D.A D.hA) hmu
    have hAB_le : Le
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        (relIntegral (BSet.and D.A B) (hB D.A D.hA)
          majorant majorant_nonneg) :=
      genRelIntegral_from_measurable_le_relIntegral_of_rowSeeds
        (S := S)
        (BSet.and D.A B)
        (hB D.A D.hA)
        u majorant hnn_u majorant_nonneg Tu (D.dominatesError n)
    have hNeg_le : Le
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        ((majorant.sub
          (prop_4_2_chi_f_rep D.A D.hA majorant majorant_nonneg)).integral) :=
      genRelIntegral_neg_le_complementIntegral_of_rowSeeds
        (S := S) D.A D.hA
        u majorant hnn_u majorant_nonneg Tu (D.dominatesError n)
    have hAB_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        D.epsAB :=
      lt_of_le_of_lt hAB_le hAB_majorant_small
    have hNeg_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        D.epsNeg :=
      lt_of_le_of_lt hNeg_le D.majorantNegSmall
    exact ⟨VB, VAB, VnegA, hAB_lt, hNeg_lt⟩


/-- Remaining-atoms version of
`lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data`.

The majorant side is unchanged; the error-side direct `genIB` value bridges
come from `Sec4Prop42RemainingAtomTools` instead of row seeds. -/
noncomputable def
    lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data_of_atoms
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (eps : R)
    (D : Lemma415MajorantRelChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps) :
    Lemma415SplitUniformSourceData (S := S) fn f eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := (relIntegral_abs_continuous_delta
    (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos).1
  delta_pos := (relIntegral_abs_continuous_delta
    (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos).2.1
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  pieces_sum_lt := D.pieces_sum_lt
  pieceBounds := by
    intro n _hn B hB hmu
    let u : IntegrableRep S := thm_4_15_abs_error (S := S) fn f n
    let hnn_u : RepNonneg u :=
      thm_4_15_abs_error_nonneg (S := S) fn f n
    let Tu : Sec4Prop42RemainingAtomTools (S := S) u hnn_u := hAtoms n
    let VB : Sec4GenIBValueBridge (S := S) B hB u hnn_u :=
      sec4_genIBValueBridge_of_remainingAtoms B hB u hnn_u Tu
    let VAB : Sec4GenIBValueBridge (S := S) (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA)) u hnn_u :=
      sec4_genIBValueBridge_of_remainingAtoms
        (BSet.and D.A B)
        (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
        u hnn_u Tu
    let VnegA : Sec4GenIBValueBridge (S := S) (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA) u hnn_u :=
      sec4_genIBValueBridge_of_remainingAtoms
        (BSet.neg D.A)
        (isMeasurableSet_neg_of_integrable (S := S) D.hA)
        u hnn_u Tu
    let H := relIntegral_abs_continuous_delta
      (S := S) majorant majorant_nonneg D.epsAB D.epsAB_pos
    have hAB_majorant_small : COF.lt
        (relIntegral (BSet.and D.A B) (hB D.A D.hA)
          majorant majorant_nonneg)
        D.epsAB :=
      H.2.2 (BSet.and D.A B) (hB D.A D.hA) hmu
    have hAB_le : Le
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        (relIntegral (BSet.and D.A B) (hB D.A D.hA)
          majorant majorant_nonneg) :=
      genRelIntegral_from_measurable_le_relIntegral_of_remainingAtoms
        (S := S)
        (BSet.and D.A B)
        (hB D.A D.hA)
        u majorant hnn_u majorant_nonneg Tu (D.dominatesError n)
    have hNeg_le : Le
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        ((majorant.sub
          (prop_4_2_chi_f_rep D.A D.hA majorant majorant_nonneg)).integral) :=
      genRelIntegral_neg_le_complementIntegral_of_remainingAtoms
        (S := S) D.A D.hA
        u majorant hnn_u majorant_nonneg Tu (D.dominatesError n)
    have hAB_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.and D.A B)
          (isMeasurableSet_of_integrable (S := S) (hB D.A D.hA))
          u hnn_u)
        D.epsAB :=
      lt_of_le_of_lt hAB_le hAB_majorant_small
    have hNeg_lt : COF.lt
        (genRelIntegral_from_measurable (BSet.neg D.A)
          (isMeasurableSet_neg_of_integrable (S := S) D.hA)
          u hnn_u)
        D.epsNeg :=
      lt_of_le_of_lt hNeg_le D.majorantNegSmall
    exact ⟨VB, VAB, VnegA, hAB_lt, hNeg_lt⟩


/-- Convert theorem 4.15's displayed split estimate into the source-form
uniform-`I_B` hypothesis of lemma 4.14. -/
noncomputable def lemma_4_15_uniform_ib_source_data_from_split_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (eps : R) (D : Lemma415SplitUniformSourceData (S := S) fn f eps) :
    Lemma414UniformIBSourceData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (thm_4_15_abs_error_ib_from_rowSeeds (S := S) fn f hSeeds)
      eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := D.delta
  delta_pos := D.delta_pos
  small := by
    intro n hn B hB hmu
    obtain ⟨VB, VAB, VnegA, hAB, hNeg⟩ :=
      D.pieceBounds n hn B hB hmu
    change COF.lt
      (genRelIntegral_from_measurable B hB
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
      eps
    exact thm_4_15_genIB_split_lt_of_piece_bounds
      (S := S) D.A B D.hA hB
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
      VB VAB VnegA D.epsAB D.epsNeg eps hAB hNeg D.pieces_sum_lt


/-- Remaining-atoms version of
`lemma_4_15_uniform_ib_source_data_from_split_data`. -/
noncomputable def lemma_4_15_uniform_ib_source_data_from_split_data_of_atoms
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (eps : R) (D : Lemma415SplitUniformSourceData (S := S) fn f eps) :
    Lemma414UniformIBSourceData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (lemma_4_14_ib_interface_from_genIB_remainingAtoms
        (S := S)
        (thm_4_15_abs_error (S := S) fn f)
        (thm_4_15_abs_error_nonneg (S := S) fn f)
        hAtoms)
      eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := D.delta
  delta_pos := D.delta_pos
  small := by
    intro n hn B hB hmu
    obtain ⟨VB, VAB, VnegA, hAB, hNeg⟩ :=
      D.pieceBounds n hn B hB hmu
    change COF.lt
      (genRelIntegral_from_measurable B hB
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
      eps
    exact thm_4_15_genIB_split_lt_of_piece_bounds
      (S := S) D.A B D.hA hB
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
      VB VAB VnegA D.epsAB D.epsNeg eps hAB hNeg D.pieces_sum_lt


/-- Assemble the source-complete 4.15 abs-error data from the displayed split
estimate and convergence in measure of the error sequence. -/
noncomputable def Lemma415AbsErrorSourceData.of_splitUniformData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f where
  rowSeeds := hSeeds
  uniform := fun eps heps =>
    lemma_4_15_uniform_ib_source_data_from_split_data
      (S := S) fn f hSeeds eps (hSplit eps heps)
  converge := hconv


/-- Assemble the source-complete 4.15 abs-error data from a generic
Proposition 4.2 row-seed provider and displayed split data.

This is the row-seed-provider analogue of `of_splitUniformData`: the provider
is specialized only to the theorem-4.15 abs-error sequence. -/
noncomputable def Lemma415AbsErrorSourceData.of_rowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  let hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n) :=
    fun n =>
      Lemma415Prop42RowSeedToolsProvider.rowSeeds P
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)
  Lemma415AbsErrorSourceData.of_splitUniformData
    (S := S) fn f hSeeds hSplit hconv

/-- Assemble the source-complete 4.15 abs-error data from the source majorant
estimate, by first converting it to split-uniform data. -/
noncomputable def Lemma415AbsErrorSourceData.of_majorantSplitUniformData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hMajorant : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantSplitUniformSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_splitUniformData
    (S := S) fn f hSeeds
    (fun eps heps =>
      lemma_4_15_split_uniform_source_data_from_majorant_data
        (S := S) fn f hSeeds majorant majorant_nonneg eps
        (hMajorant eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from source choice/tail
data, using absolute continuity for the `A∧B` estimate. -/
noncomputable def Lemma415AbsErrorSourceData.of_majorantChoiceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hChoice : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantChoiceSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_splitUniformData
    (S := S) fn f hSeeds
    (fun eps heps =>
      lemma_4_15_split_uniform_source_data_from_majorant_choice_data
        (S := S) fn f hSeeds majorant majorant_nonneg eps
        (hChoice eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from majorant choice data
that does not require row-seed data for the majorant. -/
noncomputable def Lemma415AbsErrorSourceData.of_majorantRelChoiceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hChoice : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantRelChoiceSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_splitUniformData
    (S := S) fn f hSeeds
    (fun eps heps =>
      lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data
        (S := S) fn f hSeeds majorant majorant_nonneg eps
        (hChoice eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from the printed
`2g` choice/tail data. -/
noncomputable def Lemma415AbsErrorSourceData.of_twoGChoiceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hTwoG : forall (eps : R), COF.lt 0 eps ->
      Lemma415TwoGChoiceSourceData
        (S := S) fn f g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_majorantChoiceData
    (S := S) fn f hSeeds (g.add g)
    (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
    (fun eps heps =>
      lemma_4_15_majorant_choice_source_data_from_two_g_choice_data
        (S := S) fn f g g_nonneg eps (hTwoG eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from `2g` tail-choice
data, deriving the displayed domination `|f_n-f| <= 2g` from
`|f_n| <= g` and `|f| <= g`. -/
noncomputable def Lemma415AbsErrorSourceData.of_twoGTailChoiceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415TwoGTailChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_twoGChoiceData
    (S := S) fn f g g_nonneg hSeeds
    (fun eps heps =>
      lemma_4_15_two_g_choice_source_data_from_tail_choice_data
        (S := S) fn f g g_nonneg hfn_dom hf_dom eps (hTail eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from source-shaped
single-`g` tail data.  This derives both `I_{-A}(2g)` from `I_{-A}(g)` and
`|f_n-f| <= 2g` from the two domination hypotheses. -/
noncomputable def Lemma415AbsErrorSourceData.of_gSingleTailChoiceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GSingleTailChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_twoGTailChoiceData
    (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds
    (fun eps heps =>
      lemma_4_15_two_g_tail_choice_source_data_from_g_single_tail_choice_data
        (S := S) g g_nonneg eps (hGTail eps heps))
    hconv


/-- Convert single-`g` tail data into the row-seed-free `2g` majorant choice
interface. -/
noncomputable def
    lemma_4_15_majorant_rel_choice_source_data_from_g_single_tail_rel_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (eps : R)
    (D : Lemma415GSingleTailRelChoiceSourceData (S := S) g g_nonneg eps) :
    Lemma415MajorantRelChoiceSourceData
      (S := S) fn f (g.add g)
      (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg) eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  epsAB_pos := D.epsAB_pos
  pieces_sum_lt := D.pieces_sum_lt
  dominatesError :=
    thm_4_15_abs_error_dominated_by_two_g
      (S := S) fn f g hfn_dom hf_dom
  majorantNegSmall :=
    thm_4_15_two_g_complement_small_from_g_neg_small
      (S := S) D.A D.hA g g_nonneg D.gSeeds
      D.epsG D.epsNeg D.gNegSmall D.gTailBudget


/-- Assemble the source-complete 4.15 abs-error data from single-`g` tail
data, without requiring row-seed data for `2g`. -/
noncomputable def Lemma415AbsErrorSourceData.of_gSingleTailRelChoiceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GSingleTailRelChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_majorantRelChoiceData
    (S := S) fn f hSeeds (g.add g)
    (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
    (fun eps heps =>
      lemma_4_15_majorant_rel_choice_source_data_from_g_single_tail_rel_choice_data
        (S := S) fn f g g_nonneg hfn_dom hf_dom eps (hGTail eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from complement-tail
single-`g` data.

This wrapper is the theorem-4.13-facing entry point: the caller may supply
`I(g - chi_A*g) < epsG`, and the preceding bridge converts it to the direct
measurable `I_{-A}(g)` form before the existing source assembly continues. -/
noncomputable def Lemma415AbsErrorSourceData.of_gComplementTailRelChoiceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GComplementTailRelChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_gSingleTailRelChoiceData
    (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds
    (fun eps heps =>
      lemma_4_15_g_single_tail_rel_choice_source_data_from_g_complement_tail_data
        (S := S) g g_nonneg eps (hGTail eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from the concrete
`coverSet` complement-tail construction.

This closes the source line "as in theorem 4.13 choose an integrable set
`A` with small `I_{-A}(g)`" up to the explicit epsilon budget data. -/
noncomputable def Lemma415AbsErrorSourceData.of_gCoverSetTailBudgetData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  Lemma415AbsErrorSourceData.of_gComplementTailRelChoiceData
    (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds
    (fun eps heps =>
      lemma_4_15_g_complement_tail_rel_choice_data_from_coverSetBudget
        (S := S) g g_nonneg eps gSeeds (hBudget eps heps))
    hconv


/-- Assemble the source-complete 4.15 abs-error data from the concrete
`coverSet` complement-tail construction and a generic Proposition 4.2
row-seed provider. -/
noncomputable def Lemma415AbsErrorSourceData.of_gCoverSetTailBudgetRowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorSourceData (S := S) fn f :=
  let hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n) :=
    fun n =>
      Lemma415Prop42RowSeedToolsProvider.rowSeeds P
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)
  Lemma415AbsErrorSourceData.of_gCoverSetTailBudgetData
    (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds
    gSeeds hBudget hconv

/-- Assemble the remaining-atoms 4.15 abs-error data from displayed split
data and convergence in measure of the error sequence. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_splitUniformData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f where
  atoms := hAtoms
  uniform := fun eps heps =>
    lemma_4_15_uniform_ib_source_data_from_split_data_of_atoms
      (S := S) fn f hAtoms eps (hSplit eps heps)
  converge := hconv


/-- Assemble remaining-atoms abs-error data from the named theorem-4.15 atom
frontier. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (F : Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_splitUniformData
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.toAtoms (S := S) fn f F)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from the three separated Step 2b
frontiers. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_splitAtomFrontiers
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Fabs : Lemma415AbsErrorFAbsRowsS1Frontier (S := S) fn f)
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_splitFrontiers
      (S := S) fn f Fabs Ps1 Ps2)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data when the Step 2b-i part is supplied
by the generic Proposition 4.2 row-to-function absolute-convergence tool. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_prop42FAbsToolAndPackFrontiers
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42FAbsRowsS1Tool (S := S))
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_prop42FAbsTool
      (S := S) fn f T Ps1 Ps2)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data after Step 2b-i has been discharged.
This matches the 1967/1985 dominated-convergence route: the domination
argument supplies integrability, leaving only the two local packing frontiers. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_packFrontiers
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_packFrontiers
      (S := S) fn f Ps1 Ps2)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from the exact `A.S1` seed tools
and the separate `A.S2` packing frontier. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_packS1SeedAndS2
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415Prop42PackOnS1SeedTools (S := S))
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_packS1SeedAndS2
      (S := S) fn f T Ps2)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from generic Proposition 4.2 tools:
exact `A.S1` local seeds plus the corrected bundled `A.S2` package. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_genericPackS1AndPackS2Tools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T1 : Lemma415Prop42PackOnS1SeedTools (S := S))
    (T2 : Lemma415Prop42PackOnS2Tool (S := S))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_genericPackS1AndPackS2Tools
      (S := S) fn f T1 T2)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from corrected package-shaped
Proposition 4.2 tools on both `A.S1` and `A.S2`. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_genericPackS1ToolAndPackS2Tool
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T1 : Lemma415Prop42PackOnS1Tool (S := S))
    (T2 : Lemma415Prop42PackOnS2Tool (S := S))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_genericPackS1ToolAndPackS2Tool
      (S := S) fn f T1 T2)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from the corrected abs-pack
provider for Proposition 4.2. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_absPackToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (P : Lemma415Prop42AbsPackToolsProvider (S := S))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_absPackToolsProvider
      (S := S) fn f P)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from corrected abs-pack tools
available only for the theorem-4.15 abs-error sequence. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_absErrorAbsPackTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_absErrorAbsPackTools
      (S := S) fn f T)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from a row-to-flat bridge plus
row seeds available only for the theorem-4.15 abs-error sequence. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_rowToFlatAndRowSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_absErrorAbsPackTools
    (S := S) fn f
    (Lemma415AbsErrorAbsPackToolsFrontier.of_rowToFlatAndRowSeedTools
      (S := S) fn f Rtf hSeeds)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from a row-to-flat bridge and a
generic Proposition 4.2 row-seed provider.

This is the source-data analogue of
`Lemma415AbsErrorAbsPackToolsFrontier.of_rowToFlatAndRowSeedToolsProvider`: the
provider first supplies corrected abs-pack tools for every nonnegative
integrable representative, and then the theorem-4.15 abs-error sequence is
specialized from that package. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_rowToFlatAndRowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_absPackToolsProvider
    (S := S) fn f
    (Lemma415Prop42AbsPackToolsProvider.of_rowToFlatAndRowSeedToolsProvider
      (S := S) Rtf P)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from a generic Proposition 4.2
row-seed provider. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_rowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_genericPackS1AndPackS2Tools
    (S := S) fn f
    (Lemma415Prop42PackOnS1SeedTools.of_rowSeedToolsProvider (S := S) P)
    (Lemma415Prop42PackOnS2Tool.of_rowSeedToolsProvider (S := S) P)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from the abs-error-specific `A.S1`
seed frontier and the separate `A.S2` packing frontier. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_absErrorPackS1SeedAndS2
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_absErrorPackS1SeedAndS2
      (S := S) fn f T Ps2)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from the abs-error-specific `A.S1`
seed frontier and the split `A.S2` rows/corrected-outer frontiers. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_absErrorS1SeedAndS2Split
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415AbsErrorRowsOnS2Frontier (S := S) fn f)
    (Outer : Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_absErrorS1SeedAndS2Split
      (S := S) fn f T Rows Outer)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data with theorem-4.15-specific `A.S1`
seeds, a generic Proposition 4.2 S2 row tool, and a corrected `A.S2` abs-outer
frontier for the abs-error sequence. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_absErrorS1SeedAndGenericRowsS2Outer
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f)
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_absErrorS1SeedAndGenericRowsS2Outer
      (S := S) fn f T Rows Outer)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data with theorem-4.15-specific `A.S1`
seeds and generic Proposition 4.2 tools for both `A.S2` rows and corrected
`A.S2` abs-outer convergence. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_absErrorS1SeedAndGenericS2Tools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415Prop42AbsOuterOnS2Tool (S := S))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_absErrorS1SeedAndGenericRowsS2Outer
    (S := S) fn f T Rows
    (Lemma415AbsErrorAbsOuterOnS2Frontier.of_prop42Tool
      (S := S) fn f Outer)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from row seeds for the abs-error
sequence. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_rowSeedTools
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_remainingAtomFrontier
    (S := S) fn f
    (Lemma415AbsErrorRemainingAtomFrontier.of_rowSeedTools
      (S := S) fn f hSeeds)
    hSplit hconv


/-- Assemble remaining-atoms abs-error data from source majorant choice/tail
data with the majorant kept on the ordinary relative/complement-integral side. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_majorantRelChoiceData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hChoice : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantRelChoiceSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_splitUniformData
    (S := S) fn f hAtoms
    (fun eps heps =>
      lemma_4_15_split_uniform_source_data_from_majorant_rel_choice_data_of_atoms
        (S := S) fn f hAtoms majorant majorant_nonneg eps
        (hChoice eps heps))
    hconv


/-- Assemble remaining-atoms abs-error data from complement-tail single-`g`
data. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_gComplementTailRelChoiceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GComplementTailRelChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_majorantRelChoiceData
    (S := S) fn f hAtoms (g.add g)
    (thm_4_15_two_g_majorant_nonneg (S := S) g g_nonneg)
    (fun eps heps =>
      lemma_4_15_majorant_rel_choice_source_data_from_g_single_tail_rel_choice_data
        (S := S) fn f g g_nonneg hfn_dom hf_dom eps
        (lemma_4_15_g_single_tail_rel_choice_source_data_from_g_complement_tail_data
          (S := S) g g_nonneg eps (hGTail eps heps)))
    hconv


/-- Assemble remaining-atoms abs-error data from the concrete `coverSet`
complement-tail construction. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_gComplementTailRelChoiceData
    (S := S) fn f g g_nonneg hfn_dom hf_dom hAtoms
    (fun eps heps =>
      lemma_4_15_g_complement_tail_rel_choice_data_from_coverSetBudget
        (S := S) g g_nonneg eps gSeeds (hBudget eps heps))
    hconv


/-- Assemble abs-error data from the concrete `coverSet` complement-tail
construction, with theorem 4.15's three Prop. 4.2 atom frontiers kept named. -/
noncomputable def Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetFrontier
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (F : Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetData
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.toAtoms (S := S) fn f F)
    gSeeds hBudget hconv


/-- Assemble abs-error data from the concrete `coverSet` complement-tail
construction and row-to-flat plus abs-error row seeds. -/
noncomputable def
    Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetRowToFlatRowSeedTools
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetFrontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_rowToFlatAndRowSeedTools
      (S := S) fn f Rtf hSeeds)
    gSeeds hBudget hconv


/-- Assemble abs-error data from the concrete `coverSet` complement-tail
construction and a generic row-to-flat plus row-seed-provider route. -/
noncomputable def
    Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetRowToFlatRowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    Lemma415AbsErrorAtomSourceData (S := S) fn f :=
  Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetFrontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_rowToFlatAndRowSeedToolsProvider
      (S := S) fn f Rtf P)
    gSeeds hBudget hconv


/-- The source proof's "apply lemma 4.14" step for theorem 4.15.

This is the first canonical, non-PFunR 4.15 endpoint: it sends
`u_n = |f_n - f|` through the completed source version of lemma 4.14. -/
noncomputable def thm_4_15_abs_error_tendsto_from_source_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (D : Lemma415AbsErrorSourceData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  thm_4_14_source_complete_from_rowSeedTools
    (S := S)
    (thm_4_15_abs_error (S := S) fn f)
    (thm_4_15_abs_error_nonneg (S := S) fn f)
    D.rowSeeds
    D.uniform
    D.converge


/-- Apply lemma 4.14 to the abs-error sequence using the lower
`remainingAtoms` interface. -/
noncomputable def thm_4_15_abs_error_tendsto_from_atom_source_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (D : Lemma415AbsErrorAtomSourceData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => (thm_4_15_abs_error (S := S) fn f n).integral) 0 :=
  thm_4_14_source_complete_from_remainingAtoms
    (S := S)
    (thm_4_15_abs_error (S := S) fn f)
    (thm_4_15_abs_error_nonneg (S := S) fn f)
    D.atoms
    D.uniform
    D.converge


/-- If the L1 error integral tends to zero, then the ordinary integrals
converge.  This is theorem 4.15's final reduction back from
`I(|f_n-f|) -> 0` to `I(f_n) -> I(f)`.

The proof uses only the already established inequality
`|I(r)| <= ||r||_1 = I(|r|)` and linearity of the completed integral. -/
def thm_4_15_integral_tendsto_of_abs_error_tendsto
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (herr : RSeq.TendstoHalf
      (fun n => ((fn n).sub f).absVal.integral) 0) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral where
  mod := herr.mod
  close := by
    intro k n hn
    have herr_close := herr.close k n hn
    have hnorm_lt :
        COF.lt ((fn n).sub f).normL1 (COF.halfPow (R := R) k) := by
      change COF.lt
        (COF.abs (((fn n).sub f).normL1 - 0))
        (COF.halfPow (R := R) k) at herr_close
      rwa [sub_zero,
        COFO.abs_of_nonneg (IntegrableRep.normL1_nonneg ((fn n).sub f))]
        at herr_close
    have hle :
        Le (COF.abs (((fn n).sub f).integral)) ((fn n).sub f).normL1 :=
      IntegrableRep.abs_integral_le_normL1 ((fn n).sub f)
    change COF.lt (COF.abs ((fn n).integral - f.integral))
      (COF.halfPow (R := R) k)
    rw [← IntegrableRep.integral_sub (fn n) f]
    exact lt_of_le_of_lt hle hnorm_lt


/-- Bishop--Cheng theorem 4.15 in the source order, up to the explicit
source-shaped data that supplies the displayed domination/uniform-`I_B`
argument.

Conclusion is the source conclusion `lim I(f_n) = I(f)`, not only the
intermediate `lim I(|f_n-f|)=0`. -/
noncomputable def thm_4_15_source_from_abs_error_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (D : Lemma415AbsErrorSourceData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_tendsto_of_abs_error_tendsto (S := S) fn f
    (thm_4_15_abs_error_tendsto_from_source_data (S := S) fn f D)


/-- Bishop--Cheng theorem 4.15 in the source order, with the abs-error side
using `Sec4Prop42RemainingAtomTools` rather than row seeds. -/
noncomputable def thm_4_15_source_from_abs_error_atom_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (D : Lemma415AbsErrorAtomSourceData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_tendsto_of_abs_error_tendsto (S := S) fn f
    (thm_4_15_abs_error_tendsto_from_atom_source_data (S := S) fn f D)


/-- Theorem 4.15 from the source displayed split estimate.

Compared with `thm_4_15_source_from_abs_error_data`, this removes one layer of
external data: the uniform-`I_B` hypothesis is now obtained from the source
split estimate.  The remaining frontier is the derivation of the two piece
bounds from domination by `g` and absolute continuity of the relative
integral. -/
noncomputable def thm_4_15_source_from_split_uniform_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_splitUniformData
      (S := S) fn f hSeeds hSplit hconv)


/-- Theorem 4.15 from the source displayed split estimate, with the
abs-error side lowered to the three `remainingAtoms` needed by the general
measurable `I_B` construction. -/
noncomputable def thm_4_15_source_from_split_uniform_atom_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hSplit : forall (eps : R), COF.lt 0 eps ->
      Lemma415SplitUniformSourceData (S := S) fn f eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_atom_data (S := S) fn f
    (Lemma415AbsErrorAtomSourceData.of_splitUniformData
      (S := S) fn f hAtoms hSplit hconv)


/-- Theorem 4.15 from the source majorant estimate.

This closes one more source step than `thm_4_15_source_from_split_uniform_data`:
the two split-piece bounds are derived from monotonicity under the majorant
(the source's `2g`).  The still-explicit frontier is deriving the majorant
data itself from only the printed domination and convergence hypotheses. -/
noncomputable def thm_4_15_source_from_majorant_split_uniform_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hMajorant : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantSplitUniformSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_majorantSplitUniformData
      (S := S) fn f hSeeds majorant majorant_nonneg hMajorant hconv)


/-- Theorem 4.15 from source choice/tail data.

Compared with `thm_4_15_source_from_majorant_split_uniform_data`, the
`A∧B` smallness hypothesis has been discharged by absolute continuity of the
majorant integral. -/
noncomputable def thm_4_15_source_from_majorant_choice_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hChoice : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantChoiceSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_majorantChoiceData
      (S := S) fn f hSeeds majorant majorant_nonneg hChoice hconv)


/-- Theorem 4.15 from source choice/tail data, with the majorant kept on the
ordinary relative/complement-integral side.

Unlike `thm_4_15_source_from_majorant_choice_data`, this endpoint does not
require row-seed data for the majorant. -/
noncomputable def thm_4_15_source_from_majorant_rel_choice_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hChoice : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantRelChoiceSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_majorantRelChoiceData
      (S := S) fn f hSeeds majorant majorant_nonneg hChoice hconv)


/-- Theorem 4.15 from source choice/tail data, with the majorant kept on the
ordinary relative/complement-integral side and the abs-error side lowered to
`Sec4Prop42RemainingAtomTools`. -/
noncomputable def thm_4_15_source_from_majorant_rel_choice_atom_data
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (majorant : IntegrableRep S) (majorant_nonneg : RepNonneg majorant)
    (hChoice : forall (eps : R), COF.lt 0 eps ->
      Lemma415MajorantRelChoiceSourceData
        (S := S) fn f majorant majorant_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_atom_data (S := S) fn f
    (Lemma415AbsErrorAtomSourceData.of_majorantRelChoiceData
      (S := S) fn f hAtoms majorant majorant_nonneg hChoice hconv)


/-- Theorem 4.15 from the printed `2g` choice/tail data.

This is the most source-faithful endpoint in this file: the arbitrary
majorant has been specialized to the expression that appears in the source
proof, namely `2g = g + g`. -/
noncomputable def thm_4_15_source_from_two_g_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hTwoG : forall (eps : R), COF.lt 0 eps ->
      Lemma415TwoGChoiceSourceData
        (S := S) fn f g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_twoGChoiceData
      (S := S) fn f g g_nonneg hSeeds hTwoG hconv)


/-- Theorem 4.15 from the printed `2g` tail-choice data, with the displayed
domination estimate derived internally from `|f_n| <= g` and `|f| <= g`.

Compared with `thm_4_15_source_from_two_g_choice_data`, this no longer asks
for `|f_n-f| <= 2g` as a field. -/
noncomputable def thm_4_15_source_from_two_g_tail_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415TwoGTailChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_twoGTailChoiceData
      (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds hTail hconv)


/-- Theorem 4.15 from source-shaped single-`g` tail-choice data.

This is currently the closest endpoint to the printed proof: the caller gives
smallness of `I_{-A}(g)`, while the file derives the source's use of
`I_{-A}(2g)` and the displayed pointwise estimate `|f_n-f| <= 2g`. -/
noncomputable def thm_4_15_source_from_g_single_tail_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GSingleTailChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_gSingleTailChoiceData
      (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds hGTail hconv)


/-- Theorem 4.15 from source-shaped single-`g` tail-choice data, without
row-seed data for `2g`.

This is now the closest endpoint to the printed proof in this file: the caller
gives smallness of `I_{-A}(g)`, and the file derives the use of `2g` through
the complement expression and additivity, while the error side alone uses the
direct `genIB` row-seed bridge. -/
noncomputable def thm_4_15_source_from_g_single_tail_rel_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GSingleTailRelChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_gSingleTailRelChoiceData
      (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds hGTail hconv)


/-- Theorem 4.15 from source-shaped complement-tail single-`g` data.

This endpoint exposes the tail hypothesis in the complement-expression form
`I(g - chi_A*g)`, matching the source proof's preceding tail-selection
machinery.  The concrete `coverSet` bridge below supplies this data from the
theorem-4.13/lemma-4.3 style cover sequence. -/
noncomputable def thm_4_15_source_from_g_complement_tail_rel_choice_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GComplementTailRelChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_gComplementTailRelChoiceData
      (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds hGTail hconv)


/-- Theorem 4.15 from source-shaped complement-tail single-`g` data, with
the abs-error side lowered to `Sec4Prop42RemainingAtomTools`. -/
noncomputable def thm_4_15_source_from_g_complement_tail_rel_choice_atom_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hGTail : forall (eps : R), COF.lt 0 eps ->
      Lemma415GComplementTailRelChoiceSourceData
        (S := S) g g_nonneg eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_atom_data (S := S) fn f
    (Lemma415AbsErrorAtomSourceData.of_gComplementTailRelChoiceData
      (S := S) fn f g g_nonneg hfn_dom hf_dom hAtoms hGTail hconv)


/-- Theorem 4.15 from the concrete `coverSet` complement-tail construction.

The remaining non-tail frontiers are explicit in the hypotheses: row seeds for
`|f_n-f|`, the domination witnesses `|f_n| <= g` and `|f| <= g`, convergence in
measure of the absolute error, and the source epsilon budget data. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_data (S := S) fn f
    (Lemma415AbsErrorSourceData.of_gCoverSetTailBudgetData
      (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds
      gSeeds hBudget hconv)


/-- The concrete `coverSet` endpoint with the source epsilon budget generated
internally by `lemma_4_15_default_tail_budget`. -/
noncomputable def thm_4_15_source_from_g_coverSet_default_budget_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_data
    (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds gSeeds
    (fun eps heps => lemma_4_15_default_tail_budget (R := R) eps heps)
    hconv


/-- Theorem 4.15 from the concrete `coverSet` complement-tail construction
and a generic Proposition 4.2 row-seed provider.

This route keeps the source-complete, non-atom lemma-4.14 interface visible:
the provider is used only to supply the `rowSeeds` field of
`Lemma415AbsErrorSourceData`. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_source_rowSeedProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  let D : Lemma415AbsErrorSourceData (S := S) fn f :=
    Lemma415AbsErrorSourceData.of_gCoverSetTailBudgetRowSeedToolsProvider
      (S := S) fn f g g_nonneg hfn_dom hf_dom P
      gSeeds hBudget hconv
  thm_4_15_source_from_abs_error_data (S := S) fn f
    D

/-- The concrete `coverSet` tail endpoint with the abs-error side supplied by
`Sec4Prop42RemainingAtomTools`.

Compared with `thm_4_15_source_from_g_coverSet_tail_budget_data`, this removes
the row-seed requirement for `|f_n-f|`; the remaining Prop. 4.2 frontier is the
three-atom package itself. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_atom_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_atom_data (S := S) fn f
    (Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetData
      (S := S) fn f g g_nonneg hfn_dom hf_dom hAtoms
      gSeeds hBudget hconv)


/-- The remaining-atoms `coverSet` endpoint with the source epsilon budget
generated internally. -/
noncomputable def thm_4_15_source_from_g_coverSet_default_budget_atom_data
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hAtoms : forall n,
      Sec4Prop42RemainingAtomTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_data
    (S := S) fn f g g_nonneg hfn_dom hf_dom hAtoms gSeeds
    (fun eps heps => lemma_4_15_default_tail_budget (R := R) eps heps)
    hconv


/-- The concrete `coverSet` tail endpoint with theorem 4.15's abs-error
Prop. 4.2 obligations split into their three named atom frontiers. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (F : Lemma415AbsErrorRemainingAtomFrontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_abs_error_atom_data (S := S) fn f
    (Lemma415AbsErrorAtomSourceData.of_gCoverSetTailBudgetFrontier
      (S := S) fn f g g_nonneg hfn_dom hf_dom F
      gSeeds hBudget hconv)


/-- The concrete `coverSet` tail endpoint with the three Step 2b atom
frontiers supplied separately. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_split_atom_frontiers
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (Fabs : Lemma415AbsErrorFAbsRowsS1Frontier (S := S) fn f)
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_splitFrontiers
      (S := S) fn f Fabs Ps1 Ps2)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint when Step 2b-i is discharged by the
generic Proposition 4.2 row-to-function absolute-convergence tool. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_prop42_fabs_tool
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415Prop42FAbsRowsS1Tool (S := S))
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_prop42FAbsTool
      (S := S) fn f T Ps1 Ps2)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint after Step 2b-i has been discharged.
The remaining inputs are precisely the Step 2b-ii and Step 2b-iii packing
frontiers. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_pack_frontiers
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (Ps1 : Lemma415AbsErrorPackOnS1Frontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_packFrontiers
      (S := S) fn f Ps1 Ps2)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint with Step 2b-ii decomposed into the
two exact `A.S1` local seeds, plus the separate Step 2b-iii `A.S2` frontier. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_pack_s1_seed_and_s2
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415Prop42PackOnS1SeedTools (S := S))
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_packS1SeedAndS2
      (S := S) fn f T Ps2)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from generic Proposition 4.2 tools:
exact `A.S1` local seeds plus the corrected bundled `A.S2` package. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_generic_pack_s1_and_s2_tools
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T1 : Lemma415Prop42PackOnS1SeedTools (S := S))
    (T2 : Lemma415Prop42PackOnS2Tool (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_pack_s1_seed_and_s2
    (S := S) fn f g g_nonneg hfn_dom hf_dom T1
    (Lemma415AbsErrorPackOnS2Frontier.of_prop42PackTool
      (S := S) fn f T2)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from corrected package-shaped
Proposition 4.2 tools on both `A.S1` and `A.S2`. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_generic_pack_s1_tool_and_s2_tool
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T1 : Lemma415Prop42PackOnS1Tool (S := S))
    (T2 : Lemma415Prop42PackOnS2Tool (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_genericPackS1ToolAndPackS2Tool
      (S := S) fn f T1 T2)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from the corrected abs-pack provider
for Proposition 4.2. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_absPackToolsProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Lemma415Prop42AbsPackToolsProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_generic_pack_s1_tool_and_s2_tool
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415Prop42PackOnS1Tool.of_absPackToolsProvider (S := S) P)
    (Lemma415Prop42PackOnS2Tool.of_absPackToolsProvider (S := S) P)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from the source-shaped general
measurable-`I_B` abs-pack provider.

The `A.S1` part factors through the standard Proposition 4.2 rows rather than
the older arbitrary-row abs-outer residual. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_generalIBSourceAbsPackProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Sec4GeneralIBSourceAbsPackProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_absPackToolsProvider
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415Prop42AbsPackToolsProvider.of_generalIBSourceAbsPackProvider
      (S := S) P)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from the refined source-shaped
general measurable-`I_B` provider with the corrected `A.S2` frontier exposed as
standard rows plus corrected absolute row-zero. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_generalIBSourceS2AbsZeroProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_absPackToolsProvider
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415Prop42AbsPackToolsProvider.of_generalIBSourceS2AbsZeroProvider
      (S := S) P)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from the refined source-shaped
general measurable-`I_B` provider whose `A.S2` side is standard rows plus
corrected standard-row abs-outer convergence. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_generalIBSourceS2StandardOuterProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_absPackToolsProvider
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415Prop42AbsPackToolsProvider.of_generalIBSourceS2StandardOuterProvider
      (S := S) P)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from corrected abs-pack tools
available only for the theorem-4.15 abs-error sequence. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_absPackTools
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorAbsPackToolsFrontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_absErrorAbsPackTools
      (S := S) fn f T)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from a row-to-flat bridge plus row
seeds available only for the theorem-4.15 abs-error sequence.

This route factors through `Lemma415AbsErrorAbsPackToolsFrontier`, making the
`Sec4ChiFCaseAbsPackTools` construction explicit while remaining weaker than a
global Proposition 4.2 abs-pack provider. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_rowToFlat_rowSeedTools
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_abs_error_absPackTools
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorAbsPackToolsFrontier.of_rowToFlatAndRowSeedTools
      (S := S) fn f Rtf hSeeds)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from a row-to-flat bridge and a
generic Proposition 4.2 row-seed provider.

Compared with the row-seed-only endpoint below, this route factors through the
stronger corrected abs-pack provider interface, exposing the exact bridge needed
to turn row-level absolute packages into flat absolute convergence data. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_generic_rowToFlat_rowSeedToolsProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (Rtf : Lemma415Prop42RowToFlatTool (S := S))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_absPackToolsProvider
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415Prop42AbsPackToolsProvider.of_rowToFlatAndRowSeedToolsProvider
      (S := S) Rtf P)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint from a generic Proposition 4.2
row-seed provider.  The `A.S2` package is kept bundled, so this route does not
claim the stronger arbitrary-row corrected outer tool. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_generic_rowSeedProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_generic_pack_s1_and_s2_tools
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415Prop42PackOnS1SeedTools.of_rowSeedToolsProvider (S := S) P)
    (Lemma415Prop42PackOnS2Tool.of_rowSeedToolsProvider (S := S) P)
    gSeeds hBudget hconv


/-- The generic row-seed-provider `coverSet` endpoint with the source epsilon
budget generated internally.  This is the compact current 4.15 entry point
when the generic Proposition 4.2 row-seed provider is available. -/
noncomputable def thm_4_15_source_from_g_coverSet_default_budget_generic_rowSeedProvider
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (P : Lemma415Prop42RowSeedToolsProvider (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_generic_rowSeedProvider
    (S := S) fn f g g_nonneg hfn_dom hf_dom P gSeeds
    (fun eps heps => lemma_4_15_default_tail_budget (R := R) eps heps)
    hconv


/-- The concrete `coverSet` tail endpoint with Step 2b-ii decomposed only for
the theorem-4.15 abs-error sequence, plus the separate Step 2b-iii frontier. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_seed_and_s2
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Ps2 : Lemma415AbsErrorPackOnS2Frontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_absErrorPackS1SeedAndS2
      (S := S) fn f T Ps2)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint with the abs-error-specific `A.S1`
seed frontier and the corrected `A.S2` frontier split into rows and abs-outer
row-sum convergence. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_seed_and_s2_split
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415AbsErrorRowsOnS2Frontier (S := S) fn f)
    (Outer : Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_seed_and_s2
    (S := S) fn f g g_nonneg hfn_dom hf_dom T
    (Lemma415AbsErrorPackOnS2Frontier.of_rowsAndAbsOuter
      (S := S) fn f Rows Outer)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint with the `A.S2` rows supplied by a
generic Proposition 4.2 row tool, while the corrected `A.S2` abs-outer part
remains theorem-4.15-specific. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_generic_rows_s2_outer
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415AbsErrorAbsOuterOnS2Frontier (S := S) fn f)
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_seed_and_s2_split
    (S := S) fn f g g_nonneg hfn_dom hf_dom T
    (Lemma415AbsErrorRowsOnS2Frontier.of_prop42Tool
      (S := S) fn f Rows)
    Outer gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint with theorem-4.15-specific `A.S1`
seeds and generic Proposition 4.2 tools for both `A.S2` rows and corrected
`A.S2` abs-outer convergence. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_generic_s2_tools
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (T : Lemma415AbsErrorPackOnS1SeedFrontier (S := S) fn f)
    (Rows : Lemma415Prop42RowsOnS2Tool (S := S))
    (Outer : Lemma415Prop42AbsOuterOnS2Tool (S := S))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_abs_error_s1_generic_rows_s2_outer
    (S := S) fn f g g_nonneg hfn_dom hf_dom T Rows
    (Lemma415AbsErrorAbsOuterOnS2Frontier.of_prop42Tool
      (S := S) fn f Outer)
    gSeeds hBudget hconv


/-- The concrete `coverSet` tail endpoint when the theorem-4.15 abs-error
Prop. 4.2 obligations are supplied as row seeds. -/
noncomputable def thm_4_15_source_from_g_coverSet_tail_budget_abs_error_rowSeedTools
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hBudget : forall (eps : R), COF.lt 0 eps ->
      Lemma415TailBudgetSourceData (R := R) eps)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_atom_frontier
    (S := S) fn f g g_nonneg hfn_dom hf_dom
    (Lemma415AbsErrorRemainingAtomFrontier.of_rowSeedTools
      (S := S) fn f hSeeds)
    gSeeds hBudget hconv


/-- The abs-error row-seed `coverSet` endpoint with the source epsilon budget
generated internally. -/
noncomputable def thm_4_15_source_from_g_coverSet_default_budget_abs_error_rowSeedTools
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (g_nonneg : RepNonneg g)
    (hfn_dom : forall n, RepNonneg (g.sub (fn n).absVal))
    (hf_dom : RepNonneg (g.sub f.absVal))
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (gSeeds : Sec4Prop42RowSeedTools (S := S) g g_nonneg)
    (hconv :
      Lemma414ConvergeInMeasureToZeroData (S := S)
        (thm_4_15_abs_error (S := S) fn f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_source_from_g_coverSet_tail_budget_abs_error_rowSeedTools
    (S := S) fn f g g_nonneg hfn_dom hf_dom hSeeds gSeeds
    (fun eps heps => lemma_4_15_default_tail_budget (R := R) eps heps)
    hconv


/-- The theorem-4.15 conclusion in the current split form.

The legacy compatibility file stops at the source proof's intermediate target
`I(|f_n-f|) -> 0`.  This source-complete file performs the final source step
back to `I(f_n) -> I(f)`, while still leaving the measurable-set `I_B`
frontier explicit.  Here "general" refers to the set argument `B`: as in
Definition 4.8, the integrand is still an integrable representative. -/
noncomputable def thm_4_15_integral_convergence_except_generalIB
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (D : Lemma415AbsErrorNonIBData (S := S) fn f)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g D) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_tendsto_of_abs_error_tendsto (S := S) fn f
    (thm_4_15_dominated_convergence_except_generalIB
      (S := S) fn f g D U)


/-- The theorem-4.15 conclusion with source PFunR convergence supplying the
non-`I_B` error-convergence data.  The remaining external datum is exactly the
uniform measurable-set `I_B` frontier. -/
noncomputable def
    thm_4_15_integral_convergence_except_generalIB_from_pfunSourceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (pfnsrc : Nat -> PFunR X R) (pf : PFunR X R)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hconv : Lemma415PFunConvergeData (S := S) pfnsrc pf)
    (hrep_fn : forall n,
      Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n))
    (hrep_f : Lemma414RepresentsPFunR (S := S) f pf)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g
      (Lemma415AbsErrorNonIBData.of_pfunConvergeAndRepresentations
        (S := S) fn f pfnsrc pf hSeeds hconv hrep_fn hrep_f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_tendsto_of_abs_error_tendsto (S := S) fn f
    (thm_4_15_dominated_convergence_except_generalIB_from_pfunSourceData
      (S := S) fn f g pfnsrc pf hSeeds hconv hrep_fn hrep_f U)


/-- Source-faithful alias for the previous `generalIB` endpoint.

The phrase means `I_B` for arbitrary measurable sets `B` and integrable
integrands, not integration of arbitrary measurable functions. -/
noncomputable def thm_4_15_integral_convergence_except_measurableSetIB
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (D : Lemma415AbsErrorNonIBData (S := S) fn f)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g D) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_except_generalIB (S := S) fn f g D U


/-- Source-faithful PFunR-data alias for the measurable-set `I_B` endpoint. -/
noncomputable def
    thm_4_15_integral_convergence_except_measurableSetIB_from_pfunSourceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (pfnsrc : Nat -> PFunR X R) (pf : PFunR X R)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hconv : Lemma415PFunConvergeData (S := S) pfnsrc pf)
    (hrep_fn : forall n,
      Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n))
    (hrep_f : Lemma414RepresentsPFunR (S := S) f pf)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g
      (Lemma415AbsErrorNonIBData.of_pfunConvergeAndRepresentations
        (S := S) fn f pfnsrc pf hSeeds hconv hrep_fn hrep_f)) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_except_generalIB_from_pfunSourceData
    (S := S) fn f g pfnsrc pf hSeeds hconv hrep_fn hrep_f U


end BishopC
