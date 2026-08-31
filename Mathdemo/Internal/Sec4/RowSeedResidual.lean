import Mathdemo.Internal.Sec4.RowSeedProvider

/-!
# Sec4 Phase2-D2b2bβ-b2b27: row-seed residual provider

`b2b25` packages four row-seed fields.  The first one is not a genuine
remaining frontier: row 0 of `prop_4_2_lambda_k` exposes the right component
`u.sub (prop_4_2_min_f_n u 0)`, and the left interleaved half of that
subtraction is the original representative `u`.

This file lifts that row-0 argument out of the theorem-4.15 source file and
narrows the general provider frontier from four fields to the three fields
that are still mathematically substantive.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Generic row-0-right reconstruction of `u` absolute convergence from the
Proposition 4.2 lambda-row absolute witnesses on `A.S1`. -/
noncomputable def sec4_fabsOfLambdaAbsRowsOnS1_of_row0Right_general
    (u : IntegrableRep S) (unn : RepNonneg u) :
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) u unn := by
  intro A hA x _hxA hrows
  let hrow0Dom :
      (prop_4_2_lambda_k A hA u (prop_4_2_n_k u) 0).MemAt x :=
    (hrows 0).fst
  let hrow0 :
      RSeq.SeriesSum
        (fun m => COF.abs
          ((prop_4_2_lambda_k A hA u (prop_4_2_n_k u) 0).valueAt
            x hrow0Dom m)) :=
    (hrows 0).snd
  dsimp [prop_4_2_lambda_k] at hrow0Dom hrow0
  let hrightDom := min2_dom_right hrow0Dom
  have hright :
      RSeq.SeriesSum
        (fun m => COF.abs
          ((u.sub (prop_4_2_min_f_n u 0)).valueAt x hrightDom m)) :=
    min2_absSeriesSum_right hrow0Dom hrow0
  exact ⟨add_dom_left hrightDom,
    add_absSeriesSum_left hrightDom hright⟩


/-- The three residual row-seed fields after the row-0-right field has been
discharged generically. -/
def Sec4Prop42RowSeedResidualTools
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4Prop42ChiAbsOnS1OfFAbs (S := S) f hnn)
    (PProd (Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn)
      (Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn))


namespace Sec4Prop42RowSeedResidualTools

def mk
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (chi_abs_on_s1_of_fabs : Sec4Prop42ChiAbsOnS1OfFAbs (S := S) f hnn)
    (abs_outer_on_s1_of_rows : Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn)
    (pack_on_s2 : Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn) :
    Sec4Prop42RowSeedResidualTools (S := S) f hnn :=
  ⟨chi_abs_on_s1_of_fabs, abs_outer_on_s1_of_rows, pack_on_s2⟩


def chi_abs_on_s1_of_fabs
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowSeedResidualTools (S := S) f hnn) :
    Sec4Prop42ChiAbsOnS1OfFAbs (S := S) f hnn :=
  T.1


def abs_outer_on_s1_of_rows
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowSeedResidualTools (S := S) f hnn) :
    Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn :=
  T.2.1


def pack_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowSeedResidualTools (S := S) f hnn) :
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn :=
  T.2.2


end Sec4Prop42RowSeedResidualTools

/-- Complete the full row-seed package from the three residual fields. -/
noncomputable def sec4_rowSeedTools_of_residualTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedResidualTools (S := S) f hnn) :
    Sec4Prop42RowSeedTools (S := S) f hnn :=
  Sec4Prop42RowSeedTools.mk
    (sec4_fabsOfLambdaAbsRowsOnS1_of_row0Right_general f hnn)
    (Sec4Prop42RowSeedResidualTools.chi_abs_on_s1_of_fabs T)
    (Sec4Prop42RowSeedResidualTools.abs_outer_on_s1_of_rows T)
    (Sec4Prop42RowSeedResidualTools.pack_on_s2 T)


/-- General measurable-`I_B` provider after the generic row-0-right field has
been removed from the frontier. -/
structure Sec4GeneralIBRowSeedResidualProvider : Type _ where
  residual : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42RowSeedResidualTools (S := S) f hnn


noncomputable def Sec4GeneralIBRowSeedResidualProvider.toRowSeedProvider
    (P : Sec4GeneralIBRowSeedResidualProvider (S := S)) :
    Sec4GeneralIBRowSeedToolsProvider (S := S) where
  rowSeeds := fun f hnn =>
    sec4_rowSeedTools_of_residualTools f hnn (P.residual f hnn)


noncomputable def sec4_genIBValueBridge_of_rowSeedResidualProvider
    (P : Sec4GeneralIBRowSeedResidualProvider (S := S))
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_rowSeedToolsProvider
    (Sec4GeneralIBRowSeedResidualProvider.toRowSeedProvider P)
    B hB f hnn


theorem sec4_genRelIntegral_eq_relIntegral_of_rowSeedResidualProvider
    (P : Sec4GeneralIBRowSeedResidualProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_rowSeedToolsProvider
    (Sec4GeneralIBRowSeedResidualProvider.toRowSeedProvider P)
    C hC f hnn


noncomputable def sec4_genIBConsistencyBridge_of_rowSeedResidualProvider
    (P : Sec4GeneralIBRowSeedResidualProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_rowSeedToolsProvider
    (Sec4GeneralIBRowSeedResidualProvider.toRowSeedProvider P)
    C hC f hnn


end BishopC
