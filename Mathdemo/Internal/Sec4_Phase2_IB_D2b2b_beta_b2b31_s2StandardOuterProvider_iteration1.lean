import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b30_s2AbsZeroProvider_iteration1

/-!
# Sec4 Phase2-D2b2b_beta-b2b31: source-shaped S2 standard-outer provider

`b2b30` exposed a very strong sufficient condition for the corrected `A.S2`
package: every standard row absolute sum is zero.  That is useful as a sharp
diagnostic, but it is stronger than what the corrected b2b20 interface needs.

The exact corrected package needs only:

* the standard Proposition 4.2 lambda rows on `A.S2`;
* convergence of the outer series of those standard row absolute sums.

This file makes that weaker, source-shaped S2 interface explicit.  It is the
preferred mainline residual after `b2b29`: no arbitrary bundled `pack_on_s2`,
and no claim that a representative-level absolute row sum vanishes merely
because the represented value is zero.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Corrected S2 standard-row outer frontier -/

/-- Corrected abs-outer convergence on `A.S2` for a fixed standard row
constructor. -/
def Sec4LambdaRowsAbsOuterOnS2ForRows
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Rows : Sec4Prop42RowsOnS2 (S := S) f hnn) : Type _ :=
  forall (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
    forall hxA : x ∈ A.S2,
      Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x
        (Rows A hA x hxA)


/-- Build the corrected `A.S2` abs-pack from standard rows and their corrected
standard-row abs-outer convergence. -/
noncomputable def sec4_packOnS2_of_rowsAbsOuter
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Rows : Sec4Prop42RowsOnS2 (S := S) f hnn)
    (Outer : Sec4LambdaRowsAbsOuterOnS2ForRows (S := S) Rows) :
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn := by
  intro A hA x hxA
  exact ⟨Rows A hA x hxA, Outer A hA x hxA⟩


/-- The stronger b2b30 row-absolute-zero frontier implies the weaker standard
S2 abs-outer frontier. -/
noncomputable def sec4_absOuterOnS2_of_rowsAbsZero
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Rows : Sec4Prop42RowsOnS2 (S := S) f hnn)
    (Zero : Sec4LambdaRowsAbsZeroOnS2ForRows (S := S) Rows) :
    Sec4LambdaRowsAbsOuterOnS2ForRows (S := S) Rows := by
  intro A hA x hxA
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x :=
    Rows A hA x hxA
  exact
    seriesSum_congr
      (fun k => by
        have hz : (hrows k).sum = 0 := by
          dsimp [hrows]
          exact Zero A hA x hxA k
        exact hz.symm)
      (sec4_zeroSeries_transparent (R := R))


/-! ## 2. Refined source-shaped provider -/

/-- Source-shaped provider with both sides attached to standard Proposition
4.2 rows.

Compared with `Sec4GeneralIBSourceAbsPackProvider`, this removes the bundled
`pack_on_s2` field.  Compared with `Sec4GeneralIBSourceS2AbsZeroProvider`, it
does not require the stronger representative-level row absolute sums to be
zero. -/
structure Sec4GeneralIBSourceS2StandardOuterProvider : Type _ where
  rowToFlat : Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S)
  charDomain : Sec4Prop42CharacteristicDomainWitness (S := S)
  standard_outer_on_s1 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42StandardAbsOuterOnS1OfFAbs (S := S) charDomain f hnn
  rows_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42RowsOnS2 (S := S) f hnn
  standard_outer_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4LambdaRowsAbsOuterOnS2ForRows (S := S) (rows_on_s2 f hnn)


namespace Sec4GeneralIBSourceS2StandardOuterProvider

/-- Forget the refined split by rebuilding the bundled corrected `A.S2`
abs-pack expected by `b2b29`. -/
noncomputable def toSourceAbsPackProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S)) :
    Sec4GeneralIBSourceAbsPackProvider (S := S) where
  rowToFlat := P.rowToFlat
  charDomain := P.charDomain
  standard_outer_on_s1 := P.standard_outer_on_s1
  pack_on_s2 := fun f hnn =>
    sec4_packOnS2_of_rowsAbsOuter (S := S)
      (P.rows_on_s2 f hnn)
      (P.standard_outer_on_s2 f hnn)


/-- The stronger b2b30 provider is a special case of the weaker standard-outer
provider. -/
noncomputable def ofSourceS2AbsZeroProvider
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S)) :
    Sec4GeneralIBSourceS2StandardOuterProvider (S := S) where
  rowToFlat := P.rowToFlat
  charDomain := P.charDomain
  standard_outer_on_s1 := P.standard_outer_on_s1
  rows_on_s2 := P.rows_on_s2
  standard_outer_on_s2 := fun f hnn =>
    sec4_absOuterOnS2_of_rowsAbsZero (S := S)
      (P.rows_on_s2 f hnn)
      (P.abs_zero_on_s2 f hnn)


/-- Corrected abs-pack tools from the standard-outer source-shaped provider. -/
noncomputable def absPackTools
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4ChiFCaseAbsPackTools (S := S) f hnn :=
  Sec4GeneralIBSourceAbsPackProvider.absPackTools
    (S := S) (toSourceAbsPackProvider P) f hnn


end Sec4GeneralIBSourceS2StandardOuterProvider

noncomputable def sec4_genIBValueBridge_of_sourceS2StandardOuterProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_sourceAbsPackProvider
    (S := S)
    (Sec4GeneralIBSourceS2StandardOuterProvider.toSourceAbsPackProvider P)
    B hB f hnn


theorem sec4_genRelIntegral_eq_relIntegral_of_sourceS2StandardOuterProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_sourceAbsPackProvider
    (S := S)
    (Sec4GeneralIBSourceS2StandardOuterProvider.toSourceAbsPackProvider P)
    C hC f hnn


noncomputable def sec4_genIBConsistencyBridge_of_sourceS2StandardOuterProvider
    (P : Sec4GeneralIBSourceS2StandardOuterProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_sourceAbsPackProvider
    (S := S)
    (Sec4GeneralIBSourceS2StandardOuterProvider.toSourceAbsPackProvider P)
    C hC f hnn


end BishopC
