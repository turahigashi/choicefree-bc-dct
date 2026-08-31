import Mathdemo.Internal.Sec4.SourceAbsPackProvider

/-!
# Sec4 Phase2-D2b2b_beta-b2b30: source-shaped S2 abs-zero provider

`b2b29` narrowed the `A.S1` residual to the standard Proposition 4.2 lambda
rows, but it still had to assume the corrected `A.S2` abs-pack as one bundled
field.  This file splits that bundled negative-side field into the two pieces
that match the printed proof structure more closely:

* construct the standard Proposition 4.2 lambda rows on `A.S2`;
* prove that each of those row absolute sums is zero.

The second item is intentionally kept explicit.  The existing signed theorem
`sec4_lambdaRowZeroOnS2` proves only that the signed row value is zero.  After
the b2b20 correction, the required outer series is the series of row absolute
sums, and `RepNonneg` is only value-level nonnegativity, not termwise
nonnegativity of the representing sequence.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Corrected S2 row-zero frontier -/

/-- For a fixed standard `A.S2` row constructor, every corrected row absolute
sum is zero.

This is the exact frontier needed to turn standard rows into the corrected
`Sec4LambdaRowsAbsPackOnS2`. -/
def Sec4LambdaRowsAbsZeroOnS2ForRows
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Rows : Sec4Prop42RowsOnS2 (S := S) f hnn) : Prop :=
  forall (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
    forall hxA : x ∈ A.S2,
      forall k : Nat, ((Rows A hA x hxA) k).snd.sum = 0


/-- Build the corrected `A.S2` abs-pack once standard rows and their corrected
absolute row-zero facts are available. -/
noncomputable def sec4_packOnS2_of_rowsAbsZero
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (Rows : Sec4Prop42RowsOnS2 (S := S) f hnn)
    (Zero : Sec4LambdaRowsAbsZeroOnS2ForRows (S := S) Rows) :
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn := by
  intro A hA x hxA
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x :=
    Rows A hA x hxA
  let houter : Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x hrows :=
    seriesSum_congr
      (fun k => by
        have hz : (hrows k).snd.sum = 0 := by
          dsimp [hrows]
          exact Zero A hA x hxA k
        exact hz.symm)
      (sec4_zeroSeries_transparent (R := R))
  exact ⟨hrows, houter⟩


/-! ## 2. Refined source-shaped provider -/

/-- Source-shaped provider with the `A.S2` field split into standard rows plus
corrected absolute row-zero.

Compared with `Sec4GeneralIBSourceAbsPackProvider`, this removes the bundled
`pack_on_s2` assumption and exposes the precise remaining negative-side
frontier. -/
structure Sec4GeneralIBSourceS2AbsZeroProvider : Type _ where
  rowToFlat : Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S)
  charDomain : Sec4Prop42CharacteristicDomainWitness (S := S)
  standard_outer_on_s1 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42StandardAbsOuterOnS1OfFAbs (S := S) charDomain f hnn
  rows_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42RowsOnS2 (S := S) f hnn
  abs_zero_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4LambdaRowsAbsZeroOnS2ForRows (S := S) (rows_on_s2 f hnn)


namespace Sec4GeneralIBSourceS2AbsZeroProvider

/-- Forget the refined split by rebuilding the bundled corrected `A.S2`
abs-pack expected by `b2b29`. -/
noncomputable def toSourceAbsPackProvider
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S)) :
    Sec4GeneralIBSourceAbsPackProvider (S := S) where
  rowToFlat := P.rowToFlat
  charDomain := P.charDomain
  standard_outer_on_s1 := P.standard_outer_on_s1
  pack_on_s2 := fun f hnn =>
    sec4_packOnS2_of_rowsAbsZero (S := S)
      (P.rows_on_s2 f hnn)
      (P.abs_zero_on_s2 f hnn)


/-- Corrected abs-pack tools from the refined source-shaped provider. -/
noncomputable def absPackTools
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S))
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4ChiFCaseAbsPackTools (S := S) f hnn :=
  Sec4GeneralIBSourceAbsPackProvider.absPackTools
    (S := S) (toSourceAbsPackProvider P) f hnn


end Sec4GeneralIBSourceS2AbsZeroProvider

noncomputable def sec4_genIBValueBridge_of_sourceS2AbsZeroProvider
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S))
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_sourceAbsPackProvider
    (S := S)
    (Sec4GeneralIBSourceS2AbsZeroProvider.toSourceAbsPackProvider P)
    B hB f hnn


theorem sec4_genRelIntegral_eq_relIntegral_of_sourceS2AbsZeroProvider
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_sourceAbsPackProvider
    (S := S)
    (Sec4GeneralIBSourceS2AbsZeroProvider.toSourceAbsPackProvider P)
    C hC f hnn


noncomputable def sec4_genIBConsistencyBridge_of_sourceS2AbsZeroProvider
    (P : Sec4GeneralIBSourceS2AbsZeroProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_sourceAbsPackProvider
    (S := S)
    (Sec4GeneralIBSourceS2AbsZeroProvider.toSourceAbsPackProvider P)
    C hC f hnn


end BishopC
