import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b28_sourceDomainWitness_iteration1

/-!
# Sec4 Phase2-D2b2bβ-b2b29: source-shaped abs-pack provider

`b2b28` made the missing source-domain witness for `χ_A` explicit.  The next
source-faithful narrowing is on the positive side: the printed proof constructs
the Proposition 4.2 lambda rows themselves, so the corrected abs-outer
obligation should attach to those standard rows, not to an arbitrary separately
chosen row witness.

This file introduces that standard-row outer interface and packages it
directly as `Sec4ChiFCaseAbsPackTools`.  The `A.S2` corrected package remains
explicit; the signed row-zero theorem does not by itself give the corrected
series of row absolute sums.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-- Corrected abs-outer convergence on `A.S1` for the standard Proposition 4.2
lambda rows built from the characteristic-domain witness and the supplied
`f`-absolute convergence witness.

This is weaker than `Sec4Prop42AbsOuterOnS1OfRows`: it does not assert
abs-outer convergence for arbitrary row witnesses. -/
def Sec4Prop42StandardAbsOuterOnS1OfFAbs
    (D : Sec4Prop42CharacteristicDomainWitness (S := S))
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  forall (A : BSet X) (hA : IntegrableSet1 S A) (x : X)
      (hxA : x ∈ A.S1),
    forall hfabs : RSeq.SeriesSum
      (fun m => COF.abs (((f.fn m).toFun x))),
      Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x
        (sec4_lambdaRowAbs_of_chiF_fabs
          A hA f (prop_4_2_n_k f) x
          (D.abs_on_s1 A hA x hxA)
          hfabs)


/-- Build the corrected `A.S1` abs-pack constructor from source-domain
information and the standard-row abs-outer witness. -/
noncomputable def sec4_packOnS1_of_characteristicDomain_standardOuter
    (D : Sec4Prop42CharacteristicDomainWitness (S := S))
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Outer : Sec4Prop42StandardAbsOuterOnS1OfFAbs (S := S) D f hnn) :
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) f hnn := by
  intro A hA x hxA hfabs
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x :=
    sec4_lambdaRowAbs_of_chiF_fabs
      A hA f (prop_4_2_n_k f) x
      (D.abs_on_s1 A hA x hxA)
      hfabs
  let houter : Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x hrows :=
    Outer A hA x hxA hfabs
  exact ⟨hrows, houter⟩


/-- Source-shaped general measurable-`I_B` abs-pack provider.

Compared with `Sec4GeneralIBDomainResidualProvider`, this no longer asks for
`Sec4Prop42AbsOuterOnS1OfRows` over arbitrary row witnesses.  It asks only for
the corrected abs-outer convergence of the standard Proposition 4.2 rows. -/
structure Sec4GeneralIBSourceAbsPackProvider : Type _ where
  rowToFlat : Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S)
  charDomain : Sec4Prop42CharacteristicDomainWitness (S := S)
  standard_outer_on_s1 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42StandardAbsOuterOnS1OfFAbs (S := S) charDomain f hnn
  pack_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn


namespace Sec4GeneralIBSourceAbsPackProvider

/-- The source-shaped provider supplies the corrected abs-pack tools directly.

The `A.S1` row-to-function field is the generic row-0-right reconstruction
from `b2b27`; the `A.S1` pack field is the standard-row construction above. -/
noncomputable def absPackTools
    (P : Sec4GeneralIBSourceAbsPackProvider (S := S))
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4ChiFCaseAbsPackTools (S := S) f hnn :=
  Sec4ChiFCaseAbsPackTools.mk
    P.rowToFlat
    (sec4_fabsOfLambdaAbsRowsOnS1_of_row0Right_general f hnn)
    (sec4_packOnS1_of_characteristicDomain_standardOuter
      (S := S) P.charDomain f hnn
      (P.standard_outer_on_s1 f hnn))
    (P.pack_on_s2 f hnn)


end Sec4GeneralIBSourceAbsPackProvider

noncomputable def sec4_genIBValueBridge_of_sourceAbsPackProvider
    (P : Sec4GeneralIBSourceAbsPackProvider (S := S))
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_absPackTools B hB f hnn
    (Sec4GeneralIBSourceAbsPackProvider.absPackTools
      (S := S) P f hnn)


theorem sec4_genRelIntegral_eq_relIntegral_of_sourceAbsPackProvider
    (P : Sec4GeneralIBSourceAbsPackProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_absPackTools C hC f hnn
    (Sec4GeneralIBSourceAbsPackProvider.absPackTools
      (S := S) P f hnn)


noncomputable def sec4_genIBConsistencyBridge_of_sourceAbsPackProvider
    (P : Sec4GeneralIBSourceAbsPackProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_absPackTools C hC f hnn
    (Sec4GeneralIBSourceAbsPackProvider.absPackTools
      (S := S) P f hnn)


end BishopC
