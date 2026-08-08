import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b21_rowToFlat_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b22: plug proof rowToFlat into the final three atom interface

b2b21 completes the generic atom

```
sec4_rowToFlat_source : Sec4SeriesSumRepL1FlatAbsOfAbsRows
```

with hardness 4.  Therefore the only remaining mathematical content is the
three `prop_4_2_lambda_k` atoms:

* reconstruct `f` abs on `A.S1` from row abs;
* build abs-outer packed rows on `A.S1` from `f` abs;
* build abs-outer packed rows on `A.S2`.

This file fixes the final API around exactly those three atoms and plugs in
`sec4_rowToFlat_source`.  Once `Sec4Prop42RemainingAtomTools f hnn` is
constructed, the general measurable relative integral `I_B` and the
consistency theorem are obtained immediately.
-/

#check sec4_rowToFlat_source
#check Sec4ChiFCaseAbsPackTools
#check Sec4SeriesSumRepL1FlatAbsOfAbsRows
#check Sec4FAbsOfLambdaAbsRowsOnS1
#check Sec4LambdaRowsAbsPackOnS1OfFAbs
#check Sec4LambdaRowsAbsPackOnS2
#check sec4_chiFCaseToolsData_of_absPackTools
#check sec4_genIBValueBridge_of_absPackTools
#check sec4_genRelIntegral_eq_relIntegral_of_absPackTools
#check sec4_genIBConsistencyBridge_of_absPackTools

/-! ## 1. The exact remaining atom package -/

/--
The three remaining `prop_4_2` atoms after `rowToFlat` has been completed.

This is intentionally not a structure: the fields are heavy Type-valued
witnesses, so a `PProd` chain avoids projection-generation whnf blow-ups.
-/
def Sec4Prop42RemainingAtomTools
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn)
    (PProd (Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) f hnn)
      (Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn))


namespace Sec4Prop42RemainingAtomTools

def mk
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (fabs_of_rows_s1 : Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn)
    (pack_on_s1_of_fabs : Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) f hnn)
    (pack_on_s2 : Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn) :
    Sec4Prop42RemainingAtomTools (S := S) f hnn :=
  ⟨fabs_of_rows_s1, pack_on_s1_of_fabs, pack_on_s2⟩


def fabs_of_rows_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn :=
  T.1


def pack_on_s1_of_fabs
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) f hnn :=
  T.2.1


def pack_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn :=
  T.2.2


end Sec4Prop42RemainingAtomTools

/-! ## 2. Final abs-pack tools using `sec4_rowToFlat_source` -/

/--
The corrected abs-outer case tools from exactly the three remaining atoms.
-/
noncomputable def sec4_chiFCaseAbsPackTools_of_remainingAtoms
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4ChiFCaseAbsPackTools (S := S) f hnn :=
  Sec4ChiFCaseAbsPackTools.mk
    (rowToFlat := sec4_rowToFlat_source (S := S))
    (fabs_of_rows_s1 := Sec4Prop42RemainingAtomTools.fabs_of_rows_s1 T)
    (pack_on_s1_of_fabs := Sec4Prop42RemainingAtomTools.pack_on_s1_of_fabs T)
    (pack_on_s2 := Sec4Prop42RemainingAtomTools.pack_on_s2 T)


/--
The already-completed `Sec4ChiFCaseToolsData` package from the three remaining
atoms.
-/
noncomputable def sec4_chiFCaseToolsData_of_remainingAtoms
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4ChiFCaseToolsData (S := S) f hnn :=
  sec4_chiFCaseToolsData_of_absPackTools f hnn
    (sec4_chiFCaseAbsPackTools_of_remainingAtoms f hnn T)


/-! ## 3. Final measurable relative integral bridges -/

/-- Final tools from the three remaining atoms. -/
noncomputable def sec4_prop42FinalTools_of_remainingAtoms
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  sec4_prop42FinalTools_of_absPackTools B hB f hnn
    (sec4_chiFCaseAbsPackTools_of_remainingAtoms f hnn T)


/--
Unconditional value bridge for general measurable relative integral, provided
only the three remaining `prop_4_2` atoms.
-/
noncomputable def sec4_genIBValueBridge_of_remainingAtoms
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_absPackTools B hB f hnn
    (sec4_chiFCaseAbsPackTools_of_remainingAtoms f hnn T)


/--
Consistency theorem for already integrable complemented sets, provided only
the three remaining `prop_4_2` atoms.
-/
theorem sec4_genRelIntegral_eq_relIntegral_of_remainingAtoms
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_absPackTools C hC f hnn
    (sec4_chiFCaseAbsPackTools_of_remainingAtoms f hnn T)


/--
Packaged consistency bridge for already integrable complemented sets, provided
only the three remaining `prop_4_2` atoms.
-/
noncomputable def sec4_genIBConsistencyBridge_of_remainingAtoms
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RemainingAtomTools (S := S) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_absPackTools C hC f hnn
    (sec4_chiFCaseAbsPackTools_of_remainingAtoms f hnn T)


end BishopC
