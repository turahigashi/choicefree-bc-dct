import Mathdemo.Internal.Sec4.RowToFlat

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



namespace Sec4Prop42RemainingAtomTools









end Sec4Prop42RemainingAtomTools

/-! ## 2. Final abs-pack tools using `sec4_rowToFlat_source` -/





/-! ## 3. Final measurable relative integral bridges -/









end BishopC
