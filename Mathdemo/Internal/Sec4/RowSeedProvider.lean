import Mathdemo.Internal.Sec4.RowSeedTools

/-!
# Sec4 Phase2-D2b2bβ-b2b26: general row-seed provider frontier

The general measurable relative integral `I_B` is constructed unconditionally
as a representative by the earlier Phase2-C files.  The remaining source-faithful
frontier for the full value bridge and consistency theorem is the internal
Proposition 4.2 row/cut machinery packaged as `Sec4Prop42RowSeedTools`.

This file factors that frontier once, at the general `I_B` level, instead of
leaving each downstream theorem to introduce its own local provider.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- General provider for the remaining Proposition 4.2 row/cut tools.

Supplying this provider for every non-negative integrable representative is
exactly the remaining internal `prop_4_2` obligation needed to make the
general measurable `I_B` value bridge and consistency theorem unconditional. -/
structure Sec4GeneralIBRowSeedToolsProvider : Type _ where
  rowSeeds : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42RowSeedTools (S := S) f hnn


/-- Full general measurable `I_B` value bridge from a global row-seed provider. -/
noncomputable def sec4_genIBValueBridge_of_rowSeedToolsProvider
    (P : Sec4GeneralIBRowSeedToolsProvider (S := S))
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_rowSeedTools B hB f hnn
    (P.rowSeeds f hnn)


/-- Consistency with the previous relative integral on integrable sets from a
global row-seed provider. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_rowSeedToolsProvider
    (P : Sec4GeneralIBRowSeedToolsProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_rowSeedTools C hC f hnn
    (P.rowSeeds f hnn)


/-- Packaged consistency bridge from a global row-seed provider. -/
noncomputable def sec4_genIBConsistencyBridge_of_rowSeedToolsProvider
    (P : Sec4GeneralIBRowSeedToolsProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_rowSeedTools C hC f hnn
    (P.rowSeeds f hnn)


end BishopC
