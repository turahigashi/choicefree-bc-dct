import Mathdemo.Internal.Sec4.Chapter4SourceCompletion

/-!
# Sec4 Phase2-D2b2b_beta-b2b35: local full-set rows for Proposition 4.2

This file changes the direction of the Proposition 4.2 residual.

The older residual `Sec4Prop42CharacteristicDomainWitness` asked for a global
map from membership in `A.S1` or `A.S2` to an absolute-convergence witness for
the chosen characteristic representative.  That is stronger than the printed
Bishop proof: the proof works on a suitable full set where the relevant
representatives already have pointwise absolute-convergence data.

The source-faithful local interface below keeps those two layers separate:

* the support `D(chi_A) cap D(f)` is full as a proposition;
* pointwise calculations receive an explicit `Sec4Prop42LocalWitness`, so no
  Type-level data is extracted from the propositional full-set assertion.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. The full support used by the printed Proposition 4.2 argument -/





/-! ## 2. Type-level local witnesses for calculations on that support -/



namespace Sec4Prop42LocalWitness







end Sec4Prop42LocalWitness

/-! ## 3. Standard Proposition 4.2 rows from local witnesses -/









/-! ## 4. Characteristic value facts go from witness to membership/value -/







end BishopC
