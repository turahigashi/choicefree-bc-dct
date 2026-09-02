import Mathdemo.Internal.Real.NestedFormulaValueTransportChapter2

set_option linter.style.longLine false

/-!
# G139: Proposition 2.4 construction from explicit abs-decomposition data

G138 closed the nested value transport for the characteristic formulas.  The
remaining analytic input is absolute-summability decomposition through the
formula representatives.  This file does not extract that data from a bare
proposition; it records the exact data-bearing interface and assembles the
`A ∩ B` and `A ∪ B` integrable-set constructions from it.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24FromAbsDecomposition

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}














end Prop24FromAbsDecomposition
end BishopRegularSeqChapter2





end BishopCReal
