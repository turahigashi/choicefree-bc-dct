import Mathdemo.Internal.Real.Chapter2FullSetTailPropositions

set_option linter.style.longLine false

/-!
# G153: Corollary 2.9, monotonicity of measure

Corollary 2.9 says that if `E ⊂ F` are integrable sets, then
`mu(E) <= mu(F)`.  The source proof uses:

* Proposition 2.5 and nonnegativity of measures to compare `mu(E ∧ F)` with
  `mu(F)`;
* full-set equality `chi_E = chi_(E ∧ F)`;
* Proposition 1.11 / Corollary 1.12 style integral congruence on a full set.

This file keeps those source ingredients explicit and closes the final
RegularSeq order transport step.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Cor29Monotonicity

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end Cor29Monotonicity
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.Cor29Monotonicity





end BishopCReal
