import Mathdemo.Internal.Real.Chapter2CharacteristicFormulasProposition2

set_option linter.style.longLine false

/-!
# G135: RegularSeq truth-table kernel for Chapter 2 Proposition 2.4

G134 fixed the carried characteristic-function formulas:

* `chi(A ∧ B) = 1/2 * ((chi A + chi B) - |chi A - chi B|)`;
* `chi(A ∨ B) = chi A + chi B - chi(A ∧ B)`.

This file closes the reusable RegularSeq arithmetic kernel for the `0/1`
truth table.  The set-level case split and the Definition 1.6 value-law
transport remain separate data; the scalar/representative `0/1` calculations
are now available without quotient representative extraction.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace CharacteristicTruthTable



















end CharacteristicTruthTable
end BishopRegularSeqChapter2





end BishopCReal
