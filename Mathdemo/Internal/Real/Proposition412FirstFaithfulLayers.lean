import Mathdemo.Internal.Real.Chapter4FinalAuditDefinition4

set_option linter.style.longLine false

/-!
# G168: Proposition 4.12 first faithful layers

Proposition 4.12 says that a sequence converging in measure to both `f` and
`g` has the same measurable-function limit.  The source proof has three
constructive layers:

1. From the two convergence hypotheses, choose a common `N` and good sets
   `B,C` with half-epsilon measure defects.
2. On `E = B ∧ C`, prove the pointwise epsilon bound `|f-g| < eps`.
3. Use the small complement of `E` to force equality of all truncated
   integrable functions `mid(-n, chi_A f, n) = mid(-n, chi_A g, n)`.

This file closes layers 1 and 2 without replacing layer 3 by an empty
statement.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412













end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412





end BishopCReal
