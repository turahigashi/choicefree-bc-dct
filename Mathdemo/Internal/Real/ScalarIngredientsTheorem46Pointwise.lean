import Mathdemo.Internal.Real.LiftingLocalPointwiseMidInequalitiesTheorem

set_option linter.style.longLine false

/-!
# G222: scalar ingredients for the Theorem 4.6 pointwise laws

G221 reduced the remaining Theorem 4.6 local domination obligation to
pointwise inequalities between carried mid representative values.

This file closes the scalar ingredients used by those pointwise inequalities:
nonnegativity of `f+`, `f-`, and `|f|`; the bounds `f+ ≤ |f|` and `f- ≤ |f|`;
and the behavior of `mid(-n,z,n)` on nonnegative arguments.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge




















end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46



end BishopCReal
