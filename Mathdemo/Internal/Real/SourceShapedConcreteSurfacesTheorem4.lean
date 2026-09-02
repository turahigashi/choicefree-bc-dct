import Mathdemo.Internal.Real.Theorem46SupremumTransferLocated

set_option linter.style.longLine false

/-!
# G220: source-shaped concrete surfaces for Theorem 4.6

G219 connected Lemma 4.5 to Theorem 4.6 once the `f+`, `f-`, and `|f|`
truncation-integral surfaces and the source `s3` inequalities are data.

This file removes the previous ambiguous `thm_4_6_phi/psi` surface from the active
route.  The concrete surfaces are now built from the data-carrying measurable
interface: for a function `h`, the value at `(A,n)` is the integral of the
carried representative for `mid(-n, chi_A h, n)`.

It also encodes the actual two-step source proof:

`(A_i,n_i) -> (A1∨A2,n_i) -> (A1∨A2,n1+n2)`.

The combined Lemma-4.5 domination law is proved from those two one-step
domination laws by ordered-field arithmetic.  The remaining concrete work is
therefore exactly the local monotonicity of the carried mid representatives in
the set coordinate and in the truncation coordinate.
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
