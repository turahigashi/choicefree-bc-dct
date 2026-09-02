import Mathdemo.Internal.Real.LocatedLemma45Transfer

set_option linter.style.longLine false

/-!
# G219: Theorem 4.6 supremum transfer through located Lemma 4.5

This file connects the closed located Lemma 4.5 to the source shape of Theorem
4.6.  The state carries the integrability witness for `A`, so the source
construction `s3 = (A1 ∨ A2, n1+n2)` also carries its witness by
`IntegrableSet1_or`.

The remaining concrete work for Theorem 4.6 is now sharply isolated: prove the
two source inequalities for the actual `f+`, `f-`, and `|f|` truncation
surfaces.  Once those inequalities are data, the positive and negative located
suprema follow by the proven Lemma 4.5 transfer.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46













end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46



end BishopCReal
