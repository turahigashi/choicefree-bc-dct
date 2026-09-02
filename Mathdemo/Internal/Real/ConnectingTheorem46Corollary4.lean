import Mathdemo.Internal.Real.AttachingScalarTheorem46Laws

set_option linter.style.longLine false

/-!
# G226: connecting Theorem 4.6 to Corollary 4.7 and Theorem 4.10

G225 closed the representative-level monotonicity and increment witnesses needed
for the strengthened Theorem 4.6 route.  This file packages that result in the
source-level form used downstream:

* Corollary 4.7 receives its source data explicitly: data-carrying measurable
  witnesses for `f+`, `f-`, `|f|`, and a located supremum for the `|f|` surface.
* Theorem 4.6 then supplies located suprema for the positive and negative parts.
* Theorem 4.10's data-carrying output is connected by wrapping the already
  carried measurable data, not by selecting a representative from a Prop proof.

No previous `IsMeasurable`/choice interface is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge
open SourceComplete412











end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46



end BishopCReal
