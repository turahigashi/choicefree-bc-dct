import Mathdemo.Internal.Real.ConnectingTheorem46Corollary4

set_option linter.style.longLine false

/-!
# G227: final Chapter 4 route to Proposition 4.12

G226 connected the strengthened Theorem 4.6 data to Corollary 4.7 and the
data-carrying Theorem 4.10 output.  G215 already connected data-carrying
measurability, Definition 4.11 convergence data, and definition-facing
characteristic witnesses to the no-seed Proposition 4.12 truncated-integral
equality.

This file records the end-to-end route:

* Theorem 4.10 output is a data object carrying `mid_constructor_source`.
* Definition 4.11 convergence remains a theorem premise, as in the source text.
* Characteristic witnesses are read from the integrable-set definition.
* Proposition 4.12's truncated-integral equality follows without a Prop-to-data
  selector or an external choice principle.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Chapter4To412Final

open SourceComplete412
open Proposition412.TruncatedIntegralBridge
open Prop412AssumptionDischarge
open Lemma45Theorem46






end Chapter4To412Final
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Chapter4To412Final



end BishopCReal
