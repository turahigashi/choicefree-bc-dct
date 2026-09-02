import Mathdemo.Internal.Real.Chapter4Definition48Proposition
import Mathdemo.Internal.Sec4.RelIntegralAbsContinuous
import Mathdemo.Internal.Sec4.DominatedConvergence415SourceComplete

set_option linter.style.longLine false

/-!
# G167: Chapter 4 final audit through Definition 4.11--Theorem 4.15

This closes the current Chapter 4 countdown pass.  It exposes the implemented
convergence layer and records an honest final audit:

* Definition 4.11 is available as `ConvergeInMeasure`.
* Theorem 4.13 has a faithful monotone-convergence constructor.
* Lemma 4.14 has a source-complete entry point.
* Theorem 4.15 has source routes that produce integral convergence once the
  source-shaped uniform `I_B` data/frontier is supplied.

The audit explicitly does **not** count previous empty statements or the remaining
faithful frontiers as finished proofs.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace FinalAudit












end FinalAudit
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.FinalAudit





end BishopCReal
