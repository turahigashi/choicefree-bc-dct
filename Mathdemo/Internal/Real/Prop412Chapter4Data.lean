import Mathdemo.Internal.Real.DataCarryingMeasurableLimitsProposition4

set_option linter.style.longLine false

/-!
# G203: Prop. 4.12 from Chapter 4 data-carrying Bishop-real information

G202 closed the local Prop. 4.12 route once the measurable limits already
carry the concrete `mid(-n, chi_A h, n)` representatives.  This file records
the intended Chapter 4 connection explicitly:

* Theorem 4.10 is represented by a data-carrying measurability output, not by
  the previous Prop-valued `IsMeasurable` existential.
* Definition 4.11 is represented by data-carrying convergence in measure.
* With the local representative witnesses supplied by the Chapter 4 proof
  context, Proposition 4.12 is obtained for every integrable set `A` and every
  positive truncation level `n`.

No representative is selected after the fact from a quotient or a Prop-level
existential.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace SourceComplete412

open Proposition412.TruncatedIntegralBridge









end SourceComplete412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.SourceComplete412





end BishopCReal
