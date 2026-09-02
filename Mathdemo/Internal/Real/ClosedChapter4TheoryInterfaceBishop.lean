import Mathdemo.Internal.Real.Prop412Chapter4Data

set_option linter.style.longLine false

/-!
# G204: closed Chapter 4 theory interface over Bishop reals

G203 still exposed the source bundle for Proposition 4.12 directly.  This file
packages that bundle as part of a closed Bishop-style Chapter 4 theory:

* measurable functions are elements of a Type-valued family, not bare
  Prop-valued `IsMeasurable` proofs;
* Theorem 4.10 supplies the data-carrying measurable structure internally;
* Definition 4.11 supplies convergence witnesses internally;
* the local representative witnesses are a construction law of the closed
  theory, not an extra argument to Proposition 4.12.

Thus Prop. 4.12 is exported as a theorem of the closed theory.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace ClosedTheory

open SourceComplete412
open Proposition412.TruncatedIntegralBridge








end ClosedTheory
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.ClosedTheory





end BishopCReal
