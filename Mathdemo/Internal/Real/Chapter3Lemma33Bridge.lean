import Mathdemo.Internal.Real.Chapter3Definitions313

set_option linter.style.longLine false

/-!
# G158: Chapter 3 Lemma 3.3 bridge

Definitions 3.1 and 3.2 are now exposed on the RegularSeq Chapter 3 chain.
This file connects Bishop--Cheng Lemma 3.3.

There are two deliberately separate layers:

* `lemma33_available` exposes the existing source theorem, whose Lean statement
  is `Nonempty (Lemma33Result ...)`;
* `Lemma33ExplicitData` and its accessors are the data-carrying layer used by
  subsequent transport steps.  They do not choose from `Nonempty`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter3
namespace Lemma33Bridge


















end Lemma33Bridge
end BishopRegularSeqChapter3

open BishopRegularSeqChapter3.Lemma33Bridge





end BishopCReal
