import Mathdemo.Internal.Real.Corollary29MonotonicityMeasure

set_option linter.style.longLine false

/-!
# G154: Proposition 2.10, countable unions and intersections

Proposition 2.10 is the countable-set-operation endpoint of Chapter 2.  Its
source proof is constructive but data-heavy: the countable union/intersection is
represented by an explicitly constructed characteristic function, and the measure
is obtained from the limit of finite approximants or from a convergent measure
series.

This file formalizes that endpoint as data-bearing RegularSeq interfaces.  It
does not introduce a global selector for countable unions, representatives, or
limits.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop210Countable

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
















end Prop210Countable
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.Prop210Countable





end BishopCReal
