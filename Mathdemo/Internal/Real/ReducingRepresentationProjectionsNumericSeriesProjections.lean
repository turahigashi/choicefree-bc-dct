import Mathdemo.Internal.Real.ReducingLocalAbsProjectionsRepresentationLevel

set_option linter.style.longLine false

/-!
# G142: reducing representation projections to numeric series projections

G141 reduced Chapter 2 abs-projections to representation-level projection
data for `pairInterleave`, `smulSeq`, and `absRepSeq`.  This file factors
those again to pure RegularSeq series projection bridges:

* binary merged series projection;
* scalar-multiplied absolute series projection;
* ternary merged series middle projection.

This isolates the remaining analytic work in a small series API, instead of
leaving it entangled with L1 representatives or set formulas.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24SeriesProjection

open Prop24RepresentationAbsProjection













end Prop24SeriesProjection
end BishopRegularSeqChapter2





end BishopCReal
