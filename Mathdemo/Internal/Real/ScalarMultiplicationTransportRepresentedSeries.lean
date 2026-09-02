import Mathdemo.Internal.Real.TermwiseSeriesTransportNegativeOneScalar

set_option linter.style.longLine false

/-!
# G146: scalar multiplication transport for represented series

G145 closed termwise transport and the negative-one scalar recovery.  This file
closes the reusable fixed-scalar series transport.  As a result, the remaining
half-scalar recovery is reduced to a termwise representative identity
`|u| ~ 2 * |(1/2)u|`, rather than a series-level mystery.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24HalfRecover

open Prop24RefinedSeriesFrontier
open Prop24ScalarRecover










end Prop24HalfRecover
end BishopRegularSeqChapter2





end BishopCReal
