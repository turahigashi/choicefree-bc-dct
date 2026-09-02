import Mathdemo.Internal.Real.RefinedNonnegativeSubseriesFrontierProposition2

set_option linter.style.longLine false

/-!
# G145: termwise series transport and the negative-one scalar recover

G144 refined the Proposition 2.4 scalar frontier to scalar-specific recovery
for `1/2` and `-1`.  This file closes the reusable termwise-transport lemma
for `BishopRegularSeqSeriesSum` and uses it to construct the `-1` recovery
data from the already proved representative identity `|-u| = |u|`.

The half-scalar recovery remains the real scalar-rescaling frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24ScalarRecover

open Prop24RefinedSeriesFrontier









end Prop24ScalarRecover
end BishopRegularSeqChapter2





end BishopCReal
