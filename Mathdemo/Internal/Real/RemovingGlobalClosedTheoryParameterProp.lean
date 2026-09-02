import Mathdemo.Internal.Real.ClosedChapter4TheoryInterfaceBishop

set_option linter.style.longLine false

/-!
# G205: removing the global closed-theory parameter from Prop. 4.12

G204 still used a global `BishopRealChapter4ClosedTheory` parameter.  That was
useful for closing the Prop. 4.12 proof shape, but it also hid construction
obligations inside a theory record.

This file removes that global parameter.  The remaining data are attached to the
Bishop measurable function object itself.  This is still not the final
raw-Bishop-real discharge: the intrinsic function data must next be constructed
from the earlier Chapter 4 development, especially the data-carrying 4.10 route
and the local representative-witness synthesis.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Prop412AssumptionDischarge

open Proposition412.TruncatedIntegralBridge
open SourceComplete412







end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Prop412AssumptionDischarge





end BishopCReal
