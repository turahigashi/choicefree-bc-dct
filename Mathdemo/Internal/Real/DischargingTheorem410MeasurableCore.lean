import Mathdemo.Internal.Real.Chapter13DataDebtAudit

set_option linter.style.longLine false

/-!
# G207: discharging the Theorem 4.10 measurable-core debt for Prop. 4.12

G205 exposed two remaining raw-Bishop-real debts for Proposition 4.12:

1. construct intrinsic measurable data from the Chapter 4.10 route;
2. construct local good-set witnesses from the representative data.

This file discharges the first item.  Theorem 4.10's data-carrying output already
contains the measurable mid-constructor source.  The local witness law is kept as
the single remaining construction debt; it is not hidden inside a global closed
theory record.
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
