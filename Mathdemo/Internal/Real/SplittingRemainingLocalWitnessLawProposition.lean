import Mathdemo.Internal.Real.DischargingTheorem410MeasurableCore

set_option linter.style.longLine false

/-!
# G208: splitting the remaining local-witness law for Proposition 4.12

G207 removed the global closed-theory wrapper and discharged the Theorem 4.10
measurable-core part of Proposition 4.12.  The remaining datum was the local
good-set witness law.

This file does not mark that analytic frontier as complete.  Instead it replaces
the one large law-shaped assumption by the two source obligations it actually
contains:

1. pointwise absolute convergence of the characteristic representative of `A`
   on each common good set;
2. pointwise seed data for the complement and bad-set representatives built
   from the explicit mid representatives.

Thus the debt is no longer hidden behind a Prop.4.12-level wrapper.  The
remaining work is visibly at representative-data level, where it must be
discharged from the Bishop-real source information.
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
