import Mathdemo.Internal.Real.RemovingGlobalClosedTheoryParameterProp

set_option linter.style.longLine false

/-!
# G206: Chapter 1--3 data-debt audit

G205 made the remaining Proposition 4.12 construction debts explicit.  This file
records the corresponding status for Chapters 1--3: the current mainline does not
carry a Prop.4.12-style undischarged data-carrying assumption before Chapter 4.

The previous G109 selector-based extraction artifact remains available only as a
documented adapter audit.  It is not counted as the Bishop RegularSeq mainline.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqCh1To3AssumptionAudit












end BishopRegularSeqCh1To3AssumptionAudit

open BishopRegularSeqCh1To3AssumptionAudit





end BishopCReal
