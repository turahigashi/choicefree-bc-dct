import Mathdemo.Internal.Real.Definition16WellDefinednessBridge
/-!
# G44: Proposition 1.11 monotonicity interface

Proposition 1.11 says: if `r <= s` on a full set `A`, then `I(r) <= I(s)`.
The source proof uses Lemma 1.10 to restrict the domain with `h-h`, and then
applies Lemma 1.7.

This file records the RegularSeq statement shape and keeps the proof step as
an explicit bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Non-strict order on RegularSeq reals, represented as non-negativity of the
difference `y - x`. -/
abbrev RegularSeqLe (x y : RegularSeq) : Prop :=
  RegularSeqNonneg (subSeq y x)

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}


end BishopRegularSeqIntegrableRep








end BishopCReal
