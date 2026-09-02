import Mathdemo.Internal.Real.FinalGoalResetChapters14

/-!
# G34: chapter 1, Lemma 1.5 closure over Bishop RegularSeq reals

Lemma 1.5 says that if `f,g in L`, then `max(f,g)` and `min(f,g)` are in `L`.
The source proof uses

* `(f - g)^+ = 1/2 * ((f - g) + |f - g|)`;
* `max(f,g) = g + (f - g)^+`;
* `min(f,g) = -max(-f,-g)`.

This file formalizes that proof pattern over the RegularSeq integration-space
interface from G33.
-/

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Additive inverse of a partial function, using the RegularSeq scalar `-1`. -/
def neg (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  smul Arch (negSeq oneSeq) f





end BishopRegularSeqPFun

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Closure under additive inverse, derived from scalar closure. -/
theorem def11_neg_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    BishopRegularSeqPFun.neg Arch f ∈ S.core.L :=
  S.core.smul_mem (negSeq oneSeq) hf









end BishopCReal
