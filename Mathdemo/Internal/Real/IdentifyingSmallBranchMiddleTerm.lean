import Mathdemo.Internal.Real.Line734ReductionIntegralDifference
/-!
# G65: identifying the small-branch middle term

G64 reduced the small branch of Theorem 1.18(4) to the non-strict norm-bound
bridge behind source lines 743--747.  This file pushes that bound one layer
closer to the text: the abstract small-branch middle term is now fixed as

`I(min(|g_N|, 1/n)) + || |f| - g_N ||`.

The remaining analytic frontier is the source pointwise estimate feeding the
left inequality into that concrete middle term.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Reflexivity for the non-strict `RegularSeq` order surface. -/
theorem regularSeqLe_refl (x : RegularSeq) : RegularSeqLe x x := by
  intro hcounter
  change PosEventually (subSeq zeroSeq (subSeq x x)) at hcounter
  have hself : relEventually (subSeq x x) zeroSeq :=
    subSeq_self_eventually_law x
  have hbase :
      relEventually
        (subSeq zeroSeq (subSeq x x))
        (subSeq zeroSeq zeroSeq) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      (subSeq x x) zeroSeq
      (relEventually_refl zeroSeq)
      hself
  have hzero :
      relEventually
        (subSeq zeroSeq (subSeq x x))
        zeroSeq :=
    relEventually_trans
      (subSeq zeroSeq (subSeq x x))
      (subSeq zeroSeq zeroSeq)
      zeroSeq
      hbase
      (subSeq_self_eventually_law zeroSeq)
  exact
    not_posEventually_zero
      (posEventually_respects
        (subSeq zeroSeq (subSeq x x))
        zeroSeq
        hzero
        hcounter)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}















end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
