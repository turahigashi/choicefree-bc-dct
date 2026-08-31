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

/-- Difference of partial functions, with domain intersection. -/
def sub (Arch : ScalarMulArchimedeanData)
    (f g : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  linComb Arch oneSeq (negSeq oneSeq) f g

/-- Positive part in the source proof of Lemma 1.5, expressed by
`1/2 * (h + |h|)`. -/
def posFormula (Arch : ScalarMulArchimedeanData)
    (h : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  smul Arch halfSeq (add h (absf h))

/-- Source formula `max(f,g) = g + (f-g)^+`. -/
def maxFormula (Arch : ScalarMulArchimedeanData)
    (f g : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  add g (posFormula Arch (sub Arch f g))

/-- Source formula `min(f,g) = -max(-f,-g)`. -/
def minFormula (Arch : ScalarMulArchimedeanData)
    (f g : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  neg Arch (maxFormula Arch (neg Arch f) (neg Arch g))

end BishopRegularSeqPFun

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Closure under additive inverse, derived from scalar closure. -/
theorem def11_neg_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    BishopRegularSeqPFun.neg Arch f ∈ S.core.L :=
  S.core.smul_mem (negSeq oneSeq) hf

/-- Closure under subtraction. -/
theorem def11_sub_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f g : BishopRegularSeqPFun X}
    (hf : f ∈ S.core.L) (hg : g ∈ S.core.L) :
    BishopRegularSeqPFun.sub Arch f g ∈ S.core.L :=
  def11_linComb_mem S oneSeq (negSeq oneSeq) hf hg

/-- Closure of the positive-part formula used in Lemma 1.5. -/
theorem def11_posFormula_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {h : BishopRegularSeqPFun X} (hh : h ∈ S.core.L) :
    BishopRegularSeqPFun.posFormula Arch h ∈ S.core.L :=
  S.core.smul_mem halfSeq
    (S.core.add_mem hh (S.core.abs_mem hh))

/-- Lemma 1.5, maximum part, in the source formula form. -/
theorem lemma15_maxFormula_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f g : BishopRegularSeqPFun X}
    (hf : f ∈ S.core.L) (hg : g ∈ S.core.L) :
    BishopRegularSeqPFun.maxFormula Arch f g ∈ S.core.L :=
  S.core.add_mem hg
    (def11_posFormula_mem S (def11_sub_mem S hf hg))

/-- Lemma 1.5, minimum part, in the source formula form. -/
theorem lemma15_minFormula_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f g : BishopRegularSeqPFun X}
    (hf : f ∈ S.core.L) (hg : g ∈ S.core.L) :
    BishopRegularSeqPFun.minFormula Arch f g ∈ S.core.L := by
  have hnf : BishopRegularSeqPFun.neg Arch f ∈ S.core.L :=
    def11_neg_mem S hf
  have hng : BishopRegularSeqPFun.neg Arch g ∈ S.core.L :=
    def11_neg_mem S hg
  have hmax :
      BishopRegularSeqPFun.maxFormula Arch
        (BishopRegularSeqPFun.neg Arch f)
        (BishopRegularSeqPFun.neg Arch g) ∈ S.core.L :=
    lemma15_maxFormula_mem S hnf hng
  exact def11_neg_mem S hmax

/-- Integral of the additive inverse, with Bishop equality. -/
theorem def11_I_neg
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    relEventually
      (S.core.I (BishopRegularSeqPFun.neg Arch f))
      (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I f)) :=
  S.core.I_smul (negSeq oneSeq) hf

/-- Integral of a difference, as the linearity instance `1*f + (-1)*g`. -/
theorem def11_I_sub
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f g : BishopRegularSeqPFun X}
    (hf : f ∈ S.core.L) (hg : g ∈ S.core.L) :
    relEventually
      (S.core.I (BishopRegularSeqPFun.sub Arch f g))
      (addSeq
        (mulSeqConcreteWith Arch oneSeq (S.core.I f))
        (mulSeqConcreteWith Arch (negSeq oneSeq) (S.core.I g))) :=
  def11_I_linComb S oneSeq (negSeq oneSeq) hf hg

/-- Progress after G34: Lemma 1.5 closure is now available in the new
Bishop-real route. -/
def bishopRegularSeqCh1To4ProgressAfterG34 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 24
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 30
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G34: formalized the Lemma 1.5 max/min closure pattern over Bishop \
    RegularSeq integration spaces."


end BishopCReal
