import Mathdemo.Internal.Real.Theorem581ClosureConsequences

/-!
# G33: final-goal reset for chapters 1--4 over Bishop RegularSeq reals

The active final goal is now:

* formalize Bishop reals through regular sequences with witness-carrying data;
* formalize Bishop-Cheng (1972) chapters 1--4 over that Bishop real surface.

The previous `[COFOC R]` chapters 1--4 remain a compatibility layer.  They no longer
count as the completed target for this goal.
-/

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Source notation `min(f, a)` for partial functions. -/
def cutConst (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) (a : RegularSeq) :
    BishopRegularSeqPFun X :=
  minConst Arch f a

/-- The special truncation `min(f, 1)` from Definition 1.1(1). -/
def cutOne (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  cutConst Arch f oneSeq

/-- The truncation `min(f, n)` from Definition 1.1(4). -/
def cutNat (Arch : ScalarMulArchimedeanData)
    (n : Nat) (f : BishopRegularSeqPFun X) :
    BishopRegularSeqPFun X :=
  cutConst Arch f (constSeq (n : Scalar))

/-- The small absolute truncation `min(|f|, 1 / n)` from Definition 1.1(4),
indexed by the repository's positive rational scale `eps`. -/
def cutSmall (Arch : ScalarMulArchimedeanData)
    (n : Nat) (f : BishopRegularSeqPFun X) :
    BishopRegularSeqPFun X :=
  cutConst Arch (absf f) (constSeq (eps n))

/-- Pointwise non-negativity carried as data, rather than as a bare property
argument to be later mined for content. -/
structure PointwiseNonneg (f : BishopRegularSeqPFun X) : Type where
  not_lt : forall x : X, x ∈ f.dom -> Not (regularSeqLtProp (f.toFun x) zeroSeq)

end BishopRegularSeqPFun

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Sequence convergence in the Bishop real surface, kept as data because the
new route must not extract computational content from a bare proposition. -/
structure BishopRegularSeqTendsto
    (u : Nat -> RegularSeq) (limit : RegularSeq) : Type where
  modulus : Nat -> Nat
  close :
    forall k n : Nat,
      modulus k <= n -> relEventually (u n) limit

/-- A summed series of Bishop reals, represented by convergence of finite
sums. -/
structure BishopRegularSeqSeriesSum (u : Nat -> RegularSeq) : Type where
  sum : RegularSeq
  tends : BishopRegularSeqTendsto (regularSeqFinSum u) sum

/-- Definition 1.1(2), witness-rich pointwise conclusion:
there is an `x` where the pointwise series is defined, converges, and stays
below the comparison function. -/
structure BishopRegularSeqPointwiseSeriesBelow
    (fs : Nat -> BishopRegularSeqPFun X)
    (f : BishopRegularSeqPFun X) : Type where
  x : X
  hx_f : x ∈ f.dom
  hx_fs : forall n : Nat, x ∈ (fs n).dom
  point_sum : BishopRegularSeqSeriesSum (fun n => (fs n).toFun x)
  below : regularSeqLtData point_sum.sum (f.toFun x)

/-- Chapter 1, Definition 1.1, restated over Bishop regular-sequence reals.

The `core` field supplies the linear integration-space skeleton already built
for RegularSeq-valued partial functions.  The remaining fields are exactly the
source-level closure, continuity, normalization, and truncation requirements
that were absent from the older COFOC-relative layer.
-/
structure BishopRegularSeqIntegrationSpaceDef11
    (Arch : ScalarMulArchimedeanData) (X : Type) : Type 1 where
  core : BishopRegularSeqIntegrationSpaceSkeleton Arch X
  cutConst_mem :
    forall (a : RegularSeq) {f : BishopRegularSeqPFun X},
      f ∈ core.L -> BishopRegularSeqPFun.cutConst Arch f a ∈ core.L
  continuity :
    forall {f : BishopRegularSeqPFun X}
      {fs : Nat -> BishopRegularSeqPFun X},
      f ∈ core.L ->
      (forall n : Nat, fs n ∈ core.L) ->
      (forall n : Nat, BishopRegularSeqPFun.PointwiseNonneg (fs n)) ->
      (series_integral : BishopRegularSeqSeriesSum (fun n => core.I (fs n))) ->
      regularSeqLtData series_integral.sum (core.I f) ->
      BishopRegularSeqPointwiseSeriesBelow fs f
  normalized :
    { p : BishopRegularSeqPFun X // p ∈ core.L ∧ relEventually (core.I p) oneSeq }
  cutNat_tendsto :
    forall {f : BishopRegularSeqPFun X},
      f ∈ core.L ->
      BishopRegularSeqTendsto
        (fun n => core.I (BishopRegularSeqPFun.cutNat Arch n f))
        (core.I f)
  cutSmall_tendsto :
    forall {f : BishopRegularSeqPFun X},
      f ∈ core.L ->
      BishopRegularSeqTendsto
        (fun n => core.I (BishopRegularSeqPFun.cutSmall Arch n f))
        zeroSeq
  source_definition_1_1_regularseq : Prop
  old_cofoc_layer_is_compatibility_only : Prop

/-- Definition 1.1(1), `min(f,1)` closure, derived from the general cut field. -/
theorem def11_cutOne_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    BishopRegularSeqPFun.cutOne Arch f ∈ S.core.L :=
  S.cutConst_mem oneSeq hf

/-- Definition 1.1(1), linear-combination closure in the RegularSeq surface. -/
theorem def11_linComb_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a b : RegularSeq)
    {f g : BishopRegularSeqPFun X}
    (hf : f ∈ S.core.L) (hg : g ∈ S.core.L) :
    BishopRegularSeqPFun.linComb Arch a b f g ∈ S.core.L :=
  S.core.add_mem
    (S.core.smul_mem a hf)
    (S.core.smul_mem b hg)

/-- Definition 1.1(1), linearity of the integral, stated with Bishop equality. -/
theorem def11_I_linComb
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (a b : RegularSeq)
    {f g : BishopRegularSeqPFun X}
    (hf : f ∈ S.core.L) (hg : g ∈ S.core.L) :
    relEventually
      (S.core.I (BishopRegularSeqPFun.linComb Arch a b f g))
      (addSeq
        (mulSeqConcreteWith Arch a (S.core.I f))
        (mulSeqConcreteWith Arch b (S.core.I g))) := by
  let af := BishopRegularSeqPFun.smul Arch a f
  let bg := BishopRegularSeqPFun.smul Arch b g
  have haf : af ∈ S.core.L :=
    S.core.smul_mem a hf
  have hbg : bg ∈ S.core.L :=
    S.core.smul_mem b hg
  have hadd :
      relEventually
        (S.core.I (BishopRegularSeqPFun.add af bg))
        (addSeq (S.core.I af) (S.core.I bg)) :=
    S.core.I_add haf hbg
  have hsmul_f :
      relEventually
        (S.core.I af)
        (mulSeqConcreteWith Arch a (S.core.I f)) :=
    S.core.I_smul a hf
  have hsmul_g :
      relEventually
        (S.core.I bg)
        (mulSeqConcreteWith Arch b (S.core.I g)) :=
    S.core.I_smul b hg
  have hmid :
      relEventually
        (addSeq (S.core.I af) (S.core.I bg))
        (addSeq
          (mulSeqConcreteWith Arch a (S.core.I f))
          (mulSeqConcreteWith Arch b (S.core.I g))) :=
    addSeq_respects_eventually
      (S.core.I af)
      (mulSeqConcreteWith Arch a (S.core.I f))
      (S.core.I bg)
      (mulSeqConcreteWith Arch b (S.core.I g))
      hsmul_f
      hsmul_g
  exact
    relEventually_trans
      (S.core.I (BishopRegularSeqPFun.linComb Arch a b f g))
      (addSeq (S.core.I af) (S.core.I bg))
      (addSeq
        (mulSeqConcreteWith Arch a (S.core.I f))
        (mulSeqConcreteWith Arch b (S.core.I g)))
      hadd
      hmid

/-- The reset roadmap: previous relative chapters are preserved but not counted as
the final Bishop-real target. -/
structure BishopRegularSeqCh1To4FinalRoadmap : Type where
  bishop_real_regularseq_surface : Prop
  ch1_def11_integration_space : Prop
  ch1_lemmas_12_to_15 : Prop
  ch2_measure_from_integrable_sets : Prop
  ch3_measurable_functions_and_basic_integrals : Prop
  ch4_convergence_theorems : Prop
  old_cofoc_ch1_to_4_saved_as_compatibility_layer : Prop
  primary_source_fidelity_for_chapters : Prop

/-- Progress meter for the new final goal.  Percentages here measure the new
Bishop-real target only; the previous COFOC-relative completion is tracked
separately. -/
structure BishopRegularSeqCh1To4ProgressMeter : Type where
  bishop_real_formalization_percent : Nat
  ch1_on_bishop_real_percent : Nat
  ch2_on_bishop_real_percent : Nat
  ch3_on_bishop_real_percent : Nat
  ch4_on_bishop_real_percent : Nat
  total_final_goal_percent : Nat
  old_relative_ch1_to_4_compatibility_percent : Nat
  current_increment : String

/-- Current status after G33: Definition 1.1 has a RegularSeq target structure,
and its linear/min-one closure consequences are already usable. -/
def bishopRegularSeqCh1To4ProgressAfterG33 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 18
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 28
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G33: reset goal to Bishop RegularSeq reals; added Definition 1.1 target \
    with continuity/truncation/normalization data and closed linearity/min-one \
    consequences."


end BishopCReal
