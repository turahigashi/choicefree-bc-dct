import Mathdemo.Internal.Real.BishopFaithfulMeasureSkeletonRegularSeqReals
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








end BishopCReal
