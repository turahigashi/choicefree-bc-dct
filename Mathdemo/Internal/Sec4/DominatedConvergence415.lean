import Mathdemo.Internal.Sec4.RelIntegralAbsContinuous

/-!
# Sec4 theorem 4.15: legacy PFunR-compatible DCT wrapper

This file does not try to close the source-level domination and convergence
bridges in one step.  It isolates the verified kernel step:

* set `u_n = |f_n - f|`;
* apply the previous PFunR-compatible lemma 4.14 wrapper to `u_n`;
* obtain `I(|f_n - f|) -> 0`.

The source-complete lemma 4.14 entry point is
`thm_4_14_source_complete` in
`RelIntegralAbsContinuous.lean`.
This file is retained as a compatibility path for earlier 4.15 experiments,
not as the canonical source-faithful 4.15 route.

The remaining bridges are kept as explicit data:

* a faithful PFunR representation and convergence-to-zero datum for `u_n`;
* the uniform `I_B` datum for `u_n`, later derived from domination by `g`;
* the row-seed package needed by the current general measurable integral
  construction.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-! ## PFunR-level error scaffolding -/

/-- The zero partial function used as the target of the DCT error sequence. -/
def thm_4_15_pfun_zero : PFunR X R where
  dom := Set.univ
  toFun := fun _ _ => 0


/-- The zero partial function satisfies the lemma-4.14 zero-function
interface. -/
def thm_4_15_pfun_zero_is_zero :
    Lemma414ZeroPFunR (thm_4_15_pfun_zero (X := X) (R := R)) where
  value_zero := by
    intro x hx
    rfl


/-- Difference of partial functions, on the intersection of their domains. -/
def PFunR.sub (p q : PFunR X R) : PFunR X R where
  dom := p.dom ∩ q.dom
  toFun := fun x hx => p.toFun x hx.1 - q.toFun x hx.2


/-- Absolute value of a partial function, on the same domain. -/
def PFunR.absVal (p : PFunR X R) : PFunR X R where
  dom := p.dom
  toFun := fun x hx => COF.abs (p.toFun x hx)


/-- PFunR-level DCT error sequence `|pfn n - pf|`.

This is only the source-side shape.  Convergence of this sequence to zero is
still passed as Type-valued data, matching the choice-free lemma-4.14 API. -/
def thm_4_15_pfun_abs_error
    (pfn : Nat -> PFunR X R) (pf : PFunR X R) : Nat -> PFunR X R :=
  fun n => (PFunR.sub (pfn n) pf).absVal


/-- Type-valued PFunR convergence in measure, from `pfn` to `pf`.

This is the nonzero-target analogue of `Lemma414PFunConvergeToZeroData`.
It keeps the witnesses as data, avoiding extraction from the Prop-valued
`ConvergeInMeasure`. -/
structure Lemma415PFunConvergeData
    (pfn : Nat -> PFunR X R) (pf : PFunR X R) : Type _ where
  close : forall (A : BSet X) (hA : IntegrableSet1 S A)
      (eps : R), COF.lt 0 eps ->
    Sigma (fun N : Nat =>
      forall n, N <= n ->
        Sigma (fun C : BSet X =>
          Sigma (fun hC : IntegrableSet1 S C =>
            PProd (C.S1 ⊆ A.S1 ∩ pf.dom ∩ (pfn n).dom)
              (PProd
                (COF.lt (measure1 S (IntegrableSet1_sub hA hC)) eps)
                (forall (x : X) (_hxC : x ∈ C.S1)
                    (hxpf : x ∈ pf.dom) (hxfn : x ∈ (pfn n).dom),
                  COF.lt
                    (COF.abs (pf.toFun x hxpf - (pfn n).toFun x hxfn))
                    eps)))))


/-- If `pfn -> pf` in the Type-valued PFunR sense, then the absolute error
sequence `|pfn - pf|` converges to the canonical zero PFunR. -/
def lemma_4_15_pfun_abs_error_converge_to_zero
    (pfn : Nat -> PFunR X R) (pf : PFunR X R)
    (hconv : Lemma415PFunConvergeData (S := S) pfn pf) :
    Lemma414PFunConvergeToZeroData (S := S)
      (thm_4_15_pfun_abs_error pfn pf)
      (thm_4_15_pfun_zero (X := X) (R := R)) where
  close := by
    intro A hA eps heps
    obtain ⟨N, hN⟩ := hconv.close A hA eps heps
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hsubset, hmeasure, hpoint⟩ := hN n hn
    refine ⟨C, hC, ?_⟩
    refine ⟨?_, ?_⟩
    · intro x hxC
      have hxpack := hsubset hxC
      exact ⟨⟨hxpack.1.1, trivial⟩, ⟨hxpack.2, hxpack.1.2⟩⟩
    refine ⟨hmeasure, ?_⟩
    intro x hxC hxz hxerr
    have hxpf : x ∈ pf.dom := hxerr.2
    have hxfn : x ∈ (pfn n).dom := hxerr.1
    have hpt := hpoint x hxC hxpf hxfn
    change COF.lt
      (COF.abs ((0 : R) -
        COF.abs ((pfn n).toFun x hxfn - pf.toFun x hxpf))) eps
    have hzero_abs :
        (0 : R) - COF.abs ((pfn n).toFun x hxfn - pf.toFun x hxpf) =
          - COF.abs ((pfn n).toFun x hxfn - pf.toFun x hxpf) := by
      ring
    rw [hzero_abs, COFO.abs_neg,
      COFO.abs_of_nonneg
        (abs_nonneg ((pfn n).toFun x hxfn - pf.toFun x hxpf))]
    have hsym :
        (pfn n).toFun x hxfn - pf.toFun x hxpf =
          - (pf.toFun x hxpf - (pfn n).toFun x hxfn) := by
      ring
    rw [hsym, COFO.abs_neg]
    exact hpt


/-- The nonnegative error sequence used in Bishop--Cheng theorem 4.15:
`u_n = |f_n - f|`. -/
noncomputable def thm_4_15_abs_error
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) :
    Nat -> IntegrableRep S :=
  fun n => ((fn n).sub f).absVal


/-- If a three-way merged series converges, then the termwise sum of each
triple converges to the same value. -/
def seriesSum_add3_of_merge3 {u v w : Nat -> R}
    (h : RSeq.SeriesSum (seqMerge3 u v w)) :
    RSeq.SeriesSum (fun k => u k + v k + w k) where
  sum := h.sum
  tends :=
    { mod := h.tends.mod
      close := by
        intro k N hN
        change COF.lt
          (COF.abs (RSeq.partialSum (fun k => u k + v k + w k) N - h.sum))
          (COF.halfPow k)
        rw [partialSum_add (fun k => u k + v k) w N, partialSum_add u v N]
        rw [← partialSum_merge3_a u v w N]
        exact h.tends.close k (3 * N + 2) (by omega) }


/-- Extract the middle component from a nonnegative three-way merged series. -/
def seriesSum_merge3_second_of_nonneg {u v w : Nat -> R}
    (hu : forall n, Nonneg (u n))
    (hv : forall n, Nonneg (v n))
    (hw : forall n, Nonneg (w n))
    (h : RSeq.SeriesSum (seqMerge3 u v w)) : RSeq.SeriesSum v :=
  seriesSum_comparison hv
    (fun n => le_of_nonneg_sub (show Nonneg ((u n + v n + w n) - v n) from by
      rw [show (u n + v n + w n) - v n = u n + w n from by ring]
      exact nonneg_add (hu n) (hw n)))
    (seriesSum_add3_of_merge3 h)


/-- The absolute-value representative is nonnegative at every point of its
own absolute-convergence domain. -/
theorem repNonneg_absVal (r : IntegrableRep S) : RepNonneg r.absVal := by
  intro x habsDom habs hx
  let hrDom : r.MemAt x := fun k => by
    have hk := habsDom (3 * k + 1)
    simpa only [IntegrableRep.absVal, seqMerge3_one] using hk
  let u : Nat -> R := fun j =>
    COF.abs ((r.absDiffFn j).toFun x (r.absDiffFn_memAt hrDom j))
  let v : Nat -> R := fun k => COF.abs (r.valueAt x hrDom k)
  let w : Nat -> R := fun k =>
    COF.abs ((BFunR.smul (-1) (r.fn k)).toFun x (hrDom k))
  have hmerge : RSeq.SeriesSum (seqMerge3 u v w) := by
    refine seriesSum_congr (fun n => ?_) habs
    dsimp [u, v, w]
    rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_zero]
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_one]
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_two]
  have hfabs : RSeq.SeriesSum
      (fun k => COF.abs (r.valueAt x hrDom k)) := by
    dsimp [v] at hmerge ⊢
    exact seriesSum_merge3_second_of_nonneg
      (u := u) (v := v) (w := w)
      (fun _ => abs_nonneg _)
      (fun _ => abs_nonneg _)
      (fun _ => abs_nonneg _)
      hmerge
  let hfsum : RSeq.SeriesSum (fun k => r.valueAt x hrDom k) :=
    seriesSum_of_abs hfabs
  obtain ⟨habsValSum, habsValEq⟩ :=
    r.absVal_signed_value x hrDom hfsum
  have hx_eq : hx.sum = COF.abs hfsum.sum := by
    rw [seriesSum_unique hx habsValSum, habsValEq]
  rw [hx_eq]
  exact abs_nonneg _


/-- Nonnegativity of the theorem-4.15 error sequence is automatic from
`absVal`. -/
theorem thm_4_15_abs_error_nonneg
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) :
    forall n, RepNonneg (thm_4_15_abs_error (S := S) fn f n) :=
  fun n => repNonneg_absVal ((fn n).sub f)


/-- If `r` and `s` faithfully represent PFunRs `p` and `q`, then the rep-level
absolute error `|r-s|` faithfully represents the PFunR-level absolute error
`|p-q|`. -/
noncomputable def lemma_4_15_abs_error_represents_from_pfun_sources
    (r s : IntegrableRep S) (p q : PFunR X R)
    (hr : Lemma414RepresentsPFunR (S := S) r p)
    (hs : Lemma414RepresentsPFunR (S := S) s q) :
    Lemma414RepresentsPFunR (S := S)
      ((r.sub s).absVal) ((PFunR.sub p q).absVal) where
  value := by
    intro x hp habsAbsValDom habsAbsVal
    let subRep : IntegrableRep S := r.sub s
    let hsubDom : subRep.MemAt x := fun k => by
      have hk := habsAbsValDom (3 * k + 1)
      simpa only [IntegrableRep.absVal, seqMerge3_one] using hk
    let hrDom : r.MemAt x := add_dom_left hsubDom
    let hnegSDom : s.neg.MemAt x := add_dom_right hsubDom
    let hsDom : s.MemAt x := neg_dom hnegSDom
    let u : Nat -> R := fun j =>
      COF.abs ((subRep.absDiffFn j).toFun x
        (subRep.absDiffFn_memAt hsubDom j))
    let v : Nat -> R := fun k =>
      COF.abs (subRep.valueAt x hsubDom k)
    let w : Nat -> R := fun k =>
      COF.abs ((BFunR.smul (-1) (subRep.fn k)).toFun x (hsubDom k))
    have hmerge : RSeq.SeriesSum (seqMerge3 u v w) := by
      refine seriesSum_congr (fun n => ?_) habsAbsVal
      dsimp [u, v, w, subRep]
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_zero]
      · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_one]
      · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_two]
    have hsub_abs :
        RSeq.SeriesSum (fun k => COF.abs
          ((r.sub s).valueAt x hsubDom k)) := by
      dsimp [v] at hmerge ⊢
      exact seriesSum_merge3_second_of_nonneg
        (u := u) (v := v) (w := w)
        (fun _ => abs_nonneg _)
        (fun _ => abs_nonneg _)
        (fun _ => abs_nonneg _)
        hmerge
    have hr_abs : RSeq.SeriesSum
        (fun k => COF.abs (r.valueAt x hrDom k)) :=
      add_absSeriesSum_left hsubDom hsub_abs
    have hs_abs : RSeq.SeriesSum
        (fun k => COF.abs (s.valueAt x hsDom k)) :=
      neg_absSeriesSum hnegSDom (add_absSeriesSum_right hsubDom hsub_abs)
    let hsub_sum : RSeq.SeriesSum
        (fun k => (r.sub s).valueAt x hsubDom k) :=
      seriesSum_of_abs hsub_abs
    let hr_sum : RSeq.SeriesSum (fun k => r.valueAt x hrDom k) :=
      seriesSum_of_abs hr_abs
    let hs_sum : RSeq.SeriesSum (fun k => s.valueAt x hsDom k) :=
      seriesSum_of_abs hs_abs
    have hsub_eq : hsub_sum.sum = hr_sum.sum - hs_sum.sum := by
      have heq :=
        seriesSum_unique hsub_sum
          (add_seriesSum_value hrDom hnegSDom hr_sum
            (neg_seriesSum_value hsDom hs_sum))
      change hsub_sum.sum = hr_sum.sum + -hs_sum.sum at heq
      rwa [sub_eq_add_neg]
    obtain ⟨habsValSum, habsValEq⟩ :=
      (r.sub s).absVal_signed_value x hsubDom hsub_sum
    have habs_eq :
        (seriesSum_of_abs habsAbsVal).sum = COF.abs hsub_sum.sum := by
      rw [seriesSum_unique (seriesSum_of_abs habsAbsVal) habsValSum, habsValEq]
    have hp_dom : x ∈ p.dom := hp.1
    have hq_dom : x ∈ q.dom := hp.2
    have hr_val := hr.value x hp_dom hrDom hr_abs
    have hs_val := hs.value x hq_dom hsDom hs_abs
    calc
      (seriesSum_of_abs habsAbsVal).sum = COF.abs hsub_sum.sum := habs_eq
      _ = COF.abs (hr_sum.sum - hs_sum.sum) := by rw [hsub_eq]
      _ = COF.abs (p.toFun x hp_dom - q.toFun x hq_dom) := by
        rw [hr_val, hs_val]
      _ = ((PFunR.sub p q).absVal).toFun x hp := rfl


/-- The `I_B` interface for the 4.15 error sequence, instantiated through
the row-seed version of the general measurable integral bridge. -/
noncomputable def thm_4_15_abs_error_ib_from_rowSeeds
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n)) :
    Lemma414IBInterface (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f) :=
  lemma_4_14_ib_interface_from_genIB_rowSeedTools
    (thm_4_15_abs_error (S := S) fn f)
    (thm_4_15_abs_error_nonneg (S := S) fn f)
    hSeeds


/-- Non-`I_B` data needed for theorem 4.15 after the error sequence
`u_n = |f_n - f|` has been formed.

This structure deliberately does not contain uniform integrability.  That is
the remaining `I_B` frontier: deriving the `Lemma414UniformIBData` field from
the domination hypothesis and the general measurable relative integral. -/
structure Lemma415AbsErrorNonIBData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  pfn : Nat -> PFunR X R
  rowSeeds : forall n,
    Sec4Prop42RowSeedTools (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  pfunConverge :
    Lemma414PFunConvergeToZeroData (S := S)
      pfn (thm_4_15_pfun_zero (X := X) (R := R))
  represents : forall n,
    Lemma414RepresentsPFunR (S := S)
      (thm_4_15_abs_error (S := S) fn f n) (pfn n)


/-- Build the non-`I_B` DCT error package from source-level PFunR convergence
`pfn -> pf`.

The remaining representation field states that the chosen PFunR absolute error
actually represents the rep-level error `|f_n-f|`.  This keeps the current
development independent of the provisional `IntegrableRep.toPFunR`. -/
noncomputable def Lemma415AbsErrorNonIBData.of_pfunConverge
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (pfnsrc : Nat -> PFunR X R) (pf : PFunR X R)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hconv : Lemma415PFunConvergeData (S := S) pfnsrc pf)
    (hrep : forall n,
      Lemma414RepresentsPFunR (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_pfun_abs_error pfnsrc pf n)) :
    Lemma415AbsErrorNonIBData (S := S) fn f where
  pfn := thm_4_15_pfun_abs_error pfnsrc pf
  rowSeeds := hSeeds
  pfunConverge :=
    lemma_4_15_pfun_abs_error_converge_to_zero
      (S := S) pfnsrc pf hconv
  represents := hrep


/-- Build the non-`I_B` DCT error package from source-level PFunR convergence
and source-level representation data for `fn` and `f`. -/
noncomputable def Lemma415AbsErrorNonIBData.of_pfunConvergeAndRepresentations
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (pfnsrc : Nat -> PFunR X R) (pf : PFunR X R)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hconv : Lemma415PFunConvergeData (S := S) pfnsrc pf)
    (hrep_fn : forall n,
      Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n))
    (hrep_f : Lemma414RepresentsPFunR (S := S) f pf) :
    Lemma415AbsErrorNonIBData (S := S) fn f :=
  Lemma415AbsErrorNonIBData.of_pfunConverge
    (S := S) fn f pfnsrc pf hSeeds hconv
    (fun n =>
      lemma_4_15_abs_error_represents_from_pfun_sources
        (S := S) (fn n) f (pfnsrc n) pf (hrep_fn n) hrep_f)


/-- The sole theorem-4.15 frontier left when `I_B` generalization is not
expanded here: domination by `g` has to provide the uniform `I_B` datum for
the nonnegative error sequence. -/
structure Lemma415IBUniformFrontierData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (D : Lemma415AbsErrorNonIBData (S := S) fn f) : Type _ where
  dominatedBy : forall n, RepNonneg (g.sub (fn n).absVal)
  uniform : forall eps, COF.lt 0 eps ->
    Lemma414UniformIBData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (thm_4_15_abs_error_ib_from_rowSeeds
        (S := S) fn f D.rowSeeds) eps


/-- Data needed to apply lemma 4.14 to the DCT error sequence
`|f_n - f|`.

The `pfn` field is intentionally not fixed to the current
`IntegrableRep.toPFunR`: that function is still a provisional representative
in this development.  The `represents` field records the faithful link from
the chosen PFunR-level error functions to the rep-level series values. -/
structure Lemma415AbsErrorRowSeedData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S) : Type _ where
  pfn : Nat -> PFunR X R
  zero : PFunR X R
  rowSeeds : forall n,
    Sec4Prop42RowSeedTools (S := S)
      (thm_4_15_abs_error (S := S) fn f n)
      (thm_4_15_abs_error_nonneg (S := S) fn f n)
  uniform : forall eps, COF.lt 0 eps ->
    Lemma414UniformIBData (S := S)
      (thm_4_15_abs_error (S := S) fn f)
      (thm_4_15_abs_error_nonneg (S := S) fn f)
      (thm_4_15_abs_error_ib_from_rowSeeds
        (S := S) fn f rowSeeds) eps
  pfunConverge : Lemma414PFunConvergeToZeroData (S := S) pfn zero
  zero_is_zero : Lemma414ZeroPFunR zero
  represents : forall n,
    Lemma414RepresentsPFunR (S := S)
      (thm_4_15_abs_error (S := S) fn f n) (pfn n)


/-- Assemble the older row-seed data package from the non-`I_B` part and the
single remaining `I_B` uniform-frontier datum. -/
noncomputable def Lemma415AbsErrorRowSeedData.of_nonIB_and_IBFrontier
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (D : Lemma415AbsErrorNonIBData (S := S) fn f)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g D) :
    Lemma415AbsErrorRowSeedData (S := S) fn f where
  pfn := D.pfn
  zero := thm_4_15_pfun_zero (X := X) (R := R)
  rowSeeds := D.rowSeeds
  uniform := U.uniform
  pfunConverge := D.pfunConverge
  zero_is_zero := thm_4_15_pfun_zero_is_zero (X := X) (R := R)
  represents := D.represents


/-- The verified 4.15 kernel step: once the DCT error sequence has the data
required by lemma 4.14, its integrals converge to zero. -/
noncomputable def thm_4_15_abs_error_tendsto_from_rowSeedData
    (fn : Nat -> IntegrableRep S) (f : IntegrableRep S)
    (D : Lemma415AbsErrorRowSeedData (S := S) fn f) :
    RSeq.TendstoHalf
      (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_14_faithful_from_rowSeedTools
    (thm_4_15_abs_error (S := S) fn f)
    (thm_4_15_abs_error_nonneg (S := S) fn f)
    D.pfn D.zero D.rowSeeds D.uniform
    D.pfunConverge D.zero_is_zero D.represents


/-- Theorem 4.15 with every non-`I_B` component separated from the remaining
uniform-integrability frontier. -/
noncomputable def thm_4_15_abs_error_tendsto_from_nonIB_and_IBFrontier
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (D : Lemma415AbsErrorNonIBData (S := S) fn f)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g D) :
    RSeq.TendstoHalf
      (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_15_abs_error_tendsto_from_rowSeedData
    (S := S) fn f
    (Lemma415AbsErrorRowSeedData.of_nonIB_and_IBFrontier
      (S := S) fn f g D U)


/-- Source-shaped DCT data.  The domination hypothesis is recorded here, but
the current theorem still consumes the already-derived abs-error 4.14 data.
The next bridge is to derive `absErrorData.uniform` from `dominatedBy`. -/
structure Lemma415DominatedConvergenceRowSeedData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S) : Type _ where
  dominatedBy : forall n, RepNonneg (g.sub (fn n).absVal)
  absErrorData : Lemma415AbsErrorRowSeedData (S := S) fn f


/-- Bishop--Cheng theorem 4.15, data-reduced row-seed form.

This is the theorem-4.15 target shape `I(|f_n - f|) -> 0`; the source-level
derivation of `absErrorData` from `f_n -> f` in measure and `|f_n| <= g`
is deliberately left as the next bridge rather than hidden behind choice. -/
noncomputable def thm_4_15_dominated_convergence_from_rowSeedData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (D : Lemma415DominatedConvergenceRowSeedData (S := S) fn f g) :
    RSeq.TendstoHalf
      (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_15_abs_error_tendsto_from_rowSeedData
    (S := S) fn f D.absErrorData


/-- Bishop--Cheng theorem 4.15 in the current final form when the general
measurable `I_B` layer is intentionally left external.

All non-`I_B` work is contained in `Lemma415AbsErrorNonIBData`; the only
remaining mathematical obligation is `Lemma415IBUniformFrontierData`, namely
the derivation of uniform `I_B` control from domination by `g`. -/
noncomputable def thm_4_15_dominated_convergence_except_generalIB
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (D : Lemma415AbsErrorNonIBData (S := S) fn f)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g D) :
    RSeq.TendstoHalf
      (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_15_abs_error_tendsto_from_nonIB_and_IBFrontier
    (S := S) fn f g D U


/-- Theorem 4.15, still leaving general `I_B` external, but deriving the
PFunR absolute-error convergence from source-level PFunR convergence
`pfn -> pf`. -/
noncomputable def thm_4_15_dominated_convergence_except_generalIB_from_pfunConverge
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (pfnsrc : Nat -> PFunR X R) (pf : PFunR X R)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hconv : Lemma415PFunConvergeData (S := S) pfnsrc pf)
    (hrep : forall n,
      Lemma414RepresentsPFunR (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_pfun_abs_error pfnsrc pf n))
    (U : Lemma415IBUniformFrontierData (S := S) fn f g
      (Lemma415AbsErrorNonIBData.of_pfunConverge
        (S := S) fn f pfnsrc pf hSeeds hconv hrep)) :
    RSeq.TendstoHalf
      (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_15_dominated_convergence_except_generalIB
    (S := S) fn f g
    (Lemma415AbsErrorNonIBData.of_pfunConverge
      (S := S) fn f pfnsrc pf hSeeds hconv hrep)
    U


/-- Theorem 4.15, still leaving general `I_B` external, with the non-`I_B`
PFunR convergence and representation bridges derived from source-level data. -/
noncomputable def
    thm_4_15_dominated_convergence_except_generalIB_from_pfunSourceData
    (fn : Nat -> IntegrableRep S) (f g : IntegrableRep S)
    (pfnsrc : Nat -> PFunR X R) (pf : PFunR X R)
    (hSeeds : forall n,
      Sec4Prop42RowSeedTools (S := S)
        (thm_4_15_abs_error (S := S) fn f n)
        (thm_4_15_abs_error_nonneg (S := S) fn f n))
    (hconv : Lemma415PFunConvergeData (S := S) pfnsrc pf)
    (hrep_fn : forall n,
      Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n))
    (hrep_f : Lemma414RepresentsPFunR (S := S) f pf)
    (U : Lemma415IBUniformFrontierData (S := S) fn f g
      (Lemma415AbsErrorNonIBData.of_pfunConvergeAndRepresentations
        (S := S) fn f pfnsrc pf hSeeds hconv hrep_fn hrep_f)) :
    RSeq.TendstoHalf
      (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_15_dominated_convergence_except_generalIB
    (S := S) fn f g
    (Lemma415AbsErrorNonIBData.of_pfunConvergeAndRepresentations
      (S := S) fn f pfnsrc pf hSeeds hconv hrep_fn hrep_f)
    U


end BishopC
