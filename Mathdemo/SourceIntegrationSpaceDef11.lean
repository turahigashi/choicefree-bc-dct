import Mathdemo.BishopSec3Presented

/-!
# Bishop and Cheng's Definition 1.1, verbatim

This file transcribes Definition 1.1 of the source — E. Bishop and H. Cheng,
*Constructive Measure Theory* (Memoirs AMS 116, 1972), Section 1 — as a Lean
structure, clause by clause --- with the ambient notions (partial functions,
the ambient-total encoding of `I`, the dyadic gauge) in the development's
encoding --- and relates it to the interface
`BishopSec1P.IntSpaceC` that the development actually uses.

The source reads:

> A triple `(X, L, I)` is an *integration space* if `X` is a nonempty set with an
> equality and an inequality relation, `L` is a subset of `F(X)`, and `I` is a
> function from `L` to `ℝ`, such that the following four properties hold.
>
> (1) If `f, g ∈ L` and `α, β ∈ ℝ`, then `αf + βg`, `|f|`, `min{f,1}` belong to
>     `L`, and `I(αf + βg) = αI(f) + βI(g)`.
> (2) If `f ∈ L` and `{fₙ}` is a sequence of nonnegative functions of `L` such
>     that `Σₙ I(fₙ)` converges and `Σₙ I(fₙ) < I(f)`, then there is a point
>     `x ∈ X` such that `Σₙ fₙ(x)` converges and `Σₙ fₙ(x) < f(x)`.
> (3) There is a function `p` in `L` with `I(p) = 1`.
> (4) For every `f ∈ L`, `limₙ I(min{f,n}) = I(f)` and `limₙ I(min{|f|,n⁻¹}) = 0`.

Two remarks on the transcription.

*Existence and limits are data.*  In Bishop's constructive mathematics the
existential statement of (2) asserts that the point can be produced, and a limit
always comes with a modulus.  The Lean rendering therefore returns
`PointwiseSeriesBelowC` in (2) and `RepSeriesTendsto` in (4) rather than a
`Prop`-valued `∃` and an epsilon-delta limit.  This is faithfulness, not
strengthening: `Prop`-valued `∃` would be the weaker reading.

*Respect for equality is explicit.*  The source works with sets in Bishop's
sense, so membership in `L` and the value of `I` respect the equality of `F(X)`
by construction.  Lean's `Set (BFunC X)` does not, so the two clauses `L_resp`
and `I_resp` state it.  They add no mathematical content to the source; they
make its ambient convention explicit.
-/

namespace BishopCheng

open BishopCReal BishopSec1P

universe u

/-- **Bishop and Cheng, Definition 1.1**, transcribed clause by clause (ambient
notions in the development's encoding; see the file header). -/
structure IntegrationSpaceDef11 (X : Type u) where
  /-- `X` is nonempty.  (Source: "`X` is a nonempty set".) -/
  inhabited : X
  /-- `L` is a subset of `F(X)`, the partial functions on `X`. -/
  L : Set (BFunC X)
  /-- `I` is a function from `L` to `ℝ`. -/
  I : BFunC X → CReal
  /-- `L` respects the equality of `F(X)`.  (Ambient convention, see header.) -/
  L_resp : ∀ {f g : BFunC X}, f ∈ L → BFunC.BEquiv f g → g ∈ L
  /-- `I` respects the equality of `F(X)`.  (Ambient convention, see header.) -/
  I_resp : ∀ {f g : BFunC X}, f ∈ L → BFunC.BEquiv f g → I f ≈ I g
  /-- (1) `αf + βg ∈ L`. -/
  lin_mem : ∀ (α β : CReal) {f g : BFunC X}, f ∈ L → g ∈ L →
    BFunC.add (BFunC.smul α f) (BFunC.smul β g) ∈ L
  /-- (1) `|f| ∈ L`. -/
  abs_mem : ∀ {f : BFunC X}, f ∈ L → BFunC.absf f ∈ L
  /-- (1) `min{f,1} ∈ L`.  Note that the constant is `1`, and only `1`. -/
  cutOne_mem : ∀ {f : BFunC X}, f ∈ L → BFunC.minC f oneSeq ∈ L
  /-- (1) `I(αf + βg) = αI(f) + βI(g)`. -/
  I_lin : ∀ (α β : CReal) {f g : BFunC X}, f ∈ L → g ∈ L →
    I (BFunC.add (BFunC.smul α f) (BFunC.smul β g)) ≈
      CReal.add (CReal.mul α (I f)) (CReal.mul β (I g))
  /-- (2) The constructive continuity property.  See the header on why the
  conclusion is data. -/
  continuity : ∀ {f : BFunC X} {fs : Nat → BFunC X},
    f ∈ L → (∀ n, fs n ∈ L) → (∀ n, BFunC.PointwiseNonneg (fs n)) →
    (hI : RepSeriesSum (fun n => I (fs n))) → CReal.ltE hI.sum (I f) →
    PointwiseSeriesBelowC fs f
  /-- (3) A distinguished function of `L`. -/
  p : BFunC X
  /-- (3) It belongs to `L`. -/
  p_mem : p ∈ L
  /-- (3) Its integral is `1`.  This is the normalization clause. -/
  I_p : I p ≈ oneSeq
  /-- (4) `limₙ I(min{f,n}) = I(f)`, with a modulus. -/
  cutNat_tendsto : ∀ {f : BFunC X}, f ∈ L →
    RepSeriesTendsto (fun n => I (BFunC.cutNat n f)) (I f)
  /-- (4) `limₙ I(min{|f|,n⁻¹}) = 0`, with a modulus. -/
  cutSmall_tendsto : ∀ {f : BFunC X}, f ∈ L →
    RepSeriesTendsto (fun n => I (BFunC.cutSmall n f)) CReal.zero

/-! ## Consequences of clause (1)

The source states clause (1) as the single assertion that `αf + βg ∈ L`.  The
interface used by the development instead lists closure under addition and under
scalar multiplication separately.  The two are interderivable, but the passage
from the source form to the split form goes through the equality of `F(X)`, so it
is a proof and not a definitional unfolding.  These are those proofs. -/

/-- `1 · a = a` in the presented reals. -/
theorem one_mul_equivC (a : CReal) : CReal.mul CReal.one a ≈ a := by
  change relEventually (mulSeqConcreteWith cRatScalarMulArch oneSeq a) a
  exact mulSeqConcrete_one_left_eventually cRatScalarMulArch a

/-- `(-1) · a = -a` in the presented reals. -/
theorem neg_one_mul_equivC (a : CReal) :
    CReal.mul (CReal.neg CReal.one) a ≈ CReal.neg a := by
  change relEventually (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq) a)
    (negSeq a)
  exact mulSeq_neg_one_left_eventually_neg cRatScalarMulArch a

/-- `c·min{u,v} ≈ min{c·u, c·v}` for a nonnegative multiplier `c`.  The `min`
mirror of `BishopSec3P.thm36A1_mul_max_zeroC`, through the halfsum identity
`min{u,v} = ((u+v) - |u-v|)/2`. -/
theorem mul_min_distribC (c u v : CReal) (hc : ¬ CReal.ltE c CReal.zero) :
    CReal.mul c (CReal.min u v) ≈ CReal.min (CReal.mul c u) (CReal.mul c v) := by
  -- The absolute-value atom of the halfsum identity.
  set T := CReal.abs (CReal.add u (CReal.neg v)) with hT
  -- `|c·(u-v)| ≈ c·|u-v|` for nonnegative `c`.
  have habs_c : CReal.abs (CReal.mul c (CReal.add u (CReal.neg v))) ≈
      CReal.mul c T :=
    Setoid.trans (CReal.abs_mul c (CReal.add u (CReal.neg v)))
      (mulSeqConcrete_respects_eventually cRatScalarMulArch
        (CReal.abs c) c T T (CReal.abs_of_nonneg_E hc) (Setoid.refl T))
  -- `c·u - c·v ≈ c·(u - v)` by ring.
  have hprod : CReal.add (CReal.mul c u) (CReal.neg (CReal.mul c v)) ≈
      CReal.mul c (CReal.add u (CReal.neg v)) := by
    refine Quotient.exact ?_
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change ((mkQuot c) * (mkQuot u)) + (-((mkQuot c) * (mkQuot v)))
      = (mkQuot c) * ((mkQuot u) + (-(mkQuot v)))
    ring
  -- `|c·u - c·v| ≈ c·T`.
  have habs2 : CReal.abs (CReal.add (CReal.mul c u) (CReal.neg (CReal.mul c v))) ≈
      CReal.mul c T :=
    Setoid.trans (absSeq_respects_eventually _ _ hprod) habs_c
  -- Assemble through the two halfsum identities.
  refine Setoid.trans
    (mulSeqConcrete_respects_eventually cRatScalarMulArch c c
      (CReal.min u v)
      (CReal.mul CReal.half
        (CReal.add (CReal.add u v) (CReal.neg T)))
      (Setoid.refl c) (CReal.min_halfsum u v))
    (Setoid.trans ?_ (Setoid.symm (CReal.min_halfsum (CReal.mul c u) (CReal.mul c v))))
  -- goal: c·(½·((u+v)+(−T))) ≈ ½·((c·u+c·v)+(−|c·u+(−(c·v))|))
  have hring :
      CReal.mul c (CReal.mul CReal.half
        (CReal.add (CReal.add u v) (CReal.neg T)))
      ≈ CReal.mul CReal.half
        (CReal.add (CReal.add (CReal.mul c u) (CReal.mul c v))
          (CReal.neg (CReal.mul c T))) := by
    refine Quotient.exact ?_
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (mkQuot c) * ((mkQuot CReal.half)
        * (((mkQuot u) + (mkQuot v)) + (-(mkQuot T))))
      = (mkQuot CReal.half)
        * ((((mkQuot c) * (mkQuot u)) + ((mkQuot c) * (mkQuot v)))
            + (-((mkQuot c) * (mkQuot T))))
    ring
  have hmid :
      CReal.mul CReal.half
        (CReal.add (CReal.add (CReal.mul c u) (CReal.mul c v))
          (CReal.neg (CReal.mul c T)))
      ≈ CReal.mul CReal.half
        (CReal.add (CReal.add (CReal.mul c u) (CReal.mul c v))
          (CReal.neg (CReal.abs
            (CReal.add (CReal.mul c u) (CReal.neg (CReal.mul c v)))))) :=
    mulSeqConcrete_respects_eventually cRatScalarMulArch
      CReal.half CReal.half _ _ (Setoid.refl CReal.half)
      (addSeq_respects_eventually _ _ _ _
        (Setoid.refl (CReal.add (CReal.mul c u) (CReal.mul c v)))
        (negSeq_respects_eventually _ _ (Setoid.symm habs2)))
  exact Setoid.trans hring hmid

#print axioms BishopCheng.mul_min_distribC

namespace IntegrationSpaceDef11

variable {X : Type u} (D : IntegrationSpaceDef11 X)

/-- Closure under addition: clause (1) at `α = β = 1`. -/
theorem add_mem {f g : BFunC X} (hf : f ∈ D.L) (hg : g ∈ D.L) :
    BFunC.add f g ∈ D.L := by
  refine D.L_resp (D.lin_mem CReal.one CReal.one hf hg) ⟨rfl, ?_⟩
  intro x _
  exact addSeq_respects_eventually _ _ _ _
    (one_mul_equivC (f.toFun x)) (one_mul_equivC (g.toFun x))

/-- Closure under scalar multiplication: clause (1) at `β = 0` and `g = f`. -/
theorem smul_mem (a : CReal) {f : BFunC X} (hf : f ∈ D.L) :
    BFunC.smul a f ∈ D.L := by
  refine D.L_resp (D.lin_mem a CReal.zero hf hf) ⟨Set.inter_self _, ?_⟩
  intro x _
  calc CReal.add (CReal.mul a (f.toFun x)) (CReal.mul CReal.zero (f.toFun x))
      ≈ CReal.add (CReal.mul a (f.toFun x)) CReal.zero :=
        addSeq_respects_eventually _ _ _ _
          (Setoid.refl (CReal.mul a (f.toFun x))) (zero_mul_equivC (f.toFun x))
    _ ≈ CReal.mul a (f.toFun x) := CReal.add_zero _

/-- Additivity of the integral: clause (1) at `α = β = 1`. -/
theorem I_add {f g : BFunC X} (hf : f ∈ D.L) (hg : g ∈ D.L) :
    D.I (BFunC.add f g) ≈ CReal.add (D.I f) (D.I g) := by
  have hEq : BFunC.BEquiv (BFunC.add f g)
      (BFunC.add (BFunC.smul CReal.one f) (BFunC.smul CReal.one g)) := by
    refine ⟨rfl, ?_⟩
    intro x _
    exact addSeq_respects_eventually _ _ _ _
      (Setoid.symm (one_mul_equivC (f.toFun x)))
      (Setoid.symm (one_mul_equivC (g.toFun x)))
  calc D.I (BFunC.add f g)
      ≈ D.I (BFunC.add (BFunC.smul CReal.one f) (BFunC.smul CReal.one g)) :=
        D.I_resp (D.add_mem hf hg) hEq
    _ ≈ CReal.add (CReal.mul CReal.one (D.I f)) (CReal.mul CReal.one (D.I g)) :=
        D.I_lin CReal.one CReal.one hf hg
    _ ≈ CReal.add (D.I f) (D.I g) :=
        addSeq_respects_eventually _ _ _ _
          (one_mul_equivC (D.I f)) (one_mul_equivC (D.I g))

/-- Homogeneity of the integral: clause (1) at `β = 0` and `g = f`. -/
theorem I_smul (a : CReal) {f : BFunC X} (hf : f ∈ D.L) :
    D.I (BFunC.smul a f) ≈ CReal.mul a (D.I f) := by
  have hEq : BFunC.BEquiv (BFunC.smul a f)
      (BFunC.add (BFunC.smul a f) (BFunC.smul CReal.zero f)) := by
    refine ⟨(Set.inter_self _).symm, ?_⟩
    intro x _
    calc CReal.mul a (f.toFun x)
        ≈ CReal.add (CReal.mul a (f.toFun x)) CReal.zero :=
          Setoid.symm (CReal.add_zero _)
      _ ≈ CReal.add (CReal.mul a (f.toFun x)) (CReal.mul CReal.zero (f.toFun x)) :=
          addSeq_respects_eventually _ _ _ _
            (Setoid.refl (CReal.mul a (f.toFun x)))
            (Setoid.symm (zero_mul_equivC (f.toFun x)))
  calc D.I (BFunC.smul a f)
      ≈ D.I (BFunC.add (BFunC.smul a f) (BFunC.smul CReal.zero f)) :=
        D.I_resp (D.smul_mem a hf) hEq
    _ ≈ CReal.add (CReal.mul a (D.I f)) (CReal.mul CReal.zero (D.I f)) :=
        D.I_lin a CReal.zero hf hf
    _ ≈ CReal.add (CReal.mul a (D.I f)) CReal.zero :=
        addSeq_respects_eventually _ _ _ _
          (Setoid.refl (CReal.mul a (D.I f))) (zero_mul_equivC (D.I f))
    _ ≈ CReal.mul a (D.I f) := CReal.add_zero _

/-! ## Corollary 1.3 of the source

The source draws from clause (2) first Lemma 1.2 and then Corollary 1.3: if
`Σᵢ I(gᵢ) > 0` then `Σᵢ gᵢ(x) > 0` at some point of the common domain.  The
sentence following Corollary 1.3 records the weaker form that is actually used:
if `Σᵢ gᵢ(x) ≥ 0` at every point of the common domain then `Σᵢ I(gᵢ) ≥ 0`.

`pos_witness` below is Corollary 1.3 at `k = 1`, and `I_nonneg` is that weaker
form at `k = 1`.  Both are obtained from clause (2) exactly as the source obtains
them: apply (2) with the zero function as the sequence. -/

/-- **Corollary 1.3 at `k = 1`.**  If the integral of `g` is positive then `g` is
positive at some point of its domain.  Proved from clause (2) with the constant
zero function in the role of the sequence, as in the source. -/
theorem pos_witness {g : BFunC X} (hg : g ∈ D.L)
    (hpos : CReal.ltE CReal.zero (D.I g)) :
    ∃ x : X, x ∈ g.dom ∧ CReal.ltE CReal.zero (g.toFun x) := by
  -- The zero function on the domain of `g`, obtained as `0 · g`.
  let z : BFunC X := ⟨fun _ => CReal.zero, g.dom⟩
  have hsmul : BFunC.smul CReal.zero g ∈ D.L := D.smul_mem CReal.zero hg
  have hzequiv : BFunC.BEquiv (BFunC.smul CReal.zero g) z :=
    ⟨rfl, fun x _ => zero_mul_equivC (g.toFun x)⟩
  have hzmem : z ∈ D.L := D.L_resp hsmul hzequiv
  have hznn : BFunC.PointwiseNonneg z := fun x _ => regularSeqLe_refl CReal.zero
  have hIz : D.I z ≈ CReal.zero := by
    calc D.I z ≈ CReal.mul CReal.zero (D.I g) :=
          Setoid.trans (Setoid.symm (D.I_resp hsmul hzequiv)) (D.I_smul CReal.zero hg)
      _ ≈ CReal.zero := zero_mul_equivC (D.I g)
  -- The series of integrals is the zero series, so it sums to zero.
  let hI : RepSeriesSum (fun _ : Nat => D.I z) :=
    repSeriesSum_congr (repSeriesSum_single CReal.zero) (fun n => by
      by_cases hn : n = 0
      · rw [if_pos hn]; exact hIz
      · rw [if_neg hn]; exact hIz)
  have hpsb := D.continuity hg (fun _ => hzmem) (fun _ => hznn) hI hpos
  refine ⟨hpsb.x, hpsb.hx_f, ?_⟩
  -- The pointwise series is again the zero series.
  let hzero : RepSeriesSum (fun _ : Nat => CReal.zero) :=
    repSeriesSum_congr (repSeriesSum_single CReal.zero) (fun n => by
      by_cases hn : n = 0
      · rw [if_pos hn]; exact relEventually_refl CReal.zero
      · rw [if_neg hn]; exact relEventually_refl CReal.zero)
  have hsum : hpsb.point_sum.sum ≈ CReal.zero :=
    repSeriesSum_unique hpsb.point_sum hzero
  exact regularSeqLtProp_of_left_eventual (Setoid.symm hsum) hpsb.below

/-- **The weak form of Corollary 1.3 at `k = 1`.**  A nonnegative function of `L`
has nonnegative integral.  This is the statement the source records immediately
after Corollary 1.3, and it is what `IntSpaceC` carries as the field
`I_nonneg`; the present proof shows that carrying it is not necessary. -/
theorem I_nonneg {f : BFunC X} (hf : f ∈ D.L)
    (hnn : BFunC.PointwiseNonneg f) : RegularSeqLe zeroSeq (D.I f) := by
  intro hneg
  have hsymI : relEventually (D.I f) (subSeq (D.I f) zeroSeq) :=
    relEventually_symm _ _ (subSeq_zero_right_eventually (D.I f))
  have hIneg : regularSeqLtProp (D.I f) CReal.zero :=
    regularSeqLtProp_of_left_eventual hsymI hneg
  have hnfmem : BFunC.smul (CReal.neg CReal.one) f ∈ D.L :=
    D.smul_mem (CReal.neg CReal.one) hf
  have hInf : D.I (BFunC.smul (CReal.neg CReal.one) f) ≈ CReal.neg (D.I f) :=
    Setoid.trans (D.I_smul (CReal.neg CReal.one) hf) (neg_one_mul_equivC (D.I f))
  have hsymF : relEventually (CReal.neg (D.I f))
      (D.I (BFunC.smul (CReal.neg CReal.one) f)) := relEventually_symm _ _ hInf
  have hpos : CReal.ltE CReal.zero (D.I (BFunC.smul (CReal.neg CReal.one) f)) :=
    regularSeqLtProp_of_right_eventual hsymF
      (BishopSec3P.regularSeqLtProp_zero_lt_negC hIneg)
  obtain ⟨x, hxdom, hxpos⟩ := D.pos_witness hnfmem hpos
  have hxneg : regularSeqLtProp CReal.zero (CReal.neg (f.toFun x)) :=
    regularSeqLtProp_of_right_eventual (neg_one_mul_equivC (f.toFun x)) hxpos
  have hsymN : relEventually (f.toFun x) (CReal.neg (CReal.neg (f.toFun x))) :=
    relEventually_symm _ _ (negSeq_negSeq_eventually (f.toFun x))
  have hfx : regularSeqLtProp (f.toFun x) CReal.zero :=
    regularSeqLtProp_of_left_eventual hsymN
      (BishopSec3P.regularSeqLtProp_neg_lt_zeroC hxneg)
  exact hnn x hxdom
    (regularSeqLtProp_of_left_eventual
      (subSeq_zero_right_eventually (f.toFun x)) hfx)

/-! ## The source's own truncation remark

Clause (1) provides truncation at the constant `1` only.  The source's remark
recovers `min{f,a}` for a constant `a` carrying a positivity witness by
`min{f,a} = a·min{a⁻¹f,1}`: the witness is exactly what `a⁻¹` requires, since
inversion of a presented real is partial and takes `PosEventuallyData` as its
domain condition.  This is `cutPos_mem` below, and it is precisely the field
`IntSpaceC.cutPos_mem` of the interface — so the adapter that follows needs no
hypotheses at all.  (Truncation at exactly `0`, `min{f,0} = (f - |f|)/2`, also
follows from clause (1); the interface derives it from its other fields as
`IntSpaceC.cutZero_mem`, so it is not a field and the adapter owes nothing for
it.  Truncation at an *arbitrary* constant would be strictly stronger than the
source and fails for a negative constant in the standard models: for
`L = L¹(ℝ)` and `a < 0`, `min(f,a) ≤ a < 0` everywhere, so `min(f,a) ∉ L`.) -/

/-- **The source's remark, formalized**: truncation at a constant with a
positivity witness, from clause (1) alone, via `min{f,a} = a·min{a⁻¹f,1}`. -/
theorem cutPos_mem (a : CReal) (h : PosEventuallyData a) {f : BFunC X}
    (hf : f ∈ D.L) : BFunC.minC f a ∈ D.L := by
  have hnn : ¬ CReal.ltE a CReal.zero := (CutConstWitnessC.pos h).not_neg
  set inv := CReal.invPos a h with hinvdef
  have hres : BFunC.smul a (BFunC.minC (BFunC.smul inv f) CReal.one) ∈ D.L :=
    D.smul_mem a (D.cutOne_mem (D.smul_mem inv hf))
  refine D.L_resp hres ⟨rfl, ?_⟩
  intro x _
  show CReal.mul a (CReal.min (CReal.mul inv (f.toFun x)) CReal.one) ≈
    CReal.min (f.toFun x) a
  calc
    CReal.mul a (CReal.min (CReal.mul inv (f.toFun x)) CReal.one)
        ≈ CReal.min (CReal.mul a (CReal.mul inv (f.toFun x)))
            (CReal.mul a CReal.one) :=
          mul_min_distribC a (CReal.mul inv (f.toFun x)) CReal.one hnn
    _ ≈ CReal.min (f.toFun x) a := by
          refine minSeqWith_respects_eventually cRatScalarMulArch _ _ _ _
            ?_ (CReal.mul_one a)
          calc
            CReal.mul a (CReal.mul inv (f.toFun x))
                ≈ CReal.mul (CReal.mul a inv) (f.toFun x) :=
                  Setoid.symm (CReal.mul_assoc a inv (f.toFun x))
            _ ≈ CReal.mul CReal.one (f.toFun x) :=
                  mulSeqConcrete_respects_eventually cRatScalarMulArch
                    (CReal.mul a inv) CReal.one (f.toFun x) (f.toFun x)
                    (CReal.mul_invPos_eventually_one a h)
                    (Setoid.refl (f.toFun x))
            _ ≈ f.toFun x := one_mul_equivC (f.toFun x)

/-! ## The adapter

Every field of `IntSpaceC` is available from Definition 1.1, **with no
hypotheses**: fourteen fields out of fourteen.

Note in particular that `IntSpaceC.I_nonneg` is *not* carried as an
assumption.  It is `I_nonneg` above, derived from clause (2); the interface
carries it as a field but does not need to.  Likewise `IntSpaceC.cutPos_mem`
is `cutPos_mem` above, the source's own remark on truncation at a witnessed
positive constant. -/

/-- **Adapter**: an integration space in the sense of Bishop and Cheng's
Definition 1.1 yields the interface used by the development, unconditionally. -/
def toIntSpaceC : IntSpaceC X where
  L := D.L
  I := D.I
  L_resp := D.L_resp
  I_resp := D.I_resp
  add_mem := D.add_mem
  smul_mem := D.smul_mem
  abs_mem := D.abs_mem
  cutPos_mem := fun a h {_f} hf => D.cutPos_mem a h hf
  I_add := D.I_add
  I_smul := D.I_smul
  cutNat_tendsto := D.cutNat_tendsto
  cutSmall_tendsto := D.cutSmall_tendsto
  I_nonneg := D.I_nonneg
  continuity := D.continuity

end IntegrationSpaceDef11

#print axioms BishopCheng.IntegrationSpaceDef11.pos_witness
#print axioms BishopCheng.IntegrationSpaceDef11.I_nonneg
#print axioms BishopCheng.IntegrationSpaceDef11.add_mem
#print axioms BishopCheng.IntegrationSpaceDef11.smul_mem
#print axioms BishopCheng.IntegrationSpaceDef11.I_add
#print axioms BishopCheng.IntegrationSpaceDef11.I_smul
#print axioms BishopCheng.IntegrationSpaceDef11.cutPos_mem
#print axioms BishopCheng.IntegrationSpaceDef11.toIntSpaceC

end BishopCheng
