import Mathdemo.BishopSec3Presented

/-!
# Bishop and Cheng's Definition 1.1: a clause-by-clause encoded transcription

This file gives a clause-by-clause transcription of the four displayed clauses
of Definition 1.1 of E. Bishop and H. Cheng, *Constructive Measure Theory*
(Memoirs AMS 116, 1972), Section 1, relative to the development's encoding of
the ambient notions.  In particular, partial functions carry values only on
their domains, `I` carries values only on `L`, and the source's
apartness and strong-extensionality structures are not represented here.  The
file then derives, without additional hypotheses, all fourteen fields of the
working interface `BishopSec1P.IntSpaceC`.

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

open BishopCReal BishopSec1P BishopSec3P

universe u

/-! ## The source gauge `1/(n+1)`

Clause (4) of the source reads `limₙ I(min{|f|,n⁻¹}) = 0`.  The constant is the
source's own `n⁻¹`, built here as a presented real from a positivity witness;
no rational inverse is assumed.  The development's interface uses the dyadic
gauge `2⁻ⁿ`, and the passage from one to the other is the machine-checked
result `IntegrationSpaceDef11.cutSmall_tendsto_of_src` below. -/

/-- The source's gauge `1/(n+1)`, as a presented real with a positivity
witness. -/
def srcGauge (n : Nat) : CReal :=
  CReal.invPos (constSeq (Nat.cast (n + 1))) (natCast_succ_posDataC n)

/-- `1/(n+1)` is positive. -/
def srcGauge_posData (n : Nat) : PosEventuallyData (srcGauge n) :=
  CReal.invPos_posData _ (natCast_succ_posDataC n)

/-- The source's small cut `min{|f|, 1/(n+1)}` of clause (4). -/
def cutSmallSrc (n : Nat) (f : BFunC X) : BFunC X :=
  BFunC.minC (BFunC.absf f) (srcGauge n)

/-- `2^{-(n+1)} ≤ 1/(n+1)`: the dyadic gauge is dominated by the source gauge
at the same index.  The proof multiplies through by `n+1` and cancels, the
same algebra as the source's own remark `min{f,n} = n·min{n⁻¹f,1}`. -/
theorem halfPow_succ_le_srcGauge (n : Nat) :
    RegularSeqLe (halfPow (n + 1)) (srcGauge n) := by
  let denom : CReal := constSeq (Nat.cast (n + 1))
  let hpos : PosEventuallyData denom := natCast_succ_posDataC n
  let T : Nat := 2 ^ (n + 1)
  have hnat : n + 1 ≤ T := BishopC.lemma33H4_succ_le_two_pow_succ n
  have hcast : RegularSeqLe denom (constSeq (Nat.cast T)) :=
    natCast_leC (n + 1) T hnat
  have hhp_nn : RegularSeqNonneg (halfPow (n + 1)) :=
    regularSeqNonneg_of_zero_le
      (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_halfPow (n + 1)))
  have hsg_nn : RegularSeqNonneg (srcGauge n) :=
    regularSeqNonneg_of_zero_le
      (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_of_posData (srcGauge_posData n)))
  have hprod_nn : RegularSeqNonneg (CReal.mul (halfPow (n + 1)) (srcGauge n)) :=
    CReal.mul_nonneg_E hhp_nn hsg_nn
  have hmul : RegularSeqLe
      (CReal.mul denom (CReal.mul (halfPow (n + 1)) (srcGauge n)))
      (CReal.mul (constSeq (Nat.cast T)) (CReal.mul (halfPow (n + 1)) (srcGauge n))) :=
    regularSeqLe_mul_right_of_nonnegC hcast hprod_nn
  have hleft : CReal.mul denom (CReal.mul (halfPow (n + 1)) (srcGauge n))
      ≈ halfPow (n + 1) :=
    mul_invPos_scale_cancelC denom (halfPow (n + 1)) hpos
  have hscalar : (Nat.cast T : Scalar) * eps (n + 1) = 1 := by
    show (Nat.cast (2 ^ (n + 1)) : Scalar) * eps (n + 1) = 1
    rw [mul_comm]
    exact eps_mul_natCast_twoPow (n + 1)
  have hunit : CReal.mul (constSeq (Nat.cast T)) (halfPow (n + 1)) ≈ CReal.one := by
    calc CReal.mul (constSeq (Nat.cast T)) (halfPow (n + 1))
        = CReal.mul (constSeq (Nat.cast T)) (constSeq (eps (n + 1))) := rfl
      _ ≈ constSeq ((Nat.cast T : Scalar) * eps (n + 1)) :=
        constSeq_mulC (Nat.cast T) (eps (n + 1))
      _ = CReal.one := by rw [hscalar]; rfl
  have hright : CReal.mul (constSeq (Nat.cast T))
      (CReal.mul (halfPow (n + 1)) (srcGauge n)) ≈ srcGauge n := by
    calc CReal.mul (constSeq (Nat.cast T)) (CReal.mul (halfPow (n + 1)) (srcGauge n))
        ≈ CReal.mul (CReal.mul (constSeq (Nat.cast T)) (halfPow (n + 1))) (srcGauge n) :=
          Setoid.symm (CReal.mul_assoc _ _ _)
      _ ≈ CReal.mul CReal.one (srcGauge n) :=
          CReal.mul_respects_equiv _ CReal.one _ _ hunit (Setoid.refl _)
      _ ≈ srcGauge n := CReal.one_mul _
  exact regularSeqLe_of_left_eventual (Setoid.symm hleft)
    (regularSeqLe_of_right_eventual hright hmul)

/-- `1/(n+1) ≤ 2^{-k}` whenever `2^k ≤ n+1`: an eventual reverse comparison
from the source gauge to a prescribed dyadic gauge. -/
theorem srcGauge_le_halfPow {k n : Nat} (h : 2 ^ k ≤ n + 1) :
    RegularSeqLe (srcGauge n) (halfPow k) := by
  let denom : CReal := constSeq (Nat.cast (n + 1))
  let hpos : PosEventuallyData denom := natCast_succ_posDataC n
  have hcast : RegularSeqLe (constSeq (Nat.cast (2 ^ k))) denom :=
    natCast_leC (2 ^ k) (n + 1) h
  have hhp_nn : RegularSeqNonneg (halfPow k) :=
    regularSeqNonneg_of_zero_le
      (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_halfPow k))
  have hsg_nn : RegularSeqNonneg (srcGauge n) :=
    regularSeqNonneg_of_zero_le
      (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_of_posData (srcGauge_posData n)))
  have hprod_nn : RegularSeqNonneg (CReal.mul (halfPow k) (srcGauge n)) :=
    CReal.mul_nonneg_E hhp_nn hsg_nn
  have hmul : RegularSeqLe
      (CReal.mul (constSeq (Nat.cast (2 ^ k))) (CReal.mul (halfPow k) (srcGauge n)))
      (CReal.mul denom (CReal.mul (halfPow k) (srcGauge n))) :=
    regularSeqLe_mul_right_of_nonnegC hcast hprod_nn
  have hright : CReal.mul denom (CReal.mul (halfPow k) (srcGauge n)) ≈ halfPow k :=
    mul_invPos_scale_cancelC denom (halfPow k) hpos
  have hscalar : (Nat.cast (2 ^ k) : Scalar) * eps k = 1 := by
    rw [mul_comm]
    exact eps_mul_natCast_twoPow k
  have hunit : CReal.mul (constSeq (Nat.cast (2 ^ k))) (halfPow k) ≈ CReal.one := by
    calc CReal.mul (constSeq (Nat.cast (2 ^ k))) (halfPow k)
        = CReal.mul (constSeq (Nat.cast (2 ^ k))) (constSeq (eps k)) := rfl
      _ ≈ constSeq ((Nat.cast (2 ^ k) : Scalar) * eps k) :=
        constSeq_mulC (Nat.cast (2 ^ k)) (eps k)
      _ = CReal.one := by rw [hscalar]; rfl
  have hleft : CReal.mul (constSeq (Nat.cast (2 ^ k)))
      (CReal.mul (halfPow k) (srcGauge n)) ≈ srcGauge n := by
    calc CReal.mul (constSeq (Nat.cast (2 ^ k))) (CReal.mul (halfPow k) (srcGauge n))
        ≈ CReal.mul (CReal.mul (constSeq (Nat.cast (2 ^ k))) (halfPow k)) (srcGauge n) :=
          Setoid.symm (CReal.mul_assoc _ _ _)
      _ ≈ CReal.mul CReal.one (srcGauge n) :=
          CReal.mul_respects_equiv _ CReal.one _ _ hunit (Setoid.refl _)
      _ ≈ srcGauge n := CReal.one_mul _
  exact regularSeqLe_of_left_eventual (Setoid.symm hleft)
    (regularSeqLe_of_right_eventual hright hmul)

#print axioms BishopCheng.srcGauge_le_halfPow
#print axioms BishopCheng.srcGauge
#print axioms BishopCheng.cutSmallSrc
#print axioms BishopCheng.halfPow_succ_le_srcGauge

/-- **Bishop and Cheng, Definition 1.1**, transcribed clause by clause (ambient
notions in the development's encoding; see the file header). -/
structure IntegrationSpaceDef11 (X : Type u) where
  /-- `X` is nonempty.  (Source: "`X` is a nonempty set".) -/
  inhabited : X
  /-- `L` is a subset of `F(X)`, the partial functions on `X`. -/
  L : Set (BFunC X)
  /-- `I` is a function from `L` to `ℝ`. -/
  I : ∀ f : BFunC X, f ∈ L → CReal
  /-- `L` respects the equality of `F(X)`.  (Ambient convention, see header.) -/
  L_resp : ∀ {f g : BFunC X}, f ∈ L → BFunC.BEquiv f g → g ∈ L
  /-- `I` respects the equality of `F(X)`.  (Ambient convention, see header.) -/
  I_resp : ∀ {f g : BFunC X} (hf : f ∈ L) (hfg : BFunC.BEquiv f g),
    I f hf ≈ I g (L_resp hf hfg)
  /-- (1) `αf + βg ∈ L`. -/
  lin_mem : ∀ (α β : CReal) {f g : BFunC X}, f ∈ L → g ∈ L →
    BFunC.add (BFunC.smul α f) (BFunC.smul β g) ∈ L
  /-- (1) `|f| ∈ L`. -/
  abs_mem : ∀ {f : BFunC X}, f ∈ L → BFunC.absf f ∈ L
  /-- (1) `min{f,1} ∈ L`.  Note that the constant is `1`, and only `1`. -/
  cutOne_mem : ∀ {f : BFunC X}, f ∈ L → BFunC.minC f oneSeq ∈ L
  /-- (1) `I(αf + βg) = αI(f) + βI(g)`. -/
  I_lin : ∀ (α β : CReal) {f g : BFunC X} (hf : f ∈ L) (hg : g ∈ L),
    I (BFunC.add (BFunC.smul α f) (BFunC.smul β g))
        (lin_mem α β hf hg) ≈
      CReal.add (CReal.mul α (I f hf)) (CReal.mul β (I g hg))
  /-- (2) The constructive continuity property.  See the header on why the
  conclusion is data. -/
  continuity : ∀ {f : BFunC X} {fs : Nat → BFunC X}
    (hf : f ∈ L) (hfs : ∀ n, fs n ∈ L),
    (∀ n, BFunC.PointwiseNonneg (fs n)) →
    (hI : RepSeriesSum (fun n => I (fs n) (hfs n))) →
    CReal.ltE hI.sum (I f hf) →
    PointwiseSeriesBelowC fs f
  /-- (3) A distinguished function of `L`. -/
  p : BFunC X
  /-- (3) It belongs to `L`. -/
  p_mem : p ∈ L
  /-- (3) Its integral is `1`.  This is the normalization clause. -/
  I_p : I p p_mem ≈ oneSeq
  /-- (4) `limₙ I(min{f,n}) = I(f)`, with a modulus. -/
  cutNat_tendsto : ∀ {f : BFunC X} (hf : f ∈ L)
    (hcut : ∀ n, BFunC.cutNat n f ∈ L),
    RepSeriesTendsto (fun n => I (BFunC.cutNat n f) (hcut n)) (I f hf)
  /-- (4) `limₙ I(min{|f|,n⁻¹}) = 0`, with a modulus.  The cut is at the
  source's own gauge `1/(n+1)` (`cutSmallSrc`), not at the development's
  dyadic gauge; the two are related by the machine-checked theorem
  `cutSmall_tendsto_of_src`. -/
  cutSmallSrc_tendsto : ∀ {f : BFunC X} (hf : f ∈ L)
    (hcut : ∀ n, cutSmallSrc n f ∈ L),
    RepSeriesTendsto (fun n => I (cutSmallSrc n f) (hcut n)) CReal.zero

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
  intro x hx
  exact addSeq_respects_eventually _ _ _ _
    (one_mul_equivC (f.toFun x hx.1)) (one_mul_equivC (g.toFun x hx.2))

/-- Closure under scalar multiplication: clause (1) at `β = 0` and `g = f`. -/
theorem smul_mem (a : CReal) {f : BFunC X} (hf : f ∈ D.L) :
    BFunC.smul a f ∈ D.L := by
  refine D.L_resp (D.lin_mem a CReal.zero hf hf) ⟨Set.inter_self _, ?_⟩
  intro x hx
  calc CReal.add (CReal.mul a (f.toFun x hx.1))
        (CReal.mul CReal.zero (f.toFun x hx.2))
      ≈ CReal.add (CReal.mul a (f.toFun x hx.1)) CReal.zero :=
        addSeq_respects_eventually _ _ _ _
          (Setoid.refl (CReal.mul a (f.toFun x hx.1)))
          (zero_mul_equivC (f.toFun x hx.2))
    _ ≈ CReal.mul a (f.toFun x (by simpa using hx.1)) := CReal.add_zero _

/-- Additivity of the integral: clause (1) at `α = β = 1`. -/
theorem I_add {f g : BFunC X} (hf : f ∈ D.L) (hg : g ∈ D.L) :
    D.I (BFunC.add f g) (D.add_mem hf hg) ≈
      CReal.add (D.I f hf) (D.I g hg) := by
  have hEq : BFunC.BEquiv (BFunC.add f g)
      (BFunC.add (BFunC.smul CReal.one f) (BFunC.smul CReal.one g)) := by
    refine ⟨rfl, ?_⟩
    intro x hx
    exact addSeq_respects_eventually _ _ _ _
      (Setoid.symm (one_mul_equivC (f.toFun x hx.1)))
      (Setoid.symm (one_mul_equivC (g.toFun x hx.2)))
  calc D.I (BFunC.add f g) (D.add_mem hf hg)
      ≈ D.I (BFunC.add (BFunC.smul CReal.one f) (BFunC.smul CReal.one g))
          (D.lin_mem CReal.one CReal.one hf hg) :=
        D.I_resp (D.add_mem hf hg) hEq
    _ ≈ CReal.add (CReal.mul CReal.one (D.I f hf))
          (CReal.mul CReal.one (D.I g hg)) :=
        D.I_lin CReal.one CReal.one hf hg
    _ ≈ CReal.add (D.I f hf) (D.I g hg) :=
        addSeq_respects_eventually _ _ _ _
          (one_mul_equivC (D.I f hf)) (one_mul_equivC (D.I g hg))

/-- Homogeneity of the integral: clause (1) at `β = 0` and `g = f`. -/
theorem I_smul (a : CReal) {f : BFunC X} (hf : f ∈ D.L) :
    D.I (BFunC.smul a f) (D.smul_mem a hf) ≈ CReal.mul a (D.I f hf) := by
  have hEq : BFunC.BEquiv (BFunC.smul a f)
      (BFunC.add (BFunC.smul a f) (BFunC.smul CReal.zero f)) := by
    refine ⟨(Set.inter_self _).symm, ?_⟩
    intro x hx
    calc CReal.mul a (f.toFun x hx)
        ≈ CReal.add (CReal.mul a (f.toFun x hx)) CReal.zero :=
          Setoid.symm (CReal.add_zero _)
      _ ≈ CReal.add (CReal.mul a (f.toFun x hx))
            (CReal.mul CReal.zero (f.toFun x hx)) :=
          addSeq_respects_eventually _ _ _ _
            (Setoid.refl (CReal.mul a (f.toFun x hx)))
            (Setoid.symm (zero_mul_equivC (f.toFun x hx)))
  calc D.I (BFunC.smul a f) (D.smul_mem a hf)
      ≈ D.I (BFunC.add (BFunC.smul a f) (BFunC.smul CReal.zero f))
          (D.lin_mem a CReal.zero hf hf) :=
        D.I_resp (D.smul_mem a hf) hEq
    _ ≈ CReal.add (CReal.mul a (D.I f hf))
          (CReal.mul CReal.zero (D.I f hf)) :=
        D.I_lin a CReal.zero hf hf
    _ ≈ CReal.add (CReal.mul a (D.I f hf)) CReal.zero :=
        addSeq_respects_eventually _ _ _ _
          (Setoid.refl (CReal.mul a (D.I f hf))) (zero_mul_equivC (D.I f hf))
    _ ≈ CReal.mul a (D.I f hf) := CReal.add_zero _

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
    (hpos : CReal.ltE CReal.zero (D.I g hg)) :
    ∃ x : X, ∃ hx : x ∈ g.dom, CReal.ltE CReal.zero (g.toFun x hx) := by
  -- The zero function on the domain of `g`, obtained as `0 · g`.
  let z : BFunC X := ⟨g.dom, fun _ _ => CReal.zero⟩
  have hsmul : BFunC.smul CReal.zero g ∈ D.L := D.smul_mem CReal.zero hg
  have hzequiv : BFunC.BEquiv (BFunC.smul CReal.zero g) z :=
    ⟨rfl, fun x hx => zero_mul_equivC (g.toFun x hx)⟩
  have hzmem : z ∈ D.L := D.L_resp hsmul hzequiv
  have hznn : BFunC.PointwiseNonneg z := fun x _ => regularSeqLe_refl CReal.zero
  have hIz : D.I z hzmem ≈ CReal.zero := by
    calc D.I z hzmem ≈ CReal.mul CReal.zero (D.I g hg) :=
          Setoid.trans (Setoid.symm (D.I_resp hsmul hzequiv)) (D.I_smul CReal.zero hg)
      _ ≈ CReal.zero := zero_mul_equivC (D.I g hg)
  -- The series of integrals is the zero series, so it sums to zero.
  let hI : RepSeriesSum (fun _ : Nat => D.I z hzmem) :=
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
    (hnn : BFunC.PointwiseNonneg f) : RegularSeqLe zeroSeq (D.I f hf) := by
  intro hneg
  have hsymI : relEventually (D.I f hf) (subSeq (D.I f hf) zeroSeq) :=
    relEventually_symm _ _ (subSeq_zero_right_eventually (D.I f hf))
  have hIneg : regularSeqLtProp (D.I f hf) CReal.zero :=
    regularSeqLtProp_of_left_eventual hsymI hneg
  have hnfmem : BFunC.smul (CReal.neg CReal.one) f ∈ D.L :=
    D.smul_mem (CReal.neg CReal.one) hf
  have hInf : D.I (BFunC.smul (CReal.neg CReal.one) f) hnfmem ≈
      CReal.neg (D.I f hf) :=
    Setoid.trans (D.I_smul (CReal.neg CReal.one) hf)
      (neg_one_mul_equivC (D.I f hf))
  have hsymF : relEventually (CReal.neg (D.I f hf))
      (D.I (BFunC.smul (CReal.neg CReal.one) f) hnfmem) :=
    relEventually_symm _ _ hInf
  have hpos : CReal.ltE CReal.zero
      (D.I (BFunC.smul (CReal.neg CReal.one) f) hnfmem) :=
    regularSeqLtProp_of_right_eventual hsymF
      (BishopSec3P.regularSeqLtProp_zero_lt_negC hIneg)
  obtain ⟨x, hxdom, hxpos⟩ := D.pos_witness hnfmem hpos
  have hxneg : regularSeqLtProp CReal.zero (CReal.neg (f.toFun x hxdom)) :=
    regularSeqLtProp_of_right_eventual (neg_one_mul_equivC (f.toFun x hxdom)) hxpos
  have hsymN : relEventually (f.toFun x hxdom)
      (CReal.neg (CReal.neg (f.toFun x hxdom))) :=
    relEventually_symm _ _ (negSeq_negSeq_eventually (f.toFun x hxdom))
  have hfx : regularSeqLtProp (f.toFun x hxdom) CReal.zero :=
    regularSeqLtProp_of_left_eventual hsymN
      (BishopSec3P.regularSeqLtProp_neg_lt_zeroC hxneg)
  exact hnn x hxdom
    (regularSeqLtProp_of_left_eventual
      (subSeq_zero_right_eventually (f.toFun x hxdom)) hfx)

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

/-- **The same algebra as the source's positive-integer remark, generalized**:
truncation at a constant with a
positivity witness, from clause (1) alone, via `min{f,a} = a·min{a⁻¹f,1}`. -/
theorem cutPos_mem (a : CReal) (h : PosEventuallyData a) {f : BFunC X}
    (hf : f ∈ D.L) : BFunC.minC f a ∈ D.L := by
  have hnn : ¬ CReal.ltE a CReal.zero := (CutConstWitnessC.pos h).not_neg
  set inv := CReal.invPos a h with hinvdef
  have hres : BFunC.smul a (BFunC.minC (BFunC.smul inv f) CReal.one) ∈ D.L :=
    D.smul_mem a (D.cutOne_mem (D.smul_mem inv hf))
  refine D.L_resp hres ⟨rfl, ?_⟩
  intro x hx
  show CReal.mul a (CReal.min (CReal.mul inv (f.toFun x hx)) CReal.one) ≈
    CReal.min (f.toFun x hx) a
  calc
    CReal.mul a (CReal.min (CReal.mul inv (f.toFun x hx)) CReal.one)
        ≈ CReal.min (CReal.mul a (CReal.mul inv (f.toFun x hx)))
            (CReal.mul a CReal.one) :=
          mul_min_distribC a (CReal.mul inv (f.toFun x hx)) CReal.one hnn
    _ ≈ CReal.min (f.toFun x hx) a := by
          refine minSeqWith_respects_eventually cRatScalarMulArch _ _ _ _
            ?_ (CReal.mul_one a)
          calc
            CReal.mul a (CReal.mul inv (f.toFun x hx))
                ≈ CReal.mul (CReal.mul a inv) (f.toFun x hx) :=
                  Setoid.symm (CReal.mul_assoc a inv (f.toFun x hx))
            _ ≈ CReal.mul CReal.one (f.toFun x hx) :=
                  mulSeqConcrete_respects_eventually cRatScalarMulArch
                    (CReal.mul a inv) CReal.one (f.toFun x hx) (f.toFun x hx)
                    (CReal.mul_invPos_eventually_one a h)
                    (Setoid.refl (f.toFun x hx))
            _ ≈ f.toFun x hx := one_mul_equivC (f.toFun x hx)

/-! ## The gauge bridge

The interface field `IntSpaceC.cutSmall_tendsto` is stated at the dyadic gauge
`2⁻ⁿ`.  Clause (4) above is stated at the source's gauge `1/(n+1)`.  The
passage from the latter to the former is proved here, so that the adapter
below derives every field of the interface from Definition 1.1 itself. -/

/-- Reproduction of a one-line lemma that is `private` upstream. -/
theorem addC_congr {a a' b b' : CReal} (ha : a ≈ a') (hb : b ≈ b') :
    CReal.add a b ≈ CReal.add a' b' :=
  CReal.add_respects_equiv a a' b b' ha hb

/-- Reproduction of a one-line lemma that is `private` upstream. -/
theorem addC_negOne_mul_right_sub (a b : CReal) :
    CReal.add a (CReal.mul (CReal.neg CReal.one) b) ≈ CReal.sub a b := by
  change addSeq a (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq) b) ≈ subSeq a b
  exact addSeq_negOneMul_right_eventually_subSeq cRatScalarMulArch a b

/-- Reproduction of a lemma proved downstream of this module. -/
theorem ltProp_abs_sub_of_repClose_succ {x y : CReal} {K : Nat}
    (hclose : RepCloseAtGauge (K + 1) x y) :
    regularSeqLtProp (CReal.abs (CReal.sub x y)) (halfPow K) := by
  rcases hclose with ⟨N, hN⟩
  have hlt : regularSeqLtData (absSeq (subSeq x y)) (constSeq (eps K)) := by
    refine ⟨K + 2, N, ?_⟩
    intro n hn
    have hle_point : BishopCReal.Le
        (BishopC.COF_core.abs (x.val (n + 2) - y.val (n + 2))) (eps (K + 1)) :=
      hN (n + 2) (Nat.le_trans hn (Nat.le_add_right n 2))
    have hgap := scalar_eps_gap_of_le_succ
      (a := BishopC.COF_core.abs (x.val (n + 2) - y.val (n + 2))) K hle_point
    simpa [subSeq, subVal, constSeq, constVal, absSeq, absVal, addIndex]
      using hgap
  simpa [CReal.abs, CReal.sub, halfPow, CReal.epsSeq] using hlt.toProp

/-- `z ≤ |z - 0|`. -/
theorem le_abs_sub_zero (z : CReal) :
    RegularSeqLe z (CReal.abs (CReal.sub z CReal.zero)) := by
  have h1 : RegularSeqLe z (absSeq z) := base_le_abs_base_regularSeqLe z
  have h2 : relEventually (absSeq z) (absSeq (subSeq z zeroSeq)) :=
    relEventually_symm _ _ (absSeq_respects_eventually (subSeq z zeroSeq) z
      (subSeq_zero_right_eventually z))
  exact regularSeqLe_of_right_eventual h2 h1

/-- `I(f + (-1)·g) ≈ I f - I g`. -/
theorem I_sub {f g : BFunC X} (hf : f ∈ D.L) (hg : g ∈ D.L) :
    D.I (BFunC.add f (BFunC.smul (CReal.neg CReal.one) g))
        (D.add_mem hf (D.smul_mem (CReal.neg CReal.one) hg)) ≈
      CReal.sub (D.I f hf) (D.I g hg) := by
  have hsmul : D.I (BFunC.smul (CReal.neg CReal.one) g)
        (D.smul_mem (CReal.neg CReal.one) hg) ≈
      CReal.mul (CReal.neg CReal.one) (D.I g hg) :=
    D.I_smul (CReal.neg CReal.one) hg
  calc
    D.I (BFunC.add f (BFunC.smul (CReal.neg CReal.one) g))
        (D.add_mem hf (D.smul_mem (CReal.neg CReal.one) hg))
        ≈ CReal.add (D.I f hf)
            (D.I (BFunC.smul (CReal.neg CReal.one) g)
              (D.smul_mem (CReal.neg CReal.one) hg)) :=
          D.I_add hf (D.smul_mem (CReal.neg CReal.one) hg)
    _ ≈ CReal.add (D.I f hf) (CReal.mul (CReal.neg CReal.one) (D.I g hg)) :=
          addC_congr (Setoid.refl (D.I f hf)) hsmul
    _ ≈ CReal.sub (D.I f hf) (D.I g hg) :=
          addC_negOne_mul_right_sub (D.I f hf) (D.I g hg)

/-- Monotonicity of `I`, from clause (2) through `I_nonneg`. -/
theorem I_mono {f g : BFunC X}
    (hf : f ∈ D.L) (hg : g ∈ D.L) (hfg : BFunC.PointwiseLE f g) :
    RegularSeqLe (D.I f hf) (D.I g hg) := by
  let neg_f : BFunC X := BFunC.smul (CReal.neg CReal.one) f
  let diff : BFunC X := BFunC.add g neg_f
  have hneg_mem : neg_f ∈ D.L := by
    simpa [neg_f] using D.smul_mem (CReal.neg CReal.one) hf
  have hdiff_mem : diff ∈ D.L := by
    simpa [diff] using D.add_mem hg hneg_mem
  have hdiff_nn : BFunC.PointwiseNonneg diff := by
    intro x hx
    have hx' : x ∈ g.dom ∩ f.dom := by
      simpa [diff, neg_f, BFunC.add, BFunC.smul] using hx
    have hxg : x ∈ g.dom := hx'.1
    have hxf : x ∈ f.dom := hx'.2
    have hdiff_val :
        relEventually (diff.toFun x hx)
          (subSeq (g.toFun x hxg) (f.toFun x hxf)) := by
      change relEventually
        (addSeq (g.toFun x hxg)
          (mulSeqConcreteWith cRatScalarMulArch (negSeq oneSeq) (f.toFun x hxf)))
        (subSeq (g.toFun x hxg) (f.toFun x hxf))
      exact addSeq_negOneMul_right_eventually_subSeq
        cRatScalarMulArch (g.toFun x hxg) (f.toFun x hxf)
    have hdiff_zero_to_sub :
        relEventually (subSeq (diff.toFun x hx) zeroSeq)
          (subSeq (g.toFun x hxg) (f.toFun x hxf)) :=
      relEventually_trans
        (subSeq (diff.toFun x hx) zeroSeq) (diff.toFun x hx)
        (subSeq (g.toFun x hxg) (f.toFun x hxf))
        (subSeq_zero_right_eventually (diff.toFun x hx)) hdiff_val
    change RegularSeqNonneg (subSeq (diff.toFun x hx) zeroSeq)
    exact regularSeqNonneg_of_eventual hdiff_zero_to_sub (hfg.le_val x hxf)
  have hI_diff_nonneg : RegularSeqLe zeroSeq (D.I diff hdiff_mem) :=
    D.I_nonneg hdiff_mem hdiff_nn
  have hI_to_sub : relEventually (D.I diff hdiff_mem)
      (subSeq (D.I g hg) (D.I f hf)) := by
    simpa [diff, neg_f] using D.I_sub hg hf
  have hzero_sub : RegularSeqLe zeroSeq (subSeq (D.I g hg) (D.I f hf)) :=
    regularSeqLe_of_right_eventual hI_to_sub hI_diff_nonneg
  change RegularSeqNonneg (subSeq (D.I g hg) (D.I f hf))
  exact regularSeqNonneg_of_zero_le hzero_sub

/-- `min{|f|, 1/(n+1)} ∈ L`, by clause (1) through `cutPos_mem`. -/
theorem cutSmallSrc_mem {f : BFunC X} (hf : f ∈ D.L) (n : Nat) :
    cutSmallSrc n f ∈ D.L :=
  D.cutPos_mem (srcGauge n) (srcGauge_posData n) (D.abs_mem hf)

/-- `min{|f|, 2⁻ⁿ} ∈ L`, by clause (1) through `cutPos_mem`. -/
theorem cutSmall_mem {f : BFunC X} (hf : f ∈ D.L) (n : Nat) :
    BFunC.cutSmall n f ∈ D.L :=
  D.cutPos_mem (halfPow n) (epsConst_posDataC n) (D.abs_mem hf)

/-- Pointwise `min{|f|, 2^{-(n+1)}} ≤ min{|f|, 1/(n+1)}`. -/
theorem cutSmall_succ_le_cutSmallSrc (f : BFunC X) (n : Nat) :
    BFunC.PointwiseLE (BFunC.cutSmall (n + 1) f) (cutSmallSrc n f) where
  dom_eq := rfl
  le_val := fun _x _hx => CReal.min_right_monoC (halfPow_succ_le_srcGauge n)

/-- **The gauge bridge.**  Clause (4) at the source's gauge `1/(n+1)` yields
the interface's clause at the dyadic gauge `2⁻ⁿ`, with the modulus
reindexed. -/
def cutSmall_tendsto_of_src {f : BFunC X} (hf : f ∈ D.L)
    (h : RepSeriesTendsto
      (fun n => D.I (cutSmallSrc n f) (D.cutSmallSrc_mem hf n)) CReal.zero) :
    RepSeriesTendsto
      (fun n => D.I (BFunC.cutSmall n f) (D.cutSmall_mem hf n)) CReal.zero where
  mod := fun k => h.mod (k + 1) + 1
  close := by
    intro k n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : h.mod (k + 1) ≤ m := by omega
    have hclose : RepCloseAtGauge (k + 1 + 1)
        (D.I (cutSmallSrc m f) (D.cutSmallSrc_mem hf m)) CReal.zero :=
      h.close (k + 1) m hm
    have hy : regularSeqLtProp
        (CReal.abs (CReal.sub
          (D.I (cutSmallSrc m f) (D.cutSmallSrc_mem hf m)) CReal.zero))
        (halfPow (k + 1)) :=
      ltProp_abs_sub_of_repClose_succ hclose
    have hnn : BFunC.PointwiseNonneg (BFunC.cutSmall (m + 1) f) := by
      intro x hx
      exact regularSeqLe_zero_of_nonneg
        (lemma43Min_nonnegC (absSeq_regularSeqNonneg (f.toFun x hx))
          (regularSeqNonneg_of_zero_le
            (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_halfPow (m + 1)))))
    have hx : RegularSeqNonneg
        (D.I (BFunC.cutSmall (m + 1) f) (D.cutSmall_mem hf (m + 1))) :=
      regularSeqNonneg_of_zero_le (D.I_nonneg (D.cutSmall_mem hf (m + 1)) hnn)
    have hcmp : RegularSeqLe
        (D.I (BFunC.cutSmall (m + 1) f) (D.cutSmall_mem hf (m + 1)))
        (D.I (cutSmallSrc m f) (D.cutSmallSrc_mem hf m)) :=
      D.I_mono (D.cutSmall_mem hf (m + 1)) (D.cutSmallSrc_mem hf m)
        (cutSmall_succ_le_cutSmallSrc f m)
    exact repCloseAtGauge_zero_of_nonneg_le_ltC hx
      (regularSeqLe_trans hcmp (le_abs_sub_zero _)) hy

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
  cutNat_tendsto_raw := fun {_f} hf hcut => D.cutNat_tendsto hf hcut
  cutSmall_tendsto_raw := fun {_f} hf _hcut =>
    D.cutSmall_tendsto_of_src hf
      (D.cutSmallSrc_tendsto hf (D.cutSmallSrc_mem hf))
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
#print axioms BishopCheng.IntegrationSpaceDef11.I_sub
#print axioms BishopCheng.IntegrationSpaceDef11.I_mono
#print axioms BishopCheng.IntegrationSpaceDef11.cutSmallSrc_mem
#print axioms BishopCheng.IntegrationSpaceDef11.cutSmall_mem
#print axioms BishopCheng.IntegrationSpaceDef11.cutSmall_succ_le_cutSmallSrc
#print axioms BishopCheng.IntegrationSpaceDef11.cutSmall_tendsto_of_src
#print axioms BishopCheng.IntegrationSpaceDef11.toIntSpaceC

end BishopCheng
