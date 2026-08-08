import Mathdemo.BishopSec3Presented

/-!
# Bishop and Cheng's Definition 1.1, verbatim

This file transcribes Definition 1.1 of the source (`ronbun2793`, Section 1) as a
Lean structure, field for field, and relates it to the interface
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

/-- **Bishop and Cheng, Definition 1.1**, transcribed field for field. -/
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

/-! ## The adapter

Every field of `IntSpaceC` is now available from Definition 1.1 except **one**,
which is taken as an explicit argument.  Isolating it is the point of the
statement: it says precisely how far Definition 1.1 goes and what has to be
added.

Note in particular that `IntSpaceC.I_nonneg` is *not* among the assumptions.  It
is `I_nonneg` above, derived from clause (2); the interface carries it as a field
but does not need to.

* `hcut` is the gap, and it is not an artefact of the transcription.  Clause
  (1) provides truncation at the constant `1` only.  The source's own remark
  recovers `min{f,n}` for a positive integer `n` by `min{f,n} = n·min{n⁻¹f,1}`,
  and `min{f,0} = (f - |f|)/2` follows from clause (1) as well; but both routes
  need the constant to carry a positivity witness, since `n⁻¹` requires `n` to be
  apart from `0` and a case distinction between `a = 0` and `a > 0` is not
  available constructively.  `IntSpaceC.cutConst_mem` demands truncation at an
  *arbitrary* constant, which for a negative constant fails in the standard
  models: for `L = L¹(ℝ)` and `a < 0`, `min(f,a) ≤ a < 0` everywhere, so
  `min(f,a) ∉ L`.  The two constants the development actually truncates at are
  `n` (`cutNat`) and `εₙ` (`cutSmall`), both of which carry such a witness. -/

/-- **Adapter**: an integration space in the sense of Bishop and Cheng's
Definition 1.1 yields the interface used by the development, given the two
arguments discussed above. -/
def toIntSpaceC
    (hcut : ∀ (a : CReal) {f : BFunC X}, f ∈ D.L → BFunC.minC f a ∈ D.L) :
    IntSpaceC X where
  L := D.L
  I := D.I
  L_resp := D.L_resp
  I_resp := D.I_resp
  add_mem := D.add_mem
  smul_mem := D.smul_mem
  abs_mem := D.abs_mem
  cutConst_mem := hcut
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
#print axioms BishopCheng.IntegrationSpaceDef11.toIntSpaceC

end BishopCheng
