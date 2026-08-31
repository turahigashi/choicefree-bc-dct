import Mathdemo.SourceIntegrationSpaceDef11

/-!
# Point evaluation as an integration space

The concrete example shipped with the artifact so far is the zero-integral space,
which is admissible only because Definition~2.1 of the paper imposes no
normalization.  This file supplies a second, *normalized* example: point
evaluation at a fixed point `x₀`.

`L` is the set of partial functions defined at `x₀` and `I` is evaluation at
`x₀`.  The constant function `1` then lies in `L` with integral `1`, so this is a
model of Bishop and Cheng's Definition 1.1 clause (3), which the zero-integral
space is not.

**Every clause of Definition 1.1 is discharged, with no hypotheses.**  For
point evaluation, the two source-level limits of clause (4) reduce to
statements about the truncations of a single real,

* `min{c,n} → c`, which holds with a constant modulus once `n` passes the
  Archimedean bound of `c`, and
* `min{|c|,1/(n+1)} → 0`, the source-gauge limit used by `diracDef11`,

and both are proved below, together with the auxiliary dyadic limit
`min{|c|,2⁻ⁿ} → 0`.  Composing with the adapter of
`Mathdemo.SourceIntegrationSpaceDef11` — which is itself hypothesis-free —
yields an integration space in the sense of Definition 2.1 as well.  This is
therefore a nondegenerate concrete model, and it is unconditional.
-/

namespace BishopCheng

open BishopCReal BishopSec1P

universe u

variable {X : Type u}

/-- The partial functions that are defined at `x₀`. -/
def diracL (x₀ : X) : Set (BFunC X) := {f | x₀ ∈ f.dom}

/-- Evaluation at `x₀`. -/
def diracI (x₀ : X) (f : BFunC X) (hf : f ∈ diracL x₀) : CReal :=
  f.toFun x₀ hf

/-- The constant function `1`, defined at every point. -/
def oneEverywhere (X : Type u) : BFunC X where
  dom := Set.univ
  toFun := fun _ _ => CReal.one

/-- The Archimedean upper bound of `BishopSec1P.exists_nat_geC`, with the witness
made explicit so that it can be used as data.  The statement of `exists_nat_geC`
is a `Prop`-valued existential and therefore cannot supply the modulus of a
`RepSeriesTendsto`, which is data; the proof below is that of `exists_nat_geC`
with its witness `2 ^ CReal.mulArchBound φ` written out. -/
theorem natGeBound_spec (φ : CReal) :
    RegularSeqLe φ (constSeq (Nat.cast (2 ^ CReal.mulArchBound φ))) := by
  have hspec : BishopC.Le
      ((BishopC.COF.abs (φ.val 1) + 1) * eps (CReal.mulArchBound φ)) 1 :=
    standardBoundWith_spec_base cRatScalarMulArch φ
  apply regularSeqLe_of_indexed_pointwise_le
  intro n
  change BishopC.Le (φ.val (n + 1))
    ((Nat.cast (2 ^ CReal.mulArchBound φ) : Scalar))
  have hbase : BishopC.Le (BishopC.COF.abs (φ.val 1) + 1)
      ((Nat.cast (2 ^ CReal.mulArchBound φ) : Scalar)) := by
    have hmul := scalar_mul_le_mul_right hspec
      (scalar_natCast_nonneg (2 ^ CReal.mulArchBound φ))
    rw [show ((BishopC.COF.abs (φ.val 1) + 1) * eps (CReal.mulArchBound φ))
            * Nat.cast (2 ^ CReal.mulArchBound φ)
          = (BishopC.COF.abs (φ.val 1) + 1)
            * (eps (CReal.mulArchBound φ)
              * Nat.cast (2 ^ CReal.mulArchBound φ)) from by ring,
        eps_mul_natCast_twoPow (CReal.mulArchBound φ), mul_one, one_mul] at hmul
    exact hmul
  have htri := scalar_abs_sub_le_three (φ.val (n + 1)) (φ.val 1) 0 0
  rw [show φ.val (n + 1) - (0 : Scalar) = φ.val (n + 1) from by ring,
      show φ.val 1 - (0 : Scalar) = φ.val 1 from by ring,
      show BishopC.COF.abs ((0 : Scalar) - 0) = 0 from by
        rw [show (0 : Scalar) - 0 = 0 from by ring]; exact scalarCOFOSeed.abs_zero,
      show BishopC.COF.abs (φ.val 1) + (0 : Scalar) = BishopC.COF.abs (φ.val 1) from by ring] at htri
  have hreg : BishopC.Le (BishopC.COF.abs (φ.val (n + 1) - φ.val 1)) (eps (n + 1) + eps 1) :=
    φ.regular (n + 1) 1
  have hepsle : BishopC.Le (eps (n + 1) + eps 1) (1 : Scalar) := by
    have h1 : BishopC.Le (eps (n + 1)) (eps 1) :=
      eps_le_of_le (Nat.succ_le_succ (Nat.zero_le n))
    have hsum : BishopC.Le (eps (n + 1) + eps 1) (eps 1 + eps 1) :=
      BishopC.le_add h1 (BishopC.le_refl (eps 1))
    rw [eps_succ_add_self 0, show eps 0 = (1 : Scalar) from rfl] at hsum
    exact hsum
  have hbound : BishopC.Le (BishopC.COF.abs (φ.val (n + 1)))
      ((eps (n + 1) + eps 1) + BishopC.COF.abs (φ.val 1)) :=
    BishopC.le_trans htri (BishopC.le_add hreg (BishopC.le_refl _))
  have hbound2 : BishopC.Le (BishopC.COF.abs (φ.val (n + 1)))
      ((1 : Scalar) + BishopC.COF.abs (φ.val 1)) :=
    BishopC.le_trans hbound (BishopC.le_add hepsle (BishopC.le_refl _))
  have hval_abs : BishopC.Le (BishopC.COF.abs (φ.val (n + 1))) (BishopC.COF.abs (φ.val 1) + 1) := by
    rw [show (1 : Scalar) + BishopC.COF.abs (φ.val 1) = BishopC.COF.abs (φ.val 1) + 1 from by ring]
      at hbound2
    exact hbound2
  exact BishopC.le_trans (scalarCOFOSeed.le_abs_self (φ.val (n + 1)))
    (BishopC.le_trans hval_abs hbase)

/-- **The first limit of clause (4), for a single real.**  `min{c,n} → c`.

Once `n` exceeds the Archimedean bound of `c`, the truncation *is* `c`, so the
modulus is constant. -/
noncomputable def cutNat_tendsto_point (c : CReal) :
    RepSeriesTendsto
      (fun n : Nat => CReal.min c (constSeq (Nat.cast n))) c where
  mod := fun _ => 2 ^ CReal.mulArchBound c
  close := by
    intro k n hn
    have hle : RegularSeqLe c (constSeq (Nat.cast n)) :=
      regularSeqLe_trans (natGeBound_spec c) (natCast_le_of_leC hn)
    exact bc1_repClose_of_relEventually (CReal.min_eq_left_of_leC hle) (k + 1)

/-- **The second limit of clause (4), for a single real.**  `min{|c|,2⁻ⁿ} → 0`.

The truncation is squeezed between `0` and `2⁻ⁿ`, and `2⁻ⁿ` is eventually below
any given gauge; both steps are available for the presented reals. -/
noncomputable def cutSmall_tendsto_point (c : CReal) :
    RepSeriesTendsto
      (fun n : Nat => CReal.min (CReal.abs c) (CReal.epsSeq n)) CReal.zero where
  mod := fun k => k + 2
  close := by
    intro k n hn
    refine BishopSec3P.lemma43RepCloseAtGauge_zero_of_abs_le_ltC
      (y := CReal.epsSeq n) ?_ ?_
    · -- `|min{|c|,2⁻ⁿ}| ≤ 2⁻ⁿ`
      have hcomm : relEventually (CReal.min (CReal.abs c) (CReal.epsSeq n))
          (CReal.min (CReal.epsSeq n) (CReal.abs c)) :=
        minSeqWith_comm_eventually cRatScalarMulArch _ _
      have habs :
          relEventually (CReal.abs (CReal.min (CReal.abs c) (CReal.epsSeq n)))
            (CReal.abs (CReal.min (CReal.epsSeq n) (CReal.abs c))) :=
        absSeq_respects_eventually _ _ hcomm
      have h1 :
          RegularSeqLe (CReal.abs (CReal.min (CReal.epsSeq n) (CReal.abs c)))
            (CReal.abs (CReal.epsSeq n)) :=
        CReal.abs_min_const_le (absSeq_regularSeqNonneg c) _
      have h2 : CReal.abs (CReal.epsSeq n) ≈ CReal.epsSeq n :=
        CReal.abs_of_nonneg_E
          (regularSeqNonneg_of_zero_le
            (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_halfPow n)))
      exact regularSeqLe_of_right_eventual h2
        (regularSeqLe_of_left_eventual habs h1)
    · -- `2⁻ⁿ < 2⁻⁽ᵏ⁺¹⁾` because `n ≥ k+2`
      exact regularSeqLtProp_of_le_of_lt (halfPow_antitone_leC hn)
        (regularSeqLtProp_halfPow_succ (k + 1))

/-- **The second limit of clause (4) at the source's gauge**, for a single
real: `min{|c|, 1/(n+1)} → 0`.  Same squeeze as the dyadic version, with
`srcGauge_le_halfPow` supplying the eventual bound. -/
noncomputable def cutSmallSrc_tendsto_point (c : CReal) :
    RepSeriesTendsto
      (fun n : Nat => CReal.min (CReal.abs c) (srcGauge n)) CReal.zero where
  mod := fun k => 2 ^ (k + 2)
  close := by
    intro k n hn
    refine BishopSec3P.lemma43RepCloseAtGauge_zero_of_abs_le_ltC
      (y := srcGauge n) ?_ ?_
    · have hcomm : relEventually (CReal.min (CReal.abs c) (srcGauge n))
          (CReal.min (srcGauge n) (CReal.abs c)) :=
        minSeqWith_comm_eventually cRatScalarMulArch _ _
      have habs :
          relEventually (CReal.abs (CReal.min (CReal.abs c) (srcGauge n)))
            (CReal.abs (CReal.min (srcGauge n) (CReal.abs c))) :=
        absSeq_respects_eventually _ _ hcomm
      have h1 :
          RegularSeqLe (CReal.abs (CReal.min (srcGauge n) (CReal.abs c)))
            (CReal.abs (srcGauge n)) :=
        CReal.abs_min_const_le (absSeq_regularSeqNonneg c) _
      have h2 : CReal.abs (srcGauge n) ≈ srcGauge n :=
        CReal.abs_of_nonneg_E
          (regularSeqNonneg_of_zero_le
            (regularSeqLe_of_ltPropC
              (regularSeqLtProp_zero_of_posData (srcGauge_posData n))))
      exact regularSeqLe_of_right_eventual h2
        (regularSeqLe_of_left_eventual habs h1)
    · exact regularSeqLtProp_of_le_of_lt
        (srcGauge_le_halfPow (Nat.le_succ_of_le hn))
        (regularSeqLtProp_halfPow_succ (k + 1))

/-- **Point evaluation is an integration space in the sense of Definition 1.1**,
with no remaining hypotheses. -/
noncomputable def diracDef11 (x₀ : X) : IntegrationSpaceDef11 X where
  inhabited := x₀
  L := diracL x₀
  I := diracI x₀
  L_resp := by
    intro f g hf hfg
    show x₀ ∈ g.dom
    rw [← hfg.1]
    exact hf
  I_resp := by
    intro f g hf hfg
    exact hfg.2 x₀ hf
  lin_mem := by
    intro α β f g hf hg
    exact ⟨hf, hg⟩
  abs_mem := by
    intro f hf
    exact hf
  cutOne_mem := by
    intro f hf
    exact hf
  I_lin := by
    intro α β f g _hf _hg
    exact Setoid.refl _
  continuity := by
    intro f fs hf hfs _hnn hI hlt
    exact ⟨x₀, hf, hfs, hI, hlt⟩
  p := oneEverywhere X
  p_mem := by
    show x₀ ∈ (oneEverywhere X).dom
    trivial
  I_p := Setoid.refl _
  cutNat_tendsto := by
    intro f hf _hcut
    exact cutNat_tendsto_point (f.toFun x₀ hf)
  cutSmallSrc_tendsto := by
    intro f hf _hcut
    exact cutSmallSrc_tendsto_point (f.toFun x₀ hf)

/-- Truncation at an arbitrary constant stays in `L`, because truncation does
not change the domain.  The adapter no longer needs this (it derives the
interface's witnessed truncation field from Definition 1.1 itself); it is kept
as a remark: the incomparability of Remark 2.2 is invisible in this model,
exactly as it is in every model whose functions are total at the points that
matter. -/
theorem diracCutConst (x₀ : X) (a : CReal) {f : BFunC X}
    (hf : f ∈ diracL x₀) : BFunC.minC f a ∈ diracL x₀ := hf

/-- The interface of Definition 2.1 for point evaluation, obtained from
Definition 1.1 through the (hypothesis-free) adapter. -/
noncomputable def diracIntSpaceC (x₀ : X) : IntSpaceC X :=
  (diracDef11 x₀).toIntSpaceC

#print axioms BishopCheng.natGeBound_spec
#print axioms BishopCheng.cutNat_tendsto_point
#print axioms BishopCheng.cutSmall_tendsto_point
#print axioms BishopCheng.cutSmallSrc_tendsto_point
#print axioms BishopCheng.diracDef11
#print axioms BishopCheng.diracIntSpaceC
#print axioms BishopCheng.diracCutConst

end BishopCheng
