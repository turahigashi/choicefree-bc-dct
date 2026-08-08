import Mathdemo.Internal.Sec4GenIB

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-A1: choice-free scaffolding for the general relative integral `I_B`

This file starts the direct construction route for the relative integral
component.

The central point is to avoid proving non-negativity of
`g_{k+1}.sub g_k`; instead the tail is represented by single positive pieces
`χ_{D_k}·f`, where `D_k = (A_{k+1} ∧ B) - (A_k ∧ B)`.

The file contains:
* stable names for `A_k ∧ B`, `D_k`, their integrability data, and the
  corresponding `χ_D·f` representatives;
* a fully explicit `min2` non-negativity lemma;
* an abstract but kernel-checkable bridge for the hardest part of
  `seriesSumRep_L1_repNonneg`: converting the flattened absolute convergence
  of `seriesSumRep_L1` into row absolute/signed sums;
* the direct `genIB` representative once the norm-majorant series is supplied.

Every declaration is followed by a dependency-audit command.  The import and a few exact
API names may need the first kernel pass to adjust, especially
`IntegrableSet1_sub` and the internal unfolding of `prop_4_2_chi_f_rep`.
-/

#check coverApart
#check coverSet
#check coverSet_int
#check coverSet_tendsto
#check IsMeasurableSet
#check IntegrableSet1_sub
#check prop_4_2_chi_f_rep
#check prop_4_2_lambda_k
#check prop_4_2_n_k
#check prop_4_2_lambda_sum
#check seriesSumRep_L1
#check seriesSumRep_L1_value
#check seriesSumRep_L1_hsplit_value
#check IntegrableRep.normL1_eq_integral_of_nonneg
#check relIntegral
#check relIntegral_mono_le
#check relIntegral_or_add_and

/-! ## 1. The increasing cover, intersected with the measurable set `B` -/

/-- `A_k ∧ B`, where `A_k = {f ≥ t_k}` is the choice-free cover from Phase 1a. -/
noncomputable def sec4CoverAnd
    (B : BSet X) (f : IntegrableRep S) (k : Nat) : BSet X :=
  BSet.and (coverSet f k) B


/-- Integrability of `A_k ∧ B`, using measurability of `B`. -/
noncomputable def sec4CoverAnd_int
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (sec4CoverAnd B f k) :=
  hB (coverSet f k) (coverSet_int f k)


/--
The one-step layer
`D_k = (A_{k+1} ∧ B) - (A_k ∧ B)`.
-/
noncomputable def sec4CoverDiff
    (B : BSet X) (f : IntegrableRep S) (k : Nat) : BSet X :=
  BSet.sub (sec4CoverAnd B f (k + 1)) (sec4CoverAnd B f k)


/--
Integrability of `D_k`.

The exact shape of `IntegrableSet1_sub` is the first expected kernel
adjustment.  In the current development it is the Proposition 2.5 constructor.
-/
noncomputable def sec4CoverDiff_int
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (k : Nat) :
    IntegrableSet1 S (sec4CoverDiff B f k) :=
  IntegrableSet1_sub
    (sec4CoverAnd_int B hB f (k + 1))
    (sec4CoverAnd_int B hB f k)


/-- The base part `χ_{A_0 ∧ B}·f`. -/
noncomputable def sec4IB_baseRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : IntegrableRep S :=
  prop_4_2_chi_f_rep (sec4CoverAnd B f 0)
    (sec4CoverAnd_int B hB f 0) f hnn


/-- The `k`-th positive layer `χ_{D_k}·f`. -/
noncomputable def sec4IB_termRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : IntegrableRep S :=
  prop_4_2_chi_f_rep (sec4CoverDiff B f k)
    (sec4CoverDiff_int B hB f k) f hnn


/-! ## 2. RepNonneg preservation lemmas -/

/--
`min2` preserves representation non-negativity.

This is the completely local part of the preservation chain.  It uses the
existing de-interleaving lemmas for `min2` and the value theorem
`min2_value`; no value theorem for `χ_A·f` is used.
-/
theorem sec4_min2_repNonneg
    {r s : IntegrableRep S}
    (hrnn : RepNonneg r) (hsnn : RepNonneg s) :
    RepNonneg (IntegrableRep.min2 r s) := by
  intro x habs hx
  let hrAbs : RSeq.SeriesSum
      (fun n => COF.abs ((r.fn n).toFun x)) :=
    min2_absSeriesSum_left (r := r) (s := s) habs
  let hsAbs : RSeq.SeriesSum
      (fun n => COF.abs ((s.fn n).toFun x)) :=
    min2_absSeriesSum_right (r := r) (s := s) habs
  let hrVal : RSeq.SeriesSum (fun n => (r.fn n).toFun x) :=
    seriesSum_of_abs hrAbs
  let hsVal : RSeq.SeriesSum (fun n => (s.fn n).toFun x) :=
    seriesSum_of_abs hsAbs
  let hm := min2_value r s x hrVal hsVal
  have hx_eq : hx.sum = hm.val.sum := seriesSum_unique hx hm.val
  rw [hx_eq, hm.property]
  exact BishopC.le_min (hrnn x hrAbs hrVal) (hsnn x hsAbs hsVal)


/--
Pointwise bridge needed to prove non-negativity of `seriesSumRep_L1`.

For a point `x`, a flattened absolute-convergence witness for
`seriesSumRep_L1 F hsum` must provide row absolute sums, row signed sums, and
a signed outer row-sum series whose sum is the value of the flattened series.
This is the exact abstraction of the hard `seriesSumRep_L1_value` /
`seriesSumRep_L1_hsplit_value` work.
-/
structure Sec4SeriesSumRepL1PointBridge
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    (x : X)
    (hflatabs : RSeq.SeriesSum
      (fun n => COF.abs (((seriesSumRep_L1 F hsum).fn n).toFun x))) where
  rowAbs : ∀ m : Nat,
    RSeq.SeriesSum (fun n => COF.abs (((F m).fn n).toFun x))
  rowVal : ∀ m : Nat,
    RSeq.SeriesSum (fun n => ((F m).fn n).toFun x)
  rows : RSeq.SeriesSum (fun m => (rowVal m).sum)
  value_eq : (seriesSum_of_abs hflatabs).sum = rows.sum


/--
If the point bridge exists for every `x`, `seriesSumRep_L1` preserves
`RepNonneg`.

This isolates the only nontrivial `seriesSumRep_L1` point-value bookkeeping.
-/
noncomputable def sec4_seriesSumRep_L1_repNonneg_of_bridge
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    (hFnn : ∀ m : Nat, RepNonneg (F m))
    (bridge : ∀ x hflatabs,
      Sec4SeriesSumRepL1PointBridge (S := S) F hsum x hflatabs) :
    RepNonneg (seriesSumRep_L1 F hsum) := by
  intro x hflatabs hx
  let B := bridge x hflatabs
  have hrows_nonneg :
      Nonneg (B.rows.sum) :=
    seriesSum_nonneg
      (fun m => hFnn m x (B.rowAbs m) (B.rowVal m))
      B.rows
  have hx_to_rows : hx.sum = B.rows.sum := by
    calc
      hx.sum = (seriesSum_of_abs hflatabs).sum :=
        seriesSum_unique hx (seriesSum_of_abs hflatabs)
      _ = B.rows.sum := B.value_eq
  rw [hx_to_rows]
  exact hrows_nonneg


/-! ## 3. Direct `I_B` representative once the norm-majorant series is supplied -/

/-- Technical lemma used in the public import closure. -/
def Sec4IBTailData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  RSeq.SeriesSum (fun k => (sec4IB_termRep B hB f hnn k).normL1)


/-- The positive tail `Σ_k χ_{D_k}·f`. -/
noncomputable def sec4IB_tailRep
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) B hB f hnn) : IntegrableRep S :=
  seriesSumRep_L1 (fun k => sec4IB_termRep B hB f hnn k) H


/--
The direct candidate for `χ_B·f`:
`χ_{A_0∧B}·f + Σ_k χ_{D_k}·f`.
-/
noncomputable def genIB_rep_from_tailData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) B hB f hnn) : IntegrableRep S :=
  (sec4IB_baseRep B hB f hnn).add (sec4IB_tailRep B hB f hnn H)


/-- Relative integral from the direct candidate. -/
noncomputable def genRelIntegral_from_tailData
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) B hB f hnn) : R :=
  (genIB_rep_from_tailData B hB f hnn H).integral


/-! ## 4. Bridges for the next kernel-loop chunks -/

/--
The value-identification target for the direct construction.

This is intentionally stated without introducing a new characteristic function
object for the general measurable set `B`: on `B.S1` the value must be the
value of `f`; on `B.S2` it must be zero.  The domain-side union information is
included because it is needed later for relative-integral convergence theorems.
-/
structure Sec4IBValueBridge
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) B hB f hnn) : Prop where
  domain :
    ∀ x, RSeq.SeriesSum
      (fun n => COF.abs (((genIB_rep_from_tailData B hB f hnn H).fn n).toFun x)) →
      x ∈ B.S1 ∪ B.S2
  value_one :
    ∀ x,
      x ∈ B.S1 →
      ∀ hflatabs : RSeq.SeriesSum
        (fun n => COF.abs (((genIB_rep_from_tailData B hB f hnn H).fn n).toFun x)),
      ∀ hfabs : RSeq.SeriesSum (fun n => COF.abs ((f.fn n).toFun x)),
      (seriesSum_of_abs hflatabs).sum = (seriesSum_of_abs hfabs).sum
  value_zero :
    ∀ x,
      x ∈ B.S2 →
      ∀ hflatabs : RSeq.SeriesSum
        (fun n => COF.abs (((genIB_rep_from_tailData B hB f hnn H).fn n).toFun x)),
      (seriesSum_of_abs hflatabs).sum = 0


/--
Consistency target with the previous relative integral for an already integrable
set.  This is the splice point for the next chunk after the direct construction
has been kernel-verified.
-/
structure Sec4IBConsistencyBridge
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (H : Sec4IBTailData (S := S) C (isMeasurableSet_of_integrable hC) f hnn) : Prop where
  integral_eq :
    genRelIntegral_from_tailData C (isMeasurableSet_of_integrable hC) f hnn H =
      relIntegral C hC f hnn


end BishopC
