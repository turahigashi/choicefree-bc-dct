import Mathdemo.Internal.CRat_iter402

set_option linter.style.longLine false

/-!
# G304: from original row flattenability to split majorants

G303 made the `seriesSumRep_L1` split explicit.  This node proves the generic
estimates that make that split usable:

* the finite-prefix row `G_m F i` has pointwise absolute sum bounded by the
  pointwise absolute sum of the original row `F i`;
* the tail row `tail_m F i` has pointwise absolute sum bounded by the same
  original row absolute sum.

Consequently, ordinary `PointwiseFlattenable F x` already supplies the split
majorants required by G303.  The remaining Proposition-2.10 problem is now
localized to proving `PointwiseFlattenable` for the original source families
`prop_2_10_F` and `prop_2_10_G`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Finite-prefix and tail estimates -/

/-- Finite triangle inequality for partial sums. -/
theorem abs_partialSum_le_abs_partialSum
    (u : Nat → R) :
    forall N : Nat,
      Le (COF.abs (RSeq.partialSum u N))
        (RSeq.partialSum (fun n => COF.abs (u n)) N)
  | 0 => le_refl _
  | N + 1 => by
      change Le
        (COF.abs (RSeq.partialSum u N + u (N + 1)))
        (RSeq.partialSum (fun n => COF.abs (u n)) N + COF.abs (u (N + 1)))
      exact le_trans (COFO.abs_add_le _ _)
        (le_add (abs_partialSum_le_abs_partialSum u N) (le_refl _))


namespace RepDefinedAt

/-- The `G_m` finite-prefix split row is bounded pointwise by the absolute
sum of the original row. -/
theorem Gm_sum_le_row_abs
    (F : Nat → IntegrableRep S)
    (i : Nat) {x : X}
    (hrow : RepDefinedAt (S := S) (F i) x) :
    Le ((RepDefinedAt.Gm (S := S) F i x).sum) hrow.sum := by
  change Le (COF.abs ((psi_m F i).toFun x)) hrow.sum
  rw [psi_m, BFunR.seqSum_toFun]
  exact le_trans
    (abs_partialSum_le_abs_partialSum
      (fun n => ((F i).fn n).toFun x) (Nm F i))
    (partialSum_le_sum
      (fun n => abs_nonneg (((F i).fn n).toFun x))
      hrow
      (Nm F i))


/-- The `tail_m` split row is bounded pointwise by the absolute sum of the
original row. -/
theorem tailm_sum_le_row_abs
    (F : Nat → IntegrableRep S)
    (i : Nat) {x : X}
    (hrow : RepDefinedAt (S := S) (F i) x) :
    Le ((RepDefinedAt.tailm (S := S) F i hrow).sum) hrow.sum := by
  change Le
    ((seriesSum_tail hrow (Nm F i)).sum)
    hrow.sum
  apply le_of_nonneg_sub
  show Nonneg (hrow.sum - ((seriesSum_tail hrow (Nm F i)).sum))
  rw [show hrow.sum - ((seriesSum_tail hrow (Nm F i)).sum)
      = RSeq.partialSum
          (fun n => COF.abs (((F i).fn n).toFun x))
          (Nm F i) from by
        change hrow.sum
            - (hrow.sum
              - RSeq.partialSum
                (fun n => COF.abs (((F i).fn n).toFun x))
                (Nm F i))
            =
              RSeq.partialSum
                (fun n => COF.abs (((F i).fn n).toFun x))
                (Nm F i)
        ring]
  exact partialSum_nonneg
    (fun n => abs_nonneg (((F i).fn n).toFun x))
    (Nm F i)


end RepDefinedAt

/-! ## 2. Build split majorants from ordinary pointwise flattenability -/

namespace SeriesSumRepL1SplitMajorants

/-- Ordinary pointwise flattenability of `F` supplies the split majorants
required by G303. -/
def ofPointwiseFlattenable
    {F : Nat → IntegrableRep S}
    {hsum : RSeq.SeriesSum (fun m => (F m).normL1)}
    {x : X}
    (P : PointwiseFlattenable (S := S) F x) :
    SeriesSumRepL1SplitMajorants (S := S) F hsum x where
  row_abs := P.row_abs
  g_majorant := P.majorant
  g_majorant_sum := P.majorant_sum
  g_row_abs_le := fun i =>
    le_trans
      (RepDefinedAt.Gm_sum_le_row_abs (S := S) F i (P.row_abs i))
      (P.row_abs_le i)
  tail_majorant := P.majorant
  tail_majorant_sum := P.majorant_sum
  tail_row_abs_le := fun i =>
    le_trans
      (RepDefinedAt.tailm_sum_le_row_abs (S := S) F i (P.row_abs i))
      (P.row_abs_le i)


end SeriesSumRepL1SplitMajorants

/-! ## 3. Proposition-2.10 witnesses reduced to ordinary pointwise flattenability -/

structure Prop210BSourcePointwiseFlattenableWitness
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) : Type _ where
  dom_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      forall m : Nat,
        x ∈ ((prop_2_10_rep A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv)).fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      forall m : Nat,
        x ∈ ((prop_2_10_rep A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv)).fn m).dom
  pointwise_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      PointwiseFlattenable (S := S)
        (prop_2_10_F A (fun k => (HA k).base)) x
  pointwise_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      PointwiseFlattenable (S := S)
        (prop_2_10_F A (fun k => (HA k).base)) x


namespace Prop210BSourcePointwiseFlattenableWitness

noncomputable def toSplitMajorantWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)}
    (W : Prop210BSourcePointwiseFlattenableWitness (S := S) A HA h_conv) :
    Prop210BSourceSplitMajorantWitness (S := S) A HA h_conv where
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  split_majorants_on_s1 := by
    intro x hx
    exact SeriesSumRepL1SplitMajorants.ofPointwiseFlattenable
      (S := S)
      (hsum := prop_2_10_F_norm_sum A (fun k => (HA k).base)
        (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
      (W.pointwise_on_s1 x hx)
  split_majorants_on_s2 := by
    intro x hx
    exact SeriesSumRepL1SplitMajorants.ofPointwiseFlattenable
      (S := S)
      (hsum := prop_2_10_F_norm_sum A (fun k => (HA k).base)
        (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
      (W.pointwise_on_s2 x hx)


end Prop210BSourcePointwiseFlattenableWitness

structure Prop210CSourcePointwiseFlattenableWitness
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) : Type _ where
  dom_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      forall m : Nat,
        x ∈ ((prop_2_10_c_rep A (fun k => (HA k).base) h_lim).fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      forall m : Nat,
        x ∈ ((prop_2_10_c_rep A (fun k => (HA k).base) h_lim).fn m).dom
  head_abs_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      RepDefinedAt (S := S) (HA 0).base.rep x
  pointwise_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      PointwiseFlattenable (S := S)
        (prop_2_10_G A (fun k => (HA k).base)) x
  pointwise_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      PointwiseFlattenable (S := S)
        (prop_2_10_G A (fun k => (HA k).base)) x


namespace Prop210CSourcePointwiseFlattenableWitness

noncomputable def toSplitMajorantWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β}
    (W : Prop210CSourcePointwiseFlattenableWitness (S := S) A HA h_lim) :
    Prop210CSourceSplitMajorantWitness (S := S) A HA h_lim where
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  head_abs_on_s2 := W.head_abs_on_s2
  split_majorants_on_s1 := by
    intro x hx
    exact SeriesSumRepL1SplitMajorants.ofPointwiseFlattenable
      (S := S)
      (hsum := prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
      (W.pointwise_on_s1 x hx)
  split_majorants_on_s2 := by
    intro x hx
    exact SeriesSumRepL1SplitMajorants.ofPointwiseFlattenable
      (S := S)
      (hsum := prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
      (W.pointwise_on_s2 x hx)


end Prop210CSourcePointwiseFlattenableWitness

/-! ## 4. Audit -/

structure Sec2OriginalPointwiseAuditAfterG304 : Type where
  finite_prefix_bound_added : Nat
  tail_bound_added : Nat
  split_majorants_from_pointwise_added : Nat
  prop210_pointwise_witness_records_added : Nat
  final_prop210_witnesses_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_original_pointwise_flattenability_problem : Nat

def sec2OriginalPointwiseAuditAfterG304 :
    Sec2OriginalPointwiseAuditAfterG304 where
  finite_prefix_bound_added := 1
  tail_bound_added := 1
  split_majorants_from_pointwise_added := 1
  prop210_pointwise_witness_records_added := 2
  final_prop210_witnesses_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_original_pointwise_flattenability_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G304OriginalPointwisePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g303 : Chapter4G303SplitRowDataPackage S
  audit : BishopC.Sec2OriginalPointwiseAuditAfterG304
  original_pointwise_reduction_added_this_step : Nat
  final_prop210_witnesses_constructed_this_step : Nat
  remaining_original_pointwise_flattenability_problem : Nat

def chapter4G304OriginalPointwisePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G304OriginalPointwisePackage S where
  g303 := chapter4G303SplitRowDataPackage S
  audit := BishopC.sec2OriginalPointwiseAuditAfterG304
  original_pointwise_reduction_added_this_step := 1
  final_prop210_witnesses_constructed_this_step := 0
  remaining_original_pointwise_flattenability_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G304. -/
def bishopRegularSeqChapter4OriginalPointwiseProgressAfterG304 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G304: proved that ordinary PointwiseFlattenable data for a family F \
    supplies the split majorants required for seriesSumRep_L1.  The remaining \
    Proposition-2.10 task is to prove PointwiseFlattenable for the original \
    source families prop_2_10_F and prop_2_10_G on the final sides."


end BishopCReal
