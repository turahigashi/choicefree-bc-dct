import Mathdemo.Internal.CRat_iter399

set_option linter.style.longLine false

/-!
# G301: pointwise flattening API for `seriesSumRep_L1`

G300 fixed the exact source representatives whose side witnesses are still
missing.  The next obstacle is not value-level eventual-zero behavior, but
pointwise absolute convergence of the flattened representatives produced by
`seriesSumRep_L1`.

This node adds a public pointwise API:

* `RepDefinedAt r x` abbreviates the Definition-2.3 pointwise absolute
  convergence condition for a representative;
* `PointwiseFlattenable F x` records rowwise absolute convergence plus a
  summable majorant for the row absolute sums;
* `seriesIntegrable_definedAt_of_pointwiseFlattenable` is the forward
  row-to-cellAt bridge;
* `SeriesSumRepL1PointwiseData` supplies the two pieces that the actual
  `seriesSumRep_L1` definition uses, namely `G_m F` and `tail_m F`.

No Proposition-2.10 side witness is constructed in this node.  It only
exposes the correct bridge theorem needed before attempting that construction.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Public pointwise representative API -/

/-- A representative is defined at `x` in the Definition-2.3 pointwise sense:
all components are defined there and its representing series is absolutely
convergent at `x`. -/
structure RepDefinedAt (r : IntegrableRep S) (x : X) : Type _ where
  dom : r.MemAt x
  series : RSeq.SeriesSum (fun m => COF.abs (r.valueAt x dom m))

/-- The signed value series associated with a pointwise-defined representative. -/
def RepValueSeries (r : IntegrableRep S) (x : X) (h : RepDefinedAt (S := S) r x) :
    Type _ :=
  RSeq.SeriesSum (fun m => r.valueAt x h.dom m)


namespace RepDefinedAt

/-- Absolute-series sum, retained as the projection-level public API. -/
abbrev sum {r : IntegrableRep S} {x : X}
    (h : RepDefinedAt (S := S) r x) : R := h.series.sum

/-- Absolute-series convergence modulus. -/
abbrev tends {r : IntegrableRep S} {x : X}
    (h : RepDefinedAt (S := S) r x) := h.series.tends

/-- Pointwise absolute convergence is stable under representative addition. -/
def add {r r' : IntegrableRep S} {x : X}
    (hr : RepDefinedAt (S := S) r x)
    (hr' : RepDefinedAt (S := S) r' x) :
    RepDefinedAt (S := S) (r.add r') x := by
  let haddDom := IntegrableRep.add_memAt hr.dom hr'.dom
  refine { dom := haddDom, series := ?_ }
  exact seriesSum_congr
    (fun n => by
      rw [add_fn_toFun r r' n x hr.dom hr'.dom,
        seqInterleave_map COF.abs
          (fun k => r.valueAt x hr.dom k)
          (fun k => r'.valueAt x hr'.dom k) n])
    (seriesSum_interleave hr.series hr'.series)


/-- Pointwise absolute convergence is stable under representative negation. -/
def neg {r : IntegrableRep S} {x : X}
    (hr : RepDefinedAt (S := S) r x) :
    RepDefinedAt (S := S) (r.neg) x := by
  refine { dom := IntegrableRep.neg_memAt hr.dom, series := ?_ }
  exact seriesSum_congr
    (fun n => by rw [neg_fn_toFun r n x hr.dom, COFO.abs_neg])
    hr.series


/-- Pointwise absolute convergence is stable under representative subtraction. -/
def sub {r r' : IntegrableRep S} {x : X}
    (hr : RepDefinedAt (S := S) r x)
    (hr' : RepDefinedAt (S := S) r' x) :
    RepDefinedAt (S := S) (r.sub r') x :=
  add hr (neg hr')


end RepDefinedAt

/-! ## 2. Rowwise pointwise flattening data -/

/-- Rowwise pointwise absolute convergence plus a summable majorant for the
row absolute sums.  This is the correct pointwise hypothesis for a forward
flattening theorem; value-level convergence of the row sums alone is not
enough. -/
structure PointwiseFlattenable
    (F : Nat → IntegrableRep S) (x : X) : Type _ where
  row_abs :
    forall i : Nat, RepDefinedAt (S := S) (F i) x
  majorant : Nat → R
  majorant_sum : RSeq.SeriesSum majorant
  row_abs_le :
    forall i : Nat, Le ((row_abs i).sum) (majorant i)


namespace PointwiseFlattenable

/-- The row absolute sums themselves are summable by comparison with the
declared majorant. -/
def rowAbsSum
    {F : Nat → IntegrableRep S} {x : X}
    (P : PointwiseFlattenable (S := S) F x) :
    RSeq.SeriesSum (fun i => (P.row_abs i).sum) :=
  seriesSum_comparison
    (fun i =>
      seriesSum_nonneg
        (fun j => abs_nonneg ((F i).valueAt x (P.row_abs i).dom j))
        (P.row_abs i).series)
    P.row_abs_le
    P.majorant_sum


end PointwiseFlattenable

/-! ## 3. Forward bridge for `seriesIntegrable` and `seriesSumRep_L1` -/

/-- Forward pointwise flattening for the `cellAt` representative used by
`seriesIntegrable`. -/
def seriesIntegrable_definedAt_of_pointwiseFlattenable
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).absConv.sum))
    {x : X}
    (P : PointwiseFlattenable (S := S) F x) :
    RepDefinedAt (S := S) (seriesIntegrable F hsum) x := by
  let hflatDom : (seriesIntegrable F hsum).MemAt x :=
    fun m => (P.row_abs (cellAt m).1).dom (cellAt m).2
  refine { dom := hflatDom, series := ?_ }
  change RSeq.SeriesSum
    (fun m => COF.abs ((F (cellAt m).1).valueAt x
      (P.row_abs (cellAt m).1).dom (cellAt m).2))
  exact cellAt_seriesSum
    (fun i j => abs_nonneg ((F i).valueAt x (P.row_abs i).dom j))
    (fun i => (P.row_abs i).series)
    P.rowAbsSum


set_option maxHeartbeats 800000 in
-- Universe elaboration for the two split-family fields exceeds the default limit.
/-- Pointwise data for the actual split used by `seriesSumRep_L1`.

The definition of `seriesSumRep_L1 F` is not a direct flattening of `F`; it is
the sum of a `G_m F` flattening and a `tail_m F` flattening.  The pointwise
bridge therefore asks for majorant data for those two source families. -/
structure SeriesSumRepL1PointwiseData
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    (x : X) : Type _ where
  g_part :
    PointwiseFlattenable (S := S) (G_m F) x
  tail_part :
    PointwiseFlattenable (S := S) (tail_m F) x


/-- Public forward bridge for `seriesSumRep_L1`: pointwise flattenability of
the two internal split families gives pointwise absolute convergence of the
final representative. -/
def seriesSumRep_L1_definedAt_of_pointwiseData
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    {x : X}
    (P : SeriesSumRepL1PointwiseData (S := S) F hsum x) :
    RepDefinedAt (S := S) (seriesSumRep_L1 F hsum) x := by
  unfold seriesSumRep_L1
  exact RepDefinedAt.add
    (seriesIntegrable_definedAt_of_pointwiseFlattenable
      (G_m F) (G_m_absConv_seriesSum F hsum) P.g_part)
    (seriesIntegrable_definedAt_of_pointwiseFlattenable
      (tail_m F) (tail_m_absConv_seriesSum F) P.tail_part)


/-! ## 4. Audit -/

structure Sec2PointwiseFlatteningAuditAfterG301 : Type where
  rep_defined_at_api_added : Nat
  pointwise_flattenable_record_added : Nat
  series_integrable_forward_bridge_added : Nat
  series_sum_rep_l1_forward_bridge_added : Nat
  prop210_side_witnesses_constructed_this_step : Nat
  clean_increment_representative_introduced_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_prop210_pointwise_data_problem : Nat

def sec2PointwiseFlatteningAuditAfterG301 :
    Sec2PointwiseFlatteningAuditAfterG301 where
  rep_defined_at_api_added := 2
  pointwise_flattenable_record_added := 1
  series_integrable_forward_bridge_added := 1
  series_sum_rep_l1_forward_bridge_added := 1
  prop210_side_witnesses_constructed_this_step := 0
  clean_increment_representative_introduced_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_prop210_pointwise_data_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G301PointwiseFlatteningPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g300 : Chapter4G300Def23SourceRepAdapterPackage S
  audit : BishopC.Sec2PointwiseFlatteningAuditAfterG301
  flattening_api_added_this_step : Nat
  prop210_side_witnesses_constructed_this_step : Nat
  remaining_prop210_pointwise_data_problem : Nat

def chapter4G301PointwiseFlatteningPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G301PointwiseFlatteningPackage S where
  g300 := chapter4G300Def23SourceRepAdapterPackage S
  audit := BishopC.sec2PointwiseFlatteningAuditAfterG301
  flattening_api_added_this_step := 1
  prop210_side_witnesses_constructed_this_step := 0
  remaining_prop210_pointwise_data_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G301. -/
def bishopRegularSeqChapter4PointwiseFlatteningProgressAfterG301 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G301: added the RepDefinedAt and PointwiseFlattenable public API, proved \
    the forward pointwise bridge for seriesIntegrable, and exposed the correct \
    split-data bridge for seriesSumRep_L1.  Proposition-2.10 still needs \
    actual pointwise majorant data for the G_m and tail_m split families."


end BishopCReal
