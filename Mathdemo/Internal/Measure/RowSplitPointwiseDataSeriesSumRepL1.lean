import Mathdemo.Internal.Measure.ReducingProposition210SideWitnesses

set_option linter.style.longLine false

/-!
# G303: row-to-split pointwise data for `seriesSumRep_L1`

G302 reduced Proposition 2.10 to pointwise data for the two split families
inside `seriesSumRep_L1`: `G_m F` and `tail_m F`.

This node adds the next layer of bookkeeping.  It proves that:

* `ofL` representatives are pointwise defined everywhere;
* `tailFrom` representatives are pointwise defined wherever the original row
  is pointwise defined;
* therefore, to build G302 split data, it is enough to provide rowwise
  pointwise data for the original `F i` plus summable majorants for the
  absolute row sums of the `G_m` and `tail_m` split families.

This still does not construct the majorants for Proposition 2.10.  It only
removes one layer of representative plumbing from the remaining problem.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise definedness for the split-row constructors -/

namespace RepDefinedAt

/-- A single-term `ofL` representative is pointwise defined on the domain of
its source partial function. -/
def ofL {g : BFunR X R} (hg : g ∈ S.L) {x : X} (hx : x ∈ g.dom) :
    RepDefinedAt (S := S) (IntegrableRep.ofL hg) x := by
  let hdom : (IntegrableRep.ofL hg).MemAt x :=
    IntegrableRep.ofL_memAt hg hx
  refine ⟨hdom, seriesSum_congr (fun n => ?_)
    (seriesSum_single (COF.abs (g.toFun x hx)))⟩
  by_cases hn : n = 0
  · subst hn
    rfl
  · simp only [IntegrableRep.valueAt, IntegrableRep.ofL, hn, if_false,
      BFunR.smul, zero_mul, COFO.abs_zero]


/-- A tail representative is pointwise defined wherever the original
representative is pointwise defined. -/
def tailFrom {r : IntegrableRep S} (p : Nat) {x : X}
    (hr : RepDefinedAt (S := S) r x) :
    RepDefinedAt (S := S) (r.tailFrom p) x := by
  let hdom : (r.tailFrom p).MemAt x := r.tailFrom_memAt p hr.dom
  refine ⟨hdom, ?_⟩
  simpa only [IntegrableRep.tailFrom, IntegrableRep.valueAt] using
    (seriesSum_tail hr.series p)


/-- The `G_m` row of the `seriesSumRep_L1` split is an `ofL` representative,
so it is pointwise defined everywhere. -/
def Gm (F : Nat → IntegrableRep S) (i : Nat) (x : X)
    (hrow : RepDefinedAt (S := S) (F i) x) :
    RepDefinedAt (S := S) (G_m F i) x :=
  ofL (S := S) (psi_m_mem F i)
    (BFunR.seqSum_mem (F i).fn x hrow.dom (Nm F i))


/-- The `tail_m` row of the `seriesSumRep_L1` split is pointwise defined
wherever the original row is pointwise defined. -/
def tailm (F : Nat → IntegrableRep S) (i : Nat) {x : X}
    (hrow : RepDefinedAt (S := S) (F i) x) :
    RepDefinedAt (S := S) (tail_m F i) x :=
  tailFrom (S := S) (Nm F i) hrow


end RepDefinedAt

/-! ## 2. Majorants for the split families -/

/-- Data sufficient to build the G301 `SeriesSumRepL1PointwiseData` from
rowwise pointwise data for the original family `F`.

The fields deliberately keep the `G_m` and `tail_m` majorants separate, because
their eventual Proposition-2.10 proofs have different mathematical sources:
`G_m` is a finite-prefix `ofL` row, while `tail_m` is a tail of the original row.
-/
structure SeriesSumRepL1SplitMajorants
    (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).normL1))
    (x : X) : Type _ where
  row_abs :
    forall i : Nat, RepDefinedAt (S := S) (F i) x
  g_majorant : Nat → R
  g_majorant_sum : RSeq.SeriesSum g_majorant
  g_row_abs_le :
    forall i : Nat,
      Le ((RepDefinedAt.Gm (S := S) F i x (row_abs i)).sum)
        (g_majorant i)
  tail_majorant : Nat → R
  tail_majorant_sum : RSeq.SeriesSum tail_majorant
  tail_row_abs_le :
    forall i : Nat,
      Le ((RepDefinedAt.tailm (S := S) F i (row_abs i)).sum)
        (tail_majorant i)


namespace SeriesSumRepL1SplitMajorants

/-- Convert split majorant data into the G301 pointwise data expected by
`seriesSumRep_L1_definedAt_of_pointwiseData`. -/
def toPointwiseData
    {F : Nat → IntegrableRep S}
    {hsum : RSeq.SeriesSum (fun m => (F m).normL1)}
    {x : X}
    (M : SeriesSumRepL1SplitMajorants (S := S) F hsum x) :
    SeriesSumRepL1PointwiseData (S := S) F hsum x where
  g_part :=
    { row_abs := fun i => RepDefinedAt.Gm (S := S) F i x (M.row_abs i)
      majorant := M.g_majorant
      majorant_sum := M.g_majorant_sum
      row_abs_le := M.g_row_abs_le }
  tail_part :=
    { row_abs := fun i => RepDefinedAt.tailm (S := S) F i (M.row_abs i)
      majorant := M.tail_majorant
      majorant_sum := M.tail_majorant_sum
      row_abs_le := M.tail_row_abs_le }


end SeriesSumRepL1SplitMajorants

/-! ## 3. Proposition-2.10 majorant-level witness records -/

/-- Proposition 2.10(b) witness reduced from G302 split pointwise data to
split majorants for `prop_2_10_F`. -/
structure Prop210BSourceSplitMajorantWitness
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
  split_majorants_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      SeriesSumRepL1SplitMajorants (S := S)
        (prop_2_10_F A (fun k => (HA k).base))
        (prop_2_10_F_norm_sum A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
        x
  split_majorants_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      SeriesSumRepL1SplitMajorants (S := S)
        (prop_2_10_F A (fun k => (HA k).base))
        (prop_2_10_F_norm_sum A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
        x


namespace Prop210BSourceSplitMajorantWitness

noncomputable def toSplitPointwiseWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)}
    (W : Prop210BSourceSplitMajorantWitness (S := S) A HA h_conv) :
    Prop210BSourceSplitPointwiseWitness (S := S) A HA h_conv where
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  split_pointwise_on_s1 := by
    intro x hx
    exact (W.split_majorants_on_s1 x hx).toPointwiseData
  split_pointwise_on_s2 := by
    intro x hx
    exact (W.split_majorants_on_s2 x hx).toPointwiseData


end Prop210BSourceSplitMajorantWitness

/-- Proposition 2.10(c) witness reduced from G302 split pointwise data to
split majorants for `prop_2_10_G`. -/
structure Prop210CSourceSplitMajorantWitness
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
  split_majorants_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      SeriesSumRepL1SplitMajorants (S := S)
        (prop_2_10_G A (fun k => (HA k).base))
        (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
        x
  split_majorants_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      SeriesSumRepL1SplitMajorants (S := S)
        (prop_2_10_G A (fun k => (HA k).base))
        (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
        x


namespace Prop210CSourceSplitMajorantWitness

noncomputable def toSplitPointwiseWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β}
    (W : Prop210CSourceSplitMajorantWitness (S := S) A HA h_lim) :
    Prop210CSourceSplitPointwiseWitness (S := S) A HA h_lim where
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  head_abs_on_s2 := W.head_abs_on_s2
  split_pointwise_on_s1 := by
    intro x hx
    exact (W.split_majorants_on_s1 x hx).toPointwiseData
  split_pointwise_on_s2 := by
    intro x hx
    exact (W.split_majorants_on_s2 x hx).toPointwiseData


end Prop210CSourceSplitMajorantWitness

/-! ## 4. Audit -/

structure Sec2SplitRowDataAuditAfterG303 : Type where
  ofL_defined_at_added : Nat
  tail_from_defined_at_added : Nat
  split_majorant_record_added : Nat
  prop210_majorant_witness_records_added : Nat
  final_prop210_witnesses_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_majorant_construction_problem : Nat

def sec2SplitRowDataAuditAfterG303 :
    Sec2SplitRowDataAuditAfterG303 where
  ofL_defined_at_added := 1
  tail_from_defined_at_added := 1
  split_majorant_record_added := 1
  prop210_majorant_witness_records_added := 2
  final_prop210_witnesses_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_majorant_construction_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G303SplitRowDataPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g302 : Chapter4G302Prop210SplitPointwisePackage S
  audit : BishopC.Sec2SplitRowDataAuditAfterG303
  split_row_data_api_added_this_step : Nat
  final_prop210_witnesses_constructed_this_step : Nat
  remaining_majorant_construction_problem : Nat

def chapter4G303SplitRowDataPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G303SplitRowDataPackage S where
  g302 := chapter4G302Prop210SplitPointwisePackage S
  audit := BishopC.sec2SplitRowDataAuditAfterG303
  split_row_data_api_added_this_step := 1
  final_prop210_witnesses_constructed_this_step := 0
  remaining_majorant_construction_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G303. -/
def bishopRegularSeqChapter4SplitRowDataProgressAfterG303 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G303: proved pointwise definedness for ofL and tailFrom split rows, and \
    reduced Proposition-2.10 split pointwise data to original row data plus \
    explicit summable majorants for the G_m and tail_m row absolute sums."


end BishopCReal
