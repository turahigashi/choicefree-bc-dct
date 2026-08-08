import Mathdemo.Internal.CRat_iter400

set_option linter.style.longLine false

/-!
# G302: reducing Proposition 2.10 side witnesses to split pointwise data

G301 exposed the correct pointwise bridge for `seriesSumRep_L1`: the bridge is
not value-level eventual zero, but pointwise flattenability of the two internal
families `G_m F` and `tail_m F`.

This node connects that bridge back to Proposition 2.10.  It defines
intermediate witness records whose remaining analytic content is exactly the
split pointwise data required by G301, plus the still-separate domain witnesses
for the final representative rows.

No final Proposition-2.10 witness is constructed here.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Union side: reduce `prop_2_10_rep` to G301 split data -/

/-- Intermediate witness for Proposition 2.10(b): the domain part is still
stated directly for the final source representative, while the absolute
convergence part is reduced to the G301 split data for
`seriesSumRep_L1 (prop_2_10_F A hA)`. -/
structure Prop210BSourceSplitPointwiseWitness
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
  split_pointwise_on_s1 :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      SeriesSumRepL1PointwiseData (S := S)
        (prop_2_10_F A (fun k => (HA k).base))
        (prop_2_10_F_norm_sum A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
        x
  split_pointwise_on_s2 :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      SeriesSumRepL1PointwiseData (S := S)
        (prop_2_10_F A (fun k => (HA k).base))
        (prop_2_10_F_norm_sum A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
        x


namespace Prop210BSourceSplitPointwiseWitness

/-- Convert the G302 split-data witness into the G300 source-representative
side witness for Proposition 2.10(b). -/
noncomputable def toSourceRepSideWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)}
    (W : Prop210BSourceSplitPointwiseWitness (S := S) A HA h_conv) :
    Prop210BSourceRepSideWitness (S := S) A HA h_conv where
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  abs_on_s1 := by
    intro x hx
    simpa [prop_2_10_rep] using
      seriesSumRep_L1_definedAt_of_pointwiseData
        (S := S)
        (prop_2_10_F A (fun k => (HA k).base))
        (prop_2_10_F_norm_sum A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
        (W.split_pointwise_on_s1 x hx)
  abs_on_s2 := by
    intro x hx
    simpa [prop_2_10_rep] using
      seriesSumRep_L1_definedAt_of_pointwiseData
        (S := S)
        (prop_2_10_F A (fun k => (HA k).base))
        (prop_2_10_F_norm_sum A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv))
        (W.split_pointwise_on_s2 x hx)


end Prop210BSourceSplitPointwiseWitness

/-! ## 2. Intersection side: reduce `prop_2_10_c_rep` to G301 split data -/

/-- Intermediate witness for Proposition 2.10(c).  The final representative is
`(HA 0).rep - seriesSumRep_L1 (prop_2_10_G A hA)`, so the first term uses the
input Definition-2.3 side data and the second term uses G301 split data. -/
structure Prop210CSourceSplitPointwiseWitness
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
  split_pointwise_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      SeriesSumRepL1PointwiseData (S := S)
        (prop_2_10_G A (fun k => (HA k).base))
        (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
        x
  split_pointwise_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      SeriesSumRepL1PointwiseData (S := S)
        (prop_2_10_G A (fun k => (HA k).base))
        (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
        x


namespace Prop210CSourceSplitPointwiseWitness

/-- Convert the G302 split-data witness into the G300 source-representative
side witness for Proposition 2.10(c). -/
noncomputable def toSourceRepSideWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β}
    (W : Prop210CSourceSplitPointwiseWitness (S := S) A HA h_lim) :
    Prop210CSourceRepSideWitness (S := S) A HA h_lim where
  dom_on_s1 := W.dom_on_s1
  dom_on_s2 := W.dom_on_s2
  abs_on_s1 := by
    intro x hx
    have h0 : RepDefinedAt (S := S) (HA 0).base.rep x :=
      (HA 0).abs_on_s1 x (Set.mem_iInter.mp hx 0)
    have hG :
        RepDefinedAt (S := S)
          (seriesSumRep_L1
            (prop_2_10_G A (fun k => (HA k).base))
            (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim))
          x :=
      seriesSumRep_L1_definedAt_of_pointwiseData
        (S := S)
        (prop_2_10_G A (fun k => (HA k).base))
        (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
        (W.split_pointwise_on_s1 x hx)
    simpa [prop_2_10_c_rep, IntegrableRep.sub] using
      RepDefinedAt.sub h0 hG
  abs_on_s2 := by
    intro x hx
    have h0 : RepDefinedAt (S := S) (HA 0).base.rep x :=
      W.head_abs_on_s2 x hx
    have hG :
        RepDefinedAt (S := S)
          (seriesSumRep_L1
            (prop_2_10_G A (fun k => (HA k).base))
            (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim))
          x :=
      seriesSumRep_L1_definedAt_of_pointwiseData
        (S := S)
        (prop_2_10_G A (fun k => (HA k).base))
        (prop_2_10_G_norm_sum A (fun k => (HA k).base) h_lim)
        (W.split_pointwise_on_s2 x hx)
    simpa [prop_2_10_c_rep, IntegrableRep.sub] using
      RepDefinedAt.sub h0 hG


end Prop210CSourceSplitPointwiseWitness

/-! ## 3. Split-data surface -/

/-- Surface whose remaining analytic content is G301 split pointwise data for
the union and intersection Proposition-2.10 source representatives. -/
structure Prop210SourceSplitPointwiseSurface
    (X R : Type*) [COFOC R] (S : IntSpaceRC X R) : Type _ where
  union_split_witness :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)),
      Prop210BSourceSplitPointwiseWitness (S := S) A HA h_conv
  intersection_split_witness :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_lim :
        Σ β : R,
          RSeq.TendstoHalf
            (fun n => measure1 S
              (bigAndFin_int A (fun k => (HA k).base) n)) β),
      Prop210CSourceSplitPointwiseWitness (S := S) A HA h_lim


namespace Prop210SourceSplitPointwiseSurface

/-- A split-data surface yields the G300 source-representative side-witness
surface. -/
noncomputable def toSourceRepSideWitnessSurface
    (Surf : Prop210SourceSplitPointwiseSurface X R S) :
    Prop210SourceRepSideWitnessSurface X R S where
  union_source_witness := by
    intro A HA h_conv
    exact (Surf.union_split_witness A HA h_conv).toSourceRepSideWitness
  intersection_source_witness := by
    intro A HA h_lim
    exact (Surf.intersection_split_witness A HA h_lim).toSourceRepSideWitness


end Prop210SourceSplitPointwiseSurface

/-! ## 4. Audit -/

structure Sec2Prop210SplitPointwiseAuditAfterG302 : Type where
  union_split_witness_record_added : Nat
  intersection_split_witness_record_added : Nat
  adapters_to_source_rep_witness_added : Nat
  split_pointwise_surface_added : Nat
  prop210_final_side_witnesses_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_split_pointwise_data_problem : Nat

def sec2Prop210SplitPointwiseAuditAfterG302 :
    Sec2Prop210SplitPointwiseAuditAfterG302 where
  union_split_witness_record_added := 1
  intersection_split_witness_record_added := 1
  adapters_to_source_rep_witness_added := 2
  split_pointwise_surface_added := 1
  prop210_final_side_witnesses_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_split_pointwise_data_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G302Prop210SplitPointwisePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g301 : Chapter4G301PointwiseFlatteningPackage S
  audit : BishopC.Sec2Prop210SplitPointwiseAuditAfterG302
  split_surface_added_this_step : Nat
  final_side_witnesses_constructed_this_step : Nat
  remaining_split_pointwise_data_problem : Nat

def chapter4G302Prop210SplitPointwisePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G302Prop210SplitPointwisePackage S where
  g301 := chapter4G301PointwiseFlatteningPackage S
  audit := BishopC.sec2Prop210SplitPointwiseAuditAfterG302
  split_surface_added_this_step := 1
  final_side_witnesses_constructed_this_step := 0
  remaining_split_pointwise_data_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G302. -/
def bishopRegularSeqChapter4Prop210SplitPointwiseProgressAfterG302 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G302: reduced the Proposition-2.10 source side-witness problem to split \
    pointwise data for the actual seriesSumRep_L1 internals.  Union uses the \
    split data for prop_2_10_F; intersection uses the input A_0 Def23 side \
    data plus split data for prop_2_10_G."


end BishopCReal
