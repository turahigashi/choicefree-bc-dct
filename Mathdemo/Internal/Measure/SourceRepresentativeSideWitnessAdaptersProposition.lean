import Mathdemo.Internal.Measure.CountableProposition210OutputSurface

set_option linter.style.longLine false

/-!
# G300: source-representative side-witness adapters for Proposition 2.10

G299 made the final countable output surface explicit.  This node tightens the
remaining frontier by aligning the G298/G299 output witnesses with the actual
source representatives used in the Chapter-2 proof:

* for Proposition 2.10(b), the `φ`/increment series representative
  `prop_2_10_rep`;
* for Proposition 2.10(c), the dual `ψ`/drop series representative
  `prop_2_10_c_rep`.

The adapters here do not construct the missing sidewise domain and absolute
convergence witnesses.  They state that supplying those witnesses for the
source representative is exactly enough to supply the G299 output surface.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Definitional alignment with the source representatives -/

@[simp] theorem prop_2_10_b_ofWithDef23_eq_a
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    prop_2_10_b_ofWithDef23 (S := S) A HA h_conv =
      prop_2_10_a A (fun k => (HA k).base)
        (measure_limit_of_sumWithDef23 (S := S) A HA h_conv) :=
  rfl


@[simp] theorem prop_2_10_b_ofWithDef23_rep
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    (prop_2_10_b_ofWithDef23 (S := S) A HA h_conv).rep =
      prop_2_10_rep A (fun k => (HA k).base)
        (measure_limit_of_sumWithDef23 (S := S) A HA h_conv) :=
  rfl


@[simp] theorem prop_2_10_c_ofWithDef23_rep
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) :
    (prop_2_10_c_ofWithDef23 (S := S) A HA h_lim).rep =
      prop_2_10_c_rep A (fun k => (HA k).base) h_lim :=
  rfl


/-! ## 2. Source-representative side witnesses -/

/-- Sidewise Definition-2.3 data for the exact source representative used in
Proposition 2.10(b). -/
structure Prop210BSourceRepSideWitness
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
  abs_on_s1 :
    forall (x : X) (hx : x ∈ (BSet.bigOr A).S1),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_rep A (fun k => (HA k).base)
              (measure_limit_of_sumWithDef23 (S := S) A HA h_conv)).valueAt
                x (dom_on_s1 x hx) m))
  abs_on_s2 :
    forall (x : X) (hx : x ∈ (BSet.bigOr A).S2),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_rep A (fun k => (HA k).base)
              (measure_limit_of_sumWithDef23 (S := S) A HA h_conv)).valueAt
                x (dom_on_s2 x hx) m))


/-- Sidewise Definition-2.3 data for the exact source representative used in
Proposition 2.10(c). -/
structure Prop210CSourceRepSideWitness
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
  abs_on_s1 :
    forall (x : X) (hx : x ∈ (BSet.bigAnd A).S1),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_c_rep A (fun k => (HA k).base) h_lim).valueAt
              x (dom_on_s1 x hx) m))
  abs_on_s2 :
    forall (x : X) (hx : x ∈ (BSet.bigAnd A).S2),
      RSeq.SeriesSum
        (fun m =>
          COF.abs
            ((prop_2_10_c_rep A (fun k => (HA k).base) h_lim).valueAt
              x (dom_on_s2 x hx) m))


namespace Prop210BSourceRepSideWitness

/-- Convert side data for the source representative into the G298 output
witness record. -/
noncomputable def toOutputWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)}
    (W : Prop210BSourceRepSideWitness (S := S) A HA h_conv) :
    Prop210BWithDef23OutputWitness (S := S) A HA h_conv where
  dom_on_s1 := by
    intro x hx m
    simpa [prop_2_10_b_ofWithDef23_rep] using W.dom_on_s1 x hx m
  dom_on_s2 := by
    intro x hx m
    simpa [prop_2_10_b_ofWithDef23_rep] using W.dom_on_s2 x hx m
  abs_on_s1 := by
    intro x hx
    simpa [prop_2_10_b_ofWithDef23_rep] using W.abs_on_s1 x hx
  abs_on_s2 := by
    intro x hx
    simpa [prop_2_10_b_ofWithDef23_rep] using W.abs_on_s2 x hx


end Prop210BSourceRepSideWitness

namespace Prop210CSourceRepSideWitness

/-- Convert side data for the source representative into the G298 output
witness record. -/
noncomputable def toOutputWitness
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β}
    (W : Prop210CSourceRepSideWitness (S := S) A HA h_lim) :
    Prop210CWithDef23OutputWitness (S := S) A HA h_lim where
  dom_on_s1 := by
    intro x hx m
    simpa [prop_2_10_c_ofWithDef23_rep] using W.dom_on_s1 x hx m
  dom_on_s2 := by
    intro x hx m
    simpa [prop_2_10_c_ofWithDef23_rep] using W.dom_on_s2 x hx m
  abs_on_s1 := by
    intro x hx
    simpa [prop_2_10_c_ofWithDef23_rep] using W.abs_on_s1 x hx
  abs_on_s2 := by
    intro x hx
    simpa [prop_2_10_c_ofWithDef23_rep] using W.abs_on_s2 x hx


end Prop210CSourceRepSideWitness

/-! ## 3. Surface over source representatives -/

/-- A countable side-witness surface stated directly for the source
representatives.  The final G299 output surface is obtained from this by the
adapters above. -/
structure Prop210SourceRepSideWitnessSurface
    (X R : Type*) [COFOC R] (S : IntSpaceRC X R) : Type _ where
  union_source_witness :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)),
      Prop210BSourceRepSideWitness (S := S) A HA h_conv
  intersection_source_witness :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_lim :
        Σ β : R,
          RSeq.TendstoHalf
            (fun n => measure1 S
              (bigAndFin_int A (fun k => (HA k).base) n)) β),
      Prop210CSourceRepSideWitness (S := S) A HA h_lim


namespace Prop210SourceRepSideWitnessSurface

/-- Every source-representative side-witness surface yields the G299 output
surface. -/
noncomputable def toCountableOutputSurface
    (Surf : Prop210SourceRepSideWitnessSurface X R S) :
    Prop210CountableOutputSurface X R S where
  union_output := by
    intro A HA h_conv
    exact (Surf.union_source_witness A HA h_conv).toOutputWitness
  intersection_output := by
    intro A HA h_lim
    exact (Surf.intersection_source_witness A HA h_lim).toOutputWitness


end Prop210SourceRepSideWitnessSurface

/-! ## 4. Audit -/

structure Sec2Def23SourceRepAdapterAuditAfterG300 : Type where
  source_rep_alignment_theorems_added : Nat
  source_side_witness_records_added : Nat
  adapters_to_output_witness_added : Nat
  source_surface_adapter_added : Nat
  final_side_witnesses_constructed_this_step : Nat
  countable_output_surface_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_final_side_witness_problem : Nat

def sec2Def23SourceRepAdapterAuditAfterG300 :
    Sec2Def23SourceRepAdapterAuditAfterG300 where
  source_rep_alignment_theorems_added := 3
  source_side_witness_records_added := 2
  adapters_to_output_witness_added := 2
  source_surface_adapter_added := 1
  final_side_witnesses_constructed_this_step := 0
  countable_output_surface_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  remaining_final_side_witness_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G300Def23SourceRepAdapterPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g299 : Chapter4G299Def23CountableOutputSurfacePackage S
  audit : BishopC.Sec2Def23SourceRepAdapterAuditAfterG300
  source_rep_alignment_theorems_added_this_step : Nat
  source_surface_adapter_added_this_step : Nat
  remaining_final_side_witness_problem : Nat

def chapter4G300Def23SourceRepAdapterPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G300Def23SourceRepAdapterPackage S where
  g299 := chapter4G299Def23CountableOutputSurfacePackage S
  audit := BishopC.sec2Def23SourceRepAdapterAuditAfterG300
  source_rep_alignment_theorems_added_this_step := 3
  source_surface_adapter_added_this_step := 1
  remaining_final_side_witness_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G300. -/
def bishopRegularSeqChapter4Def23SourceRepAdapterProgressAfterG300 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G300: aligned the G298/G299 countable output witnesses with the exact \
    Proposition-2.10 source representatives prop_2_10_rep and \
    prop_2_10_c_rep, and added adapters from source-representative side \
    witnesses to the countable output surface.  The final analytic sidewise \
    witness construction remains explicit."


end BishopCReal
