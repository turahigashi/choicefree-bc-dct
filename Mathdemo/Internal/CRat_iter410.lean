import Mathdemo.Internal.CRat_iter409

set_option linter.style.longLine false

/-!
# G311: clean-route bridge back to the source representatives

G310 closes the clean point-data route up to Definition-2.3 pointwise
definedness for the clean representatives.  The remaining source-level issue is
not a row-to-flat problem anymore: it is the bridge from the clean increment/drop
representatives back to the original telescoping representatives used by
Proposition 2.10.

This node isolates that bridge.  It does not identify the clean and source
representatives by fiat.  Instead it states the exact transport data needed to
convert the clean route into the existing `Prop210B/CSourceRepSideWitness`
surface.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Clean-to-source bridge records -/

/-- Transport data from the clean union representative to the exact source
representative used by Proposition 2.10(b).  The domain fields remain stated for
the source representative because `RepDefinedAt` only covers the absolute
series, not membership in every row domain. -/
structure Prop210BCleanToSourceBridge
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base))
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)) : Type _ where
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
  abs_on_s1_from_clean :
    forall x : X, x ∈ (BSet.bigOr A).S1 ->
      RepDefinedAt (S := S)
        (prop_2_10_rep_clean (S := S) Sel A HA clean_hsum) x ->
      RepDefinedAt (S := S)
        (prop_2_10_rep A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv)) x
  abs_on_s2_from_clean :
    forall x : X, x ∈ (BSet.bigOr A).S2 ->
      RepDefinedAt (S := S)
        (prop_2_10_rep_clean (S := S) Sel A HA clean_hsum) x ->
      RepDefinedAt (S := S)
        (prop_2_10_rep A (fun k => (HA k).base)
          (measure_limit_of_sumWithDef23 (S := S) A HA h_conv)) x


/-- Transport data from the clean intersection representative to the exact
source representative used by Proposition 2.10(c). -/
structure Prop210CCleanToSourceBridge
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β)
    (clean_hsum :
      RSeq.SeriesSum
        (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)) : Type _ where
  dom_on_s1 :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      forall m : Nat,
        x ∈ ((prop_2_10_c_rep A (fun k => (HA k).base) h_lim).fn m).dom
  dom_on_s2 :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      forall m : Nat,
        x ∈ ((prop_2_10_c_rep A (fun k => (HA k).base) h_lim).fn m).dom
  abs_on_s1_from_clean :
    forall x : X, x ∈ (BSet.bigAnd A).S1 ->
      RepDefinedAt (S := S)
        (prop_2_10_c_rep_clean (S := S) Sel A HA clean_hsum) x ->
      RepDefinedAt (S := S)
        (prop_2_10_c_rep A (fun k => (HA k).base) h_lim) x
  abs_on_s2_from_clean :
    forall x : X, x ∈ (BSet.bigAnd A).S2 ->
      RepDefinedAt (S := S)
        (prop_2_10_c_rep_clean (S := S) Sel A HA clean_hsum) x ->
      RepDefinedAt (S := S)
        (prop_2_10_c_rep A (fun k => (HA k).base) h_lim) x


/-! ## 2. Route witnesses from clean point data to source side data -/

structure Prop210BCleanRouteToSourceWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) : Type _ where
  clean_hsum :
    RSeq.SeriesSum
      (fun m => (prop_2_10_F_clean (S := S) Sel A HA m).normL1)
  point_data :
    Prop210BCleanPointDataWitness (S := S) Sel A HA
  bridge :
    Prop210BCleanToSourceBridge (S := S) Sel A HA h_conv clean_hsum


namespace Prop210BCleanRouteToSourceWitness

noncomputable def toSourceRepSideWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)}
    (W : Prop210BCleanRouteToSourceWitness (S := S) Sel A HA h_conv) :
    Prop210BSourceRepSideWitness (S := S) A HA h_conv where
  dom_on_s1 := W.bridge.dom_on_s1
  dom_on_s2 := W.bridge.dom_on_s2
  abs_on_s1 := by
    intro x hx
    exact (W.bridge.abs_on_s1_from_clean x hx
      ((W.point_data.toPointwiseMajorantWitness
        (hsum := W.clean_hsum)).definedAt_on_s1 x hx)).series
  abs_on_s2 := by
    intro x hx
    exact (W.bridge.abs_on_s2_from_clean x hx
      ((W.point_data.toPointwiseMajorantWitness
        (hsum := W.clean_hsum)).definedAt_on_s2 x hx)).series


end Prop210BCleanRouteToSourceWitness

structure Prop210CCleanRouteToSourceWitness
    (Sel : BSetBinarySideSelectorSurface X)
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) : Type _ where
  clean_hsum :
    RSeq.SeriesSum
      (fun m => (prop_2_10_G_clean (S := S) Sel A HA m).normL1)
  point_data :
    Prop210CCleanPointDataWitness (S := S) Sel A HA
  bridge :
    Prop210CCleanToSourceBridge (S := S) Sel A HA h_lim clean_hsum


namespace Prop210CCleanRouteToSourceWitness

noncomputable def toSourceRepSideWitness
    {Sel : BSetBinarySideSelectorSurface X}
    {A : Nat → BSet X}
    {HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k)}
    {h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β}
    (W : Prop210CCleanRouteToSourceWitness (S := S) Sel A HA h_lim) :
    Prop210CSourceRepSideWitness (S := S) A HA h_lim where
  dom_on_s1 := W.bridge.dom_on_s1
  dom_on_s2 := W.bridge.dom_on_s2
  abs_on_s1 := by
    intro x hx
    exact (W.bridge.abs_on_s1_from_clean x hx
      ((W.point_data.toPointwiseMajorantWitness
        (hsum := W.clean_hsum)).definedAt_on_s1 x hx)).series
  abs_on_s2 := by
    intro x hx
    exact (W.bridge.abs_on_s2_from_clean x hx
      ((W.point_data.toPointwiseMajorantWitness
        (hsum := W.clean_hsum)).definedAt_on_s2 x hx)).series


end Prop210CCleanRouteToSourceWitness

/-! ## 3. Combined surface -/

structure Prop210CleanRouteToSourceSurface
    (Sel : BSetBinarySideSelectorSurface X) : Type _ where
  union_route :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)),
      Prop210BCleanRouteToSourceWitness (S := S) Sel A HA h_conv
  intersection_route :
    forall (A : Nat → BSet X)
      (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
      (h_lim :
        Σ β : R,
          RSeq.TendstoHalf
            (fun n => measure1 S
              (bigAndFin_int A (fun k => (HA k).base) n)) β),
      Prop210CCleanRouteToSourceWitness (S := S) Sel A HA h_lim


namespace Prop210CleanRouteToSourceSurface

noncomputable def toSourceRepSideWitnessSurface
    {Sel : BSetBinarySideSelectorSurface X}
    (Surf : Prop210CleanRouteToSourceSurface (S := S) Sel) :
    Prop210SourceRepSideWitnessSurface X R S where
  union_source_witness := by
    intro A HA h_conv
    exact (Surf.union_route A HA h_conv).toSourceRepSideWitness
  intersection_source_witness := by
    intro A HA h_lim
    exact (Surf.intersection_route A HA h_lim).toSourceRepSideWitness


end Prop210CleanRouteToSourceSurface

/-! ## 4. Audit -/

structure Sec2CleanToSourceBridgeAuditAfterG311 : Type where
  clean_to_source_bridge_records_added : Nat
  clean_route_witness_records_added : Nat
  clean_route_to_source_adapters_added : Nat
  clean_route_surface_added : Nat
  source_side_surface_adapter_added : Nat
  clean_pointwise_majorant_route_reused : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  remaining_clean_original_equivalence_problem : Nat

def sec2CleanToSourceBridgeAuditAfterG311 :
    Sec2CleanToSourceBridgeAuditAfterG311 where
  clean_to_source_bridge_records_added := 2
  clean_route_witness_records_added := 2
  clean_route_to_source_adapters_added := 2
  clean_route_surface_added := 1
  source_side_surface_adapter_added := 1
  clean_pointwise_majorant_route_reused := 1
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  clean_original_rep_equivalence_proved_this_step := 0
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G311CleanToSourceBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g310 : Chapter4G310CleanPointDataAssemblyPackage S
  audit : BishopC.Sec2CleanToSourceBridgeAuditAfterG311
  clean_route_to_source_surface_available : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G311CleanToSourceBridgePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G311CleanToSourceBridgePackage S where
  g310 := chapter4G310CleanPointDataAssemblyPackage S
  audit := BishopC.sec2CleanToSourceBridgeAuditAfterG311
  clean_route_to_source_surface_available := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G311. -/
def bishopRegularSeqChapter4CleanToSourceBridgeProgressAfterG311 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G311: isolated the clean-to-source representative bridge.  Clean point \
    data plus clean row majorants now convert to the existing source-side \
    witness surface exactly when domain transport and clean/original \
    representative absolute-convergence transport are supplied.  Remaining: \
    prove that bridge from the source Proposition-2.10 telescoping \
    construction."


end BishopCReal
