import Mathdemo.Internal.CRat_iter395

set_option linter.style.longLine false

/-!
# G297: base Proposition-2.10 wrappers from Def23 input

G296 prepared strong Definition-2.3 data for the finite increment families.
The existing Proposition 2.10 constructors in Chapter 2 still return the older
`IntegrableSet1` API.  This node adds thin wrappers that accept
`IntegrableSet1WithDef23` hypotheses and pass their `.base` fields to the
existing countable union/intersection constructions.

This is intentionally a base-output bridge.  It does not claim a strong
`IntegrableSet1WithDef23` result for `BSet.bigOr A` or `BSet.bigAnd A`; that
would still require the countable-side domain and absolute-convergence
witnesses for the final representative.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Countable union base wrapper -/

/-- Limit package for the finite-union measure sequence from strong Def23
input, using the existing Chapter-2 construction on `.base`. -/
noncomputable def measure_limit_of_sumWithDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    Σ α : R,
      RSeq.TendstoHalf
        (fun n => measure1 S
          (bigOrFin_int A (fun k => (HA k).base) n)) α :=
  measure_limit_of_sum A (fun k => (HA k).base) h_conv


/-- Proposition 2.10(b), accepting strong Def23 hypotheses but returning the
existing base `IntegrableSet1` result. -/
noncomputable def prop_2_10_b_ofWithDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    IntegrableSet1 S (BSet.bigOr A) :=
  prop_2_10_b A (fun k => (HA k).base) h_conv


theorem prop_2_10_b_measure_ofWithDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_conv : RSeq.SeriesSum (fun k => measure1 S (HA k).base)) :
    Le (measure1 S (prop_2_10_b_ofWithDef23 (S := S) A HA h_conv))
      h_conv.sum := by
  exact prop_2_10_b_measure A (fun k => (HA k).base) h_conv


/-! ## 2. Countable intersection base wrapper -/

/-- Proposition 2.10(c), accepting strong Def23 hypotheses but returning the
existing base `IntegrableSet1` result. -/
noncomputable def prop_2_10_c_ofWithDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) :
    IntegrableSet1 S (BSet.bigAnd A) :=
  prop_2_10_c A (fun k => (HA k).base) h_lim


theorem prop_2_10_c_measure_ofWithDef23
    (A : Nat → BSet X)
    (HA : forall k : Nat, IntegrableSet1WithDef23 (S := S) (A k))
    (h_lim :
      Σ β : R,
        RSeq.TendstoHalf
          (fun n => measure1 S
            (bigAndFin_int A (fun k => (HA k).base) n)) β) :
    measure1 S (prop_2_10_c_ofWithDef23 (S := S) A HA h_lim) =
      h_lim.fst := by
  exact prop_2_10_c_measure A (fun k => (HA k).base) h_lim


/-! ## 3. Audit -/

structure Sec2Def23Prop210BaseWrapperAuditAfterG297 : Type where
  union_base_wrapper_added : Nat
  union_measure_wrapper_added : Nat
  intersection_base_wrapper_added : Nat
  intersection_measure_wrapper_added : Nat
  strong_countable_output_claimed : Nat
  countable_domain_abs_witnesses_constructed_this_step : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat

def sec2Def23Prop210BaseWrapperAuditAfterG297 :
    Sec2Def23Prop210BaseWrapperAuditAfterG297 where
  union_base_wrapper_added := 1
  union_measure_wrapper_added := 1
  intersection_base_wrapper_added := 1
  intersection_measure_wrapper_added := 1
  strong_countable_output_claimed := 0
  countable_domain_abs_witnesses_constructed_this_step := 0
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G297Def23Prop210BaseWrapperPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g296 : Chapter4G296Def23IncrementFamilyPackage S
  audit : BishopC.Sec2Def23Prop210BaseWrapperAuditAfterG297
  base_wrappers_added_this_step : Nat
  remaining_strong_countable_output_problem : Nat

def chapter4G297Def23Prop210BaseWrapperPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G297Def23Prop210BaseWrapperPackage S where
  g296 := chapter4G296Def23IncrementFamilyPackage S
  audit := BishopC.sec2Def23Prop210BaseWrapperAuditAfterG297
  base_wrappers_added_this_step := 4
  remaining_strong_countable_output_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G297. -/
def bishopRegularSeqChapter4Def23Prop210BaseWrapperProgressAfterG297 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G297: added thin Proposition-2.10 wrappers that consume strong Def23 \
    input hypotheses and return the existing base IntegrableSet1 countable \
    union/intersection results with their measure theorems.  The strong \
    countable-output API remains an explicit frontier."


end BishopCReal
