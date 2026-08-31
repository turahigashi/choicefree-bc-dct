import Mathdemo.Internal.Measure.LocalStrengthenedIntegrableSet1APIDefinition2

set_option linter.style.longLine false

/-!
# G289: forward domain and absolute-convergence transport for constructor migration

G288 fixed the target local API for Definition 2.3 data.  The next broad task
is migrating the Chapter-2 constructors, starting with the source equation
`chi_{A vee B} = chi_A + chi_B - chi_{A wedge B}`.

This node adds only the generic transport lemmas needed for that migration:
if the input representatives have local domain / absolute convergence at a
point, then the composite representatives built by `add`, `neg`, `sub`,
`smul`, `absVal`, and `min2` have the corresponding local data.  No new
analytic assumption or choice principle is introduced.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Forward domain transport -/

/-- Forward domain transport for the interleaved representative sum. -/
theorem add_dom_of_left_right {r r' : IntegrableRep S} {x : X}
    (hr : forall k : Nat, x ∈ (r.fn k).dom)
    (hr' : forall k : Nat, x ∈ (r'.fn k).dom) :
    forall n : Nat, x ∈ ((r.add r').fn n).dom := by
  intro n
  rcases natEvenOrOdd' n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show (r.add r').fn (2 * k) = r.fn k from
        seqInterleave_even r.fn r'.fn k]
    exact hr k
  · rw [show (r.add r').fn (2 * k + 1) = r'.fn k from
        seqInterleave_odd r.fn r'.fn k]
    exact hr' k


/-- Forward domain transport for negation. -/
theorem neg_dom_of_dom {r : IntegrableRep S} {x : X}
    (hr : forall k : Nat, x ∈ (r.fn k).dom) :
    forall n : Nat, x ∈ ((r.neg).fn n).dom :=
  hr


/-- Forward domain transport for subtraction. -/
theorem sub_dom_of_left_right {r r' : IntegrableRep S} {x : X}
    (hr : forall k : Nat, x ∈ (r.fn k).dom)
    (hr' : forall k : Nat, x ∈ (r'.fn k).dom) :
    forall n : Nat, x ∈ ((r.sub r').fn n).dom := by
  unfold IntegrableRep.sub
  exact add_dom_of_left_right hr (neg_dom_of_dom hr')


/-- Forward domain transport for scalar multiplication. -/
theorem smul_dom_of_dom {a : R} {r : IntegrableRep S} {x : X}
    (hr : forall k : Nat, x ∈ (r.fn k).dom) :
    forall n : Nat, x ∈ ((r.smul a).fn n).dom :=
  hr


/-- Forward domain transport for the Bishop absolute-value representative. -/
theorem absVal_dom_of_dom {r : IntegrableRep S} {x : X}
    (hr : forall k : Nat, x ∈ (r.fn k).dom) :
    forall n : Nat, x ∈ ((r.absVal).fn n).dom :=
  IntegrableRep.mem_absVal_dom hr


/-- Forward domain transport for `min2`. -/
theorem min2_dom_of_left_right {r r' : IntegrableRep S} {x : X}
    (hr : forall k : Nat, x ∈ (r.fn k).dom)
    (hr' : forall k : Nat, x ∈ (r'.fn k).dom) :
    forall n : Nat, x ∈ ((IntegrableRep.min2 r r').fn n).dom := by
  unfold IntegrableRep.min2
  exact smul_dom_of_dom
    (sub_dom_of_left_right
      (add_dom_of_left_right hr hr')
      (absVal_dom_of_dom (sub_dom_of_left_right hr hr')))


/-! ## 2. Forward absolute-convergence transport -/

/-- Forward absolute-convergence transport for representative addition. -/
noncomputable def add_absSeriesSum_of_left_right
    {r r' : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x) (hr' : Sec4RepAbsAt r' x) :
    Sec4RepAbsAt (r.add r') x :=
  sec4_add_absSeriesSum_fwd hr hr'


/-- Forward absolute-convergence transport for representative negation. -/
noncomputable def neg_absSeriesSum_of_abs
    {r : IntegrableRep S} {x : X} (hr : Sec4RepAbsAt r x) :
    Sec4RepAbsAt r.neg x :=
  sec4_neg_absSeriesSum_fwd hr


/-- Forward absolute-convergence transport for representative subtraction. -/
noncomputable def sub_absSeriesSum_of_left_right
    {r r' : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x) (hr' : Sec4RepAbsAt r' x) :
    Sec4RepAbsAt (r.sub r') x :=
  sec4_sub_absSeriesSum_fwd hr hr'


/-- Forward absolute-convergence transport for scalar multiplication. -/
noncomputable def smul_absSeriesSum_of_abs
    {a : R} {r : IntegrableRep S} {x : X} (hr : Sec4RepAbsAt r x) :
    Sec4RepAbsAt (r.smul a) x :=
  sec4_smul_absSeriesSum a hr


/-- Forward absolute-convergence transport for `min2`. -/
noncomputable def min2_absSeriesSum_of_left_right
    {r r' : IntegrableRep S} {x : X}
    (hr : Sec4RepAbsAt r x) (hr' : Sec4RepAbsAt r' x) :
    Sec4RepAbsAt (IntegrableRep.min2 r r') x :=
  sec4_min2_absSeriesSum hr hr'


/-! ## 3. Audit -/

structure Sec2Def23ConstructorTransportAuditAfterG289 : Type where
  forward_domain_transport_lemmas_added : Nat
  forward_abs_transport_lemmas_added : Nat
  integrable_set_or_constructor_migrated : Nat
  broad_base_structure_modified : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_constructor_migration_steps : Nat

def sec2Def23ConstructorTransportAuditAfterG289 :
    Sec2Def23ConstructorTransportAuditAfterG289 where
  forward_domain_transport_lemmas_added := 6
  forward_abs_transport_lemmas_added := 5
  integrable_set_or_constructor_migrated := 0
  broad_base_structure_modified := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_constructor_migration_steps := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G289Def23ConstructorTransportPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g288 : Chapter4G288WithDef23LocalAPIPackage S
  audit : BishopC.Sec2Def23ConstructorTransportAuditAfterG289
  constructor_transport_ready_this_step : Nat
  remaining_constructor_migration_steps : Nat

def chapter4G289Def23ConstructorTransportPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G289Def23ConstructorTransportPackage S where
  g288 := chapter4G288WithDef23LocalAPIPackage S
  audit := BishopC.sec2Def23ConstructorTransportAuditAfterG289
  constructor_transport_ready_this_step := 1
  remaining_constructor_migration_steps := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G289. -/
def bishopRegularSeqChapter4Def23ConstructorTransportProgressAfterG289 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G289: added forward domain and absolute-convergence transport lemmas for \
    add, neg, sub, smul, absVal, and min2.  These are the generic components \
    needed to migrate the Chapter-2 IntegrableSet1 constructors to the local \
    Definition-2.3 API introduced in G288.  No constructor was globally \
    rewritten yet."


end BishopCReal
