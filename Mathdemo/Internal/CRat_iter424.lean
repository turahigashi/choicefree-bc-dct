import Mathdemo.Internal.CRat_iter423
import Mathdemo.Internal.CRat_iter334

set_option linter.style.longLine false

/-!
# Stage A4: rep-carrying DCT frontier audit

This node keeps the route additive.  It records the exact constructive gaps in
the plain BishopSec4 theorem signature while preserving the proven source-data
endpoint from the no-limit-domination route.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- If the right summand is defined at every convergence point of the left
summand, non-negativity of `g - h` and of `h` gives non-negativity of `g`.

For the DCT domination hypothesis this extra domain bridge is exactly the point:
`RepNonneg (g.sub (fn 0).absVal)` only speaks where the subtraction
representative is defined. -/
noncomputable def repNonneg_left_of_sub_nonneg_and_right_nonneg_on_left_domain
    (g h : IntegrableRep S)
    (hsub_nonneg : RepNonneg (g.sub h))
    (h_nonneg : RepNonneg h)
    (h_right_at_left : forall {x : X}, RepDefinedAt (S := S) g x -> RepDefinedAt (S := S) h x) :
    RepNonneg g := by
  intro x hg_dom hg_abs hg_sum
  have hh_abs : RepDefinedAt (S := S) h x :=
    h_right_at_left (x := x) ⟨hg_dom, hg_abs⟩
  let hh_sum : RSeq.SeriesSum (fun n => h.valueAt x hh_abs.dom n) :=
    seriesSum_of_abs hh_abs.series
  let hsub_abs : Sec4RepAbsAt (g.sub h) x :=
    sec4_sub_absSeriesSum_fwd ⟨hg_dom, hg_abs⟩ ⟨hh_abs.dom, hh_abs.series⟩
  let hsub_sum : RSeq.SeriesSum
      (fun n => (g.sub h).valueAt x hsub_abs.fst n) :=
    add_seriesSum_value hg_dom (IntegrableRep.neg_memAt hh_abs.dom) hg_sum
      (neg_seriesSum_value hh_abs.dom hh_sum)
  have hsub_nn : Nonneg hsub_sum.sum :=
    hsub_nonneg x hsub_abs.fst hsub_abs.snd hsub_sum
  have hh_nn : Nonneg hh_sum.sum :=
    h_nonneg x hh_abs.dom hh_abs.series hh_sum
  have htotal : Nonneg (hsub_sum.sum + hh_sum.sum) := nonneg_add hsub_nn hh_nn
  have hEq : hsub_sum.sum + hh_sum.sum = hg_sum.sum := by
    change (hg_sum.sum + -hh_sum.sum) + hh_sum.sum = hg_sum.sum
    ring
  rw [hEq] at htotal
  exact htotal

/-- The DCT-specialized form of the preceding bridge.  The additional
`h_fn0_at_g` field is not present in the public DCT signature, so this is a
diagnostic lemma rather than a proof of that signature. -/
noncomputable def dct_g_nonneg_from_bound_if_fn0_absVal_defined_on_g_domain
    (fn : Nat -> IntegrableRep S) (g : IntegrableRep S)
    (h_bound : forall n, RepNonneg (g.sub (fn n).absVal))
    (h_fn0_at_g : forall {x : X}, RepDefinedAt (S := S) g x ->
      RepDefinedAt (S := S) (fn 0).absVal x) :
    RepNonneg g :=
  repNonneg_left_of_sub_nonneg_and_right_nonneg_on_left_domain
    (S := S) g (fn 0).absVal (h_bound 0) (repNonneg_absVal (fn 0)) h_fn0_at_g


end BishopC

namespace BishopCReal

open BishopC
open BishopRegularSeqChapter4.Theorem415Route

/-- Proven DCT endpoint once the existing no-limit-domination source-data record
has been supplied.  This is definitionally the same conclusion as the public
BishopSec4 DCT stub, but it is not the plain signature because the source-data
record still contains constructive witnesses. -/
noncomputable def thm_4_15_dominated_convergence_repCarrying_from_noLimitDom_source_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : IntSpaceRC Y R}
    (fn : Nat -> IntegrableRep S)
    (f g : IntegrableRep S)
    (D : Theorem415LocalPFunSourceDataNoLimitDomination fn f g) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  theorem415_abs_error_tendsto_from_noLimitDom_source_data (S := S) (fn := fn) (f := f) (g := g) D

structure StageA4RepCarryingDCTAudit : Type where
  g_nonneg_plain_h_bound_only_closed : Nat
  g_nonneg_domain_gap_recorded : Nat
  hconv_prop_to_type_bridge_closed : Nat
  hconv_prop_to_type_gap_recorded : Nat
  source_data_alias_closed : Nat
  plain_signature_emitted : Nat
  external_witness_selector_added : Nat

noncomputable def stageA4RepCarryingDCTAudit : StageA4RepCarryingDCTAudit where
  g_nonneg_plain_h_bound_only_closed := 0
  g_nonneg_domain_gap_recorded := 1
  hconv_prop_to_type_bridge_closed := 0
  hconv_prop_to_type_gap_recorded := 1
  source_data_alias_closed := 1
  plain_signature_emitted := 0
  external_witness_selector_added := 0


end BishopCReal
