import Mathdemo.Internal.Measure.RepCarryingDCTFrontierAudit
import Mathdemo.Internal.Measure.Section2CleanProp210
import Mathdemo.Internal.Real.Theorem415SeparateLimitDomination

set_option linter.style.longLine false

/-!
# Stage A5: rep-carrying DCT wrapper and field audit

This node is additive.  It keeps the proven no-limit-domination endpoint from
iter334/iter424, but exposes the remaining source data explicitly instead of
extracting witnesses from Prop-valued convergence.
-/

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqChapter4
namespace Theorem415Route

noncomputable def theorem415_localPFun_source_data_from_repCarrying_witnesses
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S)
    (h_bound : forall n, BishopC.RepNonneg (g.sub (fn n).absVal))
    (h_g_nonneg : BishopC.RepNonneg g)
    (h_domain : BishopC.Sec4GeneralIBDomainResidualProvider (S := S))
    (h_pfun :
      BishopC.Lemma415PFunConvergeData (S := S)
        (fun n => BishopC.IntegrableRep.toPFunR (fn n))
        (BishopC.IntegrableRep.toPFunR f))
    (hrep_fn : forall n,
      BishopC.Lemma414RepresentsPFunR (S := S) (fn n)
        (BishopC.IntegrableRep.toPFunR (fn n)))
    (hrep_f :
      BishopC.Lemma414RepresentsPFunR (S := S) f
        (BishopC.IntegrableRep.toPFunR f)) :
    Theorem415LocalPFunSourceDataNoLimitDomination fn f g where
  g_nonneg := h_g_nonneg
  dominated_fn := h_bound
  domainResidualProvider := h_domain
  pfnsrc := fun n => BishopC.IntegrableRep.toPFunR (fn n)
  pf := BishopC.IntegrableRep.toPFunR f
  pfun_converges := h_pfun
  represents_fn := hrep_fn
  represents_limit := hrep_f

noncomputable def thm_4_15_dominated_convergence_repCarrying
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S)
    (h_bound : forall n, BishopC.RepNonneg (g.sub (fn n).absVal))
    (h_g_nonneg : BishopC.RepNonneg g)
    (h_domain : BishopC.Sec4GeneralIBDomainResidualProvider (S := S))
    (h_pfun :
      BishopC.Lemma415PFunConvergeData (S := S)
        (fun n => BishopC.IntegrableRep.toPFunR (fn n))
        (BishopC.IntegrableRep.toPFunR f))
    (hrep_fn : forall n,
      BishopC.Lemma414RepresentsPFunR (S := S) (fn n)
        (BishopC.IntegrableRep.toPFunR (fn n)))
    (hrep_f :
      BishopC.Lemma414RepresentsPFunR (S := S) f
        (BishopC.IntegrableRep.toPFunR f)) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  theorem415_abs_error_tendsto_from_noLimitDom_source_data
    (S := S)
    (theorem415_localPFun_source_data_from_repCarrying_witnesses
      (S := S) fn f g h_bound h_g_nonneg h_domain h_pfun hrep_fn hrep_f)

noncomputable def thm_4_15_dominated_convergence_repCarrying_if_fn0_absVal_defined_on_g_domain
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f g : BishopC.IntegrableRep S)
    (h_bound : forall n, BishopC.RepNonneg (g.sub (fn n).absVal))
    (h_fn0_at_g : forall {x : Y}, BishopC.RepDefinedAt (S := S) g x ->
      BishopC.RepDefinedAt (S := S) (fn 0).absVal x)
    (h_domain : BishopC.Sec4GeneralIBDomainResidualProvider (S := S))
    (h_pfun :
      BishopC.Lemma415PFunConvergeData (S := S)
        (fun n => BishopC.IntegrableRep.toPFunR (fn n))
        (BishopC.IntegrableRep.toPFunR f))
    (hrep_fn : forall n,
      BishopC.Lemma414RepresentsPFunR (S := S) (fn n)
        (BishopC.IntegrableRep.toPFunR (fn n)))
    (hrep_f :
      BishopC.Lemma414RepresentsPFunR (S := S) f
        (BishopC.IntegrableRep.toPFunR f)) :
    RSeq.TendstoHalf (fun n => ((fn n).sub f).absVal.integral) 0 :=
  thm_4_15_dominated_convergence_repCarrying
    (S := S) fn f g h_bound
    (BishopC.dct_g_nonneg_from_bound_if_fn0_absVal_defined_on_g_domain
      (S := S) fn g h_bound h_fn0_at_g)
    h_domain h_pfun hrep_fn hrep_f

structure StageA5RepCarryingDCTAudit : Type where
  dominated_fn_from_bound_closed : Nat
  pfun_converges_carried_as_type_data : Nat
  represents_self_toPFunR_closed : Nat
  represents_self_toPFunR_blocked_by_toPFunR_head_value : Nat
  domainResidualProvider_from_sec2_clean_rows_closed : Nat
  domainResidualProvider_needs_charDomain_and_residual_fields : Nat
  g_nonneg_from_bound_closed_without_domain_bridge : Nat
  g_nonneg_from_bound_closed_with_fn0_domain_bridge : Nat
  pfnsrc_pf_toPFunR_definitional : Nat
  prop_converge_to_type_data_bridge_emitted : Nat
  external_choice_principle_added : Nat

def stageA5RepCarryingDCTAudit : StageA5RepCarryingDCTAudit where
  dominated_fn_from_bound_closed := 1
  pfun_converges_carried_as_type_data := 1
  represents_self_toPFunR_closed := 0
  represents_self_toPFunR_blocked_by_toPFunR_head_value := 1
  domainResidualProvider_from_sec2_clean_rows_closed := 0
  domainResidualProvider_needs_charDomain_and_residual_fields := 1
  g_nonneg_from_bound_closed_without_domain_bridge := 0
  g_nonneg_from_bound_closed_with_fn0_domain_bridge := 1
  pfnsrc_pf_toPFunR_definitional := 1
  prop_converge_to_type_data_bridge_emitted := 0
  external_choice_principle_added := 0


end Theorem415Route
end BishopRegularSeqChapter4
end BishopCReal
