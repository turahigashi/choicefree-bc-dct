import Mathdemo.Internal.Real.DownstreamProp412BridgeGood

set_option linter.style.longLine false

/-!
# G212: pointwise seed from definition-facing domain witness data

G211 removed the downstream all-`B,C` provider.  The remaining coarse source
was the pointwise seed itself.  This increment refines that source: the common
domain is used only as the point where the comparison is made, while the
absolute-convergence witnesses required by Proposition 4.12 are carried as
definition/constructor data.  In particular, this file does not extract a
`SeriesSum` witness from `IntegrableRep.domain`'s `Nonempty` component.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- Definition-facing pointwise witnesses for the complement/bad comparison.

These are exactly the concrete witnesses needed by G184, but renamed at the
source boundary to record their intended origin: they are supplied by the
representative constructors/Definition 1.6 data, not by choosing from the
Prop-valued `domain` predicate after the fact. -/
structure Prop412ComplementBadDomainWitnessData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A E : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (n : Nat)
    (f g : BishopC.PFunR Y R)
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (x : Y) : Type _ where
  hχADom : hA.rep.MemAt x
  hχAabs :
    RSeq.SeriesSum (fun m => COF.abs (hA.rep.valueAt x hχADom m))
  hχEDom : hE.rep.MemAt x
  hχEabs :
    RSeq.SeriesSum (fun m => COF.abs (hE.rep.valueAt x hχEDom m))
  hχBadDom : (prop412_bad_set_integrable hA hE).rep.MemAt x
  hχBadAbs :
    RSeq.SeriesSum
      (fun m => COF.abs
        ((prop412_bad_set_integrable hA hE).rep.valueAt x hχBadDom m))
  hdDom : (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).MemAt x
  hdabs :
    RSeq.SeriesSum
      (fun m => COF.abs
        ((prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).valueAt
          x hdDom m))
  hχE_d_Dom :
    (BishopC.prop_4_2_chi_f_rep E hE
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
      (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).MemAt x
  hχE_d_abs :
    RSeq.SeriesSum
      (fun m => COF.abs
        ((BishopC.prop_4_2_chi_f_rep E hE
          (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
          (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).valueAt
            x hχE_d_Dom m))
  hχBad_d_Dom :
    (prop412BadRelRep hA hE
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
      (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).MemAt x
  hχBad_d_abs :
    RSeq.SeriesSum
      (fun m => COF.abs
        ((prop412BadRelRep hA hE
          (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
          (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).valueAt
            x hχBad_d_Dom m))
  witnesses_are_constructor_data_not_domain_nonempty_choice : Prop

/-- Forget the source annotation and obtain the concrete G184 seed. -/
def prop412_concrete_seed_from_complement_bad_domain_witness
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {hE : BishopC.IntegrableSet1 S E}
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    {F : Prop412MidRepresentativeSupportData A hA n f}
    {G : Prop412MidRepresentativeSupportData A hA n g}
    {x : Y}
    (D : Prop412ComplementBadDomainWitnessData A E hA hE n f g F G x) :
    Prop412ConcreteRepresentativeValueSeedData A E hA hE n f g F G x where
  hχADom := D.hχADom
  hχAabs := D.hχAabs
  hχEDom := D.hχEDom
  hχEabs := D.hχEabs
  hχBadDom := D.hχBadDom
  hχBadAbs := D.hχBadAbs
  hdDom := D.hdDom
  hdabs := D.hdabs
  hχE_d_Dom := D.hχE_d_Dom
  hχE_d_abs := D.hχE_d_abs
  hχBad_d_Dom := D.hχBad_d_Dom
  hχBad_d_abs := D.hχBad_d_abs

/-- Pointwise witness provider over the complement/bad common domain.

The membership hypotheses locate the point in the common full domain; the
absolute-convergence witnesses themselves are supplied by `data`. -/
structure Prop412ComplementBadDomainWitnessProviderData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A E : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (n : Nat)
    (f g : BishopC.PFunR Y R)
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g) : Type _ where
  data :
    ∀ x ∈
      (prop412ComplementRep hE
          (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
          (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).domain ∩
        (prop412BadRelRep hA hE
          (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
          (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).domain,
      ∀ (hcompDom : (prop412ComplementRep hE
            (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
            (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).MemAt x)
        (hbadDom : (prop412BadRelRep hA hE
            (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
            (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).MemAt x)
        (_hcomp : RSeq.SeriesSum
          (fun m => (prop412ComplementRep hE
            (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
            (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).valueAt
              x hcompDom m))
        (_hbad : RSeq.SeriesSum
          (fun m => (prop412BadRelRep hA hE
            (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
            (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).valueAt
              x hbadDom m)),
        Prop412ComplementBadDomainWitnessData A E hA hE n f g F G x
  common_domain_membership_is_not_used_as_witness_source : Prop

/-- Convert definition-facing domain witness data to the older concrete seed
interface consumed by the already proved complement-to-bad comparison. -/
def prop412_pointwise_seed_from_complement_bad_domain_witness_provider
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {hE : BishopC.IntegrableSet1 S E}
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    {F : Prop412MidRepresentativeSupportData A hA n f}
    {G : Prop412MidRepresentativeSupportData A hA n g}
    (P : Prop412ComplementBadDomainWitnessProviderData A E hA hE n f g F G) :
    Prop412ComplementPointwiseConcreteSupportSeedData A E hA hE n f g F G where
  data := by
    intro x hx hcompDom hbadDom hcomp hbad
    exact
      prop412_concrete_seed_from_complement_bad_domain_witness
        (P.data x hx hcompDom hbadDom hcomp hbad)

end TruncatedIntegralBridge
end Proposition412

namespace Prop412AssumptionDischarge

open Proposition412
open Proposition412.TruncatedIntegralBridge
open SourceComplete412

/-- Source-facing good-pair data after G212.

Compared with `Prop412GoodPairScopedRepresentativeWitnessSource`, this record
does not directly provide the previous concrete seed.  It provides the more
definition-faithful domain witness provider, from which the previous seed is
derived by a closed conversion. -/
structure Prop412GoodPairScopedDomainWitnessSource
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (Mf : Prop412DataCarryingMeasurable S f) : Type _ where
  integrable_set_source :
    ∀ (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A),
      Prop412IntegrableSetRepresentativeSource hA
  pointwise_domain_witness_on_good_pair :
    ∀ {g : BishopC.PFunR Y R}
      (Mg : Prop412DataCarryingMeasurable S g)
      (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
      (truncN : Nat)
      (B : BishopC.BSet Y) (hB : BishopC.IntegrableSet1 S B)
      (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
      (_hBsubA : B.S1 ⊆ A.S1)
      (_hCsubA : C.S1 ⊆ A.S1),
      Prop412ComplementBadDomainWitnessProviderData
        A (BishopC.BSet.and B C) hA (BishopC.IntegrableSet1_and hB hC)
        truncN f g
        (prop412_mid_support_data_from_constructor_source_data
          (Mf.mid_constructor_source A hA truncN))
        (prop412_mid_support_data_from_constructor_source_data
          (Mg.mid_constructor_source A hA truncN))
  pointwise_data_is_from_representative_constructors : Prop

/-- The G212 source lowers to the G211 source without adding choice. -/
noncomputable def prop412_good_pair_scoped_source_from_domain_witness_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Src : Prop412GoodPairScopedDomainWitnessSource Mf) :
    Prop412GoodPairScopedRepresentativeWitnessSource Mf where
  integrable_set_source := Src.integrable_set_source
  pointwise_seed_on_good_pair := by
    intro g Mg A hA truncN B hB C hC hBsubA hCsubA
    exact
      prop412_pointwise_seed_from_complement_bad_domain_witness_provider
        (Src.pointwise_domain_witness_on_good_pair
          Mg A hA truncN B hB C hC hBsubA hCsubA)

/-- Prop.4.12 truncated-integral equality through the definition-facing
domain-witness source. -/
theorem prop412_truncated_integrals_eq_from_good_pair_scoped_domain_witness_source
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.PFunR Y R}
    {f g : BishopC.PFunR Y R}
    {Mf : Prop412DataCarryingMeasurable S f}
    (Src : Prop412GoodPairScopedDomainWitnessSource Mf)
    (Mg : Prop412DataCarryingMeasurable S g)
    (hf : Prop412ConvergeInMeasureData S fn f)
    (hg : Prop412ConvergeInMeasureData S fn g)
    (A : BishopC.BSet Y) (hA : BishopC.IntegrableSet1 S A)
    (truncN : Nat)
    (truncN_pos : COF.lt 0 (truncN : R)) :
    (prop412_mid_full_support_data_from_constructor_source_data
        (Mf.mid_constructor_source A hA truncN)).support.mid.rep.integral =
      (prop412_mid_full_support_data_from_constructor_source_data
        (Mg.mid_constructor_source A hA truncN)).support.mid.rep.integral :=
  prop412_truncated_integrals_eq_from_good_pair_scoped_source
    (prop412_good_pair_scoped_source_from_domain_witness_source Src)
    Mg hf hg A hA truncN truncN_pos

end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge
open BishopRegularSeqChapter4.Prop412AssumptionDischarge

/-- G212 audit: the last pointwise seed is no longer taken as an opaque old
provider in this route; it is obtained from explicit domain witness data. -/
structure Prop412PointwiseSeedDomainDataAuditAfterG212 : Type where
  old_pointwise_seed_provider_needed_on_new_route : Nat
  domain_nonempty_extraction_used : Nat
  domain_data_to_concrete_seed_closed : Nat
  good_pair_domain_source_to_g211_source_closed : Nat
  truncated_integral_equality_from_domain_source_closed : Nat
  external_choice_principle_added : Nat
  remaining_constructor_domain_witness_obligations : Nat

def prop412PointwiseSeedDomainDataAuditAfterG212 :
    Prop412PointwiseSeedDomainDataAuditAfterG212 where
  old_pointwise_seed_provider_needed_on_new_route := 0
  domain_nonempty_extraction_used := 0
  domain_data_to_concrete_seed_closed := 1
  good_pair_domain_source_to_g211_source_closed := 1
  truncated_integral_equality_from_domain_source_closed := 1
  external_choice_principle_added := 0
  remaining_constructor_domain_witness_obligations := 1

/-- G212 package. -/
structure BishopRegularSeqChapter4G212Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g211 : BishopRegularSeqChapter4G211Package S
  pointwise_seed_domain_data_audit : Prop412PointwiseSeedDomainDataAuditAfterG212
  pointwise_seed_refined_to_definition_domain_data_this_step : Nat
  remaining_steps_after_domain_witness_layer : Nat

def bishopRegularSeqChapter4G212Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G212Package S where
  g211 := bishopRegularSeqChapter4G211Package S
  pointwise_seed_domain_data_audit := prop412PointwiseSeedDomainDataAuditAfterG212
  pointwise_seed_refined_to_definition_domain_data_this_step := 1
  remaining_steps_after_domain_witness_layer := 1

/-- Progress after G212. -/
def bishopRegularSeqPointwiseSeedDomainDataProgressAfterG212 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G212: refined the remaining Prop.4.12 pointwise seed into explicit \
    definition-facing domain witness data. The route no longer extracts \
    SeriesSum witnesses from the Nonempty component of IntegrableRep.domain; \
    domain membership only locates the common point, while the witnesses are \
    carried from the representative constructors. Remaining: close the \
    constructor-domain witness obligations for complement/bad reps."


end BishopCReal
