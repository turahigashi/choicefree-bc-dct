import Mathdemo.Internal.Real.PointwiseSeedDefinitionFacingDomainWitness

set_option linter.style.longLine false

/-!
# G213: direct complement-to-bad comparison from definition witnesses

G212 made the previous pointwise seed explicitly definition-facing.  This increment
goes one step further at the low-level estimate: instead of packaging a seed
as Type data, we prove the complement-to-bad comparison directly on a smaller
full set that contains all Definition 1.6 domains needed for the pointwise
calculation.

This matches the Bishop reading: witnesses are not supplied externally; they
are unfolded from the relevant integrable representatives at the point where
Proposition 1.11 asks for a pointwise inequality.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- The full set on which all Definition 1.6 witnesses needed for the
complement-to-bad pointwise comparison are simultaneously available. -/
noncomputable def prop412_definition_witness_full_set
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d) : Set Y :=
  ((((((prop412ComplementRep hE d hdnn).domain ∩
          (prop412BadRelRep hA hE d hdnn).domain) ∩
        hA.rep.domain) ∩
      hE.rep.domain) ∩
    (prop412_bad_set_integrable hA hE).rep.domain) ∩
    d.domain) ∩
    (BishopC.prop_4_2_chi_f_rep E hE d hdnn).domain

/-- The witness full set is full, because it is a finite intersection of
Definition 1.6 domains, each of which is full. -/
theorem prop412_definition_witness_full_set_isFull
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (d : BishopC.IntegrableRep S) (hdnn : BishopC.RepNonneg d) :
    BishopC.IsFull S (prop412_definition_witness_full_set hA hE d hdnn) := by
  unfold prop412_definition_witness_full_set
  exact
    BishopC.isFull_inter
      (BishopC.isFull_inter
        (BishopC.isFull_inter
          (BishopC.isFull_inter
            (BishopC.isFull_inter
              (BishopC.isFull_inter
                (prop412ComplementRep hE d hdnn).domain_isFull
                (prop412BadRelRep hA hE d hdnn).domain_isFull)
              hA.rep.domain_isFull)
            hE.rep.domain_isFull)
          (prop412_bad_set_integrable hA hE).rep.domain_isFull)
        d.domain_isFull)
      (BishopC.prop_4_2_chi_f_rep E hE d hdnn).domain_isFull

/-- The source bad-set estimate for the concrete truncated absolute difference,
proved directly from Definition 1.6 witnesses on a sufficiently small full set.

This avoids the previous `Prop412ComplementPointwiseConcreteSupportSeedData`
interface for this low-level comparison. -/
noncomputable def prop412_complement_to_bad_data_from_mid_support_full_definition_witnesses
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (hEsubA : E.S1 ⊆ A.S1)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g) :
    Prop412ComplementToBadData A E hA hE
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
      (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid) where
  complement_le_bad := by
    let d := prop412AbsTruncatedDiffRepFromMidData F.mid G.mid
    let hdnn := prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid
    change BishopC.Le
      (prop412ComplementRep hE d hdnn).integral
      (prop412BadRelRep hA hE d hdnn).integral
    refine BishopC.prop_1_11
      (prop412_definition_witness_full_set_isFull hA hE d hdnn)
      (prop412ComplementRep hE d hdnn)
      (prop412BadRelRep hA hE d hdnn)
      ?_
    intro x hx hcompDom hbadDom hcomp hbad
    unfold prop412_definition_witness_full_set at hx
    obtain ⟨hx0, hxχE_d⟩ := hx
    obtain ⟨hx1, hxd⟩ := hx0
    obtain ⟨hx2, hxBadχ⟩ := hx1
    obtain ⟨hx3, hxEχ⟩ := hx2
    obtain ⟨hxCompBad, hxAχ⟩ := hx3
    obtain ⟨hχADom, ⟨hχAabs⟩⟩ := hxAχ
    obtain ⟨hχEDom, ⟨hχEabs⟩⟩ := hxEχ
    obtain ⟨hχBadDom, ⟨hχBadAbs⟩⟩ := hxBadχ
    obtain ⟨hdDom, ⟨hdabs⟩⟩ := hxd
    obtain ⟨hχE_d_Dom, ⟨hχE_d_abs⟩⟩ := hxχE_d
    obtain ⟨_, hxBadRel⟩ := hxCompBad
    obtain ⟨hχBad_d_Dom, ⟨hχBad_d_abs⟩⟩ := hxBadRel
    let chiA := (BishopC.seriesSum_of_abs hχAabs).sum
    let chiE := (BishopC.seriesSum_of_abs hχEabs).sum
    let chiBad := (BishopC.seriesSum_of_abs hχBadAbs).sum
    let dval := (BishopC.seriesSum_of_abs hdabs).sum
    have hcompEq :
        hcomp.sum = (1 - chiE) * dval := by
      let hdv := BishopC.seriesSum_of_abs hdabs
      let hχEdv := BishopC.seriesSum_of_abs hχE_d_abs
      let hcompValue := BishopC.add_seriesSum_value hdDom
        (BishopC.IntegrableRep.neg_memAt hχE_d_Dom) hdv
        (BishopC.neg_seriesSum_value hχE_d_Dom hχEdv)
      have hsum : hcomp.sum = hcompValue.sum :=
        BishopC.seriesSum_unique hcomp hcompValue
      have hval : hcompValue.sum = (1 - chiE) * dval :=
        BishopC.prop_4_2_complement_value E hE d hdnn
          hχE_d_Dom hχEDom hdDom hχE_d_abs hχEabs hdabs
      exact hsum.trans hval
    have hbadEq :
        hbad.sum = chiBad * dval := by
      have hsum :
          hbad.sum = (BishopC.seriesSum_of_abs hχBad_d_abs).sum :=
        BishopC.seriesSum_unique hbad
          (BishopC.seriesSum_of_abs hχBad_d_abs)
      have hval :
          (BishopC.seriesSum_of_abs hχBad_d_abs).sum =
            chiBad * dval :=
        BishopC.prop_4_2_chi_f_rep_value (prop412BadSet A E)
          (prop412_bad_set_integrable hA hE) d hdnn
          hχBad_d_Dom hχBadDom hdDom hχBad_d_abs hχBadAbs hdabs
      exact hsum.trans hval
    have hmembership :
        Prop412ChiMembershipValueData A E x chiA chiE chiBad :=
      prop412_chi_membership_value_data_from_valid
        hA hE hχADom hχEDom hχBadDom hχAabs hχEabs hχBadAbs
    have houtside : chiA = 0 -> dval = 0 := by
      intro hχAzero
      exact
        prop412_abs_truncated_diff_outside_A_zero_from_mid_support
          F G hχADom hdDom hχAabs hdabs hχAzero
    rw [hcompEq, hbadEq]
    exact
      prop412_scalar_complement_le_bad_from_support_cases
        (prop412_scalar_support_cases_from_chi_membership_data
          hEsubA hmembership houtside)

/-- The G184 integral estimate no longer needs a pointwise seed when the
direct full-definition-witness route is used. -/
theorem prop412_full_integral_le_from_concrete_truncated_abs_diff_full_definition_witnesses
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hE : BishopC.IntegrableSet1 S E)
    (hA : BishopC.IntegrableSet1 S A)
    (hEsubA : E.S1 ⊆ A.S1)
    {f g : BishopC.PFunR Y R}
    (hEf : E.S1 ⊆ f.dom) (hEg : E.S1 ⊆ g.dom)
    (n : Nat) (eps : R)
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (K : Prop412GoodSetChiAAbsData A E hA)
    (hfg :
      ∀ x (hxE : x ∈ E.S1),
        COF.lt
          (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
          eps)
    (hbadBound :
      ∀ (x : Y)
        (hdfDom : (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).MemAt x)
        (hχBadDom : (prop412_bad_set_integrable hA hE).rep.MemAt x)
        (hdfabs : RSeq.SeriesSum
          (fun m => COF.abs
            ((prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).valueAt
              x hdfDom m)))
        (hχBadAbs : RSeq.SeriesSum
          (fun m => COF.abs
            ((prop412_bad_set_integrable hA hE).rep.valueAt x hχBadDom m))),
        (BishopC.seriesSum_of_abs hχBadAbs).sum = 1 ->
          BishopC.Le (BishopC.seriesSum_of_abs hdfabs).sum (n : R)) :
    BishopC.Le
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
      (eps * BishopC.measure1 S hE +
        (n : R) *
          BishopC.measure1 S (prop412_bad_set_integrable hA hE)) :=
  prop412_full_integral_le_from_value_bound_complement_data
    hE hA hEsubA hEf hEg
    (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
    (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)
    n eps
    (prop412_truncated_abs_value_data_from_mid_reps
      hA hEf hEg F.mid G.mid K)
    hfg hbadBound
    (prop412_complement_to_bad_data_from_mid_support_full_definition_witnesses
      hA hE hEsubA F G)

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G213 audit: the low-level complement-to-bad bridge can now be run without
the previous Type-level pointwise seed. -/
structure Prop412FullDefinitionWitnessAuditAfterG213 : Type where
  low_level_pointwise_seed_needed_for_complement_to_bad : Nat
  proposition_111_full_set_refined_to_all_definition_domains : Nat
  definition16_domain_witnesses_used_inside_prop_proof : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_downstream_budget_interfaces_still_mention_seed : Nat

def prop412FullDefinitionWitnessAuditAfterG213 :
    Prop412FullDefinitionWitnessAuditAfterG213 where
  low_level_pointwise_seed_needed_for_complement_to_bad := 0
  proposition_111_full_set_refined_to_all_definition_domains := 1
  definition16_domain_witnesses_used_inside_prop_proof := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_downstream_budget_interfaces_still_mention_seed := 1

/-- G213 package. -/
structure BishopRegularSeqChapter4G213Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g212 : BishopRegularSeqChapter4G212Package S
  full_definition_witness_audit : Prop412FullDefinitionWitnessAuditAfterG213
  complement_to_bad_low_level_seed_removed_this_step : Nat
  remaining_steps_after_full_definition_witness_bridge : Nat

def bishopRegularSeqChapter4G213Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G213Package S where
  g212 := bishopRegularSeqChapter4G212Package S
  full_definition_witness_audit := prop412FullDefinitionWitnessAuditAfterG213
  complement_to_bad_low_level_seed_removed_this_step := 1
  remaining_steps_after_full_definition_witness_bridge := 1

/-- Progress after G213. -/
def bishopRegularSeqFullDefinitionWitnessProgressAfterG213 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G213: proved the low-level complement-to-bad comparison directly from \
    Definition 1.6 witnesses by refining the Proposition 1.11 full set to \
    include all required representative domains. No pointwise seed or \
    Prop-to-Type witness extraction is needed for this comparison. Remaining: \
    replace the downstream dyadic/budget interfaces that still mention the \
    previous seed with this direct full-definition-witness route."


end BishopCReal
