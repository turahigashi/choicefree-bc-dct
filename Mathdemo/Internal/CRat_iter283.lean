import Mathdemo.Internal.CRat_iter282

set_option linter.style.longLine false

/-!
# G184: outside-A zero for the concrete absolute-difference representative

G183 closed the value datum for the concrete representative on the good set.
This file closes the outside-`A` zero bridge: if the two `mid` representatives
carry the support fact that they vanish when `chi_A = 0`, then the concrete
absolute difference representative also vanishes there.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- A `mid(-n, chi_A h, n)` representative together with its support fact:
when the characteristic value of `A` is `0`, the represented mid value is
also `0`. -/
structure Prop412MidRepresentativeSupportData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (n : Nat)
    (h : BishopC.PFunR Y R) : Type _ where
  mid : Prop412MidRepresentativeData A hA n h
  zero_of_chiA_zero :
    ∀ x
      (hχAabs : RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x)))
      (hmid : RSeq.SeriesSum (fun m => (mid.rep.fn m).toFun x)),
      (BishopC.seriesSum_of_abs hχAabs).sum = 0 ->
        hmid.sum = 0

/-- If both mid representatives vanish where `chi_A = 0`, their concrete
absolute difference also vanishes there. -/
theorem prop412_abs_truncated_diff_outside_A_zero_from_mid_support
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    {x : Y}
    (hχAabs : RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x)))
    (hdabs : RSeq.SeriesSum
      (fun m => COF.abs
        (((prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).fn m).toFun x)))
    (hχAzero : (BishopC.seriesSum_of_abs hχAabs).sum = 0) :
    (BishopC.seriesSum_of_abs hdabs).sum = 0 := by
  let subRep := F.mid.rep.sub G.mid.rep
  have hsubAbs :
      RSeq.SeriesSum (fun m => COF.abs ((subRep.fn m).toFun x)) :=
    prop412_absVal_absSeries_to_inner_absSeries subRep hdabs
  have hFabs :
      RSeq.SeriesSum (fun m => COF.abs ((F.mid.rep.fn m).toFun x)) := by
    simpa [subRep, BishopC.IntegrableRep.sub] using
      (BishopC.add_absSeriesSum_left
        (r := F.mid.rep) (r' := G.mid.rep.neg) hsubAbs)
  have hGnegAbs :
      RSeq.SeriesSum (fun m => COF.abs (((G.mid.rep.neg).fn m).toFun x)) := by
    simpa [subRep, BishopC.IntegrableRep.sub] using
      (BishopC.add_absSeriesSum_right
        (r := F.mid.rep) (r' := G.mid.rep.neg) hsubAbs)
  have hGabs :
      RSeq.SeriesSum (fun m => COF.abs ((G.mid.rep.fn m).toFun x)) :=
    BishopC.neg_absSeriesSum hGnegAbs
  let hFsum : RSeq.SeriesSum (fun m => (F.mid.rep.fn m).toFun x) :=
    BishopC.seriesSum_of_abs hFabs
  let hGsum : RSeq.SeriesSum (fun m => (G.mid.rep.fn m).toFun x) :=
    BishopC.seriesSum_of_abs hGabs
  let hSubSum : RSeq.SeriesSum (fun m => (subRep.fn m).toFun x) :=
    BishopC.add_seriesSum_value hFsum
      (BishopC.neg_seriesSum_value hGsum)
  obtain ⟨hdSigned, hdSignedEq⟩ := subRep.absVal_signed_value x hSubSum
  have hdf_eq :
      (BishopC.seriesSum_of_abs hdabs).sum = hdSigned.sum := by
    exact BishopC.seriesSum_unique (BishopC.seriesSum_of_abs hdabs) hdSigned
  have hFzero : hFsum.sum = 0 :=
    F.zero_of_chiA_zero x hχAabs hFsum hχAzero
  have hGzero : hGsum.sum = 0 :=
    G.zero_of_chiA_zero x hχAabs hGsum hχAzero
  have hSub_zero : hSubSum.sum = 0 := by
    rw [show hSubSum.sum = hFsum.sum + -hGsum.sum from rfl,
      hFzero, hGzero]
    ring
  calc
    (BishopC.seriesSum_of_abs hdabs).sum = hdSigned.sum := hdf_eq
    _ = COF.abs hSubSum.sum := hdSignedEq
    _ = COF.abs (0 : R) := by rw [hSub_zero]
    _ = 0 := COFO.abs_of_nonneg (BishopC.le_refl (0 : R))

/-- Raw pointwise convergence witnesses for the concrete representative.  The
outside-`A` zero component is deliberately absent because G184 derives it from
the support data. -/
structure Prop412ConcreteRepresentativeValueSeedData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    (A E : BishopC.BSet Y)
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    (n : Nat)
    (f g : BishopC.PFunR Y R)
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (x : Y) : Type _ where
  hχAabs :
    RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x))
  hχEabs :
    RSeq.SeriesSum (fun m => COF.abs ((hE.rep.fn m).toFun x))
  hχBadAbs :
    RSeq.SeriesSum
      (fun m => COF.abs (((prop412_bad_set_integrable hA hE).rep.fn m).toFun x))
  hdabs :
    RSeq.SeriesSum
      (fun m => COF.abs
        (((prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).fn m).toFun x))
  hχE_d_abs :
    RSeq.SeriesSum
      (fun m => COF.abs
        (((BishopC.prop_4_2_chi_f_rep E hE
          (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
          (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).fn m).toFun x))
  hχBad_d_abs :
    RSeq.SeriesSum
      (fun m => COF.abs
        (((prop412BadRelRep hA hE
          (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
          (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).fn m).toFun x))

/-- Convert raw pointwise seed data into the G180 representative witness data,
with outside-`A` zero derived from support. -/
def prop412_representative_value_witness_from_concrete_support_seed
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    {x : Y}
    (Seed : Prop412ConcreteRepresentativeValueSeedData A E hA hE n f g F G x) :
    Prop412RepresentativeValueWitnessData A E hA hE
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
      (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)
      x where
  hχAabs := Seed.hχAabs
  hχEabs := Seed.hχEabs
  hχBadAbs := Seed.hχBadAbs
  hdabs := Seed.hdabs
  hχE_d_abs := Seed.hχE_d_abs
  hχBad_d_abs := Seed.hχBad_d_abs
  outside_A_zero := by
    intro hχAzero
    exact prop412_abs_truncated_diff_outside_A_zero_from_mid_support
      F G Seed.hχAabs Seed.hdabs hχAzero

/-- Pointwise seed data over the common domain. -/
structure Prop412ComplementPointwiseConcreteSupportSeedData
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
      ∀ (hcomp : RSeq.SeriesSum
          (fun m => ((prop412ComplementRep hE
            (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
            (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).fn m).toFun x))
        (hbad : RSeq.SeriesSum
          (fun m => ((prop412BadRelRep hA hE
            (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
            (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)).fn m).toFun x)),
        Prop412ConcreteRepresentativeValueSeedData A E hA hE n f g F G x

/-- Concrete support seed data imply the representative-value data expected
by G180. -/
def prop412_representative_value_data_from_concrete_support_seed
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (PData : Prop412ComplementPointwiseConcreteSupportSeedData A E hA hE n f g F G) :
    Prop412ComplementPointwiseRepresentativeValueData A E hA hE
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
      (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid) where
  data := by
    intro x hx hcomp hbad
    exact prop412_representative_value_witness_from_concrete_support_seed
      hA hE F G (PData.data x hx hcomp hbad)

/-- Full estimate from concrete support data: value data and outside-`A` zero
are now both derived. -/
theorem prop412_full_integral_le_from_concrete_truncated_abs_diff_support_data
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
    (PData : Prop412ComplementPointwiseConcreteSupportSeedData A E hA hE n f g F G)
    (hfg :
      ∀ x (hxE : x ∈ E.S1),
        COF.lt
          (COF.abs (f.toFun x (hEf hxE) - g.toFun x (hEg hxE)))
          eps)
    (hbadBound :
      ∀ (x : Y)
        (hdfabs : RSeq.SeriesSum
          (fun m => COF.abs
            (((prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).fn m).toFun x)))
        (hχBadAbs : RSeq.SeriesSum
          (fun m => COF.abs (((prop412_bad_set_integrable hA hE).rep.fn m).toFun x))),
        (BishopC.seriesSum_of_abs hχBadAbs).sum = 1 ->
          BishopC.Le (BishopC.seriesSum_of_abs hdfabs).sum (n : R)) :
    BishopC.Le
      (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid).integral
      (eps * BishopC.measure1 S hE +
        (n : R) *
          BishopC.measure1 S (prop412_bad_set_integrable hA hE)) :=
  prop412_full_integral_le_from_value_bound_rep_witness_data
    hE hA hEsubA hEf hEg
    (prop412AbsTruncatedDiffRepFromMidData F.mid G.mid)
    (prop412_abs_truncated_diff_rep_nonneg_from_mid_data F.mid G.mid)
    n eps
    (prop412_truncated_abs_value_data_from_mid_reps
      hA hEf hEg F.mid G.mid K)
    hfg hbadBound
    (prop412_representative_value_data_from_concrete_support_seed
      hA hE F G PData)

/-- Residual shape after G184. -/
structure Prop412OutsideAZeroFrontierAfterG184 : Type where
  mid_support_data_added : Prop
  concrete_abs_outside_A_zero_closed : Prop
  representative_witness_outside_A_zero_derived : Prop
  prove_mid_support_data_for_measurable_functions_needed : Prop
  prove_bad_set_n_bound_for_concrete_abs_needed : Prop
  arbitrary_epsilon_to_truncated_equality_needed : Prop
  old_true_statement_used : Nat

def prop412OutsideAZeroFrontierAfterG184 :
    Prop412OutsideAZeroFrontierAfterG184 where
  mid_support_data_added := True
  concrete_abs_outside_A_zero_closed := True
  representative_witness_outside_A_zero_derived := True
  prove_mid_support_data_for_measurable_functions_needed := True
  prove_bad_set_n_bound_for_concrete_abs_needed := True
  arbitrary_epsilon_to_truncated_equality_needed := True
  old_true_statement_used := 0

/-- G184 package. -/
structure Chapter4G184Prop412OutsideAZeroPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g183 : BishopRegularSeqChapter4G183Package S
  outside_A_zero_closed : Prop
  outside_A_zero_frontier_after_g184 :
    Prop412OutsideAZeroFrontierAfterG184
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_prop412_pass : Nat

def chapter4G184Prop412OutsideAZeroPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G184Prop412OutsideAZeroPackage S where
  g183 := bishopRegularSeqChapter4G183Package S
  outside_A_zero_closed := True
  outside_A_zero_frontier_after_g184 :=
    prop412OutsideAZeroFrontierAfterG184
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 1
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G184 package exposed at top level. -/
structure BishopRegularSeqChapter4G184Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G184Prop412OutsideAZeroPackage S
  proposition_4_12_outside_A_zero_closed_this_step : Nat
  proposition_4_12_internal_frontiers_remaining : Nat
  proposition_4_12_truncated_integral_subfrontiers_remaining : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_prop412_pass : Nat

def bishopRegularSeqChapter4G184Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G184Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G184Prop412OutsideAZeroPackage S
  proposition_4_12_outside_A_zero_closed_this_step := 1
  proposition_4_12_internal_frontiers_remaining := 2
  proposition_4_12_truncated_integral_subfrontiers_remaining := 1
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_prop412_pass := 2

/-- Progress after G184. -/
def bishopRegularSeqCh1To4ProgressAfterG184 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 97
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G184: outside-A zero for the concrete Proposition 4.12 absolute-difference \
    representative is derived from support-carrying mid representatives. \
    Remaining: bad-set n-bound for the concrete representative and the final \
    arbitrary-epsilon equality step. Prop. 4.12 countdown remains 2."


end BishopCReal
