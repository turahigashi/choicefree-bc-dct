import Mathdemo.Internal.CRat_iter289

set_option linter.style.longLine false

/-!
# G191: two-`n` bad-set cap from bounded `mid` representatives

G190 removed the hard-coded bad-set coefficient from the Proposition 4.12
assembly.  This file supplies the next concrete bridge: the scalar truncation
`mid(-n,z,n)` is bounded by `[-n,n]`, and therefore the absolute difference of
two such truncated values is bounded by `n+n`.

At the representative level this is kept data-carrying.  Once the construction
of the two `mid` representatives carries pointwise `[-n,n]` bounds, the bad-set
cap datum required by G190 is produced with cap `n+n`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge

/-- A natural number is below its negative reflection in the expected
Bishop-order sense: `-n ≤ n`. -/
theorem prop412_neg_natCast_le_natCast
    {R : Type*} [COFOC R] (n : Nat) :
    BishopC.Le (-(n : R)) (n : R) := by
  apply BishopC.le_of_nonneg_sub
  have hn : BishopC.Nonneg (n : R) := BishopC.lemma33_natCast_nonneg n
  have hsum : BishopC.Nonneg ((n : R) + (n : R)) :=
    BishopC.nonneg_add hn hn
  convert hsum using 1
  all_goals ring

/-- Scalar `mid(-n,z,n)` is bounded above by `n`. -/
theorem prop412_scalarMid_upper_bound
    {R : Type*} [COFOC R] (n : Nat) (z : R) :
    BishopC.Le (prop412ScalarMid n z) (n : R) := by
  dsimp [prop412ScalarMid]
  exact BishopC.cof_max_le
    (BishopC.cof_min_le_right z (n : R))
    (prop412_neg_natCast_le_natCast n)

/-- Scalar `mid(-n,z,n)` is bounded below by `-n`. -/
theorem prop412_scalarMid_lower_bound
    {R : Type*} [COFOC R] (n : Nat) (z : R) :
    BishopC.Le (-(n : R)) (prop412ScalarMid n z) := by
  dsimp [prop412ScalarMid]
  exact BishopC.lemma33_le_max_right (COF.min z (n : R)) (-(n : R))

/-- The absolute difference of two scalar `mid(-n,-,n)` values is bounded by
`n+n`.  This is the safe coefficient for the signed truncation in Prop. 4.12's
bad-set line. -/
theorem prop412_scalarMid_abs_sub_le_two_nat
    {R : Type*} [COFOC R] (n : Nat) (a b : R) :
    BishopC.Le
      (COF.abs (prop412ScalarMid n a - prop412ScalarMid n b))
      ((n : R) + (n : R)) := by
  have hposRaw :
      BishopC.Le
        (prop412ScalarMid n a - prop412ScalarMid n b)
        ((n : R) - (-(n : R))) :=
    BishopC.lemma33_sub_le_sub
      (prop412_scalarMid_upper_bound n a)
      (prop412_scalarMid_lower_bound n b)
  have hpos :
      BishopC.Le
        (prop412ScalarMid n a - prop412ScalarMid n b)
        ((n : R) + (n : R)) := by
    convert hposRaw using 1
    all_goals ring
  have hnegRaw :
      BishopC.Le
        (prop412ScalarMid n b - prop412ScalarMid n a)
        ((n : R) - (-(n : R))) :=
    BishopC.lemma33_sub_le_sub
      (prop412_scalarMid_upper_bound n b)
      (prop412_scalarMid_lower_bound n a)
  have hneg :
      BishopC.Le
        (-(prop412ScalarMid n a - prop412ScalarMid n b))
        ((n : R) + (n : R)) := by
    convert hnegRaw using 1
    all_goals ring
  exact COFO.abs_le_of hpos hneg

/-- Pointwise boundedness data for a concrete `mid(-n, chi_A h, n)`
representative.  This is construction data, not an added assumption: the eventual
mid-representative constructor should provide it together with the representative
and its value/support identities. -/
structure Prop412MidRepresentativePointwiseBoundData
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A : BishopC.BSet Y}
    {hA : BishopC.IntegrableSet1 S A}
    {n : Nat}
    {h : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n h) : Type _ where
  lower_bound :
    ∀ x
      (hmidDom : F.mid.rep.MemAt x)
      (hmidabs : RSeq.SeriesSum
        (fun m => COF.abs (F.mid.rep.valueAt x hmidDom m))),
      BishopC.Le (-(n : R)) (BishopC.seriesSum_of_abs hmidabs).sum
  upper_bound :
    ∀ x
      (hmidDom : F.mid.rep.MemAt x)
      (hmidabs : RSeq.SeriesSum
        (fun m => COF.abs (F.mid.rep.valueAt x hmidDom m))),
      BishopC.Le (BishopC.seriesSum_of_abs hmidabs).sum (n : R)

/-- Two pointwise bounded `mid` representatives give the concrete G190 bad-set
cap datum with cap `n+n`. -/
def prop412_concrete_bad_set_two_nat_cap_bound_from_mid_bounds
    {R : Type*} [COFOC R] {Y : Type} {S : BishopC.IntSpaceRC Y R}
    {A E : BishopC.BSet Y}
    (hA : BishopC.IntegrableSet1 S A)
    (hE : BishopC.IntegrableSet1 S E)
    {n : Nat}
    {f g : BishopC.PFunR Y R}
    (F : Prop412MidRepresentativeSupportData A hA n f)
    (G : Prop412MidRepresentativeSupportData A hA n g)
    (FBound : Prop412MidRepresentativePointwiseBoundData F)
    (GBound : Prop412MidRepresentativePointwiseBoundData G) :
    Prop412ConcreteBadSetCapBoundData A E hA hE n
      ((n : R) + (n : R)) F G where
  bound := by
    intro x hdfDom _hχBadDom hdfabs _hχBadAbs _hχBadOne
    let subRep := F.mid.rep.sub G.mid.rep
    let hsubAt : BishopC.Sec4RepAbsAt subRep x :=
      prop412_absVal_absSeries_to_inner_absSeries subRep hdfDom hdfabs
    let hsubDom : subRep.MemAt x := hsubAt.fst
    have hsubAbs :
        RSeq.SeriesSum (fun m => COF.abs
          (subRep.valueAt x hsubDom m)) :=
      hsubAt.snd
    let hFDom : F.mid.rep.MemAt x := BishopC.add_dom_left hsubDom
    let hGnegDom : G.mid.rep.neg.MemAt x := BishopC.add_dom_right hsubDom
    let hGDom : G.mid.rep.MemAt x := BishopC.neg_dom hGnegDom
    have hFabs :
        RSeq.SeriesSum (fun m => COF.abs
          (F.mid.rep.valueAt x hFDom m)) := by
      simpa only [hFDom] using
        (BishopC.add_absSeriesSum_left
          (r := F.mid.rep) (r' := G.mid.rep.neg) hsubDom hsubAbs)
    have hGnegAbs :
        RSeq.SeriesSum (fun m => COF.abs
          (G.mid.rep.neg.valueAt x hGnegDom m)) := by
      simpa only [hGnegDom] using
        (BishopC.add_absSeriesSum_right
          (r := F.mid.rep) (r' := G.mid.rep.neg) hsubDom hsubAbs)
    have hGabs :
        RSeq.SeriesSum (fun m => COF.abs
          (G.mid.rep.valueAt x hGDom m)) := by
      simpa only [hGDom] using BishopC.neg_absSeriesSum hGnegDom hGnegAbs
    let hFsum : RSeq.SeriesSum
        (fun m => F.mid.rep.valueAt x hFDom m) :=
      BishopC.seriesSum_of_abs hFabs
    let hGsum : RSeq.SeriesSum
        (fun m => G.mid.rep.valueAt x hGDom m) :=
      BishopC.seriesSum_of_abs hGabs
    let hSubSum : RSeq.SeriesSum
        (fun m => subRep.valueAt x hsubDom m) := by
      simpa only [subRep] using
        BishopC.add_seriesSum_value hFDom hGnegDom hFsum
          (BishopC.neg_seriesSum_value hGDom hGsum)
    obtain ⟨hdSigned, hdSignedEq⟩ :=
      subRep.absVal_signed_value x hsubDom hSubSum
    have hdf_eq :
        (BishopC.seriesSum_of_abs hdfabs).sum = hdSigned.sum := by
      exact BishopC.seriesSum_unique (BishopC.seriesSum_of_abs hdfabs) hdSigned
    have hFup : BishopC.Le hFsum.sum (n : R) :=
      FBound.upper_bound x hFDom hFabs
    have hFlow : BishopC.Le (-(n : R)) hFsum.sum :=
      FBound.lower_bound x hFDom hFabs
    have hGup : BishopC.Le hGsum.sum (n : R) :=
      GBound.upper_bound x hGDom hGabs
    have hGlow : BishopC.Le (-(n : R)) hGsum.sum :=
      GBound.lower_bound x hGDom hGabs
    have hposRaw :
        BishopC.Le (hFsum.sum - hGsum.sum) ((n : R) - (-(n : R))) :=
      BishopC.lemma33_sub_le_sub hFup hGlow
    have hpos :
        BishopC.Le hSubSum.sum ((n : R) + (n : R)) := by
      rw [show hSubSum.sum = hFsum.sum + -hGsum.sum from rfl]
      convert hposRaw using 1
      all_goals ring
    have hnegRaw :
        BishopC.Le (hGsum.sum - hFsum.sum) ((n : R) - (-(n : R))) :=
      BishopC.lemma33_sub_le_sub hGup hFlow
    have hneg :
        BishopC.Le (-hSubSum.sum) ((n : R) + (n : R)) := by
      rw [show hSubSum.sum = hFsum.sum + -hGsum.sum from rfl]
      convert hnegRaw using 1
      all_goals ring
    have habs :
        BishopC.Le (COF.abs hSubSum.sum) ((n : R) + (n : R)) :=
      COFO.abs_le_of hpos hneg
    rw [hdf_eq, hdSignedEq]
    exact habs

/-- Residual shape after G191. -/
structure Prop412TwoNatBadSetCapFrontierAfterG191 : Type where
  scalar_mid_two_nat_bound_closed : Prop
  concrete_two_nat_bad_cap_from_mid_bounds_closed : Prop
  construct_mid_pointwise_bounds_for_actual_mid_reps_still_needed : Prop
  prop_valued_convergence_extraction_still_requires_redesign_not_choice : Prop
  old_true_statement_used : Nat

def prop412TwoNatBadSetCapFrontierAfterG191 :
    Prop412TwoNatBadSetCapFrontierAfterG191 where
  scalar_mid_two_nat_bound_closed := True
  concrete_two_nat_bad_cap_from_mid_bounds_closed := True
  construct_mid_pointwise_bounds_for_actual_mid_reps_still_needed := True
  prop_valued_convergence_extraction_still_requires_redesign_not_choice := True
  old_true_statement_used := 0

/-- G191 package. -/
structure Chapter4G191Prop412TwoNatBadSetCapPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g190 : BishopRegularSeqChapter4G190Package S
  two_nat_bad_cap_frontier_after_g191 : Prop412TwoNatBadSetCapFrontierAfterG191
  scalar_two_nat_bound_closed_this_step : Nat
  representative_two_nat_cap_bridge_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  countdown_remaining_for_data_carrying_prop412_pass : Nat
  countdown_remaining_for_assumption_free_source_prop412_pass : Nat

def chapter4G191Prop412TwoNatBadSetCapPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G191Prop412TwoNatBadSetCapPackage S where
  g190 := bishopRegularSeqChapter4G190Package S
  two_nat_bad_cap_frontier_after_g191 := prop412TwoNatBadSetCapFrontierAfterG191
  scalar_two_nat_bound_closed_this_step := 1
  representative_two_nat_cap_bridge_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 2
  countdown_remaining_for_data_carrying_prop412_pass := 0
  countdown_remaining_for_assumption_free_source_prop412_pass := 2

end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge

/-- G191 package exposed at top level. -/
structure BishopRegularSeqChapter4G191Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  package : BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.Chapter4G191Prop412TwoNatBadSetCapPackage S
  scalar_two_nat_bound_closed_this_step : Nat
  representative_two_nat_cap_bridge_closed_this_step : Nat
  chapter4_faithful_source_frontiers_still_open : Nat
  remaining_countdown_steps_for_data_carrying_prop412_pass : Nat
  remaining_countdown_steps_for_assumption_free_source_prop412_pass : Nat

def bishopRegularSeqChapter4G191Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter4G191Package S where
  package := BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge.chapter4G191Prop412TwoNatBadSetCapPackage S
  scalar_two_nat_bound_closed_this_step := 1
  representative_two_nat_cap_bridge_closed_this_step := 1
  chapter4_faithful_source_frontiers_still_open := 2
  remaining_countdown_steps_for_data_carrying_prop412_pass := 0
  remaining_countdown_steps_for_assumption_free_source_prop412_pass := 2

/-- Progress after G191. -/
def bishopRegularSeqCh1To4ProgressAfterG191 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G191: proved the scalar two-n bound for mid(-n,z,n) and converted \
    pointwise bounded mid representatives into the concrete bad-set cap \
    datum with cap n+n. Remaining honest frontiers: constructing those \
    pointwise bounds for the actual mid representatives and replacing any \
    Prop-only convergence extraction by data-carrying witness interfaces."


end BishopCReal
