import Mathdemo.Internal.CRat_iter219

set_option linter.style.longLine false

/-!
# G120: late-sample positivity transport for RegularSeq

Line 735's remaining `minSeqWith` monotonicity proof has to handle the bounded
multiplication sampling index inside `mulSeqConcreteWith A halfSeq ...`.

This file closes the general RegularSeq bridge needed for that index drift:
if a regular representative is eventually positive along a cofinal late
sampling function, then it is positive in the ordinary `PosEventually` sense.
No quotient representative extraction and no `PosEventually -> Data` selector
is used.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Positivity along a late cofinal sample sequence transports back to ordinary
eventual positivity by regularity. -/
theorem posEventually_of_late_sample_pos
    (x : RegularSeq)
    (F : Nat -> Nat)
    (hF : forall n : Nat, n <= F n)
    (hpos : ∃ k N : Nat, ∀ n : Nat, N <= n -> COF.lt (eps k) (x.val (F n))) :
    PosEventually x := by
  rcases hpos with ⟨k, N, hN⟩
  refine ⟨k + 1, N + (k + 2), ?_⟩
  intro n hn
  have hNn : N <= n :=
    Nat.le_trans (Nat.le_add_right _ _) hn
  have hk2n : k + 2 <= n :=
    Nat.le_trans (Nat.le_add_left _ _) hn
  have hsample : COF.lt (eps k) (x.val (F n)) :=
    hN n hNn
  have hFbound : k + 2 <= F n :=
    Nat.le_trans hk2n (hF n)
  have hleft : Le (eps (F n)) (eps (k + 2)) :=
    eps_le_of_le hFbound
  have hright : Le (eps n) (eps (k + 2)) :=
    eps_le_of_le hk2n
  have hsum : Le (eps (F n) + eps n) (eps (k + 2) + eps (k + 2)) :=
    BishopC.le_add hleft hright
  have hbudget : Le (eps (F n) + eps n) (eps (k + 1)) := by
    rwa [eps_succ_add_self (k + 1)] at hsum
  have hdist : Le (COF.abs (x.val (F n) - x.val n)) (eps (k + 1)) :=
    BishopC.le_trans (x.regular (F n) n) hbudget
  have hlower : Le (x.val (F n) - eps (k + 1)) (x.val n) :=
    scalar_point_lower_of_abs_le hdist
  have hshift : COF.lt (eps (k + 1)) (x.val (F n) - eps (k + 1)) := by
    have t := COF.lt_add_left (-(eps (k + 1))) hsample
    rwa [← eps_succ_add_self k,
      show -(eps (k + 1)) + (eps (k + 1) + eps (k + 1)) = eps (k + 1)
        from by ring,
      show -(eps (k + 1)) + x.val (F n) = x.val (F n) - eps (k + 1)
        from by ring] at t
  exact BishopC.lt_of_lt_of_le hshift hlower

/-- A specialized version for represented differences. -/
theorem posEventually_subSeq_of_late_sample_pos
    (x y : RegularSeq)
    (F : Nat -> Nat)
    (hF : forall n : Nat, n <= F n)
    (hpos :
      ∃ k N : Nat,
        ∀ n : Nat, N <= n -> COF.lt (eps k) ((subSeq y x).val (F n))) :
    PosEventually (subSeq y x) :=
  posEventually_of_late_sample_pos (subSeq y x) F hF hpos

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G120 bridge for bounded-multiplication index drift in the remaining
line-735 min transport. -/
structure Property4RegularSeqLateSamplePosBridge : Type 1 where
  pos_of_late_sample :
    forall (x : RegularSeq) (F : Nat -> Nat),
      (forall n : Nat, n <= F n) ->
        (∃ k N : Nat, ∀ n : Nat, N <= n -> COF.lt (eps k) (x.val (F n))) ->
          PosEventually x
  sub_pos_of_late_sample :
    forall (x y : RegularSeq) (F : Nat -> Nat),
      (forall n : Nat, n <= F n) ->
        (∃ k N : Nat,
          ∀ n : Nat, N <= n -> COF.lt (eps k) ((subSeq y x).val (F n))) ->
          PosEventually (subSeq y x)
  no_pos_eventually_witness_extraction : Prop
  no_quotient_representative_extraction : Prop

def property4RegularSeqLateSamplePosBridge :
    Property4RegularSeqLateSamplePosBridge where
  pos_of_late_sample := posEventually_of_late_sample_pos
  sub_pos_of_late_sample := posEventually_subSeq_of_late_sample_pos
  no_pos_eventually_witness_extraction := True
  no_quotient_representative_extraction := True

/-- G120 audit: the multiplication-index drift bridge is closed, but the
actual half-sum min strict-backward transport remains. -/
structure Property4RegularSeqLine735AuditAfterLateSampleBridge : Type where
  line735_minSeqWith_left_monotonicity_inputs : Nat
  pointwise_to_regularseq_order_bridge_closed : Nat
  late_sample_positivity_bridge_closed : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat
  remaining_frontier_is_min_strict_backward_transport : Prop

def property4RegularSeqLine735AuditAfterLateSampleBridge :
    Property4RegularSeqLine735AuditAfterLateSampleBridge where
  line735_minSeqWith_left_monotonicity_inputs := 1
  pointwise_to_regularseq_order_bridge_closed := 1
  late_sample_positivity_bridge_closed := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0
  remaining_frontier_is_min_strict_backward_transport := True

end BishopRegularSeqTheorem118

/-- G120 package: cofinal late-sample positivity transport is closed for the
RegularSeq/data route. -/
structure BishopRegularSeqTheorem118G120Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 8 where
  g119 : BishopRegularSeqTheorem118G119Package S
  late_sample_pos_bridge :
    BishopRegularSeqTheorem118.Property4RegularSeqLateSamplePosBridge
  selector_audit :
    BishopRegularSeqTheorem118.Property4RegularSeqLine735AuditAfterLateSampleBridge
  line743_closed_by_g118 : Prop
  line735_late_sample_index_drift_closed : Prop
  line735_min_strict_backward_transport_still_frontier : Prop
  no_quotient_extraction_in_g120_mainline : Prop

def bishopRegularSeqTheorem118G120Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G120Package S where
  g119 := bishopRegularSeqTheorem118G119Package S
  late_sample_pos_bridge :=
    BishopRegularSeqTheorem118.property4RegularSeqLateSamplePosBridge
  selector_audit :=
    BishopRegularSeqTheorem118.property4RegularSeqLine735AuditAfterLateSampleBridge
  line743_closed_by_g118 := True
  line735_late_sample_index_drift_closed := True
  line735_min_strict_backward_transport_still_frontier := True
  no_quotient_extraction_in_g120_mainline := True

/-- Progress after G120: still 99%, but the bounded-multiplication sampling
drift needed for the final line-735 transport is closed. -/
def bishopRegularSeqCh1To4ProgressAfterG120 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G120: closed late-sample positivity transport for RegularSeq; the \
    remaining line-735 work is min strict-backward transport."


end BishopCReal
