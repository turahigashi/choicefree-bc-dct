import Mathdemo.Internal.Real.Definition16L1IntegrableFunctions

/-!
# G39: Definition 1.6 well-definedness bridge via Lemma 1.7

After Definition 1.6 the source uses Lemma 1.7 to justify that the represented
integral does not depend on the chosen representation.  This file exposes that
dependency without selecting representatives implicitly: a zero-version bridge
for Lemma 1.7 is threaded into the `L1` integral congruence statement.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Non-negativity in the current RegularSeq surface, stated as absence of a
strict tail below zero. -/
abbrev RegularSeqNonneg (x : RegularSeq) : Prop :=
  Not (regularSeqLtProp x zeroSeq)

/-- If the representative difference is eventually zero, the two
representatives are eventually equal. -/
theorem relEventually_of_subSeq_zero
    (x y : RegularSeq)
    (h : relEventually (subSeq x y) zeroSeq) :
    relEventually x y := by
  intro k
  rcases h k with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hn' : N <= n - 1 := by
    omega
  have htail := hN (n - 1) hn'
  have hsucc : n - 1 + 1 = n := by
    omega
  change
    Le (COF.abs ((subSeq x y).val (n - 1) - zeroSeq.val (n - 1)))
      (eps k) at htail
  change Le (COF.abs (x.val n - y.val n)) (eps k)
  simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal, addIndex,
    hsucc]
    using htail

/-- Source-shaped input for Lemma 1.7 positivity over RegularSeq-valued
partial functions. -/
structure BishopRegularSeqLemma17PositivityInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (fn : Nat -> BishopRegularSeqPFun X) : Type 1 where
  fn_mem : forall n : Nat, fn n ∈ S.core.L
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.absf (fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum (fun n => S.core.I (fn n))
  pointwise_nonneg :
    forall x : X,
      (forall n : Nat, x ∈ (fn n).dom) ->
      BishopRegularSeqSeriesSum (fun n => absSeq ((fn n).toFun x)) ->
      forall value_sum :
        BishopRegularSeqSeriesSum (fun n => (fn n).toFun x),
        RegularSeqNonneg value_sum.sum

/-- Lemma 1.7 positivity as an explicit bridge. -/
structure BishopRegularSeqLemma17PositivityBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  to_nonneg :
    forall (fn : Nat -> BishopRegularSeqPFun X),
      forall input : BishopRegularSeqLemma17PositivityInput S fn,
        RegularSeqNonneg input.integral_sum.sum

/-- Source-shaped zero input for the representation-null consequence of Lemma
1.7: if the represented pointwise series is zero wherever the absolute series
converges, then the represented integral is zero. -/
structure BishopRegularSeqLemma17ZeroInput
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (fn : Nat -> BishopRegularSeqPFun X) : Type 1 where
  fn_mem : forall n : Nat, fn n ∈ S.core.L
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.absf (fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum (fun n => S.core.I (fn n))
  pointwise_zero :
    forall x : X,
      BishopRegularSeqSeriesSum (fun n => absSeq ((fn n).toFun x)) ->
      forall value_sum :
        BishopRegularSeqSeriesSum (fun n => (fn n).toFun x),
        relEventually value_sum.sum zeroSeq

/-- Lemma 1.7 zero consequence, kept as an explicit bridge so Definition 1.6
does not hide any data extraction. -/
structure BishopRegularSeqLemma17ZeroBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  to_zero :
    forall (fn : Nat -> BishopRegularSeqPFun X),
      forall input : BishopRegularSeqLemma17ZeroInput S fn,
        relEventually input.integral_sum.sum zeroSeq

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- If two Definition 1.6 representations have the same first partial
function, the pointwise sums supplied by their value laws agree. -/
theorem value_sums_agree_of_equiv
    (r s : BishopRegularSeqIntegrableRep S)
    (heq : equiv r s)
    (x : X)
    (hr_abs :
      BishopRegularSeqSeriesSum (fun n => absSeq ((r.fn n).toFun x)))
    (hs_abs :
      BishopRegularSeqSeriesSum (fun n => absSeq ((s.fn n).toFun x))) :
    relEventually
      ((r.value_law.value_from_abs x hr_abs).val.sum)
      ((s.value_law.value_from_abs x hs_abs).val.sum) := by
  have hx_r : x ∈ r.pfun.dom :=
    r.value_law.domain_from_abs x hr_abs
  have hpfun : relEventually (r.pfun.toFun x) (s.pfun.toFun x) :=
    heq.2 x hx_r
  have hr_value :
      relEventually
        (r.pfun.toFun x)
        ((r.value_law.value_from_abs x hr_abs).val.sum) :=
    (r.value_law.value_from_abs x hr_abs).property
  have hs_value :
      relEventually
        (s.pfun.toFun x)
        ((s.value_law.value_from_abs x hs_abs).val.sum) :=
    (s.value_law.value_from_abs x hs_abs).property
  exact
    relEventually_trans
      ((r.value_law.value_from_abs x hr_abs).val.sum)
      (s.pfun.toFun x)
      ((s.value_law.value_from_abs x hs_abs).val.sum)
      (relEventually_trans
        ((r.value_law.value_from_abs x hr_abs).val.sum)
        (r.pfun.toFun x)
        (s.pfun.toFun x)
        (relEventually_symm
          (r.pfun.toFun x)
          ((r.value_law.value_from_abs x hr_abs).val.sum)
          hr_value)
        hpfun)
      hs_value

/-- Data saying that a difference representation computes `r.integral -
s.integral` and is pointwise zero.  This is the explicit target supplied by
the source proof before invoking Lemma 1.7. -/
structure DifferenceZeroData
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  diff_fn : Nat -> BishopRegularSeqPFun X
  zero_input : BishopRegularSeqLemma17ZeroInput S diff_fn
  integral_matches_sub :
    relEventually
      zero_input.integral_sum.sum
      (subSeq r.integral s.integral)

/-- Definition 1.6 well-definedness: the zero consequence of Lemma 1.7 on a
difference representation gives equality of the represented integrals. -/
def integral_congr_from_difference_zero
    (zero_bridge : BishopRegularSeqLemma17ZeroBridge S)
    (r s : BishopRegularSeqIntegrableRep S)
    (data : DifferenceZeroData r s) :
    relEventually r.integral s.integral :=
  relEventually_of_subSeq_zero r.integral s.integral
    (relEventually_trans
      (subSeq r.integral s.integral)
      data.zero_input.integral_sum.sum
      zeroSeq
      (relEventually_symm
        data.zero_input.integral_sum.sum
        (subSeq r.integral s.integral)
        data.integral_matches_sub)
      (zero_bridge.to_zero data.diff_fn data.zero_input))

end BishopRegularSeqIntegrableRep

/-- Source-facing package for the Definition 1.6 well-definedness frontier. -/
structure BishopRegularSeqDef16WellDefinedPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  zero_bridge : BishopRegularSeqLemma17ZeroBridge S
  integral_congr :
    forall r s : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.DifferenceZeroData r s ->
        relEventually r.integral s.integral
  source_lemma_1_7_zero_is_the_frontier : Prop

/-- Build the Definition 1.6 well-definedness package from the zero form of
Lemma 1.7. -/
def bishopRegularSeqDef16WellDefinedPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (zero_bridge : BishopRegularSeqLemma17ZeroBridge S) :
    BishopRegularSeqDef16WellDefinedPackage S where
  zero_bridge := zero_bridge
  integral_congr := fun r s data =>
    BishopRegularSeqIntegrableRep.integral_congr_from_difference_zero
      zero_bridge r s data
  source_lemma_1_7_zero_is_the_frontier := True

/-- Progress after G39: Definition 1.6 now has a source-shaped
well-definedness bridge through Lemma 1.7's zero consequence. -/
def bishopRegularSeqCh1To4ProgressAfterG39 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 46
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 38
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G39: added the Definition 1.6 well-definedness bridge via the zero \
    consequence of Lemma 1.7."


end BishopCReal
