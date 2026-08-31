import Mathdemo.Internal.Real.FiniteSumsChapter1Lemma1

/-!
# G36: common-domain extraction for chapter 1, Lemma 1.2

G35 obtained the pointwise witness delivered by Definition 1.1(2).  This file
extracts the common-domain information used in the statement of Lemma 1.2:
the witness point lies in the domains of all finitely many `g_i` and in every
domain of the sequence `f_n`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Membership in the domain of a finite sum implies membership in each
summand domain up to the finite bound. -/
theorem finSum_dom_of_le
    (F : Nat -> BishopRegularSeqPFun X) {x : X} :
    forall {n i : Nat},
      i <= n -> x ∈ (finSum F n).dom -> x ∈ (F i).dom
  | 0, i, hi, hx => by
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa [hi0, finSum] using hx
  | Nat.succ n, i, hi, hx => by
      by_cases hlast : i = Nat.succ n
      · simpa [hlast, finSum] using hx.2
      · have hlt : i < Nat.succ n := Nat.lt_of_le_of_ne hi hlast
        have hle : i <= n := Nat.le_of_lt_succ hlt
        exact finSum_dom_of_le F hle hx.1

/-- The finite side of Lemma 1.2 gives membership in each `g_i` domain. -/
theorem lemma12FiniteSide_dom_g_of_le
    (g f : Nat -> BishopRegularSeqPFun X) {x : X}
    {k N i : Nat}
    (hi : i <= k)
    (hx : x ∈ (lemma12FiniteSide g f k N).dom) :
    x ∈ (g i).dom := by
  have hx' :
      x ∈ (add (finSum g k) (finSum f N)).dom := by
    simpa [lemma12FiniteSide] using hx
  exact finSum_dom_of_le g hi hx'.1

/-- The finite side of Lemma 1.2 gives membership in each initial `f_i`
domain. -/
theorem lemma12FiniteSide_dom_f_of_le
    (g f : Nat -> BishopRegularSeqPFun X) {x : X}
    {k N i : Nat}
    (hi : i <= N)
    (hx : x ∈ (lemma12FiniteSide g f k N).dom) :
    x ∈ (f i).dom := by
  have hx' :
      x ∈ (add (finSum g k) (finSum f N)).dom := by
    simpa [lemma12FiniteSide] using hx
  exact finSum_dom_of_le f hi hx'.2

end BishopRegularSeqPFun

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Common-domain data extracted from the continuity witness in Lemma 1.2. -/
structure BishopRegularSeqLemma12CommonDomain
    (g f : Nat -> BishopRegularSeqPFun X) (k N : Nat) : Type where
  x : X
  hx_g : forall i : Nat, i <= k -> x ∈ (g i).dom
  hx_f : forall n : Nat, x ∈ (f n).dom
  tail_point_sum :
    BishopRegularSeqSeriesSum
      (fun n => (BishopRegularSeqPFun.tail f N n).toFun x)
  tail_below_finite :
    regularSeqLtData tail_point_sum.sum
      ((BishopRegularSeqPFun.lemma12FiniteSide g f k N).toFun x)

/-- Convert the Definition 1.1(2) pointwise witness into the common-domain
form used by Lemma 1.2. -/
def lemma12_commonDomain_from_continuity
    (g f : Nat -> BishopRegularSeqPFun X)
    (k N : Nat)
    (w :
      BishopRegularSeqPointwiseSeriesBelow
        (BishopRegularSeqPFun.tail f N)
        (BishopRegularSeqPFun.lemma12FiniteSide g f k N)) :
    BishopRegularSeqLemma12CommonDomain g f k N where
  x := w.x
  hx_g := fun i hi =>
    BishopRegularSeqPFun.lemma12FiniteSide_dom_g_of_le
      g f hi w.hx_f
  hx_f := fun i =>
    if hle : i <= N then
      BishopRegularSeqPFun.lemma12FiniteSide_dom_f_of_le
        g f hle w.hx_f
    else
      have hlt : N < i := Nat.lt_of_not_ge hle
      have hEq : N + (i - N) = i := by
        omega
      by
        simpa [BishopRegularSeqPFun.tail, hEq] using w.hx_fs (i - N)
  tail_point_sum := w.point_sum
  tail_below_finite := w.below

/-- Combine G35's continuity step with the common-domain extraction. -/
def lemma12_commonDomain_from_cut
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (g f : Nat -> BishopRegularSeqPFun X)
    (hg : forall n : Nat, g n ∈ S.core.L)
    (hf : forall n : Nat, f n ∈ S.core.L)
    (hnonneg : forall n : Nat, BishopRegularSeqPFun.PointwiseNonneg (f n))
    (k N : Nat)
    (cut : BishopRegularSeqLemma12CutData S g f k N) :
    BishopRegularSeqLemma12CommonDomain g f k N :=
  lemma12_commonDomain_from_continuity g f k N
    (lemma12_continuity_step S g f hg hf hnonneg k N cut)

/-- The final source-shaped positive conclusion for Lemma 1.2, isolated as
the remaining order-and-series arithmetic target. -/
structure BishopRegularSeqLemma12PositiveConclusion
    (g f : Nat -> BishopRegularSeqPFun X) (k : Nat) : Type where
  x : X
  hx_g : forall i : Nat, i <= k -> x ∈ (g i).dom
  hx_f : forall n : Nat, x ∈ (f n).dom
  full_point_sum :
    BishopRegularSeqSeriesSum (fun n => (f n).toFun x)
  positive :
    regularSeqLtData zeroSeq
      (addSeq
        (regularSeqFinSum (fun i => (g i).toFun x) k)
        full_point_sum.sum)

/-- The precise bridge still needed after G36. -/
structure BishopRegularSeqLemma12OrderSeriesBridge
    (g f : Nat -> BishopRegularSeqPFun X) : Type where
  to_positive :
    forall {k N : Nat},
      BishopRegularSeqLemma12CommonDomain g f k N ->
      BishopRegularSeqLemma12PositiveConclusion g f k

/-- Progress after G36: the point returned by Definition 1.1(2) has been
converted into the common-domain point required by Lemma 1.2. -/
def bishopRegularSeqCh1To4ProgressAfterG36 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 34
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 33
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G36: extracted the common-domain point from Lemma 1.2's continuity \
    witness; the remaining target is order/series arithmetic."


end BishopCReal
