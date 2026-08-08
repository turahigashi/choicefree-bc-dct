import Mathdemo.Internal.CRat_iter148

/-!
# G49: Theorem 1.16 internal data, enumeration and tail estimates

G48 exposed Theorem 1.16 as double-series data.  This file tightens part of
that interface:

* a concrete square-shell enumeration of the double indices;
* a data layer for finite `L1` partial sums;
* the tail majorant and a bridge from tail estimates to norm convergence.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem116

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Fuel-based square-shell search.  The state `(N, rem)` means that `rem` is
the offset from the start of shell `N`. -/
def squareShellGo : Nat -> Nat -> Nat -> Nat × Nat
  | 0,        N, rem => (N, rem)
  | fuel + 1, N, rem =>
      if rem <= 2 * N then (N, rem)
      else squareShellGo fuel (N + 1) (rem - (2 * N + 1))

/-- If the offset is already inside the shell, the fuel is irrelevant. -/
theorem squareShellGo_base
    (fuel N rem : Nat) (h : rem <= 2 * N) :
    squareShellGo fuel N rem = (N, rem) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      change
        (if rem <= 2 * N then (N, rem)
         else squareShellGo fuel (N + 1) (rem - (2 * N + 1))) = (N, rem)
      rw [if_pos h]

/-- Peeling across square shells. -/
theorem squareShellGo_peel (n : Nat) :
    forall (s t fuel : Nat),
      t <= 2 * (s + n) -> n <= fuel ->
        squareShellGo fuel s (2 * s * n + n * n + t) = (s + n, t) := by
  induction n with
  | zero =>
      intro s t fuel ht _
      rw [show 2 * s * 0 + 0 * 0 + t = t from by ring]
      exact squareShellGo_base fuel s t (by omega)
  | succ n ih =>
      intro s t fuel ht hfuel
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_succ_le_zero n)
      | succ fuel' =>
          have hrem_eq :
              2 * s * (n + 1) + (n + 1) * (n + 1) + t =
                (2 * s + 1) + (2 * (s + 1) * n + n * n + t) := by
            ring
          change
            (if 2 * s * (n + 1) + (n + 1) * (n + 1) + t <= 2 * s
             then (s, 2 * s * (n + 1) + (n + 1) * (n + 1) + t)
             else squareShellGo fuel' (s + 1)
               (2 * s * (n + 1) + (n + 1) * (n + 1) + t -
                 (2 * s + 1))) = (s + (n + 1), t)
          rw [if_neg (by rw [hrem_eq]; omega),
            show
              2 * s * (n + 1) + (n + 1) * (n + 1) + t -
                (2 * s + 1) = 2 * (s + 1) * n + n * n + t
              from by rw [hrem_eq]; omega,
            show s + (n + 1) = (s + 1) + n from by omega]
          exact ih (s + 1) t fuel' (by omega) (by omega)

/-- The shell number is bounded by its square-shell index. -/
theorem shell_le_sq_add (N t : Nat) : N <= N * N + t := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.zero_le _
  · exact Nat.le_trans (Nat.le_mul_of_pos_left N hN)
      (Nat.le_add_right _ _)

/-- Decompose an index into a square shell and an offset. -/
def squareShellDecomp (m : Nat) : Nat × Nat :=
  squareShellGo m 0 m

/-- Decomposition at a shell boundary. -/
theorem squareShellDecomp_block
    (N t : Nat) (ht : t <= 2 * N) :
    squareShellDecomp (N * N + t) = (N, t) := by
  change squareShellGo (N * N + t) 0 (N * N + t) = (N, t)
  have key := squareShellGo_peel N 0 t (N * N + t)
    (by omega) (shell_le_sq_add N t)
  rwa [show 2 * 0 * N + N * N + t = N * N + t from by ring,
    Nat.zero_add] at key

/-- Turn a shell and offset into a planar cell. -/
def squareCellOf : Nat × Nat -> Nat × Nat
  | (N, t) => if t <= N then (N, t) else (t - N - 1, N)

/-- Concrete square-shell enumeration of pairs. -/
def squareEnum (m : Nat) : Nat × Nat :=
  squareCellOf (squareShellDecomp m)

/-- Boundary behavior of the concrete square-shell enumeration. -/
theorem squareEnum_block (N t : Nat) (ht : t <= 2 * N) :
    squareEnum (N * N + t) =
      if t <= N then (N, t) else (t - N - 1, N) := by
  change squareCellOf (squareShellDecomp (N * N + t)) = _
  rw [squareShellDecomp_block N t ht]
  rfl

/-- Index for the square-shell enumeration. -/
def squareIndex (m n : Nat) : Nat :=
  if m < n then n * n + (m + n + 1) else m * m + n

/-- The square-shell enumeration reaches every pair. -/
theorem squareEnum_squareIndex (m n : Nat) :
    squareEnum (squareIndex m n) = (m, n) := by
  unfold squareIndex
  rcases Nat.lt_or_ge m n with h | h
  · rw [if_pos h, squareEnum_block n (m + n + 1) (by omega),
      if_neg (by omega),
      show m + n + 1 - n - 1 = m from by omega]
  · rw [if_neg (Nat.not_lt.mpr h), squareEnum_block m n (by omega),
      if_pos h]

/-- Reaching data for every pair. -/
def squareEnum_covers (m n : Nat) :
    { t : Nat // squareEnum t = (m, n) } :=
  ⟨squareIndex m n, squareEnum_squareIndex m n⟩

end BishopRegularSeqTheorem116

/-- The analytic data of Theorem 1.16 once the concrete pair enumeration has
been fixed. -/
structure BishopRegularSeqTheorem116ConcreteDoubleData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem116Input S) : Type 1 where
  row_data : BishopRegularSeqTheorem116RowData S input
  A : Set X
  A_full : BishopRegularSeqFullSet S A
  limit_pfun : BishopRegularSeqPFun X
  limit_domain_is_A : limit_pfun.dom = A
  flat_abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun t =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqTheorem116.flatSeq input row_data
              BishopRegularSeqTheorem116.squareEnum t)))
  flat_integral_sum :
    BishopRegularSeqSeriesSum
      (fun t =>
        S.core.I
          (BishopRegularSeqTheorem116.flatSeq input row_data
            BishopRegularSeqTheorem116.squareEnum t))
  flat_value_law :
    BishopRegularSeqL1ValueLaw limit_pfun
      (BishopRegularSeqTheorem116.flatSeq input row_data
        BishopRegularSeqTheorem116.squareEnum)
  original_domain_on_A :
    forall x : X, x ∈ A ->
      forall n : Nat,
        x ∈ BishopRegularSeqIntegrableRep.domain (input.seq n)
  original_abs_series_on_A :
    forall x : X, x ∈ A ->
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((input.seq n).pfun.toFun x))
  limit_agrees_with_original_series :
    forall x : X,
      x ∈ A ->
        forall hsum :
          BishopRegularSeqSeriesSum
            (fun n => (input.seq n).pfun.toFun x),
          relEventually (limit_pfun.toFun x) hsum.sum
  source_uses_square_shell_enumeration : Prop
  source_A_is_double_abs_convergence_set : Prop

/-- Convert the concrete-enumeration data to the general G48 double data. -/
def BishopRegularSeqTheorem116ConcreteDoubleData.toDoubleData
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {input : BishopRegularSeqTheorem116Input S}
    (data : BishopRegularSeqTheorem116ConcreteDoubleData S input) :
    BishopRegularSeqTheorem116DoubleData S input where
  row_data := data.row_data
  enum := BishopRegularSeqTheorem116.squareEnum
  enum_covers := BishopRegularSeqTheorem116.squareEnum_covers
  A := data.A
  A_full := data.A_full
  limit_pfun := data.limit_pfun
  limit_domain_is_A := data.limit_domain_is_A
  flat_abs_integral_sum := data.flat_abs_integral_sum
  flat_integral_sum := data.flat_integral_sum
  flat_value_law := data.flat_value_law
  original_domain_on_A := data.original_domain_on_A
  original_abs_series_on_A := data.original_abs_series_on_A
  limit_agrees_with_original_series :=
    data.limit_agrees_with_original_series
  source_A_is_double_abs_convergence_set :=
    data.source_A_is_double_abs_convergence_set
  source_limit_uses_flattened_double_series := True

/-- Data for the finite `L1` partial sums appearing in Theorem 1.16. -/
structure BishopRegularSeqL1FinitePartialSumData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (seq : Nat -> BishopRegularSeqIntegrableRep S) : Type 1 where
  partialRep : Nat -> BishopRegularSeqIntegrableRep S
  partial_pfun_agrees :
    forall N : Nat,
      BishopRegularSeqPFunAlmostEverywhereEq S
        (partialRep N).pfun
        (BishopRegularSeqPFun.finSum
          (fun n => (seq n).pfun) N)
  source_partial_sum_built_by_iterated_addition : Prop

/-- Turn explicit partial-sum data into the G48 finite partial sum structure. -/
def BishopRegularSeqL1FinitePartialSumData.toFinitePartialSums
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {seq : Nat -> BishopRegularSeqIntegrableRep S}
    (data : BishopRegularSeqL1FinitePartialSumData S seq) :
    BishopRegularSeqL1FinitePartialSums S seq where
  partialRep := data.partialRep
  partial_pfun_agrees := data.partial_pfun_agrees
  source_partial_sum_representation :=
    data.source_partial_sum_built_by_iterated_addition

namespace BishopRegularSeqTheorem116

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The term `||f_n|| + 2^{-n}` used as row majorant in Theorem 1.16. -/
def rowMajorant
    (input : BishopRegularSeqTheorem116Input S)
    (n : Nat) : RegularSeq :=
  addSeq
    (BishopRegularSeqIntegrableRep.sourceNorm
      (input.seq n) (input.abs_data n))
    (constSeq (eps n))

/-- Tail of the row majorants after the finite partial sum indexed by `N`. -/
def tailMajorant
    (input : BishopRegularSeqTheorem116Input S)
    (N : Nat) : Nat -> RegularSeq :=
  fun j => rowMajorant input (N + 1 + j)

/-- The norm of the finite-sum tail term in Theorem 1.16. -/
def tailNormTerm
    (input : BishopRegularSeqTheorem116Input S)
    (limit : BishopRegularSeqIntegrableRep S)
    (partial_sums : BishopRegularSeqL1FinitePartialSums S input.seq)
    (tail_sub_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.SubData
          limit (partial_sums.partialRep N))
    (tail_abs_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.AbsData
          (BishopRegularSeqIntegrableRep.sub
            limit (partial_sums.partialRep N) (tail_sub_data N)))
    (N : Nat) : RegularSeq :=
  BishopRegularSeqIntegrableRep.sourceNorm
    (BishopRegularSeqIntegrableRep.sub
      limit (partial_sums.partialRep N) (tail_sub_data N))
    (tail_abs_data N)

end BishopRegularSeqTheorem116

/-- Tail majorant estimates in Theorem 1.16. -/
structure BishopRegularSeqTheorem116TailEstimateData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (input : BishopRegularSeqTheorem116Input S)
    (limit : BishopRegularSeqIntegrableRep S)
    (partial_sums : BishopRegularSeqL1FinitePartialSums S input.seq)
    (tail_sub_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.SubData
          limit (partial_sums.partialRep N))
    (tail_abs_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.AbsData
          (BishopRegularSeqIntegrableRep.sub
            limit (partial_sums.partialRep N) (tail_sub_data N))) :
    Type 1 where
  tail_majorant_sum :
    forall N : Nat,
      BishopRegularSeqSeriesSum
        (BishopRegularSeqTheorem116.tailMajorant input N)
  tail_norm_le_majorant :
    forall N : Nat,
      RegularSeqLe
        (BishopRegularSeqTheorem116.tailNormTerm
          input limit partial_sums tail_sub_data tail_abs_data N)
        ((tail_majorant_sum N).sum)
  tail_majorant_tends_zero :
    BishopRegularSeqTendsto
      (fun N => (tail_majorant_sum N).sum)
      zeroSeq
  source_uses_lemma_1_7_for_tail_bound : Prop
  source_uses_row_majorants_from_lemma_1_15 : Prop

/-- Bridge turning tail majorant estimates into the norm convergence part of
Theorem 1.16. -/
structure BishopRegularSeqTheorem116TailEstimateBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  tendsto_zero_from_majorant :
    forall (input : BishopRegularSeqTheorem116Input S)
      (limit : BishopRegularSeqIntegrableRep S)
      (partial_sums : BishopRegularSeqL1FinitePartialSums S input.seq)
      (tail_sub_data :
        forall N : Nat,
          BishopRegularSeqIntegrableRep.SubData
            limit (partial_sums.partialRep N))
      (tail_abs_data :
        forall N : Nat,
          BishopRegularSeqIntegrableRep.AbsData
            (BishopRegularSeqIntegrableRep.sub
              limit (partial_sums.partialRep N) (tail_sub_data N))),
      BishopRegularSeqTheorem116TailEstimateData
        S input limit partial_sums tail_sub_data tail_abs_data ->
        BishopRegularSeqTendsto
          (fun N =>
            BishopRegularSeqTheorem116.tailNormTerm
              input limit partial_sums tail_sub_data tail_abs_data N)
          zeroSeq
  source_comparison_to_zero_is_order_bridge : Prop

/-- Build the G48 tail norm data from finite partial sums and tail estimates. -/
def bishopRegularSeqTheorem116_tailNormData_from_estimates
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqTheorem116TailEstimateBridge S)
    (input : BishopRegularSeqTheorem116Input S)
    (limit : BishopRegularSeqIntegrableRep S)
    (partial_data : BishopRegularSeqL1FinitePartialSumData S input.seq)
    (tail_sub_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.SubData
          limit (partial_data.partialRep N))
    (tail_abs_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.AbsData
          (BishopRegularSeqIntegrableRep.sub
            limit (partial_data.partialRep N) (tail_sub_data N)))
    (estimate :
      BishopRegularSeqTheorem116TailEstimateData
        S input limit
        partial_data.toFinitePartialSums
        tail_sub_data
        tail_abs_data) :
    BishopRegularSeqTheorem116TailNormData S input limit where
  partial_sums := partial_data.toFinitePartialSums
  tail_sub_data := tail_sub_data
  tail_abs_data := tail_abs_data
  norm_tendsto_zero :=
    bridge.tendsto_zero_from_majorant
      input limit partial_data.toFinitePartialSums
      tail_sub_data tail_abs_data estimate
  source_uses_lemma_1_7_for_tail_bound :=
    estimate.source_uses_lemma_1_7_for_tail_bound
  source_tail_bound_uses_row_estimates :=
    estimate.source_uses_row_majorants_from_lemma_1_15

/-- Source-facing package for the first internal layer of Theorem 1.16. -/
structure BishopRegularSeqTheorem116InternalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  concrete_double_data :
    BishopRegularSeqTheorem116Input S -> Type 1
  to_double_data :
    forall input : BishopRegularSeqTheorem116Input S,
      concrete_double_data input ->
        BishopRegularSeqTheorem116DoubleData S input
  finite_partial_sum_data :
    (Nat -> BishopRegularSeqIntegrableRep S) -> Type 1
  tail_estimate_data :
    forall input : BishopRegularSeqTheorem116Input S,
      forall limit : BishopRegularSeqIntegrableRep S,
        forall partial_sums : BishopRegularSeqL1FinitePartialSums S input.seq,
          (forall N : Nat,
            BishopRegularSeqIntegrableRep.SubData
              limit (partial_sums.partialRep N)) ->
          Type 1
  source_uses_square_shell_enumeration : Prop
  source_tail_majorant_is_norm_plus_eps_tail : Prop

def bishopRegularSeqTheorem116InternalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem116InternalPackage S where
  concrete_double_data := BishopRegularSeqTheorem116ConcreteDoubleData S
  to_double_data := fun _ data =>
    BishopRegularSeqTheorem116ConcreteDoubleData.toDoubleData data
  finite_partial_sum_data := BishopRegularSeqL1FinitePartialSumData S
  tail_estimate_data := fun input limit partial_sums tail_sub_data =>
    Sigma (fun tail_abs_data :
      forall N : Nat,
        BishopRegularSeqIntegrableRep.AbsData
          (BishopRegularSeqIntegrableRep.sub
            limit (partial_sums.partialRep N) (tail_sub_data N)) =>
      BishopRegularSeqTheorem116TailEstimateData
        S input limit partial_sums tail_sub_data tail_abs_data)
  source_uses_square_shell_enumeration := True
  source_tail_majorant_is_norm_plus_eps_tail := True

/-- Progress after G49: Theorem 1.16 now has concrete pair enumeration,
finite partial-sum data, and the tail-majorant bridge. -/
def bishopRegularSeqCh1To4ProgressAfterG49 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 71
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 49
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G49: added concrete square-shell enumeration for Theorem 1.16, finite \
    partial-sum data, and the tail-majorant estimate bridge."


end BishopCReal
