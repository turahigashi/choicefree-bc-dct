import Mathdemo.Internal.CRat_iter407

set_option linter.style.longLine false

/-!
# G309: finite-support majorants for clean side classifiers

G308 constructed row side classifiers from explicit source-row side data.  This
node adds cutoff-aware versions for the four Proposition-2.10 final sides and
proves that the induced `0/1` row majorants are summable by eventual zero.

The key point is that the inside union and outside intersection cases use an
explicit hit index; they do not extract that index from a raw existential
membership proof.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Finite support summability -/

theorem partialSum_eq_of_zero_after
    (u : Nat → R) (N : Nat)
    (hzero : forall i : Nat, N < i -> u i = 0) :
    forall n : Nat, N ≤ n -> RSeq.partialSum u n = RSeq.partialSum u N
| 0, hN => by
    have hN0 : N = 0 := Nat.le_zero.mp hN
    subst hN0
    rfl
| n + 1, hN => by
    by_cases hNn : N ≤ n
    · change RSeq.partialSum u n + u (n + 1) = RSeq.partialSum u N
      rw [partialSum_eq_of_zero_after u N hzero n hNn,
        hzero (n + 1) (Nat.lt_of_le_of_lt hNn (Nat.lt_succ_self n)),
        add_zero]
    · have hEq : N = n + 1 := by omega
      subst hEq
      rfl


/-- A sequence with a zero tail is summable, with sum equal to its finite
prefix partial sum. -/
def seriesSum_of_zero_after
    (u : Nat → R) (N : Nat)
    (hzero : forall i : Nat, N < i -> u i = 0) :
    RSeq.SeriesSum u where
  sum := RSeq.partialSum u N
  tends :=
    { mod := fun _ => N
      close := by
        intro k n hn
        change COF.lt
          (COF.abs (RSeq.partialSum u n - RSeq.partialSum u N))
          (COF.halfPow k)
        rw [partialSum_eq_of_zero_after u N hzero n hn,
          show RSeq.partialSum u N - RSeq.partialSum u N = (0 : R) from by ring,
          COFO.abs_zero]
        exact halfPow_pos k }


/-! ## 2. Eventually-negative row facts -/

def BSetPointSideData.domain
    {A : Nat → BSet X} {x : X}
    (sideA : BSetPointSideData A x) :
    forall i : Nat, x ∈ (A i).S1 ∪ (A i).S2 :=
  fun i =>
    match sideA i with
    | PSum.inl h => Or.inl h
    | PSum.inr h => Or.inr h


theorem bigOrFinIncrement_s2_after_hit
    (A : Nat → BSet X) {x : X}
    (sideA : BSetPointSideData A x)
    (hit : BigOrS1Hit A x) :
    forall i : Nat, hit.index < i -> x ∈ (bigOrFinIncrementSet A i).S2
| 0, hi => False.elim (Nat.not_lt_zero hit.index hi)
| n + 1, hi => by
    have hd := BSetPointSideData.domain sideA
    have hKn : hit.index ≤ n := Nat.lt_succ_iff.mp hi
    have hKn1 : hit.index ≤ n + 1 := Nat.le_trans hKn (Nat.le_succ n)
    have hC : x ∈ (bigOrFin A (n + 1)).S1 :=
      bigOrFin_mem_S1 A hd (n + 1) hit.index hKn1 hit.mem
    have hD : x ∈ (bigOrFin A n).S1 :=
      bigOrFin_mem_S1 A hd n hit.index hKn hit.mem
    exact SubS2Case.toMem (SubS2Case.both hC hD)


theorem bigOrFinIncrement_s2_of_all_s2
    (A : Nat → BSet X) {x : X}
    (all_s2 : forall i : Nat, x ∈ (A i).S2) :
    forall i : Nat, x ∈ (bigOrFinIncrementSet A i).S2
| 0 => all_s2 0
| n + 1 => by
    have hC : x ∈ (bigOrFin A (n + 1)).S2 :=
      bigOrFin_mem_S2 A all_s2 (n + 1)
    have hD : x ∈ (bigOrFin A n).S2 :=
      bigOrFin_mem_S2 A all_s2 n
    exact SubS2Case.toMem (SubS2Case.neither hC hD)


theorem bigAndFinDrop_s2_of_all_s1
    (A : Nat → BSet X) {x : X}
    (all_s1 : forall i : Nat, x ∈ (A i).S1) :
    forall i : Nat, x ∈ (bigAndFinDropSet A i).S2
| 0 =>
    SubS2Case.toMem (SubS2Case.both (all_s1 0) (all_s1 0))
| n + 1 => by
    have hC : x ∈ (bigAndFin A n).S1 :=
      bigAndFin_mem_S1 A all_s1 n
    have hD : x ∈ (bigAndFin A (n + 1)).S1 :=
      bigAndFin_mem_S1 A all_s1 (n + 1)
    exact SubS2Case.toMem (SubS2Case.both hC hD)


theorem bigAndFinDrop_s2_after_hit
    (A : Nat → BSet X) {x : X}
    (sideA : BSetPointSideData A x)
    (hit : BigAndS2Hit A x) :
    forall i : Nat, hit.index < i -> x ∈ (bigAndFinDropSet A i).S2
| 0, hi => False.elim (Nat.not_lt_zero hit.index hi)
| n + 1, hi => by
    have hd := BSetPointSideData.domain sideA
    have hKn : hit.index ≤ n := Nat.lt_succ_iff.mp hi
    have hKn1 : hit.index ≤ n + 1 := Nat.le_trans hKn (Nat.le_succ n)
    have hC : x ∈ (bigAndFin A n).S2 :=
      bigAndFin_mem_S2 A hd n hit.index hKn hit.mem
    have hD : x ∈ (bigAndFin A (n + 1)).S2 :=
      bigAndFin_mem_S2 A hd (n + 1) hit.index hKn1 hit.mem
    exact SubS2Case.toMem (SubS2Case.neither hC hD)


/-! ## 3. Cutoff-aware classifiers and majorant sums -/

namespace BigOrPointSideData

def finiteRowSide
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointSideData A x) :
    RowSideClassifier (bigOrFinIncrementSet A) x :=
  fun i =>
    if hi : D.hit.index < i then
      PSum.inr (bigOrFinIncrement_s2_after_hit A D.sideA D.hit i hi)
    else
      bigOrFinIncrementSideClassifier A D.sideA i


theorem finiteRowSide_majorant_zero_after
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointSideData A x) :
    forall i : Nat, D.hit.index < i ->
      rowSideMajorant (R := R) (bigOrFinIncrementSet A) x D.finiteRowSide i = 0 := by
  intro i hi
  simp [rowSideMajorant, finiteRowSide, hi]


def finiteRowSideMajorantSum
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointSideData A x) :
    RSeq.SeriesSum
      (rowSideMajorant (R := R) (bigOrFinIncrementSet A) x D.finiteRowSide) :=
  seriesSum_of_zero_after
    (rowSideMajorant (R := R) (bigOrFinIncrementSet A) x D.finiteRowSide)
    D.hit.index
    (finiteRowSide_majorant_zero_after (R := R) D)


end BigOrPointSideData

namespace BigOrPointOutsideData

def zeroRowSide
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointOutsideData A x) :
    RowSideClassifier (bigOrFinIncrementSet A) x :=
  fun i => PSum.inr (bigOrFinIncrement_s2_of_all_s2 A D.all_s2 i)


theorem zeroRowSide_majorant_zero
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointOutsideData A x) :
    forall i : Nat,
      rowSideMajorant (R := R) (bigOrFinIncrementSet A) x D.zeroRowSide i = 0 := by
  intro i
  simp [rowSideMajorant, zeroRowSide]


def zeroRowSideMajorantSum
    {A : Nat → BSet X} {x : X}
    (D : BigOrPointOutsideData A x) :
    RSeq.SeriesSum
      (rowSideMajorant (R := R) (bigOrFinIncrementSet A) x D.zeroRowSide) :=
  seriesSum_of_zero_after
    (rowSideMajorant (R := R) (bigOrFinIncrementSet A) x D.zeroRowSide)
    0
    (fun i _ => zeroRowSide_majorant_zero (R := R) D i)


end BigOrPointOutsideData

namespace BigAndPointInsideData

def zeroRowSide
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointInsideData A x) :
    RowSideClassifier (bigAndFinDropSet A) x :=
  fun i => PSum.inr (bigAndFinDrop_s2_of_all_s1 A D.all_s1 i)


theorem zeroRowSide_majorant_zero
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointInsideData A x) :
    forall i : Nat,
      rowSideMajorant (R := R) (bigAndFinDropSet A) x D.zeroRowSide i = 0 := by
  intro i
  simp [rowSideMajorant, zeroRowSide]


def zeroRowSideMajorantSum
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointInsideData A x) :
    RSeq.SeriesSum
      (rowSideMajorant (R := R) (bigAndFinDropSet A) x D.zeroRowSide) :=
  seriesSum_of_zero_after
    (rowSideMajorant (R := R) (bigAndFinDropSet A) x D.zeroRowSide)
    0
    (fun i _ => zeroRowSide_majorant_zero (R := R) D i)


end BigAndPointInsideData

namespace BigAndPointOutsideData

def finiteRowSide
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointOutsideData A x) :
    RowSideClassifier (bigAndFinDropSet A) x :=
  fun i =>
    if hi : D.hit.index < i then
      PSum.inr (bigAndFinDrop_s2_after_hit A D.sideA D.hit i hi)
    else
      bigAndFinDropSideClassifier A D.sideA i


theorem finiteRowSide_majorant_zero_after
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointOutsideData A x) :
    forall i : Nat, D.hit.index < i ->
      rowSideMajorant (R := R) (bigAndFinDropSet A) x D.finiteRowSide i = 0 := by
  intro i hi
  simp [rowSideMajorant, finiteRowSide, hi]


def finiteRowSideMajorantSum
    {A : Nat → BSet X} {x : X}
    (D : BigAndPointOutsideData A x) :
    RSeq.SeriesSum
      (rowSideMajorant (R := R) (bigAndFinDropSet A) x D.finiteRowSide) :=
  seriesSum_of_zero_after
    (rowSideMajorant (R := R) (bigAndFinDropSet A) x D.finiteRowSide)
    D.hit.index
    (finiteRowSide_majorant_zero_after (R := R) D)


end BigAndPointOutsideData

/-! ## 4. Audit -/

structure Sec2CleanFiniteSupportMajorantAuditAfterG309 : Type where
  zero_tail_series_sum_added : Nat
  source_domain_from_side_data_added : Nat
  union_inside_eventual_s2_added : Nat
  union_outside_all_s2_added : Nat
  intersection_inside_all_s2_added : Nat
  intersection_outside_eventual_s2_added : Nat
  cutoff_aware_classifiers_added : Nat
  majorant_sums_added : Nat
  raw_prop_membership_to_type_extraction_used : Nat
  external_choice_principle_added : Nat
  clean_original_rep_equivalence_proved_this_step : Nat
  remaining_clean_original_equivalence_problem : Nat

def sec2CleanFiniteSupportMajorantAuditAfterG309 :
    Sec2CleanFiniteSupportMajorantAuditAfterG309 where
  zero_tail_series_sum_added := 1
  source_domain_from_side_data_added := 1
  union_inside_eventual_s2_added := 1
  union_outside_all_s2_added := 1
  intersection_inside_all_s2_added := 1
  intersection_outside_eventual_s2_added := 1
  cutoff_aware_classifiers_added := 4
  majorant_sums_added := 4
  raw_prop_membership_to_type_extraction_used := 0
  external_choice_principle_added := 0
  clean_original_rep_equivalence_proved_this_step := 0
  remaining_clean_original_equivalence_problem := 1


end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

structure Chapter4G309CleanFiniteSupportMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g308 : Chapter4G308CleanSideClassifierConstructionPackage S
  audit : BishopC.Sec2CleanFiniteSupportMajorantAuditAfterG309
  finite_support_majorant_api_available : Nat
  remaining_clean_original_equivalence_problem : Nat

def chapter4G309CleanFiniteSupportMajorantPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G309CleanFiniteSupportMajorantPackage S where
  g308 := chapter4G308CleanSideClassifierConstructionPackage S
  audit := BishopC.sec2CleanFiniteSupportMajorantAuditAfterG309
  finite_support_majorant_api_available := 1
  remaining_clean_original_equivalence_problem := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G309. -/
def bishopRegularSeqChapter4CleanFiniteSupportMajorantProgressAfterG309 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G309: proved summability of the 0/1 rowSideMajorants for the clean \
    Proposition-2.10 side classifiers by explicit finite-support/eventual-zero \
    data.  Remaining: assemble clean classified-row witnesses and connect the \
    clean increment/drop representatives to the original telescoping reps."


end BishopCReal
