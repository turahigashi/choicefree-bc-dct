import Mathdemo.Internal.Real.DiagonalRepresentativeCandidate

/-!
# Regularity of the diagonal representative candidate

`DiagonalRepresentativeCandidate` fixed the value-level diagonal candidate.  This file proves that
the candidate is a regular representative.  The proof uses a three-term
triangle estimate:

```
L m → selected_m q → selected_n q → L n
```

where `q` is chosen after opening the representative Cauchy tail witness.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Budget for the branch where the middle Cauchy estimate is taken at gauge
`m+6`. -/
theorem repDiagonal_regular_budget_left (m n : Nat) :
    Le (eps (m + 5) + (eps (m + 6) + eps (n + 5)))
      (eps m + eps n) := by
  have hm5 : Le (eps (m + 5)) (eps (m + 1)) :=
    eps_le_of_le (by omega)
  have hm6 : Le (eps (m + 6)) (eps (m + 1)) :=
    eps_le_of_le (by omega)
  have hm_pair : Le (eps (m + 5) + eps (m + 6)) (eps m) := by
    have hsum := BishopC.le_add hm5 hm6
    rwa [eps_succ_add_self m] at hsum
  have hn5 : Le (eps (n + 5)) (eps n) :=
    eps_le_of_le (by omega)
  have hsum := BishopC.le_add hm_pair hn5
  rwa [show (eps (m + 5) + eps (m + 6)) + eps (n + 5)
      = eps (m + 5) + (eps (m + 6) + eps (n + 5)) from by ring] at hsum

/-- Budget for the branch where the middle Cauchy estimate is taken at gauge
`n+6`. -/
theorem repDiagonal_regular_budget_right (m n : Nat) :
    Le (eps (m + 5) + (eps (n + 6) + eps (n + 5)))
      (eps m + eps n) := by
  have hm5 : Le (eps (m + 5)) (eps m) :=
    eps_le_of_le (by omega)
  have hn6 : Le (eps (n + 6)) (eps (n + 1)) :=
    eps_le_of_le (by omega)
  have hn5 : Le (eps (n + 5)) (eps (n + 1)) :=
    eps_le_of_le (by omega)
  have hn_pair : Le (eps (n + 6) + eps (n + 5)) (eps n) := by
    have hsum := BishopC.le_add hn6 hn5
    rwa [show eps (n + 1) + eps (n + 1) = eps n
      from eps_succ_add_self n] at hsum
  exact BishopC.le_add hm5 hn_pair

/-- The value-level diagonal candidate is a regular CReal representative. -/
theorem repDiagonalVal_regular
    (w : Nat → RegularSeq)
    (hc : CRealRepSequenceCauchyData w) :
    RegularVal (repDiagonalVal w hc) := by
  intro m n
  by_cases hmn : m ≤ n
  · have hclose :
        RepCloseAtGauge (m + 6)
          (w (repDiagonalIndex hc m))
          (w (repDiagonalIndex hc n)) :=
      repCloseAtGauge_diagonal_indices hc
        (k := m + 6) (m := m) (n := n)
        (by unfold repDiagonalSlack; omega)
        (by unfold repDiagonalSlack; omega)
    rcases hclose with ⟨N, hN⟩
    let q : Nat := N + repDiagonalSample m + repDiagonalSample n
    have hqN : N ≤ q := by
      unfold q
      omega
    have hqm : repDiagonalSample m ≤ q := by
      unfold q
      omega
    have hqn : repDiagonalSample n ≤ q := by
      unfold q
      omega
    have hab :
        Le
          (COF.abs
            (repDiagonalVal w hc m -
              (w (repDiagonalIndex hc m)).val q))
          (eps (m + 5)) :=
      repDiagonalVal_same_rep_tail w hc hqm
    have hbc :
        Le
          (COF.abs
            ((w (repDiagonalIndex hc m)).val q -
              (w (repDiagonalIndex hc n)).val q))
          (eps (m + 6)) :=
      hN q hqN
    have hcd :
        Le
          (COF.abs
            ((w (repDiagonalIndex hc n)).val q -
              repDiagonalVal w hc n))
          (eps (n + 5)) :=
      same_rep_tail_to_repDiagonalVal w hc hqn
    have htri :=
      scalar_abs_sub_le_three
        (repDiagonalVal w hc m)
        ((w (repDiagonalIndex hc m)).val q)
        ((w (repDiagonalIndex hc n)).val q)
        (repDiagonalVal w hc n)
    have hsum := BishopC.le_add hab (BishopC.le_add hbc hcd)
    exact BishopC.le_trans htri
      (BishopC.le_trans hsum (repDiagonal_regular_budget_left m n))
  · have hnm : n ≤ m := by omega
    have hclose :
        RepCloseAtGauge (n + 6)
          (w (repDiagonalIndex hc m))
          (w (repDiagonalIndex hc n)) :=
      repCloseAtGauge_diagonal_indices hc
        (k := n + 6) (m := m) (n := n)
        (by unfold repDiagonalSlack; omega)
        (by unfold repDiagonalSlack; omega)
    rcases hclose with ⟨N, hN⟩
    let q : Nat := N + repDiagonalSample m + repDiagonalSample n
    have hqN : N ≤ q := by
      unfold q
      omega
    have hqm : repDiagonalSample m ≤ q := by
      unfold q
      omega
    have hqn : repDiagonalSample n ≤ q := by
      unfold q
      omega
    have hab :
        Le
          (COF.abs
            (repDiagonalVal w hc m -
              (w (repDiagonalIndex hc m)).val q))
          (eps (m + 5)) :=
      repDiagonalVal_same_rep_tail w hc hqm
    have hbc :
        Le
          (COF.abs
            ((w (repDiagonalIndex hc m)).val q -
              (w (repDiagonalIndex hc n)).val q))
          (eps (n + 6)) :=
      hN q hqN
    have hcd :
        Le
          (COF.abs
            ((w (repDiagonalIndex hc n)).val q -
              repDiagonalVal w hc n))
          (eps (n + 5)) :=
      same_rep_tail_to_repDiagonalVal w hc hqn
    have htri :=
      scalar_abs_sub_le_three
        (repDiagonalVal w hc m)
        ((w (repDiagonalIndex hc m)).val q)
        ((w (repDiagonalIndex hc n)).val q)
        (repDiagonalVal w hc n)
    have hsum := BishopC.le_add hab (BishopC.le_add hbc hcd)
    exact BishopC.le_trans htri
      (BishopC.le_trans hsum (repDiagonal_regular_budget_right m n))

/-- Bundled regular representative from the diagonal candidate. -/
def repDiagonalSeq
    (w : Nat → RegularSeq)
    (hc : CRealRepSequenceCauchyData w) : RegularSeq where
  val := repDiagonalVal w hc
  regular := repDiagonalVal_regular w hc





end BishopCReal

