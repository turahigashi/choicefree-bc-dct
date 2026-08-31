import Mathdemo.Internal.Real.RepresentativeClosenessCalculusDiagonalFrontier

/-!
# Diagonal representative candidate

The remaining `CRealRepDiagonalLimitCloseData` needs an actual representative
limit.  This file fixes the value-level candidate, using the monotone Cauchy
envelope from `RepresentativeClosenessCalculusDiagonalFrontier`:

```
L n = (w (envelope (n + 6))).val (n + 6)
```

The offset leaves dyadic budget for the later regularity and tail-closeness
proofs.  This file proves only the bookkeeping facts about the chosen envelope
indices and the same-representative tail estimate; it does not yet bundle a
`RegularSeq`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Fixed dyadic slack used by the current diagonal candidate. -/
def repDiagonalSlack : Nat := 6

/-- The representative index selected for diagonal value `n`. -/
def repDiagonalIndex {w : Nat → RegularSeq}
    (hc : CRealRepSequenceCauchyData w) (n : Nat) : Nat :=
  repCauchyEnvelope hc (n + repDiagonalSlack)

/-- The internal sample index selected for diagonal value `n`. -/
def repDiagonalSample (n : Nat) : Nat :=
  n + repDiagonalSlack

/-- Value-level diagonal candidate. -/
def repDiagonalVal (w : Nat → RegularSeq)
    (hc : CRealRepSequenceCauchyData w) (n : Nat) : Scalar :=
  (w (repDiagonalIndex hc n)).val (repDiagonalSample n)

/-- The selected diagonal representative index covers any Cauchy gauge up to
`n + repDiagonalSlack`. -/
theorem cmod_le_repDiagonalIndex_of_le
    {w : Nat → RegularSeq}
    (hc : CRealRepSequenceCauchyData w)
    {k n : Nat} (hkn : k ≤ n + repDiagonalSlack) :
    hc.cmod k ≤ repDiagonalIndex hc n := by
  exact cmod_le_repCauchyEnvelope hc hkn


/-- Two selected diagonal representative indices are Cauchy-close whenever both
selected envelopes cover the requested gauge. -/
theorem repCloseAtGauge_diagonal_indices
    {w : Nat → RegularSeq}
    (hc : CRealRepSequenceCauchyData w)
    {k m n : Nat}
    (hkm : k ≤ m + repDiagonalSlack)
    (hkn : k ≤ n + repDiagonalSlack) :
    RepCloseAtGauge k
      (w (repDiagonalIndex hc m))
      (w (repDiagonalIndex hc n)) := by
  exact repCloseAtGauge_envelope_indices hc hkm hkn

/-- The diagonal value at `n` is close to later samples of the same selected
representative. -/
theorem repDiagonalVal_same_rep_tail
    (w : Nat → RegularSeq)
    (hc : CRealRepSequenceCauchyData w)
    {n q : Nat} (hq : repDiagonalSample n ≤ q) :
    Le
      (COF.abs
        (repDiagonalVal w hc n -
          (w (repDiagonalIndex hc n)).val q))
      (eps (n + 5)) := by
  have hbase :
      Le
        (COF.abs
          ((w (repDiagonalIndex hc n)).val (repDiagonalSample n) -
            (w (repDiagonalIndex hc n)).val q))
        (eps (repDiagonalSample n) + eps q) :=
    (w (repDiagonalIndex hc n)).regular (repDiagonalSample n) q
  have hqeps : Le (eps q) (eps (repDiagonalSample n)) :=
    eps_le_of_le hq
  have hsum :
      Le (eps (repDiagonalSample n) + eps q)
        (eps (repDiagonalSample n) + eps (repDiagonalSample n)) :=
    BishopC.le_add (BishopC.le_refl (eps (repDiagonalSample n))) hqeps
  have hbudget :
      Le (eps (repDiagonalSample n) + eps q) (eps (n + 5)) := by
    have hsamp : repDiagonalSample n = n + 5 + 1 := by
      unfold repDiagonalSample repDiagonalSlack
      omega
    rwa [hsamp, eps_succ_add_self (n + 5)] at hsum
  exact BishopC.le_trans hbase hbudget

/-- Symmetric form of `repDiagonalVal_same_rep_tail`, often more convenient in
triangle estimates. -/
theorem same_rep_tail_to_repDiagonalVal
    (w : Nat → RegularSeq)
    (hc : CRealRepSequenceCauchyData w)
    {n q : Nat} (hq : repDiagonalSample n ≤ q) :
    Le
      (COF.abs
        ((w (repDiagonalIndex hc n)).val q -
          repDiagonalVal w hc n))
      (eps (n + 5)) := by
  have h := repDiagonalVal_same_rep_tail w hc hq
  rw [show (w (repDiagonalIndex hc n)).val q - repDiagonalVal w hc n =
      -(repDiagonalVal w hc n - (w (repDiagonalIndex hc n)).val q) from by ring]
  change Le
    (BishopCRat.CRat.absF
      (-(repDiagonalVal w hc n - (w (repDiagonalIndex hc n)).val q)))
    (eps (n + 5))
  rw [scalarCOFOSeed.abs_neg
    (repDiagonalVal w hc n - (w (repDiagonalIndex hc n)).val q)]
  exact h





end BishopCReal

