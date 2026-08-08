import Mathdemo.Internal.CRat_iter91

/-!
# Representative diagonal limit close data

`CRat_iter91` proved that the diagonal candidate is a regular representative.
This file proves the remaining tail-closeness estimate and bundles the actual
`CRealRepDiagonalLimitCloseData` required by `CRat_iter88`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A regular representative has small tail oscillation once the sample index is
far enough beyond the requested gauge. -/
theorem regular_tail_bound_at_gauge
    (x : RegularSeq) {k p q : Nat}
    (hkp : k + 4 ≤ p) (hpq : p ≤ q) :
    Le (COF.abs (x.val p - x.val q)) (eps (k + 3)) := by
  have hbase :
      Le (COF.abs (x.val p - x.val q)) (eps p + eps q) :=
    x.regular p q
  have hp : Le (eps p) (eps (k + 4)) :=
    eps_le_of_le hkp
  have hq : Le (eps q) (eps (k + 4)) :=
    eps_le_of_le (Nat.le_trans hkp hpq)
  have hsum : Le (eps p + eps q) (eps (k + 4) + eps (k + 4)) :=
    BishopC.le_add hp hq
  have hbudget : Le (eps p + eps q) (eps (k + 3)) := by
    rwa [show k + 4 = k + 3 + 1 from by omega,
      eps_succ_add_self (k + 3)] at hsum
  exact BishopC.le_trans hbase hbudget

/-- Three `k+3` errors fit into the requested `k+1` tail gauge. -/
theorem repDiagonal_tail_close_budget (k : Nat) :
    Le (eps (k + 3) + (eps (k + 3) + eps (k + 3))) (eps (k + 1)) := by
  have hleft : Le (eps (k + 3)) (eps (k + 2)) :=
    eps_le_of_le (by omega)
  have hpair : Le (eps (k + 3) + eps (k + 3)) (eps (k + 2)) := by
    rw [show k + 3 = k + 2 + 1 from by omega,
      eps_succ_add_self (k + 2)]
    exact BishopC.le_refl (eps (k + 2))
  have hsum := BishopC.le_add hleft hpair
  rwa [show k + 2 = k + 1 + 1 from by omega,
    eps_succ_add_self (k + 1)] at hsum

/-- The regular diagonal candidate is the representative limit of the
representative-Cauchy sequence. -/
theorem repDiagonalSeq_close_to_limit
    (w : Nat → RegularSeq)
    (hc : CRealRepSequenceCauchyData w) :
    ∀ k n : Nat, repCauchyEnvelope hc (k + 3) ≤ n →
      RepCloseAtGauge (k + 1) (w n) (repDiagonalSeq w hc) := by
  intro k n hn
  refine ⟨k + 4, ?_⟩
  intro p hp
  have hn_cmod : hc.cmod (k + 3) ≤ n :=
    Nat.le_trans (cmod_le_repCauchyEnvelope hc (Nat.le_refl _)) hn
  have hidx_cmod : hc.cmod (k + 3) ≤ repDiagonalIndex hc p :=
    cmod_le_repDiagonalIndex_of_le hc (by unfold repDiagonalSlack; omega)
  have hclose :
      RepCloseAtGauge (k + 3) (w n) (w (repDiagonalIndex hc p)) :=
    hc.close_eventually (k + 3) n (repDiagonalIndex hc p)
      hn_cmod hidx_cmod
  rcases hclose with ⟨N, hN⟩
  let q : Nat := N + p + repDiagonalSample p
  have hqN : N ≤ q := by
    unfold q
    omega
  have hpq : p ≤ q := by
    unfold q
    omega
  have hsampleq : repDiagonalSample p ≤ q := by
    unfold q
    omega
  have hab :
      Le (COF.abs ((w n).val p - (w n).val q)) (eps (k + 3)) :=
    regular_tail_bound_at_gauge (w n) hp hpq
  have hbc :
      Le
        (COF.abs
          ((w n).val q -
            (w (repDiagonalIndex hc p)).val q))
        (eps (k + 3)) :=
    hN q hqN
  have hcd :
      Le
        (COF.abs
          ((w (repDiagonalIndex hc p)).val q -
            (repDiagonalSeq w hc).val p))
        (eps (k + 3)) := by
    change
      Le
        (COF.abs
          ((w (repDiagonalIndex hc p)).val q -
            repDiagonalVal w hc p))
        (eps (k + 3))
    exact BishopC.le_trans
      (same_rep_tail_to_repDiagonalVal w hc hsampleq)
      (eps_le_of_le (by omega))
  have htri :=
    scalar_abs_sub_le_three
      ((w n).val p)
      ((w n).val q)
      ((w (repDiagonalIndex hc p)).val q)
      ((repDiagonalSeq w hc).val p)
  have hsum := BishopC.le_add hab (BishopC.le_add hbc hcd)
  exact BishopC.le_trans htri
    (BishopC.le_trans hsum (repDiagonal_tail_close_budget k))

/-- The representative diagonal-limit close data required by `CRat_iter88`. -/
def cRealRepDiagonalLimitCloseData : CRealRepDiagonalLimitCloseData where
  limit := repDiagonalSeq
  lmod := fun _w hc k => repCauchyEnvelope hc (k + 3)
  close_to_limit := by
    intro w hc k n hn
    exact repDiagonalSeq_close_to_limit w hc k n hn

/-- Conditional `COFOC` assembly with the representative diagonal frontier now
closed.  The remaining hypotheses are the previously isolated global
representative witness, strict-order decidability fork, and strict-order data
extraction. -/
@[reducible] def cRealQuotCOFOCWithPositiveInverseDecidableClosedDiagonal
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (hdec : CRealQuotLTDecidable)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    BishopC.COFOC CRealQuot :=
  cRealQuotCOFOCWithPositiveInverseDecidableOfRepDiagonalClose
    A rep hdec ltDataOf cRealRepDiagonalLimitCloseData

/-- Frontier after the representative diagonal construction itself is closed. -/
structure CRealQuotAfterRepDiagonalClosedFrontier : Type where
  remove_global_rep_witness : Prop
  remove_decidable_order_fork : Prop
  remove_lt_data_extraction_argument : Prop

def cRealQuotAfterRepDiagonalClosedFrontier :
    CRealQuotAfterRepDiagonalClosedFrontier where
  remove_global_rep_witness := True
  remove_decidable_order_fork := True
  remove_lt_data_extraction_argument := True

end BishopCReal

