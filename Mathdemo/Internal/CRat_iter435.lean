import Mathdemo.Internal.CRat_iter432

set_option linter.style.longLine false

/-!
# Stage A14.3: hardness-4 frontier discharge node

This additive file keeps the 4.6/4.7 interfaces intact and closes the
4.7 cutoff-bound frontier once the required cutoff-to-dominator order data is
carried explicitly.  It does not add any selector-based ingredient.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-- Point order data over the common full domain of each cutoff representative
and the dominating representative.  This is exactly the input needed by
`prop_1_11` to turn point order into integral order. -/
structure Cor47CutoffLeDominatingRepData (f : DataPFunR X R)
    (hm : IsMeasurableData S f) (g : IntegrableRep S)
    (A : BSet X) (hA : IntegrableSet1 S A) : Type _ where
  cutoff_le_g :
    forall n x,
      forall (hcutDom : (thm46CutoffSeq hm A hA n).MemAt x)
        (hgDom : g.MemAt x),
      forall
        (hcut : RSeq.SeriesSum
          (fun m => (thm46CutoffSeq hm A hA n).valueAt x hcutDom m))
        (hg : RSeq.SeriesSum (fun m => g.valueAt x hgDom m)),
        Le hcut.sum hg.sum

/-- Discharge of the 4.7 cutoff integral bound from point order, using
`prop_1_11` on the common full domain. -/
theorem cor_4_7_dominates_cutoffs_discharged
    (f : DataPFunR X R) (hm : IsMeasurableData S f) (g : IntegrableRep S)
    (A : BSet X) (hA : IntegrableSet1 S A)
    (D : Cor47CutoffLeDominatingRepData (S := S) f hm g A hA) :
    forall n, Le ((thm46CutoffSeq hm A hA n).integral) g.integral := by
  intro n
  exact prop_1_11
    (isFull_inter (thm46CutoffSeq hm A hA n).domain_isFull g.domain_isFull)
    (thm46CutoffSeq hm A hA n) g
    (fun x _hx hcutDom hgDom hcut hg =>
      D.cutoff_le_g n x hcutDom hgDom hcut hg)

/-- Rebuild the 4.7 frontier package with `dominates_cutoffs` supplied by the
discharge lemma above.  The remaining 4.6 MCT frontier data is passed through. -/
def cor_4_7_frontier_data_from_discharged_cutoffs
    (f : DataPFunR X R) (hm : IsMeasurableData S f) (g : IntegrableRep S)
    (A : BSet X) (hA : IntegrableSet1 S A)
    (h_g_nonneg : RepNonneg g)
    (Dle : Cor47CutoffLeDominatingRepData (S := S) f hm g A hA)
    (D46 : Thm46MCTFrontierData (S := S) f hm A hA g.integral) :
    Cor47DominatedFrontierData (S := S) f hm g A hA where
  g_nonneg := h_g_nonneg
  dominates_cutoffs := cor_4_7_dominates_cutoffs_discharged
    (S := S) f hm g A hA Dle
  mct_data := D46

structure StageA14FrontierDischargeAudit : Type where
  dominates_cutoffs_via_prop_1_11 : Nat
  needs_explicit_cutoff_order_data : Nat
  represents_limit_from_current_data : Nat
  needs_located_exhaustion_data : Nat

def stageA14FrontierDischargeAudit : StageA14FrontierDischargeAudit where
  dominates_cutoffs_via_prop_1_11 := 1
  needs_explicit_cutoff_order_data := 1
  represents_limit_from_current_data := 0
  needs_located_exhaustion_data := 1

end BishopC
