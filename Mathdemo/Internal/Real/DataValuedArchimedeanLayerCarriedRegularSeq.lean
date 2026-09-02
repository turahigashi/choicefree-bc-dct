import Mathdemo.Internal.Real.PositiveInverseArchimedeanOrderLayerRegularSeq

/-!
# Data-valued Archimedean layer for carried RegularSeq positivity

`PositiveInverseArchimedeanOrderLayerRegularSeq` left the RegularSeq Archimedean statement at Prop level.  The
source-shaped data route can do better when positivity is carried explicitly:
from `PosEventuallyData x`, the dyadic lower bound is read directly from the
tail witness.  No strict-order search is needed for this data-indexed branch.

The remaining selector boundary is narrower: converting an arbitrary
Prop-valued positivity proof back into `PosEventuallyData`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A carried positive-tail witness directly supplies a dyadic constant below
the representative. -/
def regularSeqArchimedeanPositiveData
    {x : RegularSeq} (hx : PosEventuallyData x) :
    Sigma (fun k : Nat => regularSeqLtData (constSeq (eps k)) x) := by
  refine ⟨hx.k + 1, ?_⟩
  refine
    { k := hx.k + 1
      N := hx.N
      tail_pos := ?_ }
  intro n hn
  have hxpos := hx.tail_pos (n + 1) (Nat.le_trans hn (Nat.le_succ n))
  change COF.lt (eps hx.k) (x.val (n + 1)) at hxpos
  have hshift : COF.lt (eps (hx.k + 1))
      (x.val (n + 1) - eps (hx.k + 1)) := by
    have t := COF.lt_add_left (-(eps (hx.k + 1))) hxpos
    rwa [← eps_succ_add_self hx.k,
      show -(eps (hx.k + 1)) + (eps (hx.k + 1) + eps (hx.k + 1)) =
          eps (hx.k + 1)
        from by ring,
      show -(eps (hx.k + 1)) + x.val (n + 1) =
          x.val (n + 1) - eps (hx.k + 1)
        from by ring] at t
  change COF.lt (eps (hx.k + 1))
    (x.val (n + 1) - eps (hx.k + 1))
  exact hshift


/-- Data form of the representative multiplicative Archimedean bound:
the witness is the standard dyadic bound, not a searched natural number. -/
def regularSeqMulArchimedean_const_data
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    { m : Nat //
      ¬ regularSeqLtProp oneSeq
        (mulSeqConcreteWith A (absSeq x) (constSeq (eps m))) } := by
  refine ⟨standardBoundWith A x, ?_⟩
  change ¬ PosEventually
    (subSeq
      (mulSeqConcreteWith A (absSeq x)
        (constSeq (eps (standardBoundWith A x))))
      oneSeq)
  exact not_posEventually_abs_mul_standard_sub_one_with A x

/-- Data-valued Archimedean layer available on the RegularSeq route when
positive evidence is kept as data. -/
structure CRealRegularSeqArchimedeanDataLayer
    (A : ScalarMulArchimedeanData) : Type 1 where
  archimedeanProp : CRealRegularSeqArchimedeanPropLayer A
  archimedean_posData :
    ∀ {x : RegularSeq}, PosEventuallyData x →
      Sigma (fun k : Nat => regularSeqLtData (constSeq (eps k)) x)
  archimedean_posProp :
    ∀ {x : RegularSeq}, PosEventuallyData x →
      ∃ k : Nat, regularSeqLtProp (constSeq (eps k)) x
  mul_archimedean_const_data :
    ∀ x : RegularSeq,
      { m : Nat //
        ¬ regularSeqLtProp oneSeq
          (mulSeqConcreteWith A (absSeq x) (constSeq (eps m))) }
  carried_positive_data_needs_no_order_decision : Prop
  prop_to_data_conversion_remains_selector_boundary : Prop


/-- RegularSeq package after promoting carried positivity to data-valued
Archimedean lower bounds. -/
structure CRealRegularSeqDataCOFOCArchDataPackage
    (A : ScalarMulArchimedeanData) : Type 1 where
  archInvPackage : CRealRegularSeqDataCOFOCArchInvPackage A
  archimedeanData : CRealRegularSeqArchimedeanDataLayer A
  positive_inputs_are_data_indexed : Prop
  dyadic_lower_bound_witness_is_extracted_from_data : Prop
  no_decidable_strict_order_used_in_regularseq_data_branch : Prop




end BishopCReal

set_option linter.style.longLine false

