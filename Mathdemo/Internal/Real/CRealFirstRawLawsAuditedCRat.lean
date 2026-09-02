import Mathdemo.Internal.Real.CRealRegularSequenceLayerLiveCRat

/-!
# CReal first raw laws over the audited CRat seed

This file closes the first genuinely CReal-side proof obligations over the live
`CRat` scalar: reflexivity/symmetry of the raw Bishop equality relation and the
regularity/respect facts for negation.

It deliberately does not claim transitivity, addition, multiplication, or
completeness.  Those require the next dyadic triangle/reindexing layer.
-/

namespace BishopCReal

open BishopC
open BishopCRat



/-- Negation preserves regularity of representatives. -/
theorem neg_regular (x : RegularSeq) : RegularVal (negVal x.val) := by
  intro m n
  unfold negVal
  change Le (BishopCRat.CRat.absF (-x.val m - -x.val n)) (eps m + eps n)
  rw [show -x.val m - -x.val n = -(x.val m - x.val n) from by ring,
    scalarCOFOSeed.abs_neg (x.val m - x.val n)]
  exact x.regular m n

/-- Negation respects raw Bishop equality. -/
theorem neg_respects (x y : RegularSeq) (hxy : rel x y) :
    relVal (negVal x.val) (negVal y.val) := by
  intro n
  change Le (BishopCRat.CRat.absF (-x.val n - -y.val n)) (tol n)
  rw [show -x.val n - -y.val n = -(x.val n - y.val n) from by ring,
    scalarCOFOSeed.abs_neg (x.val n - y.val n)]
  exact hxy n



end BishopCReal

