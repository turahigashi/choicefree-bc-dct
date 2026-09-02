import Mathdemo.Internal.Real.LateSamplePositivityTransportRegularSeq

set_option linter.style.longLine false

/-!
# G121: strict-backward transport for the remaining min monotonicity frontier

G118 reduced Theorem 1.18 property (4) to the line-735 left monotonicity of
`minSeqWith`.  G119 and G120 closed two supporting RegularSeq bridges.  This
file factors the remaining monotonicity target through the Bishop-style
contrapositive shape:

if a strict counterexample to `min x c <= min y c` can be transported backward
to a strict counterexample to `x <= y`, then the desired non-strict
`RegularSeqLe` monotonicity follows.

This avoids extracting representatives from a quotient and avoids any selector
from `Prop` positivity to data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- A Bishop-style contrapositive for the remaining line-735 min monotonicity.

The hypothesis is the genuine scalar/RegularSeq frontier: strict positivity of
`min x c - min y c` must imply strict positivity of `x - y`.  Once that strict
backward transport is available, the ordinary non-strict `RegularSeqLe`
monotonicity follows by contradiction against the definition of `RegularSeqLe`.
-/
theorem minSeqWith_monotone_left_regularSeqLe_of_strict_backward
    (A : ScalarMulArchimedeanData)
    (strict_backward :
      forall x y c : RegularSeq,
        regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) ->
          regularSeqLtProp y x)
    (x y c : RegularSeq)
    (hxy : RegularSeqLe x y) :
    RegularSeqLe (minSeqWith A x c) (minSeqWith A y c) := by
  intro hcounter
  have hstrict_min :
      regularSeqLtProp (minSeqWith A y c) (minSeqWith A x c) := by
    exact regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hyx : regularSeqLtProp y x :=
    strict_backward x y c hstrict_min
  exact regularSeqLe_not_lt_reverse_prop hxy hyx

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
