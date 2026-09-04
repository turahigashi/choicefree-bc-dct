import Mathdemo.Internal.Real.OrderChainingTheorem1184
/-!
# G60: line 734 reduction through the integral of the difference

G59 identified the source middle term on lines 734--735 as
`I(|min(f,n)-min(g,n)|)`.  This file closes the algebraic identification
needed for line 734: the source left side is the absolute value of the
integral of the explicit `L1` difference representative.

The analytic estimate `|I(h)| <= I(|h|)` is kept as its own source-level
bridge, so the remaining frontier is stated at the right level.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Multiplication by the representative `-1` agrees with additive inverse. -/
theorem mulSeq_neg_one_left_eventually_neg
    (Arch : ScalarMulArchimedeanData)
    (x : RegularSeq) :
    relEventually
      (mulSeqConcreteWith Arch (negSeq oneSeq) x)
      (negSeq x) := by
  have hmul :
      relEventually
        (mulSeqConcreteWith Arch (negSeq oneSeq) x)
        (negSeq (mulSeqConcreteWith Arch oneSeq x)) :=
    bounded_mul_neg_left_eventually_with Arch oneSeq x
  have hone :
      relEventually (mulSeqConcreteWith Arch oneSeq x) x :=
    mulSeqConcrete_one_left_eventually Arch x
  have hneg :
      relEventually
        (negSeq (mulSeqConcreteWith Arch oneSeq x))
        (negSeq x) :=
    negSeq_respects_eventually
      (mulSeqConcreteWith Arch oneSeq x) x hone
  exact
    relEventually_trans
      (mulSeqConcreteWith Arch (negSeq oneSeq) x)
      (negSeq (mulSeqConcreteWith Arch oneSeq x))
      (negSeq x)
      hmul
      hneg

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}


end BishopRegularSeqIntegrableRep

/-- Non-strict order is stable under eventual equality on the left side. -/
theorem regularSeqLe_of_left_eventual
    {x x' y : RegularSeq}
    (hxx : relEventually x x')
    (hle : RegularSeqLe x' y) :
    RegularSeqLe x y := by
  intro hcounter
  have hbase :
      relEventually (subSeq y x) (subSeq y x') :=
    subSeq_respects_eventually
      y y x x'
      (relEventually_refl y)
      hxx
  have hneg :
      relEventually
        (subSeq zeroSeq (subSeq y x))
        (subSeq zeroSeq (subSeq y x')) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      (subSeq y x) (subSeq y x')
      (relEventually_refl zeroSeq)
      hbase
  exact
    hle
      (posEventually_respects
        (subSeq zeroSeq (subSeq y x))
        (subSeq zeroSeq (subSeq y x'))
        hneg
        hcounter)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}







end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
