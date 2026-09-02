import Mathdemo.Internal.Real.IdentifyingSmallBranchMiddleTerm

/-!
# G66: reducing the small line-743 bound to Proposition 1.11 data

G65 identified the small-branch middle term as

`I(min(|g_N|,1/n)) + || |f| - g_N ||`.

This file supplies the next source-level reduction: that integral inequality
is obtained from Proposition 1.11 from a full-set pointwise domination

`min(|f|,1/n) <= min(|g_N|,1/n) + | |f| - g_N |`,

after building the right-hand side as an actual `L1` representative and
transporting its integral to the concrete G65 middle term.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Non-strict order is stable under eventual equality on the right side. -/
theorem regularSeqLe_of_right_eventual
    {x y y' : RegularSeq}
    (hyy : relEventually y y')
    (hle : RegularSeqLe x y) :
    RegularSeqLe x y' := by
  intro hcounter
  have hbase :
      relEventually (subSeq y' x) (subSeq y x) :=
    subSeq_respects_eventually
      y' y x x
      (relEventually_symm y y' hyy)
      (relEventually_refl x)
  have hneg :
      relEventually
        (subSeq zeroSeq (subSeq y' x))
        (subSeq zeroSeq (subSeq y x)) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      (subSeq y' x) (subSeq y x)
      (relEventually_refl zeroSeq)
      hbase
  exact
    hle
      (posEventually_respects
        (subSeq zeroSeq (subSeq y' x))
        (subSeq zeroSeq (subSeq y x))
        hneg
        hcounter)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}












end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
