import Mathdemo.Internal.Measure.FiniteBigOrFinBigAndFinClosureDef23Data

set_option linter.style.longLine false

/-!
# G295: finite difference closure for Def23 data

G294 gave strong Definition-2.3 data for the finite approximants
`bigOrFin A n` and `bigAndFin A n`.  This node adds the corresponding finite
step-difference closures:

* `(A_0 ∪ ... ∪ A_{n+1}) - (A_0 ∪ ... ∪ A_n)`;
* `(A_0 ∩ ... ∩ A_n) - (A_0 ∩ ... ∩ A_{n+1})`.

These are the finite set-level counterparts of the increment/decrement terms
used around Proposition 2.10.  As in G293-G294, the construction is conditional
on the explicit `BSetBinarySideSelectorSurface`; this file does not construct
that surface and does not extract Type data from raw Prop membership.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

namespace BSetBinarySideSelectorSurface

/-! ## 1. Finite union step differences -/





/-! ## 2. Finite intersection step differences -/





end BSetBinarySideSelectorSurface

/-! ## 3. Audit -/




end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route



end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
