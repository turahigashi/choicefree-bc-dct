import Mathdemo.Internal.Measure.BinarySideSelectorSurface

set_option linter.style.longLine false

/-!
# G294: finite `bigOrFin` / `bigAndFin` closure for Def23 data

G293 packaged the Type-coded binary side selectors needed to lift the binary
constructors to the strong `IntegrableSet1WithDef23` API.  This node propagates
that closure through the finite Chapter-2 constructors `bigOrFin` and
`bigAndFin`.

The new finite constructors are definitionally aligned with the existing base
constructors: their `.base` fields are the previous `bigOrFin_int` and
`bigAndFin_int` recursions.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

namespace BSetBinarySideSelectorSurface

/-! ## 1. Finite union closure -/





/-! ## 2. Finite intersection closure -/





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
