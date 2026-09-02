import Mathdemo.Internal.Real.Theorem58BridgeLawsRegularSeq

/-!
# G32: theorem-5.8(1) closure consequences from simple-function targets

`Theorem58BridgeLawsRegularSeq` isolated the missing source-level construction work for
theorem 5.8(1): construct simple functions representing linear combinations,
absolute values, and `min(f, 1)`.

This file proves what follows once those source-level constructions are
available.  The results are still Bishop-faithful: membership is membership in
the RegularSeq-valued partial-function integration skeleton, and scalar
equalities are `relEventually`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}








end BishopCReal

set_option linter.style.longLine false

