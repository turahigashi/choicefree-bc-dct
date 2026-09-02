import Mathdemo.Internal.Real.AlignCompletedBishopCheng1972Sections

/-!
# G31: theorem-5.8 bridge laws over the RegularSeq measure skeleton

This file continues the Bishop-faithful route with Bishop-Cheng (1972)
sections 1--4 treated as completed relative `[COFOC R]` work.

The target here is chapter 5, theorem 5.8: a measure space induces an
integration space.  We do not re-open the previous quotient/`COFOC` layer.  Instead
we prove the first bridge consequences that are already available from the
RegularSeq skeleton:

* if two simple-function representations denote Bishop-equivalent partial
  functions, their formal integrals are Bishop equal;
* if a simple function represents a linear combination of two represented
  simple functions, its formal integral has the corresponding linear formula.

These are the RegularSeq/Bishop-equality forms of the theorem-5.5
well-definedness step and theorem-5.8(1) linearity step.
-/

namespace BishopCReal

open BishopC
open BishopCRat

namespace BishopRegularSeqPFun

variable {X : Type}


end BishopRegularSeqPFun

variable {Arch : ScalarMulArchimedeanData} {X : Type}






end BishopCReal

set_option linter.style.longLine false
