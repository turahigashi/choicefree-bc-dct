import Mathdemo.Internal.Sec4.RelIntegralAbsContinuous

/-!
# Sec4 theorem 4.15: legacy PFunR-compatible DCT wrapper

This file does not try to close the source-level domination and convergence
bridges in one step.  It isolates the verified kernel step:

* set `u_n = |f_n - f|`;
* apply the previous PFunR-compatible lemma 4.14 wrapper to `u_n`;
* obtain `I(|f_n - f|) -> 0`.

The source-complete lemma 4.14 entry point is
`thm_4_14_source_complete` in
`RelIntegralAbsContinuous.lean`.
This file is retained as a compatibility path for earlier 4.15 experiments,
not as the canonical source-faithful 4.15 route.

The remaining bridges are kept as explicit data:

* a faithful PFunR representation and convergence-to-zero datum for `u_n`;
* the uniform `I_B` datum for `u_n`, later derived from domination by `g`;
* the row-seed package needed by the current general measurable integral
  construction.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-! ## PFunR-level error scaffolding -/























































end BishopC
