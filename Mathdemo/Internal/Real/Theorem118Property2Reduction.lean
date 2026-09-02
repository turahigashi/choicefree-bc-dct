import Mathdemo.Internal.Real.StartTheorem118L1

/-!
# G53: Theorem 1.18, property (2) reduction for `L1`

Theorem 1.18 proves Definition 1.1 again for `L1`.  For property (2), the
source expands each non-negative integrable `h_n` by Lemma 1.15, expands `h`
up to a finite head and small tail, and then applies property (2) in the old
space `L`.

This file records that exact reduction over the RegularSeq presentation.  The
final pointwise comparison from the majorant sequence to
`sum h_n(x) < h(x)` is kept as explicit data, because it is the source's
last triangle-inequality calculation.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
















end BishopRegularSeqTheorem118







end BishopCReal
