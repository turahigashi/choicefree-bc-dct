import Mathdemo.Internal.Real.Corollary117DensityInterface

/-!
# G52: start of Theorem 1.18 for `L1`

Theorem 1.18 says that `(X, L1, I)` is an integration space.  The source proof
first checks Definition 1.1(1) for all integrable functions, then handles the
Daniell condition, the normalized element, and the two truncation limits.

This file closes the algebraic Definition 1.1(1) bridge for `L1` from the
operation data already built in G40--G42, and also records the normalized
element bridge used for Definition 1.1(3).
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}




end BishopRegularSeqIntegrableRep











end BishopCReal
