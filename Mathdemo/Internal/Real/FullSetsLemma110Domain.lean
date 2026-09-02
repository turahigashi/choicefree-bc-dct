import Mathdemo.Internal.Real.SourceRepresentationMinF1After

/-!
# G43: full sets and the Lemma 1.10 domain bridge

Definition 1.9 says that a subset of `X` is full when it contains a countable
intersection of domains of integrable functions.  Lemma 1.10 then turns such a
countable intersection into the domain of a single integrable function.

This file introduces the witness-rich RegularSeq version of that layer.  The
deep construction in Lemma 1.10 is kept as an explicit bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}



end BishopRegularSeqIntegrableRep


namespace BishopRegularSeqFullSet

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}



end BishopRegularSeqFullSet







end BishopCReal
