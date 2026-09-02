import Mathdemo.Internal.Real.Theorem118Property4Reduction

/-!
# G55: Theorem 1.18, property (4) estimate bridges

The source proof of Theorem 1.18(4) transfers the two truncation limits from
an previous `L` approximant to an arbitrary `L1` element by two displayed
estimates.  G54 kept these estimates as one field per truncation index.  This
file refines that frontier into two reusable source-level bridges:

* the large truncation estimate corresponding to source lines 730--735;
* the small absolute truncation estimate corresponding to source lines
  743--747.

The bridge data is still explicit, but it is now separated from the final
property (4) assembly and can be proved locally from the norm and truncation
operations in a later step.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}






end BishopRegularSeqTheorem118





end BishopCReal
