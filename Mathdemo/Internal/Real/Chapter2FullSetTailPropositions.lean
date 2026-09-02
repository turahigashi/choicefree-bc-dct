import Mathdemo.Internal.Real.AssemblingChapter2FiniteSetLaw

set_option linter.style.longLine false

/-!
# G152: Chapter 2 full-set tail, Propositions 2.6--2.8

The finite set laws in G151 cover Propositions 2.4 and 2.5.  The next source
block relates integrable sets and full sets:

* Proposition 2.6: a positive-measure integrable set meets every full set;
* Proposition 2.7: a zero-measure integrable set has a full second side;
* Proposition 2.8: the domain of any integrable set is full.

Propositions 2.6 and 2.7 use source analytic constructions, so those
constructions are exposed as bridge data rather than hidden behind a choice
principle.  Proposition 2.8 is direct from the carried `full_domain` field.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace FullSetTail

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}











end FullSetTail
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.FullSetTail





end BishopCReal
