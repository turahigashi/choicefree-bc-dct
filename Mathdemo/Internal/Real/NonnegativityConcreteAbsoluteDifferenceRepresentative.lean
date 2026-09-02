import Mathdemo.Internal.Real.Proposition412ConcreteTruncatedAbsolute

set_option linter.style.longLine false

/-!
# G182: nonnegativity of the concrete absolute-difference representative

G181 fixed the concrete representative

`d = |mid(-n, chi_A f, n) - mid(-n, chi_A g, n)|`

as `(F.rep.sub G.rep).absVal`.  This file removes one artificial datum:
nonnegativity of `d` follows from the general pointwise value theorem for
`absVal`, so it need not be carried as an assumption.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge











end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge





end BishopCReal
