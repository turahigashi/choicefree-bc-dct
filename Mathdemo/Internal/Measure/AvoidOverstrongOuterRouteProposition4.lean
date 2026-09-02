import Mathdemo.Internal.Measure.SideSpecificDef23Local

set_option linter.style.longLine false

/-!
# G286: avoid the overstrong outer route for Proposition 4.2 values

G285 narrowed the remaining outer-convergence surface to the side-specific
form.  Reading the source and the existing `prop_4_2_chi_f_rep_value` theorem
more carefully shows a sharper correction:

* to identify the value of the constructed representative `chi_A * f`, one
  does **not** need to derive the constructed representative's flat absolute
  convergence from only the `chi_A` and `f` representatives;
* the source-local proof works on the common full support of the three
  representatives: `chi_A`, `f`, and the newly constructed `chi_A * f`
  representative.

The last witness is not external choice data.  It is the local Definition-1.6
domain witness for the representative constructed by Proposition 4.2 itself.
Trying to reconstruct it only from the two input representatives forces the
unnecessary and too-strong row-outer frontier isolated in G284/G285.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Three-representative local witness -/



namespace Sec4Prop42ProductLocalWitness





end Sec4Prop42ProductLocalWitness

/-! ## 2. Definition-2.3 constructors for the two sides -/





/-! ## 3. Value identification without row-outer reconstruction -/





/-! ## 4. Audit -/




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
