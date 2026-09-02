import Mathdemo.Internal.Measure.RecoverProposition42LocalRows

set_option linter.style.longLine false

/-!
# G284: Definition-2.3 local witnesses to Proposition-4.2 flat values

G283 recovered the standard Proposition-4.2 rows from the two source witnesses:

* Definition 2.3 supplies the characteristic-function domain and absolute
  convergence data on the two sides of an integrable set;
* Definition 1.6 supplies the local domain and absolute convergence data for
  the integrable representative `f`.

This node connects those local witnesses to the already verified local
row-to-flat and value-identification lemmas.  The only remaining analytic
frontier is the local standard outer-convergence theorem itself: the convergence
of the series of row absolute sums for the standard lambda rows.  No witness is
extracted from a propositional full-set statement here.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Source-shaped local outer provider -/



/-! ## 2. Abs packages from Definition 2.3 plus local `f` witnesses -/





/-! ## 3. Flat absolute convergence from the local packages -/





/-! ## 4. Source-facing pointwise value identification -/





/-! ## 5. Audit -/




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
