import Mathdemo.Internal.Real.Proposition412ChiMembershipData

set_option linter.style.longLine false

/-!
# G180: Proposition 4.12 representative witnesses to chi-membership data

G179 reduced the `A-E` side of Proposition 4.12 to pointwise
chi-membership data.  This file connects that data to the existing
representative value API:

* `IntegrableSet1.valid` supplies `chi = 0/1` and membership information;
* `prop_4_2_complement_value` supplies the complement value
  `(1 - chi_E) * d`;
* `prop_4_2_chi_f_rep_value` supplies the bad-set value
  `chi_(A-E) * d`.

The remaining source frontier is now the concrete construction of the
truncated absolute-difference representative and its outside-`A` zero
witness.
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
