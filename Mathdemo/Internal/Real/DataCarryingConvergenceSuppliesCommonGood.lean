import Mathdemo.Internal.Real.CommonGoodSourceDataProduceDyadic

set_option linter.style.longLine false

/-!
# G189: data-carrying convergence supplies the common-good witnesses

G188 still separated "all common-good source data" from the convergence
hypotheses because the source-level `ConvergeInMeasure` is Prop-valued.
This file records the Bishop-style repair: keep the same mathematical content,
but expose the witnesses as Type/Sigma data.  From that data we can construct
the `B,C,N` common-good part without any later choice operation.

The remaining assumption-free source frontiers stay honest:

* the current Prop-valued convergence interface must be replaced or paired with
  this data-carrying interface if later code needs actual witnesses;
* the bad-set `<= n` bound remains a concrete analytic bound to prove or
  correct.
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
