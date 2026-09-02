import Mathdemo.Internal.Real.SourceLevelProp412Wrapper

set_option linter.style.longLine false

/-!
# G216: Bishop/Bridges located supremum data for Chapter 4.5

Bishop-Bridges (1985) Chapter 2, Definition 4.2 defines a supremum not merely by
order-theoretic least-upper-bound minimality, but by upper-boundedness plus
points of the set arbitrarily close from below.  The previous Chapter 4 frontier
`RangeSupremum` kept only the order-theoretic Prop layer.

This increment adds the Bishop-facing data structure.  The direction used in
the constructive development is:

`LocatedRangeSupremum -> RangeSupremum`

and not the reverse.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46












end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46



end BishopCReal
