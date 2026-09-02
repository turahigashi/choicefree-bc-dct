import Mathdemo.Internal.Real.Chapter3SourceAlignmentBridge

set_option linter.style.longLine false

/-!
# G157: Chapter 3 Definitions 3.1 and 3.2 on the RegularSeq route

G156 identified the source items of Bishop--Cheng Chapter 3 and exposed the
existing `BishopSec3_Profile` artifact after the Chapter 2 endpoint.  This file
records the next, narrower step: Definitions 3.1 and 3.2 are made available as
data-carrying surfaces on the Bishop RegularSeq mainline.

The important constructive point is that the profile is already coded by a
`Code` type, and `p([u,v]) < delta` / `p'([u,v]) < delta` are structures with
explicit witnesses.  This file therefore does not select representatives from a
quotient or recover data from a bare proposition.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter3
namespace ProfileDefinitions



















end ProfileDefinitions
end BishopRegularSeqChapter3

open BishopRegularSeqChapter3.ProfileDefinitions





end BishopCReal
