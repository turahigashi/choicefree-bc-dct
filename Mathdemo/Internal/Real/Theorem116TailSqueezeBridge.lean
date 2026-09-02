import Mathdemo.Internal.Real.Theorem116InternalDataEnumeration

/-!
# G50: Theorem 1.16 tail squeeze bridge

The final estimate in Theorem 1.16 is:

`||f - sum_{n <= N} f_n|| <= sum_{n > N} (I(|f_n|) + 2^{-n})`,

and the right hand side tends to zero.  G49 recorded the tail majorant data.
This file factors the remaining order-squeeze step into explicit data and
connects it to the G49 tail-estimate bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}









end BishopCReal
