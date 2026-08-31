import Mathdemo.Internal.Real.COFOCAssemblyCauchySequenceRepresentativeData

/-!
# Cauchy-sequence representatives imply global representatives

`COFOCAssemblyCauchySequenceRepresentativeData` isolated a seemingly weaker representative principle:
representatives only for the terms of a Cauchy quotient sequence.  This file
closes the audit of that principle.

Every constant sequence is Cauchy in any `COFO`.  Therefore a provider of
representatives for all Cauchy sequences already gives a representative for
every quotient element by applying it to the constant sequence at that element.
So the `COFOCAssemblyCauchySequenceRepresentativeData` principle is a precise interface, but not a genuine
weakening of the previous global representative selector.
-/

namespace BishopCReal

open BishopC
open BishopCRat








end BishopCReal

