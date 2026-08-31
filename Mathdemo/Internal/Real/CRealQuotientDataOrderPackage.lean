import Mathdemo.Internal.Real.CRealQuotientCotransitivityDataBridge

/-!
# CReal quotient data-order package

`CRealQuotientCotransitivityDataBridge` closed the Type-valued cotransitivity split once quotient
representatives and positive-tail data are supplied explicitly.  This file
packages that idea as a data-carrying quotient order:

* the data order is `CRealQuotLTDataWitness`;
* it maps back to the existing Prop-valued `ltQuot`;
* it is irreflexive;
* it is cotransitive when a representative for the third point is supplied;
* it is preserved by adding a common left term when a representative for that
  common term is supplied.

This is still not the final `BishopC.COF CRealQuot` instance, because the live
`COF` interface stores `lt` as a `Prop`.  The remaining step is to decide how
the final COF layer will obtain the data witness needed by `lt_cotrans_data`
from that Prop-valued interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat











end BishopCReal

