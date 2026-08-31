import Mathdemo.Internal.Real.RepresentativeCarryingCompletenessRepFreeDecidable

/-!
# COFOC assembly from Cauchy-sequence representative data

`RepresentativeCarryingCompletenessRepFreeDecidable` closed representation-carrying completeness for the
representative-free decidable-order `COFO` branch.  The remaining gap to the
opaque `COFOC.complete` field is exactly representative supply for an arbitrary
Cauchy quotient sequence.

This file isolates that weaker and more precise principle.  Instead of asking
for a global representative selector for every quotient element, it asks only
for representatives of the terms of the Cauchy sequence currently being
completed.  Given that data, the `RepresentativeCarryingCompletenessRepFreeDecidable` completeness theorem assembles a
live `BishopC.COFOC CRealQuot` record for the rep-free decidable branch.
-/

namespace BishopCReal

open BishopC
open BishopCRat










end BishopCReal

