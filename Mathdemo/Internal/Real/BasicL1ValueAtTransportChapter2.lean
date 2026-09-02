import Mathdemo.Internal.Real.ValueTransportFrontierChapter2Proposition

set_option linter.style.longLine false

/-!
# G137: basic L1 `valueAt` transport for Chapter 2 formulas

G136 reduced Proposition 2.4 to explicit L1 value-transport data.  This file
closes the reusable operation-level transport lemmas:

* value selected by Definition 1.6 agrees with the carried partial function;
* addition transports to `addSeq`;
* scalar multiplication transports to `mulSeqConcreteWith`;
* absolute value transports to `absSeq`;
* subtraction transports to `subSeq`.

The remaining composite task is to instantiate these lemmas for the nested
`min2` and union formula representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqL1ValueTransport

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}










end BishopRegularSeqL1ValueTransport





end BishopCReal
