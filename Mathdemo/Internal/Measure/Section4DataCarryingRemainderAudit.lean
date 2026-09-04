import Mathdemo.Internal.Real.Proposition24MeasureIdentityLocal
import Mathdemo.Internal.BishopSec3_Profile
import Mathdemo.Internal.BishopSec4_Convergence
import Mathdemo.Internal.Sec4.ValueConsistency
import Mathdemo.Internal.Sec4.RemainingAtomsAssembly
import Mathdemo.Internal.Sec4.PrimitivePackTools
import Mathdemo.Internal.Sec4.Preservation
import Mathdemo.Internal.Sec4GenIB
import Mathdemo.Internal.Sec4.CoverChiTelescopeBridge
import Mathdemo.Internal.Sec4.LayerTelescope
import Mathdemo.Internal.Sec4.CaseRowTools
import Mathdemo.Internal.Sec4.AbsOuterPack
import Mathdemo.Internal.Sec4.RowToFlat
import Mathdemo.Internal.Sec4.StepAbs
import Mathdemo.Internal.Sec4.DichotomyData
import Mathdemo.Internal.Sec4.InternalTools
import Mathdemo.Internal.Sec4.Row1Switch
import Mathdemo.Internal.Sec4.DataCases
set_option linter.style.longLine false

/-!
# Stage A11: section 4 data-carrying remainder audit

This additive node closes the level-set data used by lemma 4.3 without passing
through the previous Prop-valued level-set witness.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

noncomputable def lemma_4_3_A_n_apart_data
    (f : IntegrableRep S) (n : Nat) :=
  thm36B1_apart_data
    (lemma35_exceptionSeq
      (thm36A2_profile f
        (COF.halfPow (R := R) (n + 1))
        (COF.halfPow (R := R) n)
        (halfPow_lt_succ n)
        (halfPow_pos (n + 1))))
    (halfPow_lt_succ n)



end BishopC
