import Mathdemo.Internal.Measure.DataPFunRCarryingDCTRoute

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

/-- Level set `A_n = {x | f(x) >= alpha_n}` carried as direct data. -/
noncomputable def lemma_4_3_A_n_data
    (f : IntegrableRep S) (n : Nat) : BSet X :=
  let D := lemma_4_3_A_n_apart_data (S := S) f n
  thm36D_levelBSet f D.1

/-- Integrability of the data-carried level set, projected from the section 3 data theorem. -/
noncomputable def lemma_4_3_A_n_integrable_data
    (f : IntegrableRep S) (n : Nat) :
    IntegrableSet1 S (lemma_4_3_A_n_data (S := S) f n) :=
  let D := lemma_4_3_A_n_apart_data (S := S) f n
  (thm_3_6_forall_apart_measure f
    (COF.halfPow (R := R) (n + 1))
    (COF.halfPow (R := R) n)
    (halfPow_lt_succ n)
    (halfPow_pos (n + 1))
    D.1 D.2.1 D.2.2.1 D.2.2.2).1

end BishopC
