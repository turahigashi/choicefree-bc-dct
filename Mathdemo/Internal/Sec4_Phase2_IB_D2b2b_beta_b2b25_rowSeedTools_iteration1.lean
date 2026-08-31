import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b24_rowAbsHelpers_iteration1
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b16_primitivePackTools_iteration1

/-!
# Sec4 Phase2-D2b2bβ-b2b25: row-seed tools for the remaining atoms

`b2b22` reduced the value bridge for the general measurable integral to
`Sec4Prop42RemainingAtomTools`.  `b2b24` supplies the per-row abs witness once
we have a characteristic abs witness for `A` and an `f` abs witness.

This file packages the next narrower interface:

* recover `f` abs from row abs on `A.S1`;
* supply `χ_A` abs on `A.S1` from `f` abs;
* supply the corrected abs-outer row series on `A.S1`;
* supply corrected packed rows on `A.S2`.

The useful new reduction here is the positive-side row construction via
`b2b24`; the negative side stays at the corrected packed-row interface.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-- Characteristic abs witness on the positive side of `A`, from an `f` abs
  witness.  This is exactly the extra datum needed by `b2b24` to build rows. -/
def Sec4Prop42ChiAbsOnS1OfFAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    Sec4RepAbsAt f x →
    Sec4RepAbsAt hA.rep x


/-- Corrected abs-outer row-sum witness on `A.S1`, once per-row abs witnesses
  are known. -/
def Sec4Prop42AbsOuterOnS1OfRows
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    ∀ hfabs : Sec4RepAbsAt f x,
    ∀ hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x,
      Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x hrows


/-- The row-seed interface below `Sec4Prop42RemainingAtomTools`.

Compared with `remainingAtoms`, the positive-side pack is split into
characteristic abs, row construction, and abs-outer construction.
-/
def Sec4Prop42RowSeedTools
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn)
    (PProd (Sec4Prop42ChiAbsOnS1OfFAbs (S := S) f hnn)
      (PProd (Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn)
        (Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn)))


namespace Sec4Prop42RowSeedTools

def mk
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (fabs_of_rows_s1 : Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn)
    (chi_abs_on_s1_of_fabs : Sec4Prop42ChiAbsOnS1OfFAbs (S := S) f hnn)
    (abs_outer_on_s1_of_rows : Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn)
    (pack_on_s2 : Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn) :
    Sec4Prop42RowSeedTools (S := S) f hnn :=
  ⟨fabs_of_rows_s1, chi_abs_on_s1_of_fabs, abs_outer_on_s1_of_rows, pack_on_s2⟩


def fabs_of_rows_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn :=
  T.1


def chi_abs_on_s1_of_fabs
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4Prop42ChiAbsOnS1OfFAbs (S := S) f hnn :=
  T.2.1


def abs_outer_on_s1_of_rows
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn :=
  T.2.2.1


def pack_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn :=
  T.2.2.2


end Sec4Prop42RowSeedTools

/-! ## Build remaining atoms from row seeds -/

/-- Positive-side per-row witnesses from characteristic abs and `b2b24`. -/
noncomputable def sec4_rowsOnS1_of_rowSeedTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4Prop42RowsOnS1OfFAbs (S := S) f hnn := by
  intro A hA x hxA hfabs
  exact sec4_lambdaRowAbs_of_chiF_fabs A hA f (prop_4_2_n_k f) x
    (Sec4Prop42RowSeedTools.chi_abs_on_s1_of_fabs T A hA x hxA hfabs)
    hfabs


/-- Positive-side corrected packed rows from row seeds. -/
noncomputable def sec4_packOnS1_of_rowSeedTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) f hnn := by
  intro A hA x hxA hfabs
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x :=
    sec4_rowsOnS1_of_rowSeedTools f hnn T A hA x hxA hfabs
  let houter : Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x hrows :=
    Sec4Prop42RowSeedTools.abs_outer_on_s1_of_rows T A hA x hxA hfabs hrows
  exact ⟨hrows, houter⟩


/-- The `remainingAtoms` package from row seeds. -/
noncomputable def sec4_remainingAtoms_of_rowSeedTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4Prop42RemainingAtomTools (S := S) f hnn :=
  Sec4Prop42RemainingAtomTools.mk
    (Sec4Prop42RowSeedTools.fabs_of_rows_s1 T)
    (sec4_packOnS1_of_rowSeedTools f hnn T)
    (Sec4Prop42RowSeedTools.pack_on_s2 T)


/-! ## Final bridges from row seeds -/

noncomputable def sec4_genIBValueBridge_of_rowSeedTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_remainingAtoms B hB f hnn
    (sec4_remainingAtoms_of_rowSeedTools f hnn T)


theorem sec4_genRelIntegral_eq_relIntegral_of_rowSeedTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_remainingAtoms C hC f hnn
    (sec4_remainingAtoms_of_rowSeedTools f hnn T)


noncomputable def sec4_genIBConsistencyBridge_of_rowSeedTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4Prop42RowSeedTools (S := S) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_remainingAtoms C hC f hnn
    (sec4_remainingAtoms_of_rowSeedTools f hnn T)


end BishopC
