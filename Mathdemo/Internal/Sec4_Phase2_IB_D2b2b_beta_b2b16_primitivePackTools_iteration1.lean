import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b15_packTools_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b16: primitive row/outer package for the final pack tools

The b2b15 kernel response confirms that b2b13→b2b14→b2b15 are all
hardness-4 clean and that the only remaining package is
`Sec4ChiFCasePackTools f hnn`.

This file pushes that package one layer deeper while also closing one of its
four fields in a useful way: on `A.S2`, once the per-row abs witnesses are
available, the outer row-sum witness is automatic from the already verified
row-zero theorem `sec4_lambdaRowZeroOnS2`.

The remaining primitives after this file are exactly the local
`prop_4_2_lambda_k` row machinery:

* build rows and an outer row-sum on `A.S1` from `f` abs;
* build rows on `A.S2`;
* extract `f` abs from a packed row witness on `A.S1`;
* build the completed flat abs from a packed row witness.

All cover/dichotomy/telescope assembly remains discharged by prior chunks.
-/

#check Sec4ChiFCasePackTools
#check Sec4LambdaRowsPackAt
#check Sec4LambdaRowsAbsAt
#check Sec4LambdaRowsOuterSumAt
#check sec4_chiFCaseToolsData_of_packTools
#check sec4_genIBValueBridge_of_packTools
#check sec4_genRelIntegral_eq_relIntegral_of_packTools
#check sec4_genIBConsistencyBridge_of_packTools
#check sec4_lambdaRowZeroOnS2
#check sec4_zeroSeries_transparent
#check prop_4_2_lambda_k
#check prop_4_2_n_k

/-! ## 1. Primitive row and outer fields -/

/--
Build the per-row abs witnesses on `A.S1` from an `f` abs witness.
-/
def Sec4Prop42RowsOnS1OfFAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    RSeq.SeriesSum (fun m => COF.abs (((f.fn m).toFun x))) →
    Sec4LambdaRowsAbsAt (S := S) A hA f x


/--
Build the outer row-sum witness on `A.S1` once the per-row abs witnesses are
known.
-/
def Sec4Prop42OuterOnS1OfRows
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    ∀ hfabs : RSeq.SeriesSum (fun m => COF.abs (((f.fn m).toFun x))),
    ∀ hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x,
      Sec4LambdaRowsOuterSumAt (S := S) A hA f x hrows


/--
Build the per-row abs witnesses on `A.S2`.

The corresponding outer row-sum witness is automatic below because every row
has value zero on `A.S2`.
-/
def Sec4Prop42RowsOnS2
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S2 →
    Sec4LambdaRowsAbsAt (S := S) A hA f x


/--
The remaining extraction of `f` abs from a packed row witness on `A.S1`.
-/
def Sec4Prop42FAbsOfPackOnS1
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  Sec4FAbsOfLambdaRowsPackOnS1 (S := S) f hnn


/--
The remaining row-to-flat construction for the completed
`prop_4_2_chi_f_rep`.
-/
def Sec4Prop42FlatAbsOfPack
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  Sec4ChiFFlatAbsOfRowsPack (S := S) f hnn


/--
A sharper final primitive package for the `prop_4_2_chi_f_rep` internals.

Compared with `Sec4ChiFCasePackTools`, the `A.S2` outer series is no longer a
primitive: it is derived from row-zero values.
-/
def Sec4ChiFCasePrimitiveTools
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4Prop42RowsOnS1OfFAbs (S := S) f hnn)
    (PProd (Sec4Prop42OuterOnS1OfRows (S := S) f hnn)
      (PProd (Sec4Prop42RowsOnS2 (S := S) f hnn)
        (PProd (Sec4Prop42FAbsOfPackOnS1 (S := S) f hnn)
          (Sec4Prop42FlatAbsOfPack (S := S) f hnn))))


namespace Sec4ChiFCasePrimitiveTools

def mk
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (rows_on_s1_of_fabs : Sec4Prop42RowsOnS1OfFAbs (S := S) f hnn)
    (outer_on_s1_of_rows : Sec4Prop42OuterOnS1OfRows (S := S) f hnn)
    (rows_on_s2 : Sec4Prop42RowsOnS2 (S := S) f hnn)
    (fabs_of_pack_s1 : Sec4Prop42FAbsOfPackOnS1 (S := S) f hnn)
    (flat_abs_of_pack : Sec4Prop42FlatAbsOfPack (S := S) f hnn) :
    Sec4ChiFCasePrimitiveTools (S := S) f hnn :=
  ⟨rows_on_s1_of_fabs, outer_on_s1_of_rows, rows_on_s2,
    fabs_of_pack_s1, flat_abs_of_pack⟩


def rows_on_s1_of_fabs
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4Prop42RowsOnS1OfFAbs (S := S) f hnn :=
  T.1


def outer_on_s1_of_rows
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4Prop42OuterOnS1OfRows (S := S) f hnn :=
  T.2.1


def rows_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4Prop42RowsOnS2 (S := S) f hnn :=
  T.2.2.1


def fabs_of_pack_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4Prop42FAbsOfPackOnS1 (S := S) f hnn :=
  T.2.2.2.1


def flat_abs_of_pack
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4Prop42FlatAbsOfPack (S := S) f hnn :=
  T.2.2.2.2


end Sec4ChiFCasePrimitiveTools

/-! ## 2. The `A.S2` outer series is automatic from row-zero -/

/--
On `A.S2`, per-row abs witnesses automatically assemble to an outer zero
row-sum witness, because every row value is zero there.
-/
noncomputable def sec4_outerRowsOnS2_from_rows
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (A : BSet X) (hA : IntegrableSet1 S A)
    (x : X) (hxA : x ∈ A.S2)
    (hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x) :
    Sec4LambdaRowsOuterSumAt (S := S) A hA f x hrows :=
  seriesSum_congr
    (fun k => by
      change (0 : R) = (seriesSum_of_abs (hrows k)).sum
      exact (sec4_lambdaRowZeroOnS2 (S := S) f hnn
        A hA x hxA k (hrows k)).symm)
    (sec4_zeroSeries_transparent (R := R))


/-! ## 3. Build the b2b15 pack tools from the sharper primitive package -/

/-- Positive-side packed rows from `f` abs. -/
noncomputable def sec4_packOnS1_of_primitiveTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4LambdaRowsPackOnS1OfFAbs (S := S) f hnn := by
  intro A hA x hxA hfabs
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x :=
    Sec4ChiFCasePrimitiveTools.rows_on_s1_of_fabs T A hA x hxA hfabs
  let houter : Sec4LambdaRowsOuterSumAt (S := S) A hA f x hrows :=
    Sec4ChiFCasePrimitiveTools.outer_on_s1_of_rows T A hA x hxA hfabs hrows
  exact ⟨hrows, houter⟩


/-- Negative-side packed rows from row witnesses and the automatic zero outer series. -/
noncomputable def sec4_packOnS2_of_primitiveTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4LambdaRowsPackOnS2 (S := S) f hnn := by
  intro A hA x hxA
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x :=
    Sec4ChiFCasePrimitiveTools.rows_on_s2 T A hA x hxA
  let houter : Sec4LambdaRowsOuterSumAt (S := S) A hA f x hrows :=
    sec4_outerRowsOnS2_from_rows (S := S) f hnn A hA x hxA hrows
  exact ⟨hrows, houter⟩


/--
The b2b15 `Sec4ChiFCasePackTools` package from the sharper primitive tools.
-/
noncomputable def sec4_chiFCasePackTools_of_primitiveTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4ChiFCasePackTools (S := S) f hnn :=
  Sec4ChiFCasePackTools.mk
    (fabs_of_pack_s1 := Sec4ChiFCasePrimitiveTools.fabs_of_pack_s1 T)
    (pack_on_s1_of_fabs := sec4_packOnS1_of_primitiveTools f hnn T)
    (pack_on_s2 := sec4_packOnS2_of_primitiveTools f hnn T)
    (flat_abs_of_pack := Sec4ChiFCasePrimitiveTools.flat_abs_of_pack T)


/-! ## 4. Final bridges from the sharper primitive package -/

/-- Full `Sec4ChiFCaseToolsData` from primitive row tools. -/
noncomputable def sec4_chiFCaseToolsData_of_primitiveTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4ChiFCaseToolsData (S := S) f hnn :=
  sec4_chiFCaseToolsData_of_packTools f hnn
    (sec4_chiFCasePackTools_of_primitiveTools f hnn T)


/-- Final tools from primitive row tools. -/
noncomputable def sec4_prop42FinalTools_of_primitiveTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  sec4_prop42FinalTools_of_chiFCaseTools B hB f hnn
    (sec4_chiFCaseToolsData_of_primitiveTools f hnn T)


/-- Full value bridge from primitive row tools. -/
noncomputable def sec4_genIBValueBridge_of_primitiveTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_chiFCaseTools B hB f hnn
    (sec4_chiFCaseToolsData_of_primitiveTools f hnn T)


/-- Consistency theorem from primitive row tools. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_primitiveTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_primitiveTools f hnn T)


/-- Packaged consistency bridge from primitive row tools. -/
noncomputable def sec4_genIBConsistencyBridge_of_primitiveTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePrimitiveTools (S := S) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_primitiveTools f hnn T)


end BishopC
