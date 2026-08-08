import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b13_dichotomyData_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b14: reduce `Sec4ChiFCaseToolsData` to row-level lambda abs tools

The b2b12 response says that, after the `PSum` assembly, two packages remain:
`Sec4CoverDichotomyData` and `Sec4ChiFCaseToolsData`.

The previous chunk b2b13 constructs `Sec4CoverDichotomyData` generically from
`IntegrableSet1.valid` plus data-valued cotransitivity.  This file now attacks
the other package.  The only hard part of
`Sec4ChiFFAbsOfS1Data` is extracting `f`-abs convergence from the completed
`χ_A·f` representative.  We lower that extraction to row-level information
about `prop_4_2_lambda_k`.

The remaining primitive package is:

* row abs of all internal `prop_4_2_lambda_k` rows on `A.S1` implies `f` abs;
* from `f` abs on `A.S1`, build the completed `χ_A·f` flat abs;
* on `A.S2`, build the completed `χ_A·f` flat abs.

This avoids Prop-to-Type elimination and keeps all membership information in
the external `PSum`/dichotomy layer already completed in b2b13.
-/

#check Sec4ChiFCaseToolsData
#check Sec4ChiFFAbsOfS1Data
#check Sec4ChiFAbsOnS1Data
#check Sec4ChiFAbsOnS2Data
#check sec4_coverDichotomyData
#check sec4_genIBValueBridge_of_chiFCaseTools
#check sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools
#check sec4_genIBConsistencyBridge_of_chiFCaseTools
#check prop_4_2_chi_f_rep
#check prop_4_2_lambda_k
#check prop_4_2_n_k
#check seriesSumRep_L1_row_absConv

/-! ## 1. Row-level views of `prop_4_2_chi_f_rep` -/

/--
Pointwise abs convergence for every internal row of the Proposition 4.2
`χ_A·f` construction.
-/
def Sec4LambdaRowsAbsAt
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (x : X) : Type _ :=
  ∀ k : Nat,
    RSeq.SeriesSum
      (fun m => COF.abs
        ((((prop_4_2_lambda_k A hA f (prop_4_2_n_k f) k).fn m).toFun x)))


/--
Extract all row abs witnesses from a completed `χ_A·f` flat abs witness.

This is the already verified `seriesSumRep_L1_row_absConv` direction, exposed
with the exact row family used by `prop_4_2_chi_f_rep`.
-/
noncomputable def sec4_lambdaRowsAbs_of_chiFFlatAbs
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hflatabs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x))) :
    Sec4LambdaRowsAbsAt (S := S) A hA f x := by
  intro k
  unfold prop_4_2_chi_f_rep at hflatabs
  exact seriesSumRep_L1_row_absConv
    (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
    _
    (x := x)
    hflatabs
    k


/-! ## 2. The remaining internal primitive package -/

/--
Row-level extraction of `f` abs convergence on the positive side of `A`.

This is the substantive remaining part of `Sec4ChiFFAbsOfS1Data`.
It can use all row abs witnesses of `prop_4_2_lambda_k`, rather than only the
completed flat abs witness.
-/
def Sec4FAbsOfLambdaRowsOnS1
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    Sec4LambdaRowsAbsAt (S := S) A hA f x →
    RSeq.SeriesSum (fun m => COF.abs (((f.fn m).toFun x)))


/--
Flat abs construction for `χ_A·f` from an `f` abs witness on `A.S1`.

This is kept as a primitive because it is the row/flat assembly direction of
`seriesSumRep_L1`, not the already available flat-to-row direction.
-/
def Sec4ChiFFlatAbsOfFAbsOnS1
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  Sec4ChiFAbsOnS1Data (S := S) f hnn


/--
Flat abs construction for `χ_A·f` on `A.S2`.

This is the zero-domain construction for the completed `seriesSumRep_L1`
representative.
-/
def Sec4ChiFFlatAbsOnS2
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  Sec4ChiFAbsOnS2Data (S := S) f hnn


/--
Primitive internal data sufficient to build `Sec4ChiFCaseToolsData`.

The first field is row-level; the other two are exactly the remaining flat
construction directions.
-/
def Sec4ChiFCaseRowTools
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4FAbsOfLambdaRowsOnS1 (S := S) f hnn)
    (PProd (Sec4ChiFFlatAbsOfFAbsOnS1 (S := S) f hnn)
      (Sec4ChiFFlatAbsOnS2 (S := S) f hnn))


namespace Sec4ChiFCaseRowTools

def mk
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (fabs_of_rows_s1 : Sec4FAbsOfLambdaRowsOnS1 (S := S) f hnn)
    (flat_abs_on_s1 : Sec4ChiFFlatAbsOfFAbsOnS1 (S := S) f hnn)
    (flat_abs_on_s2 : Sec4ChiFFlatAbsOnS2 (S := S) f hnn) :
    Sec4ChiFCaseRowTools (S := S) f hnn :=
  ⟨fabs_of_rows_s1, flat_abs_on_s1, flat_abs_on_s2⟩


def fabs_of_rows_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4FAbsOfLambdaRowsOnS1 (S := S) f hnn :=
  T.1


def flat_abs_on_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4ChiFFlatAbsOfFAbsOnS1 (S := S) f hnn :=
  T.2.1


def flat_abs_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4ChiFFlatAbsOnS2 (S := S) f hnn :=
  T.2.2


end Sec4ChiFCaseRowTools

/-! ## 3. Build `Sec4ChiFCaseToolsData` from row tools -/

/--
The positive-side `f`-abs extractor from row-level data.
-/
noncomputable def sec4_fabsOfS1Data_of_rowTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4ChiFFAbsOfS1Data (S := S) f hnn := by
  intro A hA x hxA hflatabs
  exact Sec4ChiFCaseRowTools.fabs_of_rows_s1 T
    A hA x hxA
    (sec4_lambdaRowsAbs_of_chiFFlatAbs A hA f hnn x hflatabs)


/--
Assemble the full `Sec4ChiFCaseToolsData` package from row-level internal
tools.
-/
noncomputable def sec4_chiFCaseToolsData_of_rowTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4ChiFCaseToolsData (S := S) f hnn :=
  Sec4ChiFCaseToolsData.mk
    (fabs_of_s1 := sec4_fabsOfS1Data_of_rowTools f hnn T)
    (abs_on_s1 := Sec4ChiFCaseRowTools.flat_abs_on_s1 T)
    (abs_on_s2 := Sec4ChiFCaseRowTools.flat_abs_on_s2 T)


/-! ## 4. Final bridges from row-level internal tools -/

/-- Final tools from row-level internal tools. -/
noncomputable def sec4_prop42FinalTools_of_rowCaseTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  sec4_prop42FinalTools_of_chiFCaseTools B hB f hnn
    (sec4_chiFCaseToolsData_of_rowTools f hnn T)


/-- Full value bridge from row-level internal tools. -/
noncomputable def sec4_genIBValueBridge_of_rowCaseTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_chiFCaseTools B hB f hnn
    (sec4_chiFCaseToolsData_of_rowTools f hnn T)


/-- Consistency theorem from row-level internal tools. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_rowCaseTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_rowTools f hnn T)


/-- Packaged consistency bridge from row-level internal tools. -/
noncomputable def sec4_genIBConsistencyBridge_of_rowCaseTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseRowTools (S := S) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_rowTools f hnn T)


end BishopC
