import Mathdemo.Internal.Sec4.CaseRowTools

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b20: corrected abs-outer row package

The b2b20 source response found a genuine design bug in the previous
`rowToFlat` target: the outer series carried by `Sec4LambdaRowsPackAt` was the
series of signed row values,

```
Σ_k Σ_m row(k,m),
```

whereas the flat absolute convergence of `seriesSumRep_L1` requires the
series of row absolute sums,

```
Σ_k Σ_m |row(k,m)|.
```

This file corrects the interface.  It does not try to prove the false
signed-outer-to-flat statement.  Instead it introduces an abs-outer package and
shows that this corrected package is sufficient for the already completed
`Sec4ChiFCaseToolsData` and all final bridges.

Remaining final work after this file is exactly:

* a generic row-to-flat bridge using abs-outer row sums;
* `prop_4_2_lambda_k` cut-slice construction of the abs-outer row packages.
-/

#check Sec4ChiFCaseToolsData
#check Sec4ChiFFAbsOfS1Data
#check Sec4ChiFAbsOnS1Data
#check Sec4ChiFAbsOnS2Data
#check Sec4LambdaRowsAbsAt
#check sec4_lambdaRowsAbs_of_chiFFlatAbs
#check sec4_genIBValueBridge_of_chiFCaseTools
#check sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools
#check sec4_genIBConsistencyBridge_of_chiFCaseTools
#check seriesSumRep_L1
#check prop_4_2_chi_f_rep
#check prop_4_2_lambda_k
#check prop_4_2_n_k

/-! ## 1. Correct abs-outer row packages -/

/--
The outer convergence needed for flat absolute convergence:
the series of the row absolute sums, not the signed row sums.
-/
def Sec4LambdaRowsAbsOuterSumAt
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (x : X)
    (hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x) : Type _ :=
  RSeq.SeriesSum (fun k => (hrows k).snd.sum)


/--
Correct packed row data: per-row abs convergence plus abs-outer convergence.
-/
def Sec4LambdaRowsAbsPackAt
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (x : X) : Type _ :=
  Sigma (fun hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x =>
    Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x hrows)


namespace Sec4LambdaRowsAbsPackAt

def rows
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {x : X}
    (P : Sec4LambdaRowsAbsPackAt (S := S) A hA f x) :
    Sec4LambdaRowsAbsAt (S := S) A hA f x :=
  P.1


def outer
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {x : X}
    (P : Sec4LambdaRowsAbsPackAt (S := S) A hA f x) :
    Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x P.rows :=
  P.2


end Sec4LambdaRowsAbsPackAt

/-! ## 2. Correct generic row-to-flat target -/

/--
The correct generic row-to-flat pointwise abs bridge for `seriesSumRep_L1`.

The second convergence hypothesis is the series of row absolute sums.
-/
def Sec4SeriesSumRepL1FlatAbsOfAbsRows : Type _ :=
  ∀ (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun k => (F k).normL1))
    (x : X),
    ∀ hrows : ∀ k : Nat,
      Sec4RepAbsAt (F k) x,
    RSeq.SeriesSum (fun k => (hrows k).snd.sum) →
    Sec4RepAbsAt (seriesSumRep_L1 F hsum) x


/--
Use the correct generic row-to-flat bridge to build flat abs convergence for
`prop_4_2_chi_f_rep`.
-/
noncomputable def sec4_prop42FlatAbs_of_absPack
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (rowToFlat : Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S)) :
    ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
      Sec4LambdaRowsAbsPackAt (S := S) A hA f x →
      Sec4RepAbsAt (prop_4_2_chi_f_rep A hA f hnn) x := by
  intro A hA x P
  unfold prop_4_2_chi_f_rep
  exact rowToFlat
    (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
    _
    x
    (Sec4LambdaRowsAbsPackAt.rows P)
    (Sec4LambdaRowsAbsPackAt.outer P)


/-! ## 3. Correct final internal package -/

/--
Extract `f` abs on `A.S1` from the row abs witnesses.
The abs-outer witness is not needed for this direction.
-/
def Sec4FAbsOfLambdaAbsRowsOnS1
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  Sec4FAbsOfLambdaRowsOnS1 (S := S) f hnn


/--
Construct the correct abs-outer row package on `A.S1` from an `f` abs witness.
-/
def Sec4LambdaRowsAbsPackOnS1OfFAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    Sec4RepAbsAt f x →
    Sec4LambdaRowsAbsPackAt (S := S) A hA f x


/--
Construct the correct abs-outer row package on `A.S2`.
-/
def Sec4LambdaRowsAbsPackOnS2
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S2 →
    Sec4LambdaRowsAbsPackAt (S := S) A hA f x


/--
Correct final internal tools.

This is the first interface after the signed/abs outer correction.
-/
def Sec4ChiFCaseAbsPackTools
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S))
    (PProd (Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn)
      (PProd (Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) f hnn)
        (Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn)))


namespace Sec4ChiFCaseAbsPackTools



def rowToFlat
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4SeriesSumRepL1FlatAbsOfAbsRows (S := S) :=
  T.1


def fabs_of_rows_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4FAbsOfLambdaAbsRowsOnS1 (S := S) f hnn :=
  T.2.1


def pack_on_s1_of_fabs
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S) f hnn :=
  T.2.2.1


def pack_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn :=
  T.2.2.2


end Sec4ChiFCaseAbsPackTools

/-! ## 4. Build `Sec4ChiFCaseToolsData` from corrected tools -/

/--
Positive-side extraction: flat abs gives rows abs by the verified
flat-to-row direction; then the corrected internal extractor reconstructs
`f` abs.
-/
noncomputable def sec4_fabsOfS1Data_of_absPackTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4ChiFFAbsOfS1Data (S := S) f hnn := by
  intro A hA x hxA hflatabs
  exact Sec4ChiFCaseAbsPackTools.fabs_of_rows_s1 T
    A hA x hxA
    (sec4_lambdaRowsAbs_of_chiFFlatAbs A hA f hnn x hflatabs)


/-- Positive-side construction of flat abs from `f` abs. -/
noncomputable def sec4_absOnS1Data_of_absPackTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4ChiFAbsOnS1Data (S := S) f hnn := by
  intro A hA x hxA hfabs
  exact sec4_prop42FlatAbs_of_absPack f hnn
    (Sec4ChiFCaseAbsPackTools.rowToFlat T)
    A hA x
    (Sec4ChiFCaseAbsPackTools.pack_on_s1_of_fabs T A hA x hxA hfabs)


/-- Negative-side construction of flat abs. -/
noncomputable def sec4_absOnS2Data_of_absPackTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4ChiFAbsOnS2Data (S := S) f hnn := by
  intro A hA x hxA
  exact sec4_prop42FlatAbs_of_absPack f hnn
    (Sec4ChiFCaseAbsPackTools.rowToFlat T)
    A hA x
    (Sec4ChiFCaseAbsPackTools.pack_on_s2 T A hA x hxA)


/--
The original case-tools package from the corrected abs-outer tools.
-/
noncomputable def sec4_chiFCaseToolsData_of_absPackTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4ChiFCaseToolsData (S := S) f hnn :=
  Sec4ChiFCaseToolsData.mk
    (fabs_of_s1 := sec4_fabsOfS1Data_of_absPackTools f hnn T)
    (abs_on_s1 := sec4_absOnS1Data_of_absPackTools f hnn T)
    (abs_on_s2 := sec4_absOnS2Data_of_absPackTools f hnn T)


/-! ## 5. Final bridges from the corrected tools -/



/-- Full value bridge from corrected abs-outer tools. -/
noncomputable def sec4_genIBValueBridge_of_absPackTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_chiFCaseTools B hB f hnn
    (sec4_chiFCaseToolsData_of_absPackTools f hnn T)


/-- Consistency theorem from corrected abs-outer tools. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_absPackTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_absPackTools f hnn T)


/-- Packaged consistency bridge from corrected abs-outer tools. -/
noncomputable def sec4_genIBConsistencyBridge_of_absPackTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCaseAbsPackTools (S := S) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_absPackTools f hnn T)


end BishopC
