import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b14_caseRowTools_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b15: packed row data for the final `χ_A·f` case tools

This file continues under the assumption that b2b13 and b2b14 have been
integrated.

b2b14 reduced `Sec4ChiFCaseToolsData f hnn` to row-level tools.  The first
row-level field in b2b14 was intentionally light and only carried per-row abs
witnesses.  For the final internal construction, however, the completed
`seriesSumRep_L1` flat abs also gives an outer row-sum witness.  This file
packages that extra data explicitly.

The new package `Sec4ChiFCasePackTools` is the sharper remaining target:

* from a completed `χ_A·f` flat abs witness we build a packed row witness
  using `sec4_make_pointBridge`;
* positive-side `f`-abs extraction may use the whole packed row witness;
* positive/negative-side flat abs construction may also be routed through a
  packed row witness.

Thus, after this file, the remaining internal work is exactly the row-pack
construction for `prop_4_2_lambda_k`; all cover/dichotomy/telescope assembly
has already been discharged by the previous chunks.
-/

#check Sec4ChiFCaseToolsData
#check Sec4ChiFFAbsOfS1Data
#check Sec4ChiFAbsOnS1Data
#check Sec4ChiFAbsOnS2Data
#check Sec4LambdaRowsAbsAt
#check sec4_lambdaRowsAbs_of_chiFFlatAbs
#check sec4_make_pointBridge
#check prop_4_2_chi_f_rep
#check prop_4_2_lambda_k
#check prop_4_2_n_k
#check sec4_genIBValueBridge_of_chiFCaseTools
#check sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools
#check sec4_genIBConsistencyBridge_of_chiFCaseTools

/-! ## 1. Packed row witnesses -/

/--
Outer row-sum witness associated to a family of row abs witnesses.
-/
def Sec4LambdaRowsOuterSumAt
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (x : X)
    (hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x) : Type _ :=
  RSeq.SeriesSum (fun k => (seriesSum_of_abs (hrows k).snd).sum)


/--
A packed pointwise row witness: per-row abs convergence plus convergence of
the outer row-value series.
-/
def Sec4LambdaRowsPackAt
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (x : X) : Type _ :=
  Sigma (fun hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x =>
    Sec4LambdaRowsOuterSumAt (S := S) A hA f x hrows)


namespace Sec4LambdaRowsPackAt

def rows
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {x : X}
    (P : Sec4LambdaRowsPackAt (S := S) A hA f x) :
    Sec4LambdaRowsAbsAt (S := S) A hA f x :=
  P.1


def outer
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {x : X}
    (P : Sec4LambdaRowsPackAt (S := S) A hA f x) :
    Sec4LambdaRowsOuterSumAt (S := S) A hA f x P.rows :=
  P.2


end Sec4LambdaRowsPackAt

/--
A completed `χ_A·f` flat abs witness yields the packed row data of the
underlying `seriesSumRep_L1`.
-/
noncomputable def sec4_lambdaRowsPack_of_chiFFlatAbs
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hflat : Sec4RepAbsAt (prop_4_2_chi_f_rep A hA f hnn) x) :
    Sec4LambdaRowsPackAt (S := S) A hA f x := by
  let hflatDom := hflat.fst
  let hflatabs := hflat.snd
  unfold prop_4_2_chi_f_rep at hflatDom hflatabs
  let F : Nat → IntegrableRep S :=
    prop_4_2_lambda_k A hA f (prop_4_2_n_k f)
  let PBData := sec4_make_pointBridge F _ x hflatDom hflatabs
  let PB := PBData.val
  let hrows : Sec4LambdaRowsAbsAt (S := S) A hA f x :=
    fun k => ⟨PB.rowDom k, PB.rowAbs k⟩
  let houter : Sec4LambdaRowsOuterSumAt (S := S) A hA f x hrows :=
    seriesSum_congr
      (fun k => by
        exact seriesSum_unique (PB.rowVal k) (seriesSum_of_abs (PB.rowAbs k)))
      PB.rows
  exact ⟨hrows, houter⟩


/-! ## 2. Sharper internal primitive package -/

/--
Positive-side extraction of `f` abs convergence from the full packed row data.
-/
def Sec4FAbsOfLambdaRowsPackOnS1
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    Sec4LambdaRowsPackAt (S := S) A hA f x →
    Sec4RepAbsAt f x


/--
Positive-side construction of packed row data from an `f` abs witness.
-/
def Sec4LambdaRowsPackOnS1OfFAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S1 →
    Sec4RepAbsAt f x →
    Sec4LambdaRowsPackAt (S := S) A hA f x


/--
Negative-side construction of packed row data.  This is where the row-zero
construction for `χ_A=0` should be used.
-/
def Sec4LambdaRowsPackOnS2
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X), x ∈ A.S2 →
    Sec4LambdaRowsPackAt (S := S) A hA f x


/--
Flat abs construction of the completed `χ_A·f` representative from packed
row data.
-/
def Sec4ChiFFlatAbsOfRowsPack
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
    Sec4LambdaRowsPackAt (S := S) A hA f x →
    Sec4RepAbsAt (prop_4_2_chi_f_rep A hA f hnn) x


/--
The sharper remaining internal package for `χ_A·f`.

It explicitly separates row-pack construction/extraction from the final
row-to-flat assembly.
-/
def Sec4ChiFCasePackTools
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4FAbsOfLambdaRowsPackOnS1 (S := S) f hnn)
    (PProd (Sec4LambdaRowsPackOnS1OfFAbs (S := S) f hnn)
      (PProd (Sec4LambdaRowsPackOnS2 (S := S) f hnn)
        (Sec4ChiFFlatAbsOfRowsPack (S := S) f hnn)))


namespace Sec4ChiFCasePackTools

def mk
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (fabs_of_pack_s1 : Sec4FAbsOfLambdaRowsPackOnS1 (S := S) f hnn)
    (pack_on_s1_of_fabs : Sec4LambdaRowsPackOnS1OfFAbs (S := S) f hnn)
    (pack_on_s2 : Sec4LambdaRowsPackOnS2 (S := S) f hnn)
    (flat_abs_of_pack : Sec4ChiFFlatAbsOfRowsPack (S := S) f hnn) :
    Sec4ChiFCasePackTools (S := S) f hnn :=
  ⟨fabs_of_pack_s1, pack_on_s1_of_fabs, pack_on_s2, flat_abs_of_pack⟩


def fabs_of_pack_s1
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4FAbsOfLambdaRowsPackOnS1 (S := S) f hnn :=
  T.1


def pack_on_s1_of_fabs
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4LambdaRowsPackOnS1OfFAbs (S := S) f hnn :=
  T.2.1


def pack_on_s2
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4LambdaRowsPackOnS2 (S := S) f hnn :=
  T.2.2.1


def flat_abs_of_pack
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4ChiFFlatAbsOfRowsPack (S := S) f hnn :=
  T.2.2.2


end Sec4ChiFCasePackTools

/-! ## 3. Build the case tools from packed row tools -/

/-- Positive-side `f` abs extraction from a completed `χ_A·f` flat abs witness. -/
noncomputable def sec4_fabsOfS1Data_of_packTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4ChiFFAbsOfS1Data (S := S) f hnn := by
  intro A hA x hxA hflatabs
  exact Sec4ChiFCasePackTools.fabs_of_pack_s1 T
    A hA x hxA
    (sec4_lambdaRowsPack_of_chiFFlatAbs A hA f hnn x hflatabs)


/-- Positive-side flat abs construction from an `f` abs witness. -/
noncomputable def sec4_absOnS1Data_of_packTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4ChiFAbsOnS1Data (S := S) f hnn := by
  intro A hA x hxA hfabs
  exact Sec4ChiFCasePackTools.flat_abs_of_pack T A hA x
    (Sec4ChiFCasePackTools.pack_on_s1_of_fabs T A hA x hxA hfabs)


/-- Negative-side flat abs construction. -/
noncomputable def sec4_absOnS2Data_of_packTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4ChiFAbsOnS2Data (S := S) f hnn := by
  intro A hA x hxA
  exact Sec4ChiFCasePackTools.flat_abs_of_pack T A hA x
    (Sec4ChiFCasePackTools.pack_on_s2 T A hA x hxA)


/-- Full case-tools package from packed row tools. -/
noncomputable def sec4_chiFCaseToolsData_of_packTools
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4ChiFCaseToolsData (S := S) f hnn :=
  Sec4ChiFCaseToolsData.mk
    (fabs_of_s1 := sec4_fabsOfS1Data_of_packTools f hnn T)
    (abs_on_s1 := sec4_absOnS1Data_of_packTools f hnn T)
    (abs_on_s2 := sec4_absOnS2Data_of_packTools f hnn T)


/-! ## 4. Final bridges from packed row tools -/

/-- Final tools from packed row tools. -/
noncomputable def sec4_prop42FinalTools_of_packTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4Prop42FinalTools (S := S) B hB f hnn :=
  sec4_prop42FinalTools_of_chiFCaseTools B hB f hnn
    (sec4_chiFCaseToolsData_of_packTools f hnn T)


/-- Full value bridge from packed row tools. -/
noncomputable def sec4_genIBValueBridge_of_packTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_chiFCaseTools B hB f hnn
    (sec4_chiFCaseToolsData_of_packTools f hnn T)


/-- Consistency theorem from packed row tools. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_packTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_packTools f hnn T)


/-- Packaged consistency bridge from packed row tools. -/
noncomputable def sec4_genIBConsistencyBridge_of_packTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFCasePackTools (S := S) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_chiFCaseTools C hC f hnn
    (sec4_chiFCaseToolsData_of_packTools f hnn T)


end BishopC
