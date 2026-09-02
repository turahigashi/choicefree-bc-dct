import Mathdemo.Internal.Sec4.DichotomyData

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
    Sec4RepAbsAt
      (prop_4_2_lambda_k A hA f (prop_4_2_n_k f) k) x


/--
Extract all row abs witnesses from a completed `χ_A·f` flat abs witness.

This is the already verified `seriesSumRep_L1_row_absConv` direction, exposed
with the exact row family used by `prop_4_2_chi_f_rep`.
-/
noncomputable def sec4_lambdaRowsAbs_of_chiFFlatAbs
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (x : X)
    (hflat : Sec4RepAbsAt (prop_4_2_chi_f_rep A hA f hnn) x) :
    Sec4LambdaRowsAbsAt (S := S) A hA f x := by
  intro k
  let hflatDom := hflat.fst
  let hflatabs := hflat.snd
  unfold prop_4_2_chi_f_rep at hflatDom hflatabs
  let hrowDom := seriesSumRep_L1_F_memAt
    (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
    _ hflatDom k
  exact ⟨hrowDom, seriesSumRep_L1_row_absConv
    (prop_4_2_lambda_k A hA f (prop_4_2_n_k f))
    _
    (x := x)
    hflatDom
    hflatabs
    k⟩


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
    Sec4RepAbsAt f x








namespace Sec4ChiFCaseRowTools









end Sec4ChiFCaseRowTools

/-! ## 3. Build `Sec4ChiFCaseToolsData` from row tools -/





/-! ## 4. Final bridges from row-level internal tools -/









end BishopC
