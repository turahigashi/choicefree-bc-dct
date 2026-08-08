import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b34_chapter4SourceCompletion_iteration1

/-!
# Sec4 Phase2-D2b2b_beta-b2b35: local full-set rows for Proposition 4.2

This file changes the direction of the Proposition 4.2 residual.

The older residual `Sec4Prop42CharacteristicDomainWitness` asked for a global
map from membership in `A.S1` or `A.S2` to an absolute-convergence witness for
the chosen characteristic representative.  That is stronger than the printed
Bishop proof: the proof works on a suitable full set where the relevant
representatives already have pointwise absolute-convergence data.

The source-faithful local interface below keeps those two layers separate:

* the support `D(chi_A) cap D(f)` is full as a proposition;
* pointwise calculations receive an explicit `Sec4Prop42LocalWitness`, so no
  Type-level data is extracted from the propositional full-set assertion.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. The full support used by the printed Proposition 4.2 argument -/

/-- The common full support on which both `chi_A` and `f` have their
representative-level absolute convergence. -/
def Sec4Prop42LocalSupport
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) : Set X :=
  hA.rep.domain ∩ f.domain


/-- The common support is full, by finite intersection of full sets. -/
theorem sec4_prop42LocalSupport_full
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) :
    IsFull S (Sec4Prop42LocalSupport (S := S) A hA f) := by
  unfold Sec4Prop42LocalSupport
  exact isFull_inter (IntegrableRep.domain_isFull hA.rep)
    (IntegrableRep.domain_isFull f)


/-! ## 2. Type-level local witnesses for calculations on that support -/

/-- Pointwise data on the common support.

The domain fields record the propositional domain membership.  The absolute
convergence fields are the computational witnesses used by the row
construction.  This deliberately does not give a map from membership in
`A.S1`/`A.S2` to witnesses. -/
structure Sec4Prop42LocalWitness
    (A : BSet X) (hA : IntegrableSet1 S A)
    (f : IntegrableRep S) (x : X) : Type _ where
  chi_dom : forall m : Nat, x ∈ (hA.rep.fn m).dom
  chi_abs : RSeq.SeriesSum (fun m => COF.abs ((hA.rep.fn m).toFun x))
  f_dom : forall m : Nat, x ∈ (f.fn m).dom
  f_abs : RSeq.SeriesSum (fun m => COF.abs ((f.fn m).toFun x))


namespace Sec4Prop42LocalWitness

/-- A local witness gives membership in the propositional common support. -/
theorem mem_support
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) :
    x ∈ Sec4Prop42LocalSupport (S := S) A hA f := by
  unfold Sec4Prop42LocalSupport
  exact ⟨⟨W.chi_dom, ⟨W.chi_abs⟩⟩, ⟨W.f_dom, ⟨W.f_abs⟩⟩⟩


/-- Signed value of the characteristic representative at a local witness. -/
noncomputable def chiSigned
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) :
    RSeq.SeriesSum (fun m => (hA.rep.fn m).toFun x) :=
  seriesSum_of_abs W.chi_abs


/-- Signed value of `f` at a local witness. -/
noncomputable def fSigned
    {A : BSet X} {hA : IntegrableSet1 S A}
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) :
    RSeq.SeriesSum (fun m => (f.fn m).toFun x) :=
  seriesSum_of_abs W.f_abs


end Sec4Prop42LocalWitness

/-! ## 3. Standard Proposition 4.2 rows from local witnesses -/

/-- The lambda rows in the printed Proposition 4.2 proof have pointwise
absolute convergence at every point carrying the local `chi_A` and `f`
witnesses. -/
noncomputable def sec4_lambdaRowsAbs_of_localWitness
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) :
    Sec4LambdaRowsAbsAt (S := S) A hA f x :=
  sec4_lambdaRowAbs_of_chiF_fabs
    A hA f (prop_4_2_n_k f) x W.chi_abs W.f_abs


/-- Local replacement for the previous standard outer obligation: the outer
absolute row sum is attached to the standard rows built from a local witness. -/
def Sec4Prop42LocalStandardAbsOuterAt
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) : Type _ :=
  Sec4LambdaRowsAbsOuterSumAt (S := S) A hA f x
    (sec4_lambdaRowsAbs_of_localWitness (S := S) hA W)


/-- A future source-faithful residual should prove this local-on-full-support
outer convergence, rather than a global membership-to-witness principle. -/
def Sec4Prop42LocalStandardAbsOuterProvider
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  forall (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
    forall W : Sec4Prop42LocalWitness (S := S) A hA f x,
      Sec4Prop42LocalStandardAbsOuterAt (S := S) hA W


/-- Package the local standard rows with their local outer absolute row sum. -/
noncomputable def sec4_lambdaRowsAbsPack_of_localWitness
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x)
    (houter : Sec4Prop42LocalStandardAbsOuterAt (S := S) hA W) :
    Sec4LambdaRowsAbsPackAt (S := S) A hA f x :=
  ⟨sec4_lambdaRowsAbs_of_localWitness (S := S) hA W, houter⟩


/-! ## 4. Characteristic value facts go from witness to membership/value -/

/-- Existing `IntegrableSet1.valid` runs in the source-faithful direction:
from a characteristic absolute-convergence witness to membership in
`A.S1 union A.S2`. -/
theorem sec4_chi_mem_of_localWitness
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) :
    x ∈ A.S1 ∪ A.S2 :=
  (hA.valid x W.chi_abs).1


/-- On the positive side of the integrable set, the characteristic value is
one, using only the local characteristic witness. -/
theorem sec4_chi_value_one_of_localWitness
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x)
    (hxA : x ∈ A.S1) :
    (Sec4Prop42LocalWitness.chiSigned (S := S) W).sum = (1 : R) := by
  exact (hA.valid x W.chi_abs).2.1 hxA
    (Sec4Prop42LocalWitness.chiSigned (S := S) W)


/-- On the negative side of the integrable set, the characteristic value is
zero, using only the local characteristic witness. -/
theorem sec4_chi_value_zero_of_localWitness
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x)
    (hxA : x ∈ A.S2) :
    (Sec4Prop42LocalWitness.chiSigned (S := S) W).sum = (0 : R) := by
  exact (hA.valid x W.chi_abs).2.2 hxA
    (Sec4Prop42LocalWitness.chiSigned (S := S) W)


end BishopC
