import Mathdemo.Internal.Sec4.RowSeedResidual

/-!
# Sec4 Phase2-D2b2bβ-b2b28: source-faithful domain witnesses

The three residual row-seed fields isolated in `b2b27` are not merely missing
algebra.  With the current `IntegrableSet1` API, membership `x ∈ A.S1` or
`x ∈ A.S2` does not carry the pointwise domain witness for the characteristic
representative `hA.rep`.

In the source proof, `χ_A` is a partial function whose domain is
`A¹ ∪ A²`; therefore using `χ_A(x)` on `A¹`/`A²` implicitly carries this
domain information.  This file makes that source-side datum explicit instead
of smuggling it in as an unproved global assumption.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-- Pointwise source-domain witnesses for characteristic representatives.

This is the exact datum missing from the current `IntegrableSet1` projection:
membership in `A.S1`/`A.S2` should allow use of the characteristic function
`χ_A`, hence an absolute-convergence witness for the chosen representative.
-/
structure Sec4Prop42CharacteristicDomainWitness : Type _ where
  abs_on_s1 :
    forall (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
      x ∈ A.S1 →
      Sec4RepAbsAt hA.rep x
  abs_on_s2 :
    forall (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
      x ∈ A.S2 →
      Sec4RepAbsAt hA.rep x


/-- The first residual field is immediate once the source-domain witness for
`χ_A` is present.  The `f` abs witness is not used; it is part of the older
over-strong interface. -/
noncomputable def sec4_chiAbsOnS1_of_characteristicDomainWitness
    (D : Sec4Prop42CharacteristicDomainWitness (S := S))
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4Prop42ChiAbsOnS1OfFAbs (S := S) f hnn := by
  intro A hA x hxA _hfabs
  exact D.abs_on_s1 A hA x hxA


/-- With the characteristic domain witness, the Proposition 4.2 row witnesses
on `A.S1` follow by the already verified per-row construction. -/
noncomputable def sec4_rowsOnS1_of_characteristicDomainWitness
    (D : Sec4Prop42CharacteristicDomainWitness (S := S))
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4Prop42RowsOnS1OfFAbs (S := S) f hnn := by
  intro A hA x hxA hfabs
  exact sec4_lambdaRowAbs_of_chiF_fabs
    A hA f (prop_4_2_n_k f) x
    (D.abs_on_s1 A hA x hxA)
    hfabs


/-- A narrowed source-faithful provider: the characteristic domain witness
discharges the first residual field.  The remaining fields are kept explicit
because the current pointwise abs-outer/S2 interfaces are still stronger than
what the printed proof states. -/
structure Sec4GeneralIBDomainResidualProvider : Type _ where
  charDomain : Sec4Prop42CharacteristicDomainWitness (S := S)
  abs_outer_on_s1_of_rows : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4Prop42AbsOuterOnS1OfRows (S := S) f hnn
  pack_on_s2 : forall (f : IntegrableRep S) (hnn : RepNonneg f),
    Sec4LambdaRowsAbsPackOnS2 (S := S) f hnn


/-- Convert the source-domain residual provider to the older three-field
residual provider by filling the `χ_A` field from `charDomain`. -/
noncomputable def Sec4GeneralIBDomainResidualProvider.toResidualProvider
    (P : Sec4GeneralIBDomainResidualProvider (S := S)) :
    Sec4GeneralIBRowSeedResidualProvider (S := S) where
  residual := fun f hnn =>
    Sec4Prop42RowSeedResidualTools.mk
      (sec4_chiAbsOnS1_of_characteristicDomainWitness
        (S := S) P.charDomain f hnn)
      (P.abs_outer_on_s1_of_rows f hnn)
      (P.pack_on_s2 f hnn)


noncomputable def sec4_genIBValueBridge_of_domainResidualProvider
    (P : Sec4GeneralIBDomainResidualProvider (S := S))
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_rowSeedResidualProvider
    (Sec4GeneralIBDomainResidualProvider.toResidualProvider P)
    B hB f hnn


theorem sec4_genRelIntegral_eq_relIntegral_of_domainResidualProvider
    (P : Sec4GeneralIBDomainResidualProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_rowSeedResidualProvider
    (Sec4GeneralIBDomainResidualProvider.toResidualProvider P)
    C hC f hnn


noncomputable def sec4_genIBConsistencyBridge_of_domainResidualProvider
    (P : Sec4GeneralIBDomainResidualProvider (S := S))
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_rowSeedResidualProvider
    (Sec4GeneralIBDomainResidualProvider.toResidualProvider P)
    C hC f hnn


end BishopC
