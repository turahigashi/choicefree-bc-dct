import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b35_fullSetLocalRows_iteration1

/-!
# Sec4 Phase2-D2b2b_beta-b2b36: local flat abs and value for Proposition 4.2

`b2b35` put the Proposition 4.2 row construction on the source-faithful
full-set footing: pointwise calculations receive explicit local witnesses for
`chi_A` and `f`, instead of asking for a global `membership -> witness`
principle.

This file connects that local row package to the already proved generic
row-to-flat bridge and to the existing value theorem
`prop_4_2_chi_f_rep_value`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Local rows plus local outer convergence give flat abs convergence -/

/-- Local full-set version of the `rowToFlat` step for Proposition 4.2.

Given local witnesses for `chi_A` and `f`, and the local outer convergence of
the standard absolute row sums, the flattened representative
`prop_4_2_chi_f_rep A hA f hnn` has pointwise absolute convergence. -/
noncomputable def sec4_prop42FlatAbs_of_localWitnessOuter
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x)
    (houter : Sec4Prop42LocalStandardAbsOuterAt (S := S) hA W) :
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x)) :=
  sec4_prop42FlatAbs_of_absPack
    (S := S) f hnn sec4_rowToFlat_source A hA x
    (sec4_lambdaRowsAbsPack_of_localWitness (S := S) hA W houter)


/-- Provider form of the local flat-abs bridge. -/
noncomputable def sec4_prop42FlatAbs_of_localOuterProvider
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Outer : Sec4Prop42LocalStandardAbsOuterProvider (S := S) f hnn)
    (A : BSet X) (hA : IntegrableSet1 S A) (x : X)
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) :
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x)) :=
  sec4_prop42FlatAbs_of_localWitnessOuter
    (S := S) hA hnn W (Outer A hA x W)


/-! ## 2. Local value identification -/

/-- Local full-set value identification for the Proposition 4.2 representative:
the flat value is `chi_A(x) * f(x)` at every point carrying the local witnesses
and the local outer row convergence. -/
theorem sec4_prop42Value_of_localWitnessOuter
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x)
    (houter : Sec4Prop42LocalStandardAbsOuterAt (S := S) hA W) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbs_of_localWitnessOuter
        (S := S) hA hnn W houter)).sum =
      (Sec4Prop42LocalWitness.chiSigned (S := S) W).sum *
        (Sec4Prop42LocalWitness.fSigned (S := S) W).sum := by
  exact prop_4_2_chi_f_rep_value
    A hA f hnn
    (sec4_prop42FlatAbs_of_localWitnessOuter
      (S := S) hA hnn W houter)
    W.chi_abs
    W.f_abs


/-- On the positive side of `A`, the local value identification reduces to the
value of `f`. -/
theorem sec4_prop42Value_on_s1_of_localWitnessOuter
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x)
    (houter : Sec4Prop42LocalStandardAbsOuterAt (S := S) hA W)
    (hxA : x ∈ A.S1) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbs_of_localWitnessOuter
        (S := S) hA hnn W houter)).sum =
      (Sec4Prop42LocalWitness.fSigned (S := S) W).sum := by
  rw [sec4_prop42Value_of_localWitnessOuter
    (S := S) hA hnn W houter]
  rw [sec4_chi_value_one_of_localWitness (S := S) hA W hxA]
  ring


/-- On the negative side of `A`, the local value identification is zero. -/
theorem sec4_prop42Value_on_s2_of_localWitnessOuter
    {A : BSet X} (hA : IntegrableSet1 S A)
    {f : IntegrableRep S} (hnn : RepNonneg f)
    {x : X}
    (W : Sec4Prop42LocalWitness (S := S) A hA f x)
    (houter : Sec4Prop42LocalStandardAbsOuterAt (S := S) hA W)
    (hxA : x ∈ A.S2) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbs_of_localWitnessOuter
        (S := S) hA hnn W houter)).sum = (0 : R) := by
  rw [sec4_prop42Value_of_localWitnessOuter
    (S := S) hA hnn W houter]
  rw [sec4_chi_value_zero_of_localWitness (S := S) hA W hxA]
  ring


/-- Provider form of the local value identification. -/
theorem sec4_prop42Value_of_localOuterProvider
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (Outer : Sec4Prop42LocalStandardAbsOuterProvider (S := S) f hnn)
    (A : BSet X) (hA : IntegrableSet1 S A) (x : X)
    (W : Sec4Prop42LocalWitness (S := S) A hA f x) :
    (seriesSum_of_abs
      (sec4_prop42FlatAbs_of_localOuterProvider
        (S := S) f hnn Outer A hA x W)).sum =
      (Sec4Prop42LocalWitness.chiSigned (S := S) W).sum *
        (Sec4Prop42LocalWitness.fSigned (S := S) W).sum := by
  exact sec4_prop42Value_of_localWitnessOuter
    (S := S) hA hnn W (Outer A hA x W)


end BishopC
