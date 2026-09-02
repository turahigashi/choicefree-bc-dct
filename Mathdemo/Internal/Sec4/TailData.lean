import Mathdemo.Internal.Sec4.Preservation

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-C1: tail hsum from relative-integral increments

B2 closed the preservation chain.  This chunk starts the direct construction
of the general relative integral by reducing `Sec4IBTailData` to two
quantitative facts:

* each layer norm is the relative integral over the layer `D_k`;
* the layer relative integrals are dominated by the increments of
  `I_{A_k ∧ B}(f)`.

The remaining hard work is therefore isolated as:
`diffIntegral ≤ coverIncrement` and summability of `coverIncrement`.
-/

#check sec4IB_termRepNonneg
#check sec4IB_tailRepNonneg_closed
#check genIB_rep_from_tailData_repNonneg
#check IntegrableRep.normL1_nonneg
#check IntegrableRep.normL1_eq_integral_of_nonneg
#check relIntegral
#check relIntegral_and_mono
#check relIntegral_mono_le
#check relIntegral_or_add_and
#check coverSet_mono
#check coverSet_tendsto
#check seriesSum_comparison
#check nonneg_sub_of_le

/-! ## 1. Layer norms as layer relative integrals -/

/-- Relative integral over the layer `D_k=(A_{k+1}∧B)-(A_k∧B)`. -/
noncomputable def sec4IB_diffRelIntegral
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : R :=
  relIntegral (sec4CoverDiff B f k) (sec4CoverDiff_int B hB f k) f hnn


/--
The L1 norm of the layer representative equals the layer relative integral.
This is exactly where B2's `sec4IB_termRepNonneg` is used.
-/
theorem sec4IB_termNorm_eq_diffRelIntegral
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) :
    (sec4IB_termRep B hB f hnn k).normL1 =
      sec4IB_diffRelIntegral B hB f hnn k := by
  unfold sec4IB_diffRelIntegral relIntegral sec4IB_termRep
  exact IntegrableRep.normL1_eq_integral_of_nonneg
    (prop_4_2_chi_f_rep (sec4CoverDiff B f k)
      (sec4CoverDiff_int B hB f k) f hnn)
    (sec4IB_termRepNonneg B hB f hnn k)


/-- Non-negativity of each layer relative integral. -/
theorem sec4IB_diffRelIntegral_nonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) :
    Nonneg (sec4IB_diffRelIntegral B hB f hnn k) := by
  rw [← sec4IB_termNorm_eq_diffRelIntegral B hB f hnn k]
  exact IntegrableRep.normL1_nonneg (sec4IB_termRep B hB f hnn k)


/--
If the layer relative integrals are summable, they provide the required
`Sec4IBTailData`.
-/
noncomputable def sec4IBTailData_of_diffRelIntegralSum
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (hsumD : RSeq.SeriesSum
      (fun k => sec4IB_diffRelIntegral B hB f hnn k)) :
    Sec4IBTailData (S := S) B hB f hnn :=
  seriesSum_congr
    (fun k => (sec4IB_termNorm_eq_diffRelIntegral B hB f hnn k).symm)
    hsumD


/-! ## 2. Cover increments -/

/-- `ψ_k = I_{A_k∧B}(f)`. -/
noncomputable def sec4IB_coverIntegral
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : R :=
  relIntegral (sec4CoverAnd B f k) (sec4CoverAnd_int B hB f k) f hnn


/-- The cover increment `ψ_{k+1}-ψ_k`. -/
noncomputable def sec4IB_coverIncrement
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) : R :=
  sec4IB_coverIntegral B hB f hnn (k + 1) -
    sec4IB_coverIntegral B hB f hnn k


/-- Monotonicity of `ψ_k = I_{A_k∧B}(f)`. -/
theorem sec4IB_coverIntegral_mono
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) :
    Le (sec4IB_coverIntegral B hB f hnn k)
      (sec4IB_coverIntegral B hB f hnn (k + 1)) := by
  unfold sec4IB_coverIntegral
  exact relIntegral_and_mono (B := B) hB
    (coverSet_int f k) (coverSet_int f (k + 1))
    (coverSet_mono f k) f hnn


/-- Cover increments are non-negative. -/
theorem sec4IB_coverIncrement_nonneg
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) (k : Nat) :
    Nonneg (sec4IB_coverIncrement B hB f hnn k) := by
  unfold sec4IB_coverIncrement
  exact nonneg_sub_of_le (sec4IB_coverIntegral_mono B hB f hnn k)


/--
From a comparison with cover increments and summability of the increments,
obtain summability of the layer relative integrals.
-/
noncomputable def sec4IB_diffRelIntegralSum_of_coverIncrement
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (hcmp : ∀ k : Nat,
      Le (sec4IB_diffRelIntegral B hB f hnn k)
        (sec4IB_coverIncrement B hB f hnn k))
    (hsumInc : RSeq.SeriesSum
      (fun k => sec4IB_coverIncrement B hB f hnn k)) :
    RSeq.SeriesSum (fun k => sec4IB_diffRelIntegral B hB f hnn k) :=
  seriesSum_comparison
    (fun k => sec4IB_diffRelIntegral_nonneg B hB f hnn k)
    hcmp
    hsumInc


/--
The main C1 constructor: tail data from the two remaining C facts.
-/
noncomputable def sec4IBTailData_of_coverIncrement
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (hcmp : ∀ k : Nat,
      Le (sec4IB_diffRelIntegral B hB f hnn k)
        (sec4IB_coverIncrement B hB f hnn k))
    (hsumInc : RSeq.SeriesSum
      (fun k => sec4IB_coverIncrement B hB f hnn k)) :
    Sec4IBTailData (S := S) B hB f hnn :=
  sec4IBTailData_of_diffRelIntegralSum B hB f hnn
    (sec4IB_diffRelIntegralSum_of_coverIncrement B hB f hnn hcmp hsumInc)


/-! ## 3. Direct candidate using the increment data -/







end BishopC
