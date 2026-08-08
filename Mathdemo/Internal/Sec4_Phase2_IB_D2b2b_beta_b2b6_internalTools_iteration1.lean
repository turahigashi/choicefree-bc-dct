import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b5_chiStep_iteration1

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

/-!
# Sec4 Phase2-D2b2bβ-b2b6: final reduction to the internal `χ·f` factor bridge

The b2b5 kernel response confirms that the pointwise characteristic telescope
is complete.  The only remaining issue is internal to `prop_4_2_chi_f_rep`:

* extracting the characteristic representative's pointwise abs witness from a
  `χ_A · f` representative abs witness;
* proving that `χ_A · f` has point value zero on `A.S2`, without extracting an
  abs witness for `f`.

This file isolates exactly that internal `prop_4_2` bridge and then finishes
the measurable `I_B` value bridge and consistency from it.

Thus the remaining kernel task after this file is no longer set algebra or
telescope; it is just the generic `prop_4_2_chi_f_rep` factor plumbing.
-/

#check Sec4CanonicalCoverLayerAtomDataSucc
#check sec4_genIBValueBridge_of_atomData
#check sec4_genRelIntegral_eq_relIntegral_of_atomData
#check sec4_genIBConsistencyBridge_of_atomData
#check sec4_genIB_baseAbs_of_abs
#check sec4_genIB_tailPointBridge
#check prop_4_2_chi_f_rep
#check sec4CoverAnd_int
#check sec4CoverDiff_int

/-! ## 1. Internal `χ·f` factor bridge types -/

/--
For the successor cover `coverSet f (n+1) ∧ B`, a pointwise abs witness for
the corresponding `χ · f` representative.

This is the cover-level analogue of the base witness
`sec4_genIB_baseAbs_of_abs` and the row witness
`(sec4_genIB_tailPointBridge ...).rowAbs k`.
-/
def Sec4CoverChiFAbsSucc
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ x : X,
    ∀ hgenabs :
      RSeq.SeriesSum
        (fun m => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn m).toFun x)),
    ∀ n : Nat,
      RSeq.SeriesSum
        (fun m => COF.abs
          (((prop_4_2_chi_f_rep
              (sec4CoverAnd B f (n + 1))
              (sec4CoverAnd_int B hB f (n + 1))
              f hnn).fn m).toFun x))


/--
Generic extraction of the set-characteristic abs witness from a
`χ_A · f` representative abs witness.
-/
def Sec4SetChiAbsOfChiFAbs
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
    RSeq.SeriesSum
      (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x)) →
    RSeq.SeriesSum
      (fun m => COF.abs (((hA.rep.fn m).toFun x)))


/-- Technical lemma used in the public import closure. -/
def Sec4ChiFZeroOnS2
    (f : IntegrableRep S) (hnn : RepNonneg f) : Prop :=
  ∀ (A : BSet X) (hA : IntegrableSet1 S A) (x : X),
    x ∈ A.S2 →
    ∀ hflatabs :
      RSeq.SeriesSum
        (fun m => COF.abs (((prop_4_2_chi_f_rep A hA f hnn).fn m).toFun x)),
      (seriesSum_of_abs hflatabs).sum = 0


/--
The final internal bridge needed from the `prop_4_2_chi_f_rep` construction.

It is a `PProd` chain to avoid heavy projection generation over large
representative expressions.
-/
def Sec4ChiFInternalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f) : Type _ :=
  PProd (Sec4CoverChiFAbsSucc (S := S) B hB f hnn)
    (PProd (Sec4SetChiAbsOfChiFAbs (S := S) f hnn)
      (Sec4ChiFZeroOnS2 (S := S) f hnn))


namespace Sec4ChiFInternalTools

def mk
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (cover_chiF_abs_succ : Sec4CoverChiFAbsSucc (S := S) B hB f hnn)
    (set_chi_abs_of_chiF_abs : Sec4SetChiAbsOfChiFAbs (S := S) f hnn)
    (chiF_zero_on_s2 : Sec4ChiFZeroOnS2 (S := S) f hnn) :
    Sec4ChiFInternalTools (S := S) B hB f hnn :=
  ⟨cover_chiF_abs_succ, set_chi_abs_of_chiF_abs, chiF_zero_on_s2⟩


def cover_chiF_abs_succ
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    Sec4CoverChiFAbsSucc (S := S) B hB f hnn :=
  T.1


def set_chi_abs_of_chiF_abs
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    Sec4SetChiAbsOfChiFAbs (S := S) f hnn :=
  T.2.1


def chiF_zero_on_s2
    {B : BSet X} {hB : IsMeasurableSet (S := S) B}
    {f : IntegrableRep S} {hnn : RepNonneg f}
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    Sec4ChiFZeroOnS2 (S := S) f hnn :=
  T.2.2


end Sec4ChiFInternalTools

/-! ## 2. S2 membership facts driven by validness -/

/--
If `x∈B.S2` and the characteristic of `coverSet f n ∧ B` is defined at `x`,
then `x` is on the negative side of that intersection.
-/
theorem sec4_coverAnd_s2_of_B_s2_from_valid
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (n : Nat) (x : X)
    (hxB : x ∈ B.S2)
    (hχ : RSeq.SeriesSum
      (fun m => COF.abs ((((sec4CoverAnd_int B hB f n).rep.fn m).toFun x)))) :
    x ∈ (sec4CoverAnd B f n).S2 := by
  have hvalid := (sec4CoverAnd_int B hB f n).valid x hχ
  cases hvalid.1 with
  | inl hAnd1 =>
      exfalso
      unfold sec4CoverAnd at hAnd1
      exact B.disj x hAnd1.2 x hxB rfl
  | inr hAnd2 =>
      exact hAnd2


/--
If `x∈B.S2` and the characteristic of the layer
`(coverSet f (k+1)∧B) - (coverSet f k∧B)` is defined at `x`, then `x` is on
the negative side of that layer.
-/
theorem sec4_coverDiff_s2_of_B_s2_from_valid
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (k : Nat) (x : X)
    (hxB : x ∈ B.S2)
    (hχ : RSeq.SeriesSum
      (fun m => COF.abs ((((sec4CoverDiff_int B hB f k).rep.fn m).toFun x)))) :
    x ∈ (sec4CoverDiff B f k).S2 := by
  have hvalid := (sec4CoverDiff_int B hB f k).valid x hχ
  cases hvalid.1 with
  | inl hD1 =>
      exfalso
      unfold sec4CoverDiff at hD1
      have hU : x ∈ (sec4CoverAnd B f (k + 1)).S1 := hD1.1
      unfold sec4CoverAnd at hU
      exact B.disj x hU.2 x hxB rfl
  | inr hD2 =>
      exact hD2


/-! ## 3. Fill the five atom fields from the internal bridge -/

/-- Characteristic abs witness for the successor cover. -/
noncomputable def sec4_coverChiAbsSucc_of_internalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    ∀ x : X,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn m).toFun x)),
      ∀ n : Nat,
        RSeq.SeriesSum
          (fun m => COF.abs ((((sec4CoverAnd_int B hB f (n + 1)).rep.fn m).toFun x))) := by
  intro x hgenabs n
  exact Sec4ChiFInternalTools.set_chi_abs_of_chiF_abs T
    (sec4CoverAnd B f (n + 1))
    (sec4CoverAnd_int B hB f (n + 1))
    x
    (Sec4ChiFInternalTools.cover_chiF_abs_succ T x hgenabs n)


/-- Characteristic abs witness for the base cover. -/
noncomputable def sec4_baseChiAbs_of_internalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    ∀ x : X,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn m).toFun x)),
        RSeq.SeriesSum
          (fun m => COF.abs ((((sec4CoverAnd_int B hB f 0).rep.fn m).toFun x))) := by
  intro x hgenabs
  exact Sec4ChiFInternalTools.set_chi_abs_of_chiF_abs T
    (sec4CoverAnd B f 0)
    (sec4CoverAnd_int B hB f 0)
    x
    (sec4_genIB_baseAbs_of_abs B hB f hnn x hgenabs)


/-- Characteristic abs witness for each difference layer. -/
noncomputable def sec4_termChiAbs_of_internalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    ∀ k : Nat, ∀ x : X,
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn m).toFun x)),
        RSeq.SeriesSum
          (fun m => COF.abs ((((sec4CoverDiff_int B hB f k).rep.fn m).toFun x))) := by
  intro k x hgenabs
  let PB := sec4_genIB_tailPointBridge B hB f hnn x hgenabs
  exact Sec4ChiFInternalTools.set_chi_abs_of_chiF_abs T
    (sec4CoverDiff B f k)
    (sec4CoverDiff_int B hB f k)
    x
    (PB.rowAbs k)


/-- Base row value is zero on `B.S2`. -/
theorem sec4_baseValue_s2_of_internalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    ∀ x : X, x ∈ B.S2 →
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn m).toFun x)),
        sec4_genIB_baseValue B hB f hnn x hgenabs = 0 := by
  intro x hxB hgenabs
  let hflat := sec4_genIB_baseAbs_of_abs B hB f hnn x hgenabs
  let hχ := sec4_baseChiAbs_of_internalTools B hB f hnn T x hgenabs
  have hA2 : x ∈ (sec4CoverAnd B f 0).S2 :=
    sec4_coverAnd_s2_of_B_s2_from_valid B hB f 0 x hxB hχ
  unfold sec4_genIB_baseValue
  exact Sec4ChiFInternalTools.chiF_zero_on_s2 T
    (sec4CoverAnd B f 0)
    (sec4CoverAnd_int B hB f 0)
    x hA2 hflat


/-- Each tail row value is zero on `B.S2`. -/
theorem sec4_rowValue_s2_of_internalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    ∀ k : Nat, ∀ x : X, x ∈ B.S2 →
      ∀ hgenabs :
        RSeq.SeriesSum
          (fun m => COF.abs (((genIB_rep_from_measurable B hB f hnn).fn m).toFun x)),
        sec4_genIB_tailRowSeq B hB f hnn x hgenabs k = 0 := by
  intro k x hxB hgenabs
  let PB := sec4_genIB_tailPointBridge B hB f hnn x hgenabs
  let hflat := PB.rowAbs k
  let hχ := sec4_termChiAbs_of_internalTools B hB f hnn T k x hgenabs
  have hD2 : x ∈ (sec4CoverDiff B f k).S2 :=
    sec4_coverDiff_s2_of_B_s2_from_valid B hB f k x hxB hχ
  have hzero :
      (seriesSum_of_abs hflat).sum = 0 :=
    Sec4ChiFInternalTools.chiF_zero_on_s2 T
      (sec4CoverDiff B f k)
      (sec4CoverDiff_int B hB f k)
      x hD2 hflat
  calc
    sec4_genIB_tailRowSeq B hB f hnn x hgenabs k =
        (PB.rowVal k).sum := by
          rfl
    _ = (seriesSum_of_abs hflat).sum :=
        seriesSum_unique (PB.rowVal k) (seriesSum_of_abs hflat)
    _ = 0 := hzero


/-! ## 4. Final atom data and final bridge from the internal tools -/

/-- Fill the b2b5 atom-data package from the internal `χ·f` tools. -/
noncomputable def sec4_atomDataSucc_of_internalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    Sec4CanonicalCoverLayerAtomDataSucc (S := S) B hB f hnn := {
  cover_chi_abs_succ := sec4_coverChiAbsSucc_of_internalTools B hB f hnn T
  base_chi_abs := sec4_baseChiAbs_of_internalTools B hB f hnn T
  term_chi_abs := sec4_termChiAbs_of_internalTools B hB f hnn T
  base_value_s2 := sec4_baseValue_s2_of_internalTools B hB f hnn T
  row_value_s2 := sec4_rowValue_s2_of_internalTools B hB f hnn T
}


/-- Unconditional value bridge once the internal `χ·f` tools are supplied. -/
noncomputable def sec4_genIBValueBridge_of_internalTools
    (B : BSet X) (hB : IsMeasurableSet (S := S) B)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools (S := S) B hB f hnn) :
    Sec4GenIBValueBridge (S := S) B hB f hnn :=
  sec4_genIBValueBridge_of_atomData B hB f hnn
    (sec4_atomDataSucc_of_internalTools B hB f hnn T)


/-- Consistency theorem for already integrable complemented sets, from the internal tools. -/
theorem sec4_genRelIntegral_eq_relIntegral_of_internalTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    genRelIntegral_from_measurable C (isMeasurableSet_of_integrable hC) f hnn =
      relIntegral C hC f hnn :=
  sec4_genRelIntegral_eq_relIntegral_of_atomData C hC f hnn
    (sec4_atomDataSucc_of_internalTools
      C (isMeasurableSet_of_integrable hC) f hnn T)


/-- Packaged consistency bridge from the internal tools. -/
noncomputable def sec4_genIBConsistencyBridge_of_internalTools
    (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f)
    (T : Sec4ChiFInternalTools
      (S := S) C (isMeasurableSet_of_integrable hC) f hnn) :
    Sec4GenIBConsistencyBridge (S := S) C hC f hnn :=
  sec4_genIBConsistencyBridge_of_atomData C hC f hnn
    (sec4_atomDataSucc_of_internalTools
      C (isMeasurableSet_of_integrable hC) f hnn T)


end BishopC
