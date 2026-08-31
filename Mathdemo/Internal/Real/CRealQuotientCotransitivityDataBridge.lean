import Mathdemo.Internal.Real.CRealQuotientCOFPreInstancePackage

/-!
# CReal quotient cotransitivity data bridge

`CRealQuotientCOFPreInstancePackage` identified the remaining `COF` blocker: the live interface asks
for a Type-valued cotransitivity split

```
∀ {a b : CRealQuot}, ltQuot a b → ∀ c : CRealQuot,
  PSum (ltQuot a c) (ltQuot c b)
```

The current quotient order stores positivity as a `Prop`, so extracting the
tail witness hidden in `ltQuot a b` would itself be a new constructive
witness-extraction theorem.  This file closes the data-cotransitivity argument
once representative and positivity witnesses are supplied explicitly, and
records the exact remaining quotient witness frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Type-valued tail-stable positivity witness. -/
structure PosEventuallyData (x : RegularSeq) : Type where
  k : Nat
  N : Nat
  tail_pos : ∀ n : Nat, N ≤ n → COF.lt (eps k) (x.val n)

def PosEventuallyData.toProp {x : RegularSeq} (h : PosEventuallyData x) :
    PosEventually x :=
  ⟨h.k, h.N, h.tail_pos⟩

/-- Data-valued scalar split, using the live scalar `COF.lt_cotrans_data`
instead of the Prop-valued cotransitivity shadow. -/
def scalar_lt_split_add_data {e u v : Scalar}
    (h : COF.lt (e + e) (u + v)) : PSum (COF.lt e u) (COF.lt e v) := by
  cases COF.lt_cotrans_data h (e + v) with
  | inl hleft =>
      exact PSum.inr (by
        have t := COF.lt_add_left (-e) hleft
        rwa [show -e + (e + e) = e from by ring,
          show -e + (e + v) = v from by ring] at t)
  | inr hright =>
      exact PSum.inl (by
        have t := COF.lt_add_left (-v) hright
        rwa [show -v + (e + v) = e from by ring,
          show -v + (u + v) = u from by ring] at t)

/-- Data version of `posEventually_of_late_point`. -/
def posEventuallyData_of_late_point (x : RegularSeq) {j M : Nat}
    (hM : j + 2 ≤ M) (hpos : COF.lt (eps j) (x.val M)) :
    PosEventuallyData x where
  k := j + 1
  N := M
  tail_pos := by
    intro n hn
    have hnlarge : j + 2 ≤ n := Nat.le_trans hM hn
    have hMle : Le (eps M) (eps (j + 2)) := eps_le_of_le hM
    have hnle : Le (eps n) (eps (j + 2)) := eps_le_of_le hnlarge
    have hsum := BishopC.le_add hMle hnle
    have hbudget : Le (eps M + eps n) (eps (j + 1)) := by
      rwa [eps_succ_add_self (j + 1)] at hsum
    have hdist : Le (COF.abs (x.val M - x.val n)) (eps (j + 1)) :=
      BishopC.le_trans (x.regular M n) hbudget
    have hlower : Le (x.val M - eps (j + 1)) (x.val n) :=
      scalar_point_lower_of_abs_le hdist
    have hshift : COF.lt (eps (j + 1)) (x.val M - eps (j + 1)) := by
      have t := COF.lt_add_left (-(eps (j + 1))) hpos
      rwa [← eps_succ_add_self j,
        show -(eps (j + 1)) + (eps (j + 1) + eps (j + 1)) = eps (j + 1)
          from by ring,
        show -(eps (j + 1)) + x.val M = x.val M - eps (j + 1)
          from by ring] at t
    exact BishopC.lt_of_lt_of_le hshift hlower

/-- Representative-level Type-valued cotransitivity split. -/
def ltQuot_cotrans_mk_data (a b c : RegularSeq)
    (hpos : PosEventuallyData (subSeq b a)) :
    PSum (PosEventuallyData (subSeq c a)) (PosEventuallyData (subSeq b c)) := by
  rcases hpos with ⟨k, N, hN⟩
  let M : Nat := N + (k + 3)
  have hNM : N ≤ M := by
    unfold M
    omega
  have hMlate : k + 3 ≤ M := by
    unfold M
    omega
  have hba := hN M hNM
  change COF.lt (eps k) (b.val (M + 1) - a.val (M + 1)) at hba
  have hsplitInput :
      COF.lt (eps (k + 1) + eps (k + 1))
        ((c.val (M + 1) - a.val (M + 1)) + (b.val (M + 1) - c.val (M + 1))) := by
    rw [eps_succ_add_self k]
    rwa [show
        (c.val (M + 1) - a.val (M + 1)) + (b.val (M + 1) - c.val (M + 1))
          = b.val (M + 1) - a.val (M + 1)
        from by ring]
  cases scalar_lt_split_add_data hsplitInput with
  | inl hca =>
      exact PSum.inl (by
        change COF.lt (eps (k + 1)) ((subSeq c a).val M) at hca
        exact posEventuallyData_of_late_point (subSeq c a) hMlate hca)
  | inr hbc =>
      exact PSum.inr (by
        change COF.lt (eps (k + 1)) ((subSeq b c).val M) at hbc
        exact posEventuallyData_of_late_point (subSeq b c) hMlate hbc)

/-- The representative data split refines the existing quotient Prop order. -/
def ltQuot_cotrans_mk_data_to_prop (a b c : RegularSeq)
    (hpos : PosEventuallyData (subSeq b a)) :
    PSum (ltQuot (mkQuot a) (mkQuot c)) (ltQuot (mkQuot c) (mkQuot b)) := by
  cases ltQuot_cotrans_mk_data a b c hpos with
  | inl hca =>
      exact PSum.inl (by
        change PosEventually (subSeq c a)
        exact hca.toProp)
  | inr hbc =>
      exact PSum.inr (by
        change PosEventually (subSeq b c)
        exact hbc.toProp)

/-- Explicit representative witness for a quotient element.  Constructing this
uniformly from a quotient is the usual quotient-representative frontier. -/
structure CRealQuotRepWitness (x : CRealQuot) : Type where
  rep : RegularSeq
  eq_mk : x = mkQuot rep

/-- Explicit strict-order witness for quotient elements. -/
structure CRealQuotLTDataWitness (a b : CRealQuot) : Type where
  left : RegularSeq
  right : RegularSeq
  left_eq : a = mkQuot left
  right_eq : b = mkQuot right
  pos : PosEventuallyData (subSeq right left)

/-- If the quotient representatives and positive-tail data are supplied
explicitly, the data-valued quotient cotransitivity split is closed. -/
def ltQuot_cotrans_data_from_witness {a b c : CRealQuot}
    (hab : CRealQuotLTDataWitness a b) (hc : CRealQuotRepWitness c) :
    PSum (ltQuot a c) (ltQuot c b) := by
  rcases hab with ⟨ar, br, ha, hb, hpos⟩
  rcases hc with ⟨cr, hc⟩
  cases ltQuot_cotrans_mk_data_to_prop ar br cr hpos with
  | inl hleft =>
      exact PSum.inl (by
        rw [ha, hc]
        exact hleft)
  | inr hright =>
      exact PSum.inr (by
        rw [hc, hb]
        exact hright)

/-- Exact representative extraction needed to turn the bridge into a true
quotient-level `COF.lt_cotrans_data` implementation. -/
abbrev CRealQuotRepresentativeExtractionObligation : Type :=
  ∀ x : CRealQuot, CRealQuotRepWitness x

/-- Exact positive witness extraction needed to turn `ltQuot a b : Prop` into
the data consumed by `ltQuot_cotrans_data_from_witness`. -/
abbrev CRealQuotLTWitnessExtractionObligation : Type :=
  ∀ {a b : CRealQuot}, ltQuot a b → CRealQuotLTDataWitness a b

structure CRealQuotCOFDataCotransBridgeSeed : Type 1 where
  posData : RegularSeq → Type
  posData_to_prop : ∀ {x : RegularSeq}, posData x → PosEventually x
  scalar_split_data : ∀ {e u v : Scalar}, COF.lt (e + e) (u + v) →
    PSum (COF.lt e u) (COF.lt e v)
  late_point_data : ∀ x : RegularSeq, ∀ {j M : Nat},
    j + 2 ≤ M → COF.lt (eps j) (x.val M) → posData x
  mk_cotrans_data : ∀ a b c : RegularSeq,
    posData (subSeq b a) → PSum (posData (subSeq c a)) (posData (subSeq b c))
  mk_cotrans_data_to_prop : ∀ a b c : RegularSeq,
    posData (subSeq b a) →
      PSum (ltQuot (mkQuot a) (mkQuot c)) (ltQuot (mkQuot c) (mkQuot b))
  quotient_cotrans_from_witness : ∀ {a b c : CRealQuot},
    CRealQuotLTDataWitness a b → CRealQuotRepWitness c →
      PSum (ltQuot a c) (ltQuot c b)

def cRealQuotCOFDataCotransBridgeSeed : CRealQuotCOFDataCotransBridgeSeed where
  posData := PosEventuallyData
  posData_to_prop := fun h => h.toProp
  scalar_split_data := fun h => scalar_lt_split_add_data h
  late_point_data := posEventuallyData_of_late_point
  mk_cotrans_data := ltQuot_cotrans_mk_data
  mk_cotrans_data_to_prop := ltQuot_cotrans_mk_data_to_prop
  quotient_cotrans_from_witness := fun hab hc =>
    ltQuot_cotrans_data_from_witness hab hc

/-- Honest residual marker after the data bridge: the remaining work is not the
cotransitivity split itself, but extracting quotient representatives and
positive-tail data from the current Prop-level quotient order. -/
structure CRealQuotCOFDataCotransResidualFrontier : Type where
  representative_extraction : Prop
  lt_witness_extraction : Prop

def cRealQuotCOFDataCotransResidualFrontier :
    CRealQuotCOFDataCotransResidualFrontier where
  representative_extraction := True
  lt_witness_extraction := True

end BishopCReal

