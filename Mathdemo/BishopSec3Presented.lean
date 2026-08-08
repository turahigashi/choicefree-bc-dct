import Mathdemo.BishopSec1Presented
import Mathdemo.Internal.CRat_iter500

/-! Technical auxiliary material for the public import closure. -/

namespace BishopSec3P

open BishopCReal BishopSec1P

/-- Technical lemma used in the public import closure. -/
noncomputable def rampFnC (u v y : CReal) (hpos : PosEventuallyData (CReal.sub v u)) : CReal :=
  CReal.max
    (CReal.min
      (CReal.mul (CReal.invPos (CReal.sub v u) hpos) (CReal.sub y u))
      CReal.one)
    CReal.zero

#check @rampFnC
#print axioms rampFnC

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
private theorem mkQuot_maxSeqWith_eqC (x y : CReal) :
    mkQuot (maxSeqWith cRatScalarMulArch x y)
      = maxQuotCOFWith cRatScalarMulArch (mkQuot x) (mkQuot y) := by
  rw [maxQuotCOF_eq_concrete cRatScalarMulArch (mkQuot x) (mkQuot y)]
  rfl

/-- Technical lemma used in the public import closure. -/
theorem CReal.max_leC {a b c : CReal}
    (hac : RegularSeqLe a c) (hbc : RegularSeqLe b c) :
    RegularSeqLe (CReal.max a b) c := by
  -- body = (c-b) + (c-a) - |a-b|
  let body : CReal :=
    subSeq (addSeq (subSeq c b) (subSeq c a)) (absSeq (subSeq a b))
  -- |a-b| ≤ (c-b) + (c-a)   (= RegularSeqNonneg body)
  have hbody_le :
      RegularSeqLe (absSeq (subSeq a b))
        (addSeq (subSeq c b) (subSeq c a)) := by
    have hd_eq :
        relEventually (subSeq a b)
          (addSeq (subSeq c b) (negSeq (subSeq c a))) := by
      have hq :
          mkQuot (subSeq a b)
            = mkQuot (addSeq (subSeq c b) (negSeq (subSeq c a))) := by
        change subQuot (mkQuot a) (mkQuot b)
          = addQuot (subQuot (mkQuot c) (mkQuot b))
              (negQuot (subQuot (mkQuot c) (mkQuot a)))
        letI : CommRing CRealQuot :=
          cRealQuotCommRingConcreteWith cRatScalarMulArch
        let A : CRealQuot := mkQuot a
        let B : CRealQuot := mkQuot b
        let C : CRealQuot := mkQuot c
        change A - B = (C - B) + -(C - A)
        ring
      exact Quotient.exact hq
    have hA :
        relEventually (absSeq (subSeq a b))
          (absSeq (addSeq (subSeq c b) (negSeq (subSeq c a)))) :=
      absSeq_respects_eventually _ _ hd_eq
    have htri :
        RegularSeqLe
          (absSeq (addSeq (subSeq c b) (negSeq (subSeq c a))))
          (addSeq (absSeq (subSeq c b))
            (absSeq (negSeq (subSeq c a)))) :=
      regularSeqLe_abs_add (subSeq c b) (negSeq (subSeq c a))
    have habs_cb : absSeq (subSeq c b) ≈ subSeq c b :=
      CReal.abs_of_nonneg_E hbc
    have habs_negca : absSeq (negSeq (subSeq c a)) ≈ subSeq c a :=
      relEventually_trans _ _ _
        (absSeq_negSeq_eventually (subSeq c a))
        (CReal.abs_of_nonneg_E hac)
    have hRHS :
        relEventually
          (addSeq (absSeq (subSeq c b)) (absSeq (negSeq (subSeq c a))))
          (addSeq (subSeq c b) (subSeq c a)) :=
      addSeq_respects_eventually _ _ _ _ habs_cb habs_negca
    exact regularSeqLe_of_left_eventual hA
      (regularSeqLe_of_right_eventual hRHS htri)
  have hbody_nonneg : RegularSeqNonneg body := hbody_le
  have hhalf_nonneg : ¬ CReal.ltE CReal.half CReal.zero := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero
      (CReal.ltE_trans CReal.half_pos_E hlt)
  have hprod_nonneg : RegularSeqNonneg (CReal.mul CReal.half body) := by
    change ¬ CReal.ltE (CReal.mul CReal.half body) CReal.zero
    exact CReal.mul_nonneg_E hhalf_nonneg hbody_nonneg
  have hto_prod :
      relEventually (subSeq c (CReal.max a b))
        (CReal.mul CReal.half body) := by
    have hq :
        mkQuot (subSeq c (CReal.max a b))
          = mkQuot (CReal.mul CReal.half body) := by
      change subQuot (mkQuot c) (mkQuot (maxSeqWith cRatScalarMulArch a b))
        = mulQuotConcreteWith cRatScalarMulArch halfQuot
            (subQuot
              (addQuot (subQuot (mkQuot c) (mkQuot b))
                (subQuot (mkQuot c) (mkQuot a)))
              (absQuot (subQuot (mkQuot a) (mkQuot b))))
      rw [mkQuot_maxSeqWith_eqC a b]
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let C : CRealQuot := mkQuot c
      let U : CRealQuot := absQuot (subQuot A B)
      change C - (halfQuot * ((A + B) + U))
        = halfQuot * (((C - B) + (C - A)) - U)
      have hhalf : (halfQuot : CRealQuot) + halfQuot = 1 := halfQuot_add_half
      linear_combination (-C) * hhalf
    exact Quotient.exact hq
  change RegularSeqNonneg (subSeq c (CReal.max a b))
  exact regularSeqNonneg_of_eventual hto_prod hprod_nonneg

#print axioms BishopSec3P.CReal.max_leC

/-- Technical lemma used in the public import closure. -/
theorem CReal.zero_le_oneC : RegularSeqLe CReal.zero CReal.one :=
  regularSeqLe_of_ltPropC
    (regularSeqLtProp_of_right_eventual halfPow_zero
      (regularSeqLtProp_zero_halfPow 0))

/-- Technical lemma used in the public import closure. -/
theorem rampFnC_bound (u v y : CReal) (hpos : PosEventuallyData (CReal.sub v u)) :
    RegularSeqNonneg (rampFnC u v y hpos)
      ∧ RegularSeqLe (rampFnC u v y hpos) CReal.one := by
  refine ⟨?_, ?_⟩
  · -- 0 ≤ max(min w 1, 0)
    exact CReal.max_zero_nonneg_E _
  · -- max(min w 1, 0) ≤ 1
    exact CReal.max_leC (CReal.min_le_rightC _ _) CReal.zero_le_oneC

#print axioms BishopSec3P.rampFnC_bound

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem CReal.le_max_leftC (a b : CReal) :
    RegularSeqLe a (CReal.max a b) := by
  let d : CReal := subSeq a b
  let body : CReal := subSeq (absSeq d) d
  have hhalf_nonneg : ¬ CReal.ltE CReal.half CReal.zero := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero
      (CReal.ltE_trans CReal.half_pos_E hlt)
  have hbody_nonneg : RegularSeqNonneg body := by
    change RegularSeqLe d (absSeq d)
    apply regularSeqLe_of_not_ltQuot
    change ¬ CReal.ltE (absSeq d) d
    exact CReal.le_abs_self_E d
  have hprod_nonneg : RegularSeqNonneg (CReal.mul CReal.half body) := by
    change ¬ CReal.ltE (CReal.mul CReal.half body) CReal.zero
    exact CReal.mul_nonneg_E hhalf_nonneg hbody_nonneg
  have hto_prod :
      relEventually (subSeq (CReal.max a b) a)
        (CReal.mul CReal.half body) := by
    have hq :
        mkQuot (subSeq (CReal.max a b) a)
          = mkQuot (CReal.mul CReal.half body) := by
      change subQuot (mkQuot (maxSeqWith cRatScalarMulArch a b)) (mkQuot a)
        = mulQuotConcreteWith cRatScalarMulArch halfQuot
            (subQuot (absQuot (subQuot (mkQuot a) (mkQuot b)))
              (subQuot (mkQuot a) (mkQuot b)))
      rw [mkQuot_maxSeqWith_eqC a b]
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let D : CRealQuot := A - B
      let U : CRealQuot := absQuot D
      change (halfQuot * ((A + B) + U)) - A = halfQuot * (U - D)
      have hhalf : (halfQuot : CRealQuot) + halfQuot = 1 := halfQuot_add_half
      linear_combination A * hhalf
    exact Quotient.exact hq
  change RegularSeqNonneg (subSeq (CReal.max a b) a)
  exact regularSeqNonneg_of_eventual hto_prod hprod_nonneg

/-- Technical lemma used in the public import closure. -/
theorem CReal.le_max_rightC (a b : CReal) :
    RegularSeqLe b (CReal.max a b) := by
  let d : CReal := subSeq a b
  let body : CReal := subSeq (absSeq d) (negSeq d)
  have hhalf_nonneg : ¬ CReal.ltE CReal.half CReal.zero := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero
      (CReal.ltE_trans CReal.half_pos_E hlt)
  have hbody_nonneg : RegularSeqNonneg body := by
    change RegularSeqLe (negSeq d) (absSeq d)
    apply regularSeqLe_of_not_ltQuot
    change ¬ CReal.ltE (absSeq d) (negSeq d)
    exact CReal.neg_le_abs_E d
  have hprod_nonneg : RegularSeqNonneg (CReal.mul CReal.half body) := by
    change ¬ CReal.ltE (CReal.mul CReal.half body) CReal.zero
    exact CReal.mul_nonneg_E hhalf_nonneg hbody_nonneg
  have hto_prod :
      relEventually (subSeq (CReal.max a b) b)
        (CReal.mul CReal.half body) := by
    have hq :
        mkQuot (subSeq (CReal.max a b) b)
          = mkQuot (CReal.mul CReal.half body) := by
      change subQuot (mkQuot (maxSeqWith cRatScalarMulArch a b)) (mkQuot b)
        = mulQuotConcreteWith cRatScalarMulArch halfQuot
            (subQuot (absQuot (subQuot (mkQuot a) (mkQuot b)))
              (negQuot (subQuot (mkQuot a) (mkQuot b))))
      rw [mkQuot_maxSeqWith_eqC a b]
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let A : CRealQuot := mkQuot a
      let B : CRealQuot := mkQuot b
      let D : CRealQuot := A - B
      let U : CRealQuot := absQuot D
      change (halfQuot * ((A + B) + U)) - B = halfQuot * (U - -D)
      have hhalf : (halfQuot : CRealQuot) + halfQuot = 1 := halfQuot_add_half
      linear_combination B * hhalf
    exact Quotient.exact hq
  change RegularSeqNonneg (subSeq (CReal.max a b) b)
  exact regularSeqNonneg_of_eventual hto_prod hprod_nonneg

/-- Technical lemma used in the public import closure. -/
theorem CReal.max_eq_right_of_leC {x y : CReal} (h : RegularSeqLe x y) :
    CReal.max x y ≈ y :=
  regularSeqLe_antisymm_eventuallyC
    (CReal.max_leC h (regularSeqLe_refl y))
    (CReal.le_max_rightC x y)

/-- `y ≤ x ⟹ max x y ≈ x`。 -/
theorem CReal.max_eq_left_of_leC {x y : CReal} (h : RegularSeqLe y x) :
    CReal.max x y ≈ x :=
  regularSeqLe_antisymm_eventuallyC
    (CReal.max_leC (regularSeqLe_refl x) h)
    (CReal.le_max_leftC x y)

/-- Technical lemma used in the public import closure. -/
theorem CReal.min_eq_right_of_leC {x y : CReal} (h : RegularSeqLe y x) :
    CReal.min x y ≈ y :=
  regularSeqLe_antisymm_eventuallyC
    (CReal.min_le_rightC x y)
    (CReal.le_minC h (regularSeqLe_refl y))

#print axioms BishopSec3P.CReal.le_max_leftC
#print axioms BishopSec3P.CReal.max_eq_right_of_leC
#print axioms BishopSec3P.CReal.min_eq_right_of_leC

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem rampFnC_zero (u v y : CReal) (hpos : PosEventuallyData (CReal.sub v u))
    (hyu : RegularSeqLe y u) :
    rampFnC u v y hpos ≈ CReal.zero := by
  show CReal.max (CReal.min (CReal.mul (CReal.invPos (CReal.sub v u) hpos)
      (CReal.sub y u)) CReal.one) CReal.zero ≈ CReal.zero
  set inv : CReal := CReal.invPos (CReal.sub v u) hpos with hinv_def
  set prod : CReal := CReal.mul inv (CReal.sub y u) with hprod_def
  -- inv > 0 → inv ≥ 0
  have hinv_pos_E : CReal.ltE CReal.zero inv :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData (CReal.sub v u) hpos)
  have hinv_nonneg : RegularSeqNonneg inv := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero (CReal.ltE_trans hinv_pos_E hlt)
  -- u − y ≥ 0（= hyu）
  have huy_nonneg : RegularSeqNonneg (subSeq u y) := hyu
  -- inv·(u−y) ≥ 0
  have hpos_prod : RegularSeqNonneg (CReal.mul inv (subSeq u y)) :=
    CReal.mul_nonneg_E hinv_nonneg huy_nonneg
  -- prod ≤ 0：subSeq 0 prod = −prod ≈ inv·(u−y)
  have hprod_le_zero : RegularSeqLe prod CReal.zero := by
    change RegularSeqNonneg (subSeq CReal.zero prod)
    have hrel : relEventually (subSeq CReal.zero prod)
        (CReal.mul inv (subSeq u y)) := by
      have hq : mkQuot (subSeq CReal.zero prod)
          = mkQuot (CReal.mul inv (subSeq u y)) := by
        letI : CommRing CRealQuot :=
          cRealQuotCommRingConcreteWith cRatScalarMulArch
        have hz0 : mkQuot CReal.zero = (0 : CRealQuot) := rfl
        change subQuot (mkQuot CReal.zero)
            (mulQuotConcreteWith cRatScalarMulArch (mkQuot inv)
              (mkQuot (CReal.sub y u)))
          = mulQuotConcreteWith cRatScalarMulArch (mkQuot inv)
              (subQuot (mkQuot u) (mkQuot y))
        rw [hz0]
        change (0 : CRealQuot) - (mkQuot inv) * ((mkQuot y) - (mkQuot u))
          = (mkQuot inv) * ((mkQuot u) - (mkQuot y))
        ring
      exact Quotient.exact hq
    exact regularSeqNonneg_of_eventual hrel hpos_prod
  -- min prod 1 ≤ 0
  have hmin_le_zero : RegularSeqLe (CReal.min prod CReal.one) CReal.zero :=
    regularSeqLe_trans (CReal.min_le_leftC prod CReal.one) hprod_le_zero
  -- rampFnC = max (min prod 1) 0 ≈ 0
  exact CReal.max_eq_right_of_leC hmin_le_zero

#print axioms BishopSec3P.rampFnC_zero

/-- Technical lemma used in the public import closure. -/
theorem rampFnC_one (u v y : CReal) (hpos : PosEventuallyData (CReal.sub v u))
    (hyv : RegularSeqLe v y) :
    rampFnC u v y hpos ≈ CReal.one := by
  show CReal.max (CReal.min (CReal.mul (CReal.invPos (CReal.sub v u) hpos)
      (CReal.sub y u)) CReal.one) CReal.zero ≈ CReal.one
  set inv : CReal := CReal.invPos (CReal.sub v u) hpos with hinv_def
  set prod : CReal := CReal.mul inv (CReal.sub y u) with hprod_def
  -- inv ≥ 0
  have hinv_pos_E : CReal.ltE CReal.zero inv :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData (CReal.sub v u) hpos)
  have hinv_nonneg : RegularSeqNonneg inv := by
    intro hlt
    exact CReal.ltE_irrefl CReal.zero (CReal.ltE_trans hinv_pos_E hlt)
  -- (v−u) ≤ (y−u)  from  v ≤ y
  have hvu_le_yu : RegularSeqLe (CReal.sub v u) (CReal.sub y u) := by
    change RegularSeqNonneg (subSeq (CReal.sub y u) (CReal.sub v u))
    have hrel : relEventually (subSeq (CReal.sub y u) (CReal.sub v u))
        (subSeq y v) := by
      have hq : mkQuot (subSeq (CReal.sub y u) (CReal.sub v u))
          = mkQuot (subSeq y v) := by
        letI : CommRing CRealQuot :=
          cRealQuotCommRingConcreteWith cRatScalarMulArch
        change ((mkQuot y) - (mkQuot u)) - ((mkQuot v) - (mkQuot u))
          = (mkQuot y) - (mkQuot v)
        ring
      exact Quotient.exact hq
    exact regularSeqNonneg_of_eventual hrel hyv
  -- inv·(v−u) ≤ inv·(y−u) = prod
  have hmul_le : RegularSeqLe (CReal.mul inv (CReal.sub v u)) prod :=
    regularSeqLe_mul_left_of_nonnegC hvu_le_yu hinv_nonneg
  -- inv·(v−u) ≈ 1
  have hcancel : CReal.mul inv (CReal.sub v u) ≈ CReal.one := by
    have hcomm : CReal.mul inv (CReal.sub v u)
        ≈ CReal.mul (CReal.sub v u) inv := by
      have hq : mkQuot (CReal.mul inv (CReal.sub v u))
          = mkQuot (CReal.mul (CReal.sub v u) inv) := by
        letI : CommRing CRealQuot :=
          cRealQuotCommRingConcreteWith cRatScalarMulArch
        change (mkQuot inv) * (mkQuot (CReal.sub v u))
          = (mkQuot (CReal.sub v u)) * (mkQuot inv)
        ring
      exact Quotient.exact hq
    exact Setoid.trans hcomm
      (CReal.mul_invPos_eventually_one (CReal.sub v u) hpos)
  -- 1 ≤ prod : one ≈ inv·(v−u) ≤ prod
  have hone_le_prod : RegularSeqLe CReal.one prod := by
    change RegularSeqNonneg (subSeq prod CReal.one)
    have hle : RegularSeqNonneg (subSeq prod (CReal.mul inv (CReal.sub v u))) :=
      hmul_le
    have hrel : relEventually (subSeq prod CReal.one)
        (subSeq prod (CReal.mul inv (CReal.sub v u))) :=
      subSeq_respects_eventually prod prod CReal.one
        (CReal.mul inv (CReal.sub v u))
        (relEventually_refl prod) (Setoid.symm hcancel)
    exact regularSeqNonneg_of_eventual hrel hle
  -- Technical note.
  have hone_le_min : RegularSeqLe CReal.one (CReal.min prod CReal.one) :=
    CReal.le_minC hone_le_prod (regularSeqLe_refl CReal.one)
  have hzero_le_min : RegularSeqLe CReal.zero (CReal.min prod CReal.one) :=
    regularSeqLe_trans CReal.zero_le_oneC hone_le_min
  -- max (min prod 1) 0 ≈ min prod 1 ≈ 1
  have hmax_eq : CReal.max (CReal.min prod CReal.one) CReal.zero
      ≈ CReal.min prod CReal.one :=
    CReal.max_eq_left_of_leC hzero_le_min
  have hmin_eq : CReal.min prod CReal.one ≈ CReal.one :=
    CReal.min_eq_right_of_leC hone_le_prod
  exact Setoid.trans hmax_eq hmin_eq

#print axioms BishopSec3P.rampFnC_one

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem cof_min_one_lt_one_impC {W : CReal}
    (h : regularSeqLtProp (CReal.min W CReal.one) CReal.one) :
    regularSeqLtProp W CReal.one := by
  rcases regularSeqLtProp_cotrans (CReal.min W CReal.one) CReal.one W h with hl | hr
  · exfalso
    have h1W : RegularSeqLe CReal.one W := by
      apply regularSeqLe_of_not_ltQuot
      intro hyx
      have hW1 : regularSeqLtProp W CReal.one := by
        change PosEventually (subSeq CReal.one W) at hyx
        exact hyx
      have hmW : CReal.min W CReal.one ≈ W :=
        CReal.min_eq_left_of_leC (regularSeqLe_of_ltPropC hW1)
      exact regularSeqLtProp_irrefl W
        (regularSeqLtProp_of_left_eventual (Setoid.symm hmW) hl)
    have hmin1 : CReal.min W CReal.one ≈ CReal.one :=
      CReal.min_eq_right_of_leC h1W
    exact regularSeqLtProp_irrefl CReal.one
      (regularSeqLtProp_of_left_eventual (Setoid.symm hmin1) h)
  · exact hr

#print axioms BishopSec3P.cof_min_one_lt_one_impC

/-- Technical lemma used in the public import closure. -/
theorem rampFnC_lt_one_imp (u v y : CReal) (hpos : PosEventuallyData (CReal.sub v u))
    (h : regularSeqLtProp (rampFnC u v y hpos) CReal.one) :
    regularSeqLtProp y v := by
  have hvu_pos : regularSeqLtProp CReal.zero (CReal.sub v u) :=
    regularSeqLtProp_zero_of_posData hpos
  set inv : CReal := CReal.invPos (CReal.sub v u) hpos with hinv_def
  have h' : regularSeqLtProp
      (CReal.max (CReal.min (CReal.mul inv (CReal.sub y u)) CReal.one) CReal.zero)
      CReal.one := h
  -- step1: min(inv·(y−u),1) < 1
  have hstep1 : regularSeqLtProp
      (CReal.min (CReal.mul inv (CReal.sub y u)) CReal.one) CReal.one :=
    regularSeqLtProp_of_le_of_lt
      (CReal.le_max_leftC (CReal.min (CReal.mul inv (CReal.sub y u)) CReal.one) CReal.zero) h'
  -- step2: inv·(y−u) < 1
  have hstep2 : regularSeqLtProp (CReal.mul inv (CReal.sub y u)) CReal.one :=
    cof_min_one_lt_one_impC hstep1
  -- step3: (v−u)·(inv·(y−u)) < (v−u)·1
  have hstep3 : regularSeqLtProp
      (CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u)))
      (CReal.mul (CReal.sub v u) CReal.one) :=
    mul_lt_mul_of_pos_leftC hstep2 hvu_pos
  -- right: (v−u)·1 ≈ v−u
  have hstep3R : regularSeqLtProp
      (CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u))) (CReal.sub v u) :=
    regularSeqLtProp_of_right_eventual (CReal.mul_one (CReal.sub v u)) hstep3
  -- assoc: (v−u)·(inv·(y−u)) ≈ ((v−u)·inv)·(y−u)
  have hassoc : CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u))
      ≈ CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u) := by
    have hq : mkQuot (CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u)))
        = mkQuot (CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u)) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      change (mkQuot (CReal.sub v u)) * ((mkQuot inv) * (mkQuot (CReal.sub y u)))
        = ((mkQuot (CReal.sub v u)) * (mkQuot inv)) * (mkQuot (CReal.sub y u))
      ring
    exact Quotient.exact hq
  have hstep3L : regularSeqLtProp
      (CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u)) (CReal.sub v u) :=
    regularSeqLtProp_of_left_eventual (Setoid.symm hassoc) hstep3R
  -- cancel: (v−u)·inv ≈ 1  → ((v−u)·inv)·(y−u) ≈ y−u
  have hinv_cancel : CReal.mul (CReal.sub v u) inv ≈ CReal.one :=
    CReal.mul_invPos_eventually_one (CReal.sub v u) hpos
  have hcancel2 : CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u)
      ≈ CReal.sub y u := by
    have hq : mkQuot (CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u))
        = mkQuot (CReal.mul CReal.one (CReal.sub y u)) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      have h1 : mkQuot (CReal.mul (CReal.sub v u) inv) = mkQuot CReal.one :=
        Quotient.sound hinv_cancel
      change (mkQuot (CReal.mul (CReal.sub v u) inv)) * (mkQuot (CReal.sub y u))
        = (mkQuot CReal.one) * (mkQuot (CReal.sub y u))
      rw [h1]
    exact Setoid.trans (Quotient.exact hq) (CReal.one_mul (CReal.sub y u))
  have hstep4 : regularSeqLtProp (CReal.sub y u) (CReal.sub v u) :=
    regularSeqLtProp_of_left_eventual (Setoid.symm hcancel2) hstep3L
  -- y−u < v−u  →  y < v（subSeq cancel-right）
  show PosEventually (subSeq v y)
  have hrel : relEventually (subSeq (CReal.sub v u) (CReal.sub y u)) (subSeq v y) := by
    have hq : mkQuot (subSeq (CReal.sub v u) (CReal.sub y u)) = mkQuot (subSeq v y) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      change ((mkQuot v) - (mkQuot u)) - ((mkQuot y) - (mkQuot u))
        = (mkQuot v) - (mkQuot y)
      ring
    exact Quotient.exact hq
  exact posEventually_respects _ _ hrel hstep4

#print axioms BishopSec3P.rampFnC_lt_one_imp

/-- Technical lemma used in the public import closure. -/
theorem cof_pos_of_max_zero_posC {A : CReal}
    (h : regularSeqLtProp CReal.zero (CReal.max A CReal.zero)) :
    regularSeqLtProp CReal.zero A := by
  have hmax_le_abs : RegularSeqLe (CReal.max A CReal.zero) (CReal.abs A) :=
    regularSeqLe_of_not_ltQuot (CReal.max A CReal.zero) (CReal.abs A) (CReal.max_le_abs_E A)
  have habs : regularSeqLtProp CReal.zero (CReal.abs A) :=
    regularSeqLtProp_of_lt_of_le h hmax_le_abs
  rcases CReal.lt_or_lt_of_abs_pos_E habs with hpos | hneg
  · exact hpos
  · exfalso
    have hmax0 : CReal.max A CReal.zero ≈ CReal.zero :=
      CReal.max_eq_right_of_leC (regularSeqLe_of_ltPropC hneg)
    exact regularSeqLtProp_irrefl CReal.zero
      (regularSeqLtProp_of_right_eventual hmax0 h)

#print axioms BishopSec3P.cof_pos_of_max_zero_posC

/-- Technical lemma used in the public import closure. -/
theorem rampFnC_pos_imp (u v y : CReal) (hpos : PosEventuallyData (CReal.sub v u))
    (h : regularSeqLtProp CReal.zero (rampFnC u v y hpos)) :
    regularSeqLtProp u y := by
  have hvu_pos : regularSeqLtProp CReal.zero (CReal.sub v u) :=
    regularSeqLtProp_zero_of_posData hpos
  set inv : CReal := CReal.invPos (CReal.sub v u) hpos with hinv_def
  have h' : regularSeqLtProp CReal.zero
      (CReal.max (CReal.min (CReal.mul inv (CReal.sub y u)) CReal.one) CReal.zero) := h
  -- step1: 0 < min(inv·(y−u),1)
  have hstep1 : regularSeqLtProp CReal.zero
      (CReal.min (CReal.mul inv (CReal.sub y u)) CReal.one) :=
    cof_pos_of_max_zero_posC h'
  -- step2: 0 < inv·(y−u)
  have hstep2 : regularSeqLtProp CReal.zero (CReal.mul inv (CReal.sub y u)) :=
    regularSeqLtProp_of_lt_of_le hstep1
      (CReal.min_le_leftC (CReal.mul inv (CReal.sub y u)) CReal.one)
  -- step3: (v−u)·0 < (v−u)·(inv·(y−u))
  have hstep3 : regularSeqLtProp
      (CReal.mul (CReal.sub v u) CReal.zero)
      (CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u))) :=
    mul_lt_mul_of_pos_leftC hstep2 hvu_pos
  -- left: (v−u)·0 ≈ 0
  have hmulzero : CReal.mul (CReal.sub v u) CReal.zero ≈ CReal.zero := by
    have hq : mkQuot (CReal.mul (CReal.sub v u) CReal.zero) = mkQuot CReal.zero := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      have hz0 : mkQuot CReal.zero = (0 : CRealQuot) := rfl
      change (mkQuot (CReal.sub v u)) * (mkQuot CReal.zero) = (0 : CRealQuot)
      rw [hz0]; ring
    exact Quotient.exact hq
  have hstep3L : regularSeqLtProp CReal.zero
      (CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u))) :=
    regularSeqLtProp_of_left_eventual (Setoid.symm hmulzero) hstep3
  -- assoc + cancel: (v−u)·(inv·(y−u)) ≈ y−u
  have hassoc : CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u))
      ≈ CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u) := by
    have hq : mkQuot (CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u)))
        = mkQuot (CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u)) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      change (mkQuot (CReal.sub v u)) * ((mkQuot inv) * (mkQuot (CReal.sub y u)))
        = ((mkQuot (CReal.sub v u)) * (mkQuot inv)) * (mkQuot (CReal.sub y u))
      ring
    exact Quotient.exact hq
  have hinv_cancel : CReal.mul (CReal.sub v u) inv ≈ CReal.one :=
    CReal.mul_invPos_eventually_one (CReal.sub v u) hpos
  have hcancel2 : CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u)
      ≈ CReal.sub y u := by
    have hq : mkQuot (CReal.mul (CReal.mul (CReal.sub v u) inv) (CReal.sub y u))
        = mkQuot (CReal.mul CReal.one (CReal.sub y u)) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      have h1 : mkQuot (CReal.mul (CReal.sub v u) inv) = mkQuot CReal.one :=
        Quotient.sound hinv_cancel
      change (mkQuot (CReal.mul (CReal.sub v u) inv)) * (mkQuot (CReal.sub y u))
        = (mkQuot CReal.one) * (mkQuot (CReal.sub y u))
      rw [h1]
    exact Setoid.trans (Quotient.exact hq) (CReal.one_mul (CReal.sub y u))
  have hcancel : CReal.mul (CReal.sub v u) (CReal.mul inv (CReal.sub y u))
      ≈ CReal.sub y u := Setoid.trans hassoc hcancel2
  -- 0 < y−u
  have hstep4 : regularSeqLtProp CReal.zero (CReal.sub y u) :=
    regularSeqLtProp_of_right_eventual hcancel hstep3L
  -- 0 < y−u  →  u < y（subSeq cancel）
  show PosEventually (subSeq y u)
  have hrel : relEventually (subSeq (CReal.sub y u) CReal.zero) (subSeq y u) := by
    have hq : mkQuot (subSeq (CReal.sub y u) CReal.zero) = mkQuot (subSeq y u) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      have hz0 : mkQuot CReal.zero = (0 : CRealQuot) := rfl
      change ((mkQuot y) - (mkQuot u)) - (mkQuot CReal.zero) = (mkQuot y) - (mkQuot u)
      rw [hz0]; ring
    exact Quotient.exact hq
  exact posEventually_respects _ _ hrel hstep4

#print axioms BishopSec3P.rampFnC_pos_imp

/-- Technical lemma used in the public import closure. -/
theorem rampFnC_zero_leC (u v y : CReal) (hpos : PosEventuallyData (CReal.sub v u)) :
    RegularSeqLe CReal.zero (rampFnC u v y hpos) := by
  unfold rampFnC
  exact CReal.le_max_rightC _ CReal.zero

#print axioms BishopSec3P.rampFnC_zero_leC

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_ramp_le_global_of_right_le_leftC
    {u v p q : CReal} (hupos : PosEventuallyData (CReal.sub v u))
    (hppos : PosEventuallyData (CReal.sub q p))
    (huv : regularSeqLtProp u v) (hpq : regularSeqLtProp p q)
    (hqu : RegularSeqLe q u) :
    ∀ y : CReal, RegularSeqLe (rampFnC u v y hupos) (rampFnC p q y hppos) := by
  intro y
  apply regularSeqLe_of_not_ltQuot
  intro hbad
  have hbad' : regularSeqLtProp (rampFnC p q y hppos) (rampFnC u v y hupos) := hbad
  have hpos : regularSeqLtProp CReal.zero (rampFnC u v y hupos) :=
    regularSeqLtProp_of_le_of_lt (rampFnC_zero_leC p q y hppos) hbad'
  have hlt_one : regularSeqLtProp (rampFnC p q y hppos) CReal.one :=
    regularSeqLtProp_of_lt_of_le hbad' (rampFnC_bound u v y hupos).2
  have huy : regularSeqLtProp u y := rampFnC_pos_imp u v y hupos hpos
  have hyq : regularSeqLtProp y q := rampFnC_lt_one_imp p q y hppos hlt_one
  have huq : regularSeqLtProp u q :=
    regularSeqLtProp_of_lt_of_le huy (regularSeqLe_of_ltPropC hyq)
  exact regularSeqLtProp_irrefl u (regularSeqLtProp_of_lt_of_le huq hqu)

#print axioms BishopSec3P.thm36A2_ramp_le_global_of_right_le_leftC

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_ramp_le_global_of_intervalC
    {a b u v p q : CReal}
    (hupos : PosEventuallyData (CReal.sub v u))
    (hppos : PosEventuallyData (CReal.sub q p))
    (hau : RegularSeqLe a u) (huv : regularSeqLtProp u v) (_hvb : RegularSeqLe v b)
    (_hap : RegularSeqLe a p) (hpq : regularSeqLtProp p q) (hqb : RegularSeqLe q b)
    (hfg : ∀ x : CReal, RegularSeqLe a x → RegularSeqLe x b →
      RegularSeqLe (rampFnC u v x hupos) (rampFnC p q x hppos)) :
    ∀ y : CReal, RegularSeqLe (rampFnC u v y hupos) (rampFnC p q y hppos) := by
  intro y
  apply regularSeqLe_of_not_ltQuot
  intro hbad
  have hbad' : regularSeqLtProp (rampFnC p q y hppos) (rampFnC u v y hupos) := hbad
  have hpos : regularSeqLtProp CReal.zero (rampFnC u v y hupos) :=
    regularSeqLtProp_of_le_of_lt (rampFnC_zero_leC p q y hppos) hbad'
  have hlt_one : regularSeqLtProp (rampFnC p q y hppos) CReal.one :=
    regularSeqLtProp_of_lt_of_le hbad' (rampFnC_bound u v y hupos).2
  have huy : regularSeqLtProp u y := rampFnC_pos_imp u v y hupos hpos
  have hyq : regularSeqLtProp y q := rampFnC_lt_one_imp p q y hppos hlt_one
  have hay : RegularSeqLe a y :=
    regularSeqLe_trans hau (regularSeqLe_of_ltPropC huy)
  have hyb : RegularSeqLe y b :=
    regularSeqLe_trans (regularSeqLe_of_ltPropC hyq) hqb
  exact regularSeqLtProp_irrefl (rampFnC p q y hppos)
    (regularSeqLtProp_of_lt_of_le hbad' (hfg y hay hyb))

#print axioms BishopSec3P.thm36A2_ramp_le_global_of_intervalC

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_mul_max_zeroC (c z : CReal) (hc : ¬ CReal.ltE c CReal.zero) :
    CReal.mul c (CReal.max z CReal.zero) ≈ CReal.max (CReal.mul c z) CReal.zero := by
  -- Technical note.
  have haz : CReal.abs (CReal.add z (CReal.neg CReal.zero)) ≈ CReal.abs z := by
    apply absSeq_respects_eventually
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    have hz0 : mkQuot CReal.zero = (0 : CRealQuot) := rfl
    have hq : mkQuot (CReal.add z (CReal.neg CReal.zero)) = mkQuot z := by
      change (mkQuot z) + (-(mkQuot CReal.zero)) = mkQuot z
      rw [hz0]; ring
    exact Quotient.exact hq
  have hacz : CReal.abs (CReal.add (CReal.mul c z) (CReal.neg CReal.zero))
      ≈ CReal.abs (CReal.mul c z) := by
    apply absSeq_respects_eventually
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    have hz0 : mkQuot CReal.zero = (0 : CRealQuot) := rfl
    have hq : mkQuot (CReal.add (CReal.mul c z) (CReal.neg CReal.zero))
        = mkQuot (CReal.mul c z) := by
      change (mkQuot (CReal.mul c z)) + (-(mkQuot CReal.zero)) = mkQuot (CReal.mul c z)
      rw [hz0]; ring
    exact Quotient.exact hq
  -- |c·z| ≈ c·|z| （c ≥ 0）
  have hcabs : CReal.abs (CReal.mul c z) ≈ CReal.mul c (CReal.abs z) :=
    Setoid.trans (CReal.abs_mul c z)
      (mulSeqConcrete_respects_eventually cRatScalarMulArch (CReal.abs c) c
        (CReal.abs z) (CReal.abs z)
        (CReal.abs_of_nonneg_E hc) (relEventually_refl (CReal.abs z)))
  -- Technical note.
  refine Setoid.trans
    (mulSeqConcrete_respects_eventually cRatScalarMulArch c c
      (CReal.max z CReal.zero)
      (CReal.mul CReal.half
        (CReal.add (CReal.add z CReal.zero)
          (CReal.abs (CReal.add z (CReal.neg CReal.zero)))))
      (relEventually_refl c) (CReal.max_halfsum z CReal.zero))
    (Setoid.trans ?_ (Setoid.symm (CReal.max_halfsum (CReal.mul c z) CReal.zero)))
  -- goal: c·(½·((z+0)+|z+(−0)|)) ≈ ½·((c·z+0)+|c·z+(−0)|)
  have mid1 :
      CReal.mul c (CReal.mul CReal.half
        (CReal.add (CReal.add z CReal.zero)
          (CReal.abs (CReal.add z (CReal.neg CReal.zero)))))
      ≈ CReal.mul c (CReal.mul CReal.half
        (CReal.add (CReal.add z CReal.zero) (CReal.abs z))) :=
    mulSeqConcrete_respects_eventually cRatScalarMulArch c c _ _ (relEventually_refl c)
      (mulSeqConcrete_respects_eventually cRatScalarMulArch CReal.half CReal.half _ _
        (relEventually_refl CReal.half)
        (addSeq_respects_eventually (CReal.add z CReal.zero) (CReal.add z CReal.zero) _ _
          (relEventually_refl _) haz))
  have mid2 :
      CReal.mul CReal.half
        (CReal.add (CReal.add (CReal.mul c z) CReal.zero)
          (CReal.abs (CReal.add (CReal.mul c z) (CReal.neg CReal.zero))))
      ≈ CReal.mul CReal.half
        (CReal.add (CReal.add (CReal.mul c z) CReal.zero) (CReal.mul c (CReal.abs z))) :=
    mulSeqConcrete_respects_eventually cRatScalarMulArch CReal.half CReal.half _ _
      (relEventually_refl CReal.half)
      (addSeq_respects_eventually _ _ _ _ (relEventually_refl _) (Setoid.trans hacz hcabs))
  have hring :
      CReal.mul c (CReal.mul CReal.half
        (CReal.add (CReal.add z CReal.zero) (CReal.abs z)))
      ≈ CReal.mul CReal.half
        (CReal.add (CReal.add (CReal.mul c z) CReal.zero) (CReal.mul c (CReal.abs z))) := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    have hz0 : mkQuot CReal.zero = (0 : CRealQuot) := rfl
    refine Quotient.exact ?_
    change (mkQuot c) * ((mkQuot CReal.half)
        * (((mkQuot z) + (mkQuot CReal.zero)) + (mkQuot (CReal.abs z))))
      = (mkQuot CReal.half)
        * ((((mkQuot c) * (mkQuot z)) + (mkQuot CReal.zero))
            + ((mkQuot c) * (mkQuot (CReal.abs z))))
    rw [hz0]; ring
  exact Setoid.trans mid1 (Setoid.trans hring (Setoid.symm mid2))

#print axioms BishopSec3P.thm36A1_mul_max_zeroC

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_clamp_swapC (z : CReal) :
    CReal.min (CReal.max z CReal.zero) CReal.one
      ≈ CReal.max (CReal.min z CReal.one) CReal.zero := by
  rcases regularSeqLtProp_cotrans CReal.zero CReal.one z CReal.one_pos_E with hz | hz1
  · -- Technical note.
    have h0z : RegularSeqLe CReal.zero z := regularSeqLe_of_ltPropC hz
    have hmaxz : CReal.max z CReal.zero ≈ z := CReal.max_eq_left_of_leC h0z
    have hmin_nn : RegularSeqLe CReal.zero (CReal.min z CReal.one) :=
      CReal.le_minC h0z (regularSeqLe_of_ltPropC CReal.one_pos_E)
    have hL : CReal.min (CReal.max z CReal.zero) CReal.one ≈ CReal.min z CReal.one :=
      minSeqWith_respects_eventually cRatScalarMulArch _ _ _ _ hmaxz
        (relEventually_refl CReal.one)
    have hR : CReal.max (CReal.min z CReal.one) CReal.zero ≈ CReal.min z CReal.one :=
      CReal.max_eq_left_of_leC hmin_nn
    exact Setoid.trans hL (Setoid.symm hR)
  · -- Technical note.
    have hz1' : RegularSeqLe z CReal.one := regularSeqLe_of_ltPropC hz1
    have hminz : CReal.min z CReal.one ≈ z := CReal.min_eq_left_of_leC hz1'
    have hmax_le1 : RegularSeqLe (CReal.max z CReal.zero) CReal.one :=
      CReal.max_leC hz1' (regularSeqLe_of_ltPropC CReal.one_pos_E)
    have hL : CReal.min (CReal.max z CReal.zero) CReal.one ≈ CReal.max z CReal.zero :=
      CReal.min_eq_left_of_leC hmax_le1
    have hR : CReal.max (CReal.min z CReal.one) CReal.zero ≈ CReal.max z CReal.zero :=
      maxSeqWith_respects_eventually cRatScalarMulArch _ _ _ _ hminz
        (relEventually_refl CReal.zero)
    exact Setoid.trans hL (Setoid.symm hR)

#print axioms BishopSec3P.thm36A1_clamp_swapC

/-- Technical lemma used in the public import closure. -/
theorem sub_min_eq_max_subC (x u : CReal) :
    CReal.add x (CReal.neg (CReal.min x u))
      ≈ CReal.max (CReal.add x (CReal.neg u)) CReal.zero := by
  letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
  have hz0 : mkQuot CReal.zero = (0 : CRealQuot) := rfl
  have hHH : (mkQuot CReal.half) + (mkQuot CReal.half) = (1 : CRealQuot) := by
    calc (mkQuot CReal.half) + (mkQuot CReal.half)
        = mkQuot (CReal.add CReal.half CReal.half) := rfl
      _ = mkQuot CReal.one := Quotient.sound CReal.half_add_half
      _ = (1 : CRealQuot) := rfl
  set T : CReal := CReal.abs (CReal.add x (CReal.neg u)) with hT
  have hminA : CReal.min x u
      ≈ CReal.mul CReal.half (CReal.add (CReal.add x u) (CReal.neg T)) := CReal.min_halfsum x u
  have hA0 : CReal.add x (CReal.neg (CReal.min x u))
      ≈ CReal.add x (CReal.neg (CReal.mul CReal.half (CReal.add (CReal.add x u) (CReal.neg T)))) :=
    addSeq_respects_eventually x x _ _ (relEventually_refl x)
      (negSeq_respects_eventually _ _ hminA)
  have hAring :
      CReal.add x (CReal.neg (CReal.mul CReal.half (CReal.add (CReal.add x u) (CReal.neg T))))
      ≈ CReal.mul CReal.half (CReal.add (CReal.add x (CReal.neg u)) T) := by
    refine Quotient.exact ?_
    change (mkQuot x)
        + (-((mkQuot CReal.half) * (((mkQuot x) + (mkQuot u)) + (-(mkQuot T)))))
      = (mkQuot CReal.half) * (((mkQuot x) + (-(mkQuot u))) + (mkQuot T))
    linear_combination (-(mkQuot x)) * hHH
  have hmaxB : CReal.max (CReal.add x (CReal.neg u)) CReal.zero
      ≈ CReal.mul CReal.half
          (CReal.add (CReal.add (CReal.add x (CReal.neg u)) CReal.zero) T) := by
    refine Setoid.trans (CReal.max_halfsum (CReal.add x (CReal.neg u)) CReal.zero) ?_
    have habsB : CReal.abs (CReal.add (CReal.add x (CReal.neg u)) (CReal.neg CReal.zero)) ≈ T := by
      rw [hT]; apply absSeq_respects_eventually
      have hq : mkQuot (CReal.add (CReal.add x (CReal.neg u)) (CReal.neg CReal.zero))
          = mkQuot (CReal.add x (CReal.neg u)) := by
        change ((mkQuot x) + (-(mkQuot u))) + (-(mkQuot CReal.zero))
          = (mkQuot x) + (-(mkQuot u))
        rw [hz0]; ring
      exact Quotient.exact hq
    exact mulSeqConcrete_respects_eventually cRatScalarMulArch CReal.half CReal.half _ _
      (relEventually_refl CReal.half)
      (addSeq_respects_eventually _ _ _ _ (relEventually_refl _) habsB)
  have hBring :
      CReal.mul CReal.half (CReal.add (CReal.add (CReal.add x (CReal.neg u)) CReal.zero) T)
      ≈ CReal.mul CReal.half (CReal.add (CReal.add x (CReal.neg u)) T) := by
    refine Quotient.exact ?_
    change (mkQuot CReal.half)
        * ((((mkQuot x) + (-(mkQuot u))) + (mkQuot CReal.zero)) + (mkQuot T))
      = (mkQuot CReal.half) * (((mkQuot x) + (-(mkQuot u))) + (mkQuot T))
    rw [hz0]; ring
  exact Setoid.trans hA0
    (Setoid.trans hAring (Setoid.symm (Setoid.trans hmaxB hBring)))

#print axioms BishopSec3P.sub_min_eq_max_subC

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_value_formulaC (u v y : CReal)
    (hpos : PosEventuallyData (CReal.sub v u)) :
    CReal.min
        (CReal.mul (CReal.invPos (CReal.sub v u) hpos)
          (CReal.add y (CReal.neg (CReal.min y u)))) CReal.one
      ≈ rampFnC u v y hpos := by
  set inv := CReal.invPos (CReal.sub v u) hpos with hinv
  have hinv_pos : regularSeqLtProp CReal.zero inv :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData (CReal.sub v u) hpos)
  have hinv_nn : ¬ CReal.ltE inv CReal.zero := fun h =>
    regularSeqLtProp_irrefl inv (regularSeqLtProp_trans inv CReal.zero inv h hinv_pos)
  -- Technical note.
  have h1 : CReal.min (CReal.mul inv (CReal.add y (CReal.neg (CReal.min y u)))) CReal.one
      ≈ CReal.min (CReal.mul inv (CReal.max (CReal.add y (CReal.neg u)) CReal.zero)) CReal.one :=
    minSeqWith_respects_eventually cRatScalarMulArch _ _ _ _
      (mulSeqConcrete_respects_eventually cRatScalarMulArch inv inv _ _
        (relEventually_refl inv) (sub_min_eq_max_subC y u))
      (relEventually_refl CReal.one)
  -- step2: inv·max(z,0) ≈ max(inv·z,0)
  have h2 : CReal.min (CReal.mul inv (CReal.max (CReal.add y (CReal.neg u)) CReal.zero)) CReal.one
      ≈ CReal.min (CReal.max (CReal.mul inv (CReal.add y (CReal.neg u))) CReal.zero) CReal.one :=
    minSeqWith_respects_eventually cRatScalarMulArch _ _ _ _
      (thm36A1_mul_max_zeroC inv (CReal.add y (CReal.neg u)) hinv_nn)
      (relEventually_refl CReal.one)
  -- step3: clamp_swap
  have h3 : CReal.min (CReal.max (CReal.mul inv (CReal.add y (CReal.neg u))) CReal.zero) CReal.one
      ≈ CReal.max (CReal.min (CReal.mul inv (CReal.add y (CReal.neg u))) CReal.one) CReal.zero :=
    thm36A1_clamp_swapC (CReal.mul inv (CReal.add y (CReal.neg u)))
  -- Technical note.
  have hsub : CReal.add y (CReal.neg u) ≈ CReal.sub y u :=
    Setoid.symm (subSeq_eq_add_neg_eventually y u)
  have h4 : CReal.max (CReal.min (CReal.mul inv (CReal.add y (CReal.neg u))) CReal.one) CReal.zero
      ≈ CReal.max (CReal.min (CReal.mul inv (CReal.sub y u)) CReal.one) CReal.zero :=
    maxSeqWith_respects_eventually cRatScalarMulArch _ _ _ _
      (minSeqWith_respects_eventually cRatScalarMulArch _ _ _ _
        (mulSeqConcrete_respects_eventually cRatScalarMulArch inv inv _ _
          (relEventually_refl inv) hsub)
        (relEventually_refl CReal.one))
      (relEventually_refl CReal.zero)
  have h5 : CReal.max (CReal.min (CReal.mul inv (CReal.sub y u)) CReal.one) CReal.zero
      ≈ rampFnC u v y hpos := Setoid.refl _
  exact Setoid.trans h1 (Setoid.trans h2 (Setoid.trans h3 (Setoid.trans h4 h5)))

#print axioms BishopSec3P.thm36A1_ramp_value_formulaC

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_3_6_ramp_compC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (u v : CReal)
    (hpos : PosEventuallyData (CReal.sub v u))
    (hu : ¬ CReal.ltE u CReal.zero) : IntegrableRepC3 S :=
  (IntegrableRepC3.smul (CReal.invPos (CReal.sub v u) hpos)
      (h.sub (h.cutConstVal u hu))).cutConstVal CReal.one
    (fun h1 => regularSeqLtProp_irrefl CReal.zero
      (regularSeqLtProp_trans CReal.zero CReal.one CReal.zero CReal.one_pos_E h1))

#print axioms BishopSec3P.thm_3_6_ramp_compC

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A1_ramp_comp_value_witnessC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (u v : CReal)
    (hpos : PosEventuallyData (CReal.sub v u))
    (hu : ¬ CReal.ltE u CReal.zero)
    (x : X) (hx : RepSeriesSum (fun n => (h.fn n).toFun x)) :
    { hr : RepSeriesSum
        (fun n => ((thm_3_6_ramp_compC h u v hpos hu).fn n).toFun x) //
      relEventually hr.sum (rampFnC u v hx.sum hpos) } := by
  let inv := CReal.invPos (CReal.sub v u) hpos
  have hone : ¬ CReal.ltE CReal.one CReal.zero := fun h1 =>
    regularSeqLtProp_irrefl CReal.zero
      (regularSeqLtProp_trans CReal.zero CReal.one CReal.zero CReal.one_pos_E h1)
  -- Technical note.
  let hcut := IntegrableRepC3.cutConstVal_signed_valueC h u hu x hx
  let hneg : RepSeriesSum
      (fun n => (((h.cutConstVal u hu).neg).fn n).toFun x) :=
    neg_seriesSum_valueC3 (r := h.cutConstVal u hu) (x := x) hcut.val
  let hsub : RepSeriesSum
      (fun n => ((h.sub (h.cutConstVal u hu)).fn n).toFun x) :=
    add_seriesSum_valueC3 (r := h) (r' := (h.cutConstVal u hu).neg) (x := x) hx hneg
  -- hsub.sum defeq CReal.add hx.sum (CReal.neg hcut.val.sum)
  have hsub_sum : relEventually hsub.sum
      (CReal.add hx.sum (CReal.neg (CReal.min hx.sum u))) := by
    change relEventually (CReal.add hx.sum (CReal.neg hcut.val.sum)) _
    exact addSeq_respects_eventually hx.sum hx.sum (CReal.neg hcut.val.sum)
      (CReal.neg (CReal.min hx.sum u)) (relEventually_refl hx.sum)
      (negSeq_respects_eventually hcut.val.sum (CReal.min hx.sum u) hcut.property)
  let hsmul : RepSeriesSum
      (fun n => ((IntegrableRepC3.smul inv (h.sub (h.cutConstVal u hu))).fn n).toFun x) :=
    smul_seriesSum_valueC3 inv (r := h.sub (h.cutConstVal u hu)) (x := x) hsub
  -- hsmul.sum defeq CReal.mul inv hsub.sum
  have hsmul_sum : relEventually hsmul.sum
      (CReal.mul inv (CReal.add hx.sum (CReal.neg (CReal.min hx.sum u)))) := by
    change relEventually (CReal.mul inv hsub.sum) _
    exact mulSeqConcrete_respects_eventually cRatScalarMulArch inv inv hsub.sum
      (CReal.add hx.sum (CReal.neg (CReal.min hx.sum u)))
      (relEventually_refl inv) hsub_sum
  -- Technical note.
  let hout := IntegrableRepC3.cutConstVal_signed_valueC
    (IntegrableRepC3.smul inv (h.sub (h.cutConstVal u hu))) CReal.one hone x hsmul
  -- Technical note.
  let hrout : RepSeriesSum
      (fun n => ((thm_3_6_ramp_compC h u v hpos hu).fn n).toFun x) := hout.val
  refine ⟨hrout, ?_⟩
  show relEventually hout.val.sum (rampFnC u v hx.sum hpos)
  -- Technical note.
  have hp1 : hout.val.sum ≈ CReal.min hsmul.sum CReal.one := hout.property
  have hp2 : CReal.min hsmul.sum CReal.one
      ≈ CReal.min (CReal.mul inv (CReal.add hx.sum (CReal.neg (CReal.min hx.sum u)))) CReal.one :=
    minSeqWith_respects_eventually cRatScalarMulArch hsmul.sum
      (CReal.mul inv (CReal.add hx.sum (CReal.neg (CReal.min hx.sum u))))
      CReal.one CReal.one hsmul_sum (relEventually_refl CReal.one)
  exact Setoid.trans hp1
    (Setoid.trans hp2 (thm36A1_ramp_value_formulaC u v hx.sum hpos))

#print axioms BishopSec3P.thm36A1_ramp_comp_value_witnessC

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_comp_valueC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (u v : CReal)
    (hpos : PosEventuallyData (CReal.sub v u))
    (hu : ¬ CReal.ltE u CReal.zero)
    (x : X) (hx : RepSeriesSum (fun n => (h.fn n).toFun x))
    (hr : RepSeriesSum
      (fun n => ((thm_3_6_ramp_compC h u v hpos hu).fn n).toFun x)) :
    relEventually hr.sum (rampFnC u v hx.sum hpos) := by
  let hw := thm36A1_ramp_comp_value_witnessC h u v hpos hu x hx
  have h1 : hr.sum ≈ hw.val.sum := repSeriesSum_unique hr hw.val
  have h2 : hw.val.sum ≈ rampFnC u v hx.sum hpos := hw.property
  exact Setoid.trans h1 h2

#print axioms BishopSec3P.thm36A1_ramp_comp_valueC

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
structure Thm36A2EndpointsC (a b : CReal) where
  alpha : CReal
  beta : CReal
  gamma : CReal
  delta : CReal
  alpha_nonneg : ¬ CReal.ltE alpha CReal.zero
  hpos_ba : PosEventuallyData (CReal.sub beta alpha)
  beta_lt_a : regularSeqLtProp beta a
  b_lt_gamma : regularSeqLtProp b gamma
  gamma_nonneg : ¬ CReal.ltE gamma CReal.zero
  hpos_dg : PosEventuallyData (CReal.sub delta gamma)

/-- Technical lemma used in the public import closure. -/
inductive Thm36A2CodeC (a b : CReal) where
  | one
  | zero
  | ramp (u v : CReal) (hau : RegularSeqLe a u)
      (hposv : PosEventuallyData (CReal.sub v u)) (hvb : RegularSeqLe v b)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeFnC {a b : CReal} : Thm36A2CodeC a b → (CReal → CReal)
  | .one => fun _ => CReal.one
  | .zero => fun _ => CReal.zero
  | .ramp u v _ hposv _ => fun y => rampFnC u v y hposv

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeUC {a b : CReal} (E : Thm36A2EndpointsC a b) :
    Thm36A2CodeC a b → CReal
  | .one => E.alpha
  | .zero => E.gamma
  | .ramp u _ _ _ _ => u

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeVC {a b : CReal} (E : Thm36A2EndpointsC a b) :
    Thm36A2CodeC a b → CReal
  | .one => E.beta
  | .zero => E.delta
  | .ramp _ v _ _ _ => v

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeUV_dataC {a b : CReal} (E : Thm36A2EndpointsC a b) :
    (c : Thm36A2CodeC a b) →
      PosEventuallyData (CReal.sub (thm36A2_codeVC E c) (thm36A2_codeUC E c))
  | .one => E.hpos_ba
  | .zero => E.hpos_dg
  | .ramp _ _ _ hposv _ => hposv

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_codeU_nonnegC {a b : CReal} (ha : PosEventuallyData a)
    (E : Thm36A2EndpointsC a b) :
    (c : Thm36A2CodeC a b) → ¬ CReal.ltE (thm36A2_codeUC E c) CReal.zero
  | .one => E.alpha_nonneg
  | .zero => E.gamma_nonneg
  | .ramp u _ hau _ _ => by
      intro hu0
      have hae : regularSeqLtProp CReal.zero a := regularSeqLtProp_zero_of_posData ha
      have haz : regularSeqLtProp a CReal.zero := regularSeqLtProp_of_le_of_lt hau hu0
      exact regularSeqLtProp_irrefl CReal.zero
        (regularSeqLtProp_trans CReal.zero a CReal.zero hae haz)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeRepFnC {a b : CReal} (E : Thm36A2EndpointsC a b)
    (c : Thm36A2CodeC a b) : CReal → CReal :=
  fun y => rampFnC (thm36A2_codeUC E c) (thm36A2_codeVC E c) y (thm36A2_codeUV_dataC E c)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeRepC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal} (ha : PosEventuallyData a)
    (E : Thm36A2EndpointsC a b) (c : Thm36A2CodeC a b) : IntegrableRepC3 S :=
  thm_3_6_ramp_compC h (thm36A2_codeUC E c) (thm36A2_codeVC E c)
    (thm36A2_codeUV_dataC E c) (thm36A2_codeU_nonnegC ha E c)

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_one_le_zero_falseC (h : RegularSeqLe CReal.one CReal.zero) : False :=
  regularSeqLtProp_irrefl CReal.zero
    (regularSeqLtProp_of_lt_of_le CReal.one_pos_E h)

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_codeRepFn_le_globalC {a b : CReal} (hab : regularSeqLtProp a b)
    (E : Thm36A2EndpointsC a b) (c d : Thm36A2CodeC a b)
    (hcd : ∀ x : CReal, RegularSeqLe a x → RegularSeqLe x b →
      RegularSeqLe (thm36A2_codeFnC c x) (thm36A2_codeFnC d x)) :
    ∀ y : CReal,
      RegularSeqLe (thm36A2_codeRepFnC E c y) (thm36A2_codeRepFnC E d y) := by
  intro y
  cases c with
  | one =>
      cases d with
      | one => exact regularSeqLe_refl _
      | zero =>
          exact (thm36A2_one_le_zero_falseC
            (hcd a (regularSeqLe_refl a) (regularSeqLe_of_ltPropC hab))).elim
      | ramp p q hap hposq hqb =>
          have hpb : RegularSeqLe p b :=
            regularSeqLe_trans (regularSeqLe_of_ltPropC hposq.toProp) hqb
          have h1 : RegularSeqLe CReal.one (rampFnC p q p hposq) := hcd p hap hpb
          have h2 : RegularSeqLe (rampFnC p q p hposq) CReal.zero :=
            regularSeqLe_of_relEventually
              (rampFnC_zero p q p hposq (regularSeqLe_refl p))
          exact (thm36A2_one_le_zero_falseC (regularSeqLe_trans h1 h2)).elim
  | zero =>
      cases d with
      | one =>
          have hqu : RegularSeqLe E.beta E.gamma :=
            regularSeqLe_trans (regularSeqLe_of_ltPropC E.beta_lt_a)
              (regularSeqLe_trans (regularSeqLe_of_ltPropC hab)
                (regularSeqLe_of_ltPropC E.b_lt_gamma))
          exact thm36A2_ramp_le_global_of_right_le_leftC E.hpos_dg E.hpos_ba
            E.hpos_dg.toProp E.hpos_ba.toProp hqu y
      | zero => exact regularSeqLe_refl _
      | ramp p q hap hposq hqb =>
          have hqg : RegularSeqLe q E.gamma :=
            regularSeqLe_trans hqb (regularSeqLe_of_ltPropC E.b_lt_gamma)
          exact thm36A2_ramp_le_global_of_right_le_leftC E.hpos_dg hposq
            E.hpos_dg.toProp hposq.toProp hqg y
  | ramp u v hau hposv hvb =>
      cases d with
      | one =>
          have hbu : RegularSeqLe E.beta u :=
            regularSeqLe_trans (regularSeqLe_of_ltPropC E.beta_lt_a) hau
          exact thm36A2_ramp_le_global_of_right_le_leftC hposv E.hpos_ba
            hposv.toProp E.hpos_ba.toProp hbu y
      | zero =>
          have hav : RegularSeqLe a v :=
            regularSeqLe_trans hau (regularSeqLe_of_ltPropC hposv.toProp)
          have h1 : RegularSeqLe (rampFnC u v v hposv) CReal.zero := hcd v hav hvb
          have hone_rel : relEventually CReal.one (rampFnC u v v hposv) :=
            Setoid.symm (rampFnC_one u v v hposv (regularSeqLe_refl v))
          have h2 : RegularSeqLe CReal.one (rampFnC u v v hposv) :=
            regularSeqLe_of_relEventually hone_rel
          exact (thm36A2_one_le_zero_falseC (regularSeqLe_trans h2 h1)).elim
      | ramp p q hap hposq hqb =>
          exact thm36A2_ramp_le_global_of_intervalC hposv hposq hau hposv.toProp hvb
            hap hposq.toProp hqb (fun x hax hxb => hcd x hax hxb) y

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_codeRep_integral_monoC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal} (hab : regularSeqLtProp a b)
    (ha : PosEventuallyData a) (E : Thm36A2EndpointsC a b)
    (c d : Thm36A2CodeC a b)
    (hcd : ∀ x : CReal, RegularSeqLe a x → RegularSeqLe x b →
      RegularSeqLe (thm36A2_codeFnC c x) (thm36A2_codeFnC d x)) :
    RegularSeqLe (thm36A2_codeRepC h ha E c).integral
      (thm36A2_codeRepC h ha E d).integral := by
  refine prop_1_11C h.domain_isFull
    (thm36A2_codeRepC h ha E c) (thm36A2_codeRepC h ha E d) ?_
  intro x hx hr hr'
  obtain ⟨_, ⟨hxabs⟩⟩ := hx
  have hxsum : RepSeriesSum (fun n => (h.fn n).toFun x) := seriesSum_of_absC hxabs
  have hcval : relEventually hr.sum (thm36A2_codeRepFnC E c hxsum.sum) :=
    thm36A1_ramp_comp_valueC h (thm36A2_codeUC E c) (thm36A2_codeVC E c)
      (thm36A2_codeUV_dataC E c) (thm36A2_codeU_nonnegC ha E c) x hxsum hr
  have hdval : relEventually hr'.sum (thm36A2_codeRepFnC E d hxsum.sum) :=
    thm36A1_ramp_comp_valueC h (thm36A2_codeUC E d) (thm36A2_codeVC E d)
      (thm36A2_codeUV_dataC E d) (thm36A2_codeU_nonnegC ha E d) x hxsum hr'
  have hle : RegularSeqLe (thm36A2_codeRepFnC E c hxsum.sum)
      (thm36A2_codeRepFnC E d hxsum.sum) :=
    thm36A2_codeRepFn_le_globalC hab E c d hcd hxsum.sum
  exact regularSeqLe_trans (regularSeqLe_of_relEventually hcval)
    (regularSeqLe_trans hle
      (regularSeqLe_of_relEventually (relEventually_symm _ _ hdval)))

/-- Technical lemma used in the public import closure. -/
structure ProfileC (a b : CReal) (_hab : regularSeqLtProp a b) where
  Code : Type
  embed : Code → CReal → CReal
  F : Set Code
  bound : ∀ f : Code, f ∈ F → ∀ x : CReal, RegularSeqLe a x → RegularSeqLe x b →
    RegularSeqNonneg (embed f x) ∧ RegularSeqLe (embed f x) CReal.one
  zeroCode : Code
  has_zero : zeroCode ∈ F
  embed_zero : embed zeroCode = (fun _ => CReal.zero)
  oneCode : Code
  has_one : oneCode ∈ F
  embed_one : embed oneCode = (fun _ => CReal.one)
  separating : ∀ u v : CReal, RegularSeqLe a u → PosEventuallyData (CReal.sub v u) →
      RegularSeqLe v b →
    { f : Code //
      f ∈ F ∧
      (∀ t : CReal, RegularSeqLe a t → RegularSeqLe t u → embed f t ≈ CReal.zero) ∧
      (∀ t : CReal, RegularSeqLe v t → RegularSeqLe t b → embed f t ≈ CReal.one) }
  lambda : Code → CReal
  mono : ∀ f g : Code, f ∈ F → g ∈ F →
    (∀ x : CReal, RegularSeqLe a x → RegularSeqLe x b → RegularSeqLe (embed f x) (embed g x)) →
    RegularSeqLe (lambda f) (lambda g)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_profileC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal} (hab : regularSeqLtProp a b)
    (ha : PosEventuallyData a) (E : Thm36A2EndpointsC a b) :
    ProfileC a b hab where
  Code := Thm36A2CodeC a b
  embed := thm36A2_codeFnC
  F := Set.univ
  bound := by
    intro c _hc x _hax _hxb
    cases c with
    | one => exact ⟨regularSeqNonneg_of_zero_le CReal.zero_le_oneC, regularSeqLe_refl CReal.one⟩
    | zero =>
        exact ⟨regularSeqNonneg_of_zero_le (regularSeqLe_refl CReal.zero), CReal.zero_le_oneC⟩
    | ramp u v _ hposv _ => exact rampFnC_bound u v x hposv
  zeroCode := .zero
  has_zero := Set.mem_univ _
  embed_zero := rfl
  oneCode := .one
  has_one := Set.mem_univ _
  embed_one := rfl
  separating := by
    intro u v hau hposv hvb
    exact ⟨.ramp u v hau hposv hvb, Set.mem_univ _,
      fun t _hat htu => rampFnC_zero u v t hposv htu,
      fun t hvt _htb => rampFnC_one u v t hposv hvt⟩
  lambda := fun c => (thm36A2_codeRepC h ha E c).integral
  mono := by
    intro c d _hc _hd hcd
    exact thm36A2_codeRep_integral_monoC h hab ha E c d hcd

/-- Technical lemma used in the public import closure. -/
structure ProfileC.p_ltC {a b : CReal} {hab : regularSeqLtProp a b} (PC : ProfileC a b hab)
    (u v delta : CReal) : Type where
  f1 : PC.Code
  f1_mem : f1 ∈ PC.F
  f2 : PC.Code
  f2_mem : f2 ∈ PC.F
  cond1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b → RegularSeqLe t v →
    PC.embed f1 t ≈ CReal.zero
  cond2 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b → RegularSeqLe u t →
    PC.embed f2 t ≈ CReal.one
  gap : regularSeqLtProp (CReal.sub (PC.lambda f2) (PC.lambda f1)) delta

/-- Technical lemma used in the public import closure. -/
structure ProfileC.p_prime_ltC {a b : CReal} {hab : regularSeqLtProp a b} (PC : ProfileC a b hab)
    (u v delta : CReal) : Type where
  alpha : CReal
  alpha_pos : regularSeqLtProp CReal.zero alpha
  inner : PC.p_ltC (CReal.max a (CReal.sub u alpha)) (CReal.min b (CReal.add v alpha)) delta

/-- Technical lemma used in the public import closure. -/
def ProfileC.p_ltC_mono {a b : CReal} {hab : regularSeqLtProp a b} (PC : ProfileC a b hab)
    {u v d e : CReal} (h : PC.p_ltC u v d) (hde : RegularSeqLe d e) : PC.p_ltC u v e :=
  ⟨h.f1, h.f1_mem, h.f2, h.f2_mem, h.cond1, h.cond2,
    regularSeqLtProp_of_lt_of_le h.gap hde⟩

/-- Shrinking the interval preserves a `p_ltC` witness.

This is the CReal-native counterpart of abstract `lemma33_p_lt_subset`, and is
the first primitive needed for the P2b-beta outside-radius construction. -/
def ProfileC.p_ltC_subset {a b : CReal} {hab : regularSeqLtProp a b} (PC : ProfileC a b hab)
    {u v u' v' d : CReal}
    (h : PC.p_ltC u' v' d) (hu : RegularSeqLe u' u) (hv : RegularSeqLe v v') :
    PC.p_ltC u v d :=
  { f1 := h.f1
    f1_mem := h.f1_mem
    f2 := h.f2
    f2_mem := h.f2_mem
    cond1 := by
      intro t hat htb htv
      exact h.cond1 t hat htb (regularSeqLe_trans htv hv)
    cond2 := by
      intro t hat htb hut
      exact h.cond2 t hat htb (regularSeqLe_trans hu hut)
    gap := h.gap }

/-- Technical lemma used in the public import closure. -/
def ProfileC.p_prime_ltC_mono {a b : CReal} {hab : regularSeqLtProp a b} (PC : ProfileC a b hab)
    {u v d e : CReal} (h : PC.p_prime_ltC u v d) (hde : RegularSeqLe d e) : PC.p_prime_ltC u v e :=
  ⟨h.alpha, h.alpha_pos, PC.p_ltC_mono h.inner hde⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def natCast_lt_dataC (i j : Nat) (hij : i < j) :
    PosEventuallyData (CReal.sub (constSeq (Nat.cast j)) (constSeq (Nat.cast i))) where
  k := 1
  N := 0
  tail_pos := by
    intro n _hn
    have hval : (CReal.sub (constSeq (Nat.cast j)) (constSeq (Nat.cast i))).val n
        = (Nat.cast j : Scalar) - Nat.cast i := rfl
    rw [hval]
    have heps := eps_succ_lt_eps 0
    have hle : BishopC.Le (eps 0) ((Nat.cast j : Scalar) - Nat.cast i) := by
      rw [show eps 0 = (1 : Scalar) from rfl]
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hij
      subst hm
      have hcast : ((Nat.cast (i + m + 1) : Scalar) - Nat.cast i) = (1 : Scalar) + Nat.cast m := by
        push_cast; ring
      rw [hcast]
      have h0 : BishopC.Le (0 : Scalar) (Nat.cast m : Scalar) := scalar_natCast_nonneg m
      have hsum : BishopC.Le ((1 : Scalar) + 0) ((1 : Scalar) + Nat.cast m) :=
        BishopC.le_add (BishopC.le_refl 1) h0
      simpa using hsum
    exact BishopC.lt_of_lt_of_le heps hle

/-- Technical lemma used in the public import closure. -/
theorem natCast_ltC (i j : Nat) (hij : i < j) :
    regularSeqLtProp (constSeq (Nat.cast i)) (constSeq (Nat.cast j)) :=
  (natCast_lt_dataC i j hij).toProp

/-- Technical lemma used in the public import closure. -/
theorem natCast_leC (i j : Nat) (hij : i ≤ j) :
    RegularSeqLe (constSeq (Nat.cast i)) (constSeq (Nat.cast j)) := by
  apply regularSeqLe_of_indexed_pointwise_le
  intro m
  change BishopC.Le (Nat.cast i : Scalar) (Nat.cast j)
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le hij
  subst hm'
  have hcast : ((Nat.cast (i + m') : Scalar)) = Nat.cast i + Nat.cast m' := by push_cast; ring
  rw [hcast]
  have h0 : BishopC.Le (0 : Scalar) (Nat.cast m' : Scalar) := scalar_natCast_nonneg m'
  have hsum : BishopC.Le ((Nat.cast i : Scalar) + 0) ((Nat.cast i : Scalar) + Nat.cast m') :=
    BishopC.le_add (BishopC.le_refl _) h0
  simpa using hsum

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def bptC (a d : CReal) (i : Nat) : CReal :=
  CReal.add a (CReal.mul (constSeq (Nat.cast i)) d)

/-- Technical lemma used in the public import closure. -/
theorem bptC_zeroC (a d : CReal) : bptC a d 0 ≈ a := by
  show CReal.add a (CReal.mul (constSeq (Nat.cast 0)) d) ≈ a
  have h0 : constSeq (Nat.cast 0) ≈ CReal.zero := constSeq_natCast_zeroC
  have hstep1 : CReal.mul (constSeq (Nat.cast 0)) d ≈ CReal.mul CReal.zero d :=
    CReal.mul_respects_equiv _ _ _ _ h0 (Setoid.refl d)
  have hmul : CReal.mul (constSeq (Nat.cast 0)) d ≈ CReal.zero :=
    Setoid.trans hstep1 (zero_mul_equivC d)
  have hadd : CReal.add a (CReal.mul (constSeq (Nat.cast 0)) d) ≈ CReal.add a CReal.zero :=
    CReal.add_respects_equiv _ _ _ _ (Setoid.refl a) hmul
  exact Setoid.trans hadd (CReal.add_zero a)

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLtProp_mul_right_of_posC {a b d : CReal}
    (hab : regularSeqLtProp a b) (hd : regularSeqLtProp CReal.zero d) :
    regularSeqLtProp (CReal.mul a d) (CReal.mul b d) := by
  have hleft : regularSeqLtProp (CReal.mul d a) (CReal.mul d b) :=
    mul_lt_mul_of_pos_leftC hab hd
  have h1 : regularSeqLtProp (CReal.mul a d) (CReal.mul d b) :=
    regularSeqLtProp_of_left_eventual (CReal.mul_comm a d) hleft
  exact regularSeqLtProp_of_right_eventual (CReal.mul_comm d b) h1

/-- Technical lemma used in the public import closure. -/
theorem bptC_ltC {a d : CReal} (hd : regularSeqLtProp CReal.zero d)
    {i j : Nat} (hij : i < j) : regularSeqLtProp (bptC a d i) (bptC a d j) := by
  show regularSeqLtProp (CReal.add a (CReal.mul (constSeq (Nat.cast i)) d))
                        (CReal.add a (CReal.mul (constSeq (Nat.cast j)) d))
  have hmul : regularSeqLtProp (CReal.mul (constSeq (Nat.cast i)) d)
                               (CReal.mul (constSeq (Nat.cast j)) d) :=
    regularSeqLtProp_mul_right_of_posC (natCast_ltC i j hij) hd
  exact regularSeqLtProp_add_left a _ _ hmul

/-- Technical lemma used in the public import closure. -/
theorem hbpt_leC (a d : CReal) (hd_nn : RegularSeqNonneg d) {i j : Nat} (hij : i ≤ j) :
    RegularSeqLe (bptC a d i) (bptC a d j) := by
  show RegularSeqLe (CReal.add a (CReal.mul (constSeq (Nat.cast i)) d))
                    (CReal.add a (CReal.mul (constSeq (Nat.cast j)) d))
  have hmul : RegularSeqLe (CReal.mul (constSeq (Nat.cast i)) d)
                           (CReal.mul (constSeq (Nat.cast j)) d) :=
    regularSeqLe_mul_right_of_nonnegC (natCast_leC i j hij) hd_nn
  exact regularSeqLe_add (regularSeqLe_refl a) hmul

/-- Technical lemma used in the public import closure. -/
theorem ha_bptC (a d : CReal) (hd_nn : RegularSeqNonneg d) (i : Nat) :
    RegularSeqLe a (bptC a d i) := by
  have h := hbpt_leC a d hd_nn (Nat.zero_le i)
  exact regularSeqLe_of_left_eventual (Setoid.symm (bptC_zeroC a d)) h

/-- Technical lemma used in the public import closure. -/
theorem constSeq_natCast_succC (i : Nat) :
    constSeq (Nat.cast (i+1)) ≈ CReal.add (constSeq (Nat.cast i)) CReal.one := by
  intro k
  refine ⟨0, ?_⟩
  intro p _hp
  have hval : (constSeq (Nat.cast (i+1))).val p
      - (CReal.add (constSeq (Nat.cast i)) CReal.one).val p = (0 : Scalar) := by
    change (Nat.cast (i+1) : Scalar) - ((Nat.cast i : Scalar) + 1) = 0
    rw [Nat.cast_succ]; ring
  rw [hval]
  change BishopCReal.Le (BishopCRat.CRat.absF 0) (eps k)
  rw [scalarCOFOSeed.abs_zero]
  exact eps_nonneg k

/-- Technical lemma used in the public import closure. -/
theorem bptC_succC (a d : CReal) (i : Nat) :
    bptC a d (i+1) ≈ CReal.add (bptC a d i) d := by
  show CReal.add a (CReal.mul (constSeq (Nat.cast (i+1))) d)
     ≈ CReal.add (CReal.add a (CReal.mul (constSeq (Nat.cast i)) d)) d
  have hc : CReal.mul (constSeq (Nat.cast (i+1))) d
          ≈ CReal.mul (CReal.add (constSeq (Nat.cast i)) CReal.one) d :=
    CReal.mul_respects_equiv _ _ _ _ (constSeq_natCast_succC i) (Setoid.refl d)
  have hdist : CReal.mul (CReal.add (constSeq (Nat.cast i)) CReal.one) d
             ≈ CReal.add (CReal.mul (constSeq (Nat.cast i)) d) (CReal.mul CReal.one d) :=
    CReal.right_distrib _ _ _
  have hd2 : CReal.add (CReal.mul (constSeq (Nat.cast i)) d) (CReal.mul CReal.one d)
           ≈ CReal.add (CReal.mul (constSeq (Nat.cast i)) d) d :=
    CReal.add_respects_equiv _ _ _ _ (Setoid.refl _) (CReal.one_mul d)
  have hmul : CReal.mul (constSeq (Nat.cast (i+1))) d
            ≈ CReal.add (CReal.mul (constSeq (Nat.cast i)) d) d :=
    Setoid.trans hc (Setoid.trans hdist hd2)
  have hadd : CReal.add a (CReal.mul (constSeq (Nat.cast (i+1))) d)
            ≈ CReal.add a (CReal.add (CReal.mul (constSeq (Nat.cast i)) d) d) :=
    CReal.add_respects_equiv _ _ _ _ (Setoid.refl a) hmul
  exact Setoid.trans hadd
    (Setoid.symm (CReal.add_assoc a (CReal.mul (constSeq (Nat.cast i)) d) d))

/-- Technical lemma used in the public import closure. -/
theorem add_sub_cancel_leftC (b d : CReal) : CReal.sub (CReal.add b d) b ≈ d := by
  have h1 : CReal.sub (CReal.add b d) b ≈ CReal.add (CReal.add b d) (CReal.neg b) :=
    rel_to_relEventually _ _ (sub_eq_add_neg_raw (CReal.add b d) b)
  have h2 : CReal.add (CReal.add b d) (CReal.neg b)
          ≈ CReal.add (CReal.add d b) (CReal.neg b) :=
    CReal.add_respects_equiv _ _ _ _ (CReal.add_comm b d) (Setoid.refl _)
  have h3 : CReal.add (CReal.add d b) (CReal.neg b)
          ≈ CReal.add d (CReal.add b (CReal.neg b)) :=
    CReal.add_assoc d b (CReal.neg b)
  have h5 : CReal.add d (CReal.add b (CReal.neg b)) ≈ CReal.add d CReal.zero :=
    CReal.add_respects_equiv _ _ _ _ (Setoid.refl d) (addSeq_neg_right_eventually b)
  exact Setoid.trans h1 (Setoid.trans h2 (Setoid.trans h3 (Setoid.trans h5 (CReal.add_zero d))))

/-- Technical lemma used in the public import closure. -/
theorem bptC_sub_succC (a d : CReal) (i : Nat) :
    CReal.sub (bptC a d (i+1)) (bptC a d i) ≈ d := by
  have hs : CReal.sub (bptC a d (i+1)) (bptC a d i)
          ≈ CReal.sub (CReal.add (bptC a d i) d) (bptC a d i) :=
    CReal.sub_respects_equiv _ _ _ _ (bptC_succC a d i) (Setoid.refl _)
  exact Setoid.trans hs (add_sub_cancel_leftC (bptC a d i) d)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem mul_zero_equivC (a : CReal) : CReal.mul a CReal.zero ≈ CReal.zero := by
  have h1 : CReal.mul a CReal.zero ≈ CReal.mul CReal.zero a := CReal.mul_comm a CReal.zero
  exact Setoid.trans h1 (zero_mul_equivC a)

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLtProp_lt_add_selfC {x : CReal}
    (hx : regularSeqLtProp CReal.zero x) :
    regularSeqLtProp x (CReal.add x x) := by
  have h0 : regularSeqLtProp (CReal.add x CReal.zero) (CReal.add x x) :=
    regularSeqLtProp_add_left x CReal.zero x hx
  exact regularSeqLtProp_of_left_eventual (Setoid.symm (CReal.add_zero x)) h0

/-- Technical lemma used in the public import closure. -/
theorem half_mul_add_selfC (a : CReal) :
    CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half a) ≈ a := by
  have h1 : CReal.add (CReal.mul CReal.half a) (CReal.mul CReal.half a)
          ≈ CReal.mul (CReal.add CReal.half CReal.half) a :=
    Setoid.symm (CReal.right_distrib CReal.half CReal.half a)
  have h2 : CReal.mul (CReal.add CReal.half CReal.half) a ≈ CReal.mul CReal.one a :=
    CReal.mul_respects_equiv _ _ _ _ CReal.half_add_half (Setoid.refl a)
  exact Setoid.trans h1 (Setoid.trans h2 (CReal.one_mul a))

/-- Technical lemma used in the public import closure. -/
def sigmaC (d : CReal) : CReal := CReal.mul CReal.half (CReal.mul CReal.half d)

/-- Technical lemma used in the public import closure. -/
theorem sigmaC_posC {d : CReal} (hd : regularSeqLtProp CReal.zero d) :
    regularSeqLtProp CReal.zero (sigmaC d) := by
  have hhalf : regularSeqLtProp CReal.zero CReal.half := CReal.half_pos_E
  have hhd : regularSeqLtProp (CReal.mul CReal.half CReal.zero) (CReal.mul CReal.half d) :=
    mul_lt_mul_of_pos_leftC hd hhalf
  have hhd0 : regularSeqLtProp CReal.zero (CReal.mul CReal.half d) :=
    regularSeqLtProp_of_left_eventual (Setoid.symm (mul_zero_equivC CReal.half)) hhd
  have hσ : regularSeqLtProp (CReal.mul CReal.half CReal.zero) (sigmaC d) :=
    mul_lt_mul_of_pos_leftC hhd0 hhalf
  exact regularSeqLtProp_of_left_eventual (Setoid.symm (mul_zero_equivC CReal.half)) hσ

/-- σ+σ ≈ ½d（hsigma2）。 -/
theorem sigmaC_add_selfC (d : CReal) :
    CReal.add (sigmaC d) (sigmaC d) ≈ CReal.mul CReal.half d :=
  half_mul_add_selfC (CReal.mul CReal.half d)

/-- (σ+σ)+(σ+σ) ≈ d（hsigma4）。 -/
theorem sigmaC_quadC (d : CReal) :
    CReal.add (CReal.add (sigmaC d) (sigmaC d)) (CReal.add (sigmaC d) (sigmaC d)) ≈ d := by
  have h1 : CReal.add (CReal.add (sigmaC d) (sigmaC d)) (CReal.add (sigmaC d) (sigmaC d))
          ≈ CReal.add (CReal.mul CReal.half d) (CReal.mul CReal.half d) :=
    CReal.add_respects_equiv _ _ _ _ (sigmaC_add_selfC d) (sigmaC_add_selfC d)
  exact Setoid.trans h1 (half_mul_add_selfC d)

/-- Technical lemma used in the public import closure. -/
theorem sigmaC_two_lt_dC {d : CReal} (hd : regularSeqLtProp CReal.zero d) :
    regularSeqLtProp (CReal.add (sigmaC d) (sigmaC d)) d := by
  have hσpos : regularSeqLtProp CReal.zero (sigmaC d) := sigmaC_posC hd
  have h2pos0 : regularSeqLtProp (CReal.add CReal.zero CReal.zero)
                                 (CReal.add (sigmaC d) (sigmaC d)) :=
    regularSeqLtProp_add hσpos hσpos
  have h2pos : regularSeqLtProp CReal.zero (CReal.add (sigmaC d) (sigmaC d)) :=
    regularSeqLtProp_of_left_eventual (Setoid.symm (CReal.add_zero CReal.zero)) h2pos0
  have hlt : regularSeqLtProp (CReal.add (sigmaC d) (sigmaC d))
              (CReal.add (CReal.add (sigmaC d) (sigmaC d)) (CReal.add (sigmaC d) (sigmaC d))) :=
    regularSeqLtProp_lt_add_selfC h2pos
  exact regularSeqLtProp_of_right_eventual (sigmaC_quadC d) hlt

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def posEventuallyData_sub_zero_of_posC (x : RegularSeq)
    (h : PosEventuallyData x) : PosEventuallyData (subSeq x zeroSeq) := by
  obtain ⟨k, N, hN⟩ := h
  refine ⟨k, N, ?_⟩
  intro n hn
  have hn' : N ≤ n + 1 := Nat.le_trans hn (Nat.le_succ n)
  have hx := hN (n + 1) hn'
  change BishopC.COF.lt (eps k) (x.val (n + 1) - 0)
  rwa [sub_zero]

/-- Technical lemma used in the public import closure. -/
def posEventuallyData_mul_concrete_withC
    (A : ScalarMulArchimedeanData) (x y : RegularSeq)
    (hx : PosEventuallyData (subSeq x zeroSeq))
    (hy : PosEventuallyData (subSeq y zeroSeq)) :
    PosEventuallyData (mulSeqConcreteWith A x y) := by
  obtain ⟨kx, Nx, hNx⟩ := hx
  obtain ⟨ky, Ny, hNy⟩ := hy
  refine ⟨kx + ky, Nx + Ny, ?_⟩
  intro n hn
  have hnX : Nx ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hnY : Ny ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  set q : Nat := mulIndexCoreFromBound (mulBoundWith A x y) n with hqdef
  have hnq : n ≤ q := by
    rw [hqdef]
    exact le_mulIndexCoreFromBound (mulBoundWith A x y) n
  have hqX : Nx ≤ q := Nat.le_trans hnX hnq
  have hqY : Ny ≤ q := Nat.le_trans hnY hnq
  have hxraw := hNx q hqX
  have hyraw := hNy q hqY
  have hidx : mulIndexFromBound (mulBoundWith A x y) n = q + 1 := by
    rw [hqdef]
    exact mulIndexFromBound_eq_core_succ (mulBoundWith A x y) n
  have hxpoint : BishopC.COF.lt (eps kx)
      (x.val (mulIndexFromBound (mulBoundWith A x y) n)) := by
    rw [hidx]
    change BishopC.COF.lt (eps kx) (x.val (q + 1) - 0) at hxraw
    rwa [sub_zero] at hxraw
  have hypoint : BishopC.COF.lt (eps ky)
      (y.val (mulIndexFromBound (mulBoundWith A x y) n)) := by
    rw [hidx]
    change BishopC.COF.lt (eps ky) (y.val (q + 1) - 0) at hyraw
    rwa [sub_zero] at hyraw
  change BishopC.COF.lt (eps (kx + ky))
    (x.val (mulIndexFromBound (mulBoundWith A x y) n) *
      y.val (mulIndexFromBound (mulBoundWith A x y) n))
  rw [eps_add_mul_local kx ky]
  exact scalar_mul_lt_mul_of_pos_bounds hxpoint hypoint (eps_pos kx) (eps_pos ky)

/-- Technical lemma used in the public import closure. -/
def CReal.mul_pos_EDC {a b : CReal}
    (ha : regularSeqLtData CReal.zero a) (hb : regularSeqLtData CReal.zero b) :
    regularSeqLtData CReal.zero (CReal.mul a b) := by
  change PosEventuallyData
    (subSeq (mulSeqConcreteWith cRatScalarMulArch a b) zeroSeq)
  exact posEventuallyData_sub_zero_of_posC _
    (posEventuallyData_mul_concrete_withC cRatScalarMulArch a b ha hb)

/-- Technical lemma used in the public import closure. -/
def regularSeqLtData_zero_halfPowC (k : Nat) :
    regularSeqLtData zeroSeq (halfPow k) := by
  refine ⟨k + 1, 0, ?_⟩
  intro n _hn
  change BishopC.COF.lt (eps (k + 1)) (eps k - 0)
  rw [show eps k - 0 = eps k by ring]
  exact eps_succ_lt_eps k

/-- The Lemma 3.3 theta unit `D/(n+1)`. -/
noncomputable def lemma33ThetaC (D : CReal) (n : Nat) : CReal :=
  CReal.mul D
    (CReal.invPos (constSeq (Nat.cast (n + 1)))
      (natCast_succ_posDataC n))

/-- Nonnegativity of `theta = D/(n+1)`. -/
theorem lemma33Theta_nonnegC {D : CReal} {n : Nat}
    (hD : RegularSeqNonneg D) :
    RegularSeqNonneg (lemma33ThetaC D n) := by
  let q : CReal := constSeq (Nat.cast (n + 1))
  let inv : CReal := CReal.invPos q (natCast_succ_posDataC n)
  have hinv_pos : regularSeqLtProp CReal.zero inv :=
    regularSeqLtProp_zero_of_posData
      (CReal.invPos_posData q (natCast_succ_posDataC n))
  have hinv_nn : RegularSeqNonneg inv :=
    regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC hinv_pos)
  simpa [lemma33ThetaC, q, inv] using CReal.mul_nonneg_E hD hinv_nn

/-- If `D < (n+1) eps`, then `theta = D/(n+1) < eps`. -/
theorem lemma33Theta_lt_epsC {D eps : CReal} {n : Nat}
    (hDlt : regularSeqLtProp D
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    regularSeqLtProp (lemma33ThetaC D n) eps := by
  let q : CReal := constSeq (Nat.cast (n + 1))
  let inv : CReal := CReal.invPos q (natCast_succ_posDataC n)
  have hinv_pos : regularSeqLtProp CReal.zero inv :=
    regularSeqLtProp_zero_of_posData
      (CReal.invPos_posData q (natCast_succ_posDataC n))
  have hscaled : regularSeqLtProp
      (CReal.mul D inv)
      (CReal.mul (CReal.mul q eps) inv) := by
    simpa [q, inv] using regularSeqLtProp_mul_right_of_posC hDlt hinv_pos
  have hrhs : CReal.mul (CReal.mul q eps) inv ≈ eps :=
    Setoid.trans (CReal.mul_assoc q eps inv)
      (mul_invPos_scale_cancelC q eps (natCast_succ_posDataC n))
  exact regularSeqLtProp_of_right_eventual hrhs (by
    simpa [lemma33ThetaC, q, inv] using hscaled)

/-- Budget identity `D ≈ (n+1) * theta`. -/
theorem lemma33Theta_budgetC (D : CReal) (n : Nat) :
    D ≈ CReal.mul (constSeq (Nat.cast (n + 1))) (lemma33ThetaC D n) := by
  let q : CReal := constSeq (Nat.cast (n + 1))
  exact Setoid.symm (by
    simpa [lemma33ThetaC, q] using
      mul_invPos_scale_cancelC q D (natCast_succ_posDataC n))

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def half_pos_dataC : regularSeqLtData CReal.zero CReal.half := by
  refine ⟨2, 0, fun n _ => ?_⟩
  exact eps_two_lt_half

/-- Technical lemma used in the public import closure. -/
def sub_pos_dataC {a b : CReal} (hab : regularSeqLtData a b) :
    regularSeqLtData CReal.zero (CReal.sub b a) :=
  posEventuallyData_sub_zero_of_posC (subSeq b a) hab

/-- data σ-pos: 0 < d ⟹ 0 < σ(=¼d)。 -/
def sigmaC_pos_dataC {d : CReal} (hd : regularSeqLtData CReal.zero d) :
    regularSeqLtData CReal.zero (sigmaC d) := by
  change regularSeqLtData CReal.zero (CReal.mul CReal.half (CReal.mul CReal.half d))
  exact CReal.mul_pos_EDC half_pos_dataC (CReal.mul_pos_EDC half_pos_dataC hd)

/-- Technical lemma used in the public import closure. -/
def half_scale_pos_dataC {d : RegularSeq}
    (hd : regularSeqLtData CReal.zero d) :
    regularSeqLtData CReal.zero (halfScaleC d) := by
  obtain ⟨k, N, hN⟩ := hd
  refine ⟨k + 1, N, ?_⟩
  intro n hn
  have hdn := hN n hn
  rw [show (subSeq d CReal.zero).val n = d.val (n + 1) from by
        change d.val (n + 1) - (0 : Scalar) = d.val (n + 1); ring] at hdn
  have hmul := scalar_mul_lt_mul_left hdn scalarCOFOSeed.half_pos
  rw [show (subSeq (halfScaleC d) CReal.zero).val n = BishopCRat.CRat.half * d.val (n + 1) from by
        change BishopCRat.CRat.half * d.val (n + 1) - (0 : Scalar)
             = BishopCRat.CRat.half * d.val (n + 1); ring,
     ← half_eps_succ_eq k]
  exact hmul

/-! Technical auxiliary material for the public import closure. -/

/-- rel-transport of tail-stable positivity data (choice-free). -/
def posEventuallyData_relT (x y : RegularSeq) (hrel : rel x y)
    (h : PosEventuallyData x) : PosEventuallyData y := by
  obtain ⟨k, N, hN⟩ := h
  refine posEventuallyData_of_late_point y (j := k + 1) (M := N + (k + 3)) (by omega) ?_
  set M := N + (k + 3) with hMdef
  have hxM : BishopC.COF.lt (eps k) (x.val M) := hN M (by omega)
  have hlow : Le (x.val M - tol M) (y.val M) := rel_point_lower x y hrel M
  have htolM : Le (tol M) (eps (k + 1)) := by
    have h1 : Le (eps M) (eps (k + 2)) := eps_le_of_le (by omega)
    have hsum := BishopC.le_add h1 h1
    rw [eps_succ_add_self (k + 1)] at hsum
    exact hsum
  have hbound : Le (eps (k + 1) + tol M) (eps k) := by
    have hh := BishopC.le_add (BishopC.le_refl (eps (k + 1))) htolM
    rw [eps_succ_add_self k] at hh
    exact hh
  have hlt_sum : BishopC.COF.lt (eps (k + 1) + tol M) (x.val M) :=
    scalar_lt_of_le_of_lt hbound hxM
  have hshift : BishopC.COF.lt (eps (k + 1)) (x.val M - tol M) := by
    have t := BishopC.COF.lt_add_left (-(tol M)) hlt_sum
    rwa [show -(tol M) + (eps (k + 1) + tol M) = eps (k + 1) from by ring,
      show -(tol M) + x.val M = x.val M - tol M from by ring] at t
  exact BishopC.lt_of_lt_of_le hshift hlow

/-- rel-transport of the DATA strict order `regularSeqLtData`. -/
def regularSeqLtData_relT (x x' y y' : RegularSeq)
    (hx : rel x x') (hy : rel y y')
    (h : regularSeqLtData x y) : regularSeqLtData x' y' :=
  posEventuallyData_relT (subSeq y x) (subSeq y' x') (sub_respects y y' x x' hy hx) h

/-- data `d − 2σ > 0` (= `data 2σ < d`, `σ = ¼d` pointwise-scaleC): transport
`data ½d>0` (`half_scale_pos_dataC hd`) along the raw rel `½d ≈ d − 2σ`
(`two_sigma_sub_bridge`, instantiated at the concrete `z := CReal.zero`) via
`posEventuallyData_relT`. This is the pointwise-scaleC substitute for the step-4
grid input `data v−u>0` (`u = bpt(i-1)+σ, v = bpt i − σ`, `v−u = d−2σ`): the
scalar-scale σ makes the `2σ ≈ ½d` identity a *raw* `rel`, hence DATA-transportable
choice-free, where the previous `sigmaC` (`CReal.mul`) `σ+σ≈½d` only held `relEventually`
(∃, choice-blocked). Companion to `half_scale_pos_dataC`. -/
def sigmaScaleC_two_lt_dataC {d : RegularSeq}
    (hd : regularSeqLtData CReal.zero d) :
    regularSeqLtData (addSeq (sigmaScaleC d) (sigmaScaleC d)) d :=
  posEventuallyData_relT
    (subSeq (halfScaleC d) CReal.zero)
    (subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d)))
    (two_sigma_sub_bridge d CReal.zero (fun _ => rfl))
    (half_scale_pos_dataC hd)

/-- Technical lemma used in the public import closure. -/
def gridSlot_lt_dataC {a d : CReal} (hd : regularSeqLtData CReal.zero d) (j : Nat) :
    regularSeqLtData (addSeq (bptRC a d j) (sigmaScaleC d))
                     (subSeq (bptRC a d (j + 1)) (sigmaScaleC d)) :=
  posEventuallyData_relT
    (subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d)))
    (subSeq (subSeq (bptRC a d (j + 1)) (sigmaScaleC d))
            (addSeq (bptRC a d j) (sigmaScaleC d)))
    (two_sigma_sub_bridge_grid a d j)
    (sigmaScaleC_two_lt_dataC hd)

/-- Technical lemma used in the public import closure. -/
theorem bptRC_equiv_bptC (a d : CReal) (i : Nat) : bptRC a d i ≈ bptC a d i := by
  induction i with
  | zero => exact Setoid.symm (bptC_zeroC a d)
  | succ i ih =>
    show CReal.add (bptRC a d i) d ≈ bptC a d (i + 1)
    refine Setoid.trans ?_ (Setoid.symm (bptC_succC a d i))
    exact CReal.add_respects_equiv _ _ _ _ ih (Setoid.refl d)

/-- Technical lemma used in the public import closure. -/
theorem constSeq_mulC (p q : Scalar) :
    relEventually (CReal.mul (constSeq p) (constSeq q)) (constSeq (p * q)) := by
  intro k
  refine ⟨0, ?_⟩
  intro n _hn
  have hval :
      (CReal.mul (constSeq p) (constSeq q)).val n - (constSeq (p * q)).val n = (0 : Scalar) := by
    change (p * q) - (p * q) = 0
    ring
  rw [hval]
  change BishopCReal.Le (BishopCRat.CRat.absF 0) (eps k)
  rw [scalarCOFOSeed.abs_zero]
  exact eps_nonneg k

/-- Technical lemma used in the public import closure. -/
theorem bptC_KC {a b d : CReal} (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) :
    bptC a d (2 ^ e) ≈ b := by
  show CReal.add a (CReal.mul (constSeq (Nat.cast (2 ^ e))) d) ≈ b
  have hscalar : (Nat.cast (2 ^ e) : Scalar) * eps e = 1 := by
    rw [mul_comm]; exact eps_mul_natCast_twoPow e
  have hKH : relEventually (CReal.mul (constSeq (Nat.cast (2 ^ e))) (halfPow e)) CReal.one := by
    calc CReal.mul (constSeq (Nat.cast (2 ^ e))) (halfPow e)
        = CReal.mul (constSeq (Nat.cast (2 ^ e))) (constSeq (eps e)) := rfl
      _ ≈ constSeq (Nat.cast (2 ^ e) * eps e) := constSeq_mulC _ _
      _ = constSeq (1 : Scalar) := by rw [hscalar]
      _ = CReal.one := rfl
  have hreassoc :
      relEventually
        (CReal.mul (constSeq (Nat.cast (2 ^ e))) (CReal.mul (CReal.sub b a) (halfPow e)))
        (CReal.mul (CReal.sub b a) (CReal.mul (constSeq (Nat.cast (2 ^ e))) (halfPow e))) := by
    calc CReal.mul (constSeq (Nat.cast (2 ^ e))) (CReal.mul (CReal.sub b a) (halfPow e))
        ≈ CReal.mul (CReal.mul (constSeq (Nat.cast (2 ^ e))) (CReal.sub b a)) (halfPow e) :=
          Setoid.symm (CReal.mul_assoc _ _ _)
      _ ≈ CReal.mul (CReal.mul (CReal.sub b a) (constSeq (Nat.cast (2 ^ e)))) (halfPow e) :=
          CReal.mul_respects_equiv _ _ _ _ (CReal.mul_comm _ _) (Setoid.refl _)
      _ ≈ CReal.mul (CReal.sub b a) (CReal.mul (constSeq (Nat.cast (2 ^ e))) (halfPow e)) :=
          CReal.mul_assoc _ _ _
  have hmulD :
      relEventually (CReal.mul (constSeq (Nat.cast (2 ^ e))) d) (CReal.sub b a) := by
    calc CReal.mul (constSeq (Nat.cast (2 ^ e))) d
        ≈ CReal.mul (constSeq (Nat.cast (2 ^ e))) (CReal.mul (CReal.sub b a) (halfPow e)) :=
          CReal.mul_respects_equiv _ _ _ _ (Setoid.refl _) hdeq
      _ ≈ CReal.mul (CReal.sub b a) (CReal.mul (constSeq (Nat.cast (2 ^ e))) (halfPow e)) := hreassoc
      _ ≈ CReal.mul (CReal.sub b a) CReal.one :=
          CReal.mul_respects_equiv _ _ _ _ (Setoid.refl _) hKH
      _ ≈ CReal.sub b a := CReal.mul_one _
  have hadd :
      relEventually (CReal.add a (CReal.mul (constSeq (Nat.cast (2 ^ e))) d))
                    (CReal.add a (CReal.sub b a)) :=
    CReal.add_respects_equiv _ _ _ _ (Setoid.refl a) hmulD
  have hfin : relEventually (CReal.add a (CReal.sub b a)) b :=
    Setoid.trans (CReal.add_comm a (CReal.sub b a)) (addSeq_sub_right_cancel_eventually b a)
  exact Setoid.trans hadd hfin

/-- Technical lemma used in the public import closure. -/
theorem ha_bptRC (a d : CReal) (hd_nn : RegularSeqNonneg d) (i : Nat) :
    RegularSeqLe a (bptRC a d i) :=
  regularSeqLe_of_right_eventual (Setoid.symm (bptRC_equiv_bptC a d i)) (ha_bptC a d hd_nn i)

/-- Technical lemma used in the public import closure. -/
theorem hbptRC_leC (a d : CReal) (hd_nn : RegularSeqNonneg d) {i j : Nat} (hij : i ≤ j) :
    RegularSeqLe (bptRC a d i) (bptRC a d j) :=
  regularSeqLe_of_left_eventual (bptRC_equiv_bptC a d i)
    (regularSeqLe_of_right_eventual (Setoid.symm (bptRC_equiv_bptC a d j)) (hbpt_leC a d hd_nn hij))

/-- Technical lemma used in the public import closure. -/
theorem hbptRC_b {a b d : CReal} (hd_nn : RegularSeqNonneg d) (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) {i : Nat} (hi : i ≤ 2 ^ e) :
    RegularSeqLe (bptRC a d i) b := by
  have hend : RegularSeqLe (bptRC a d (2 ^ e)) b :=
    regularSeqLe_of_right_eventual
      (Setoid.trans (bptRC_equiv_bptC a d (2 ^ e)) (bptC_KC e hdeq))
      (regularSeqLe_refl (bptRC a d (2 ^ e)))
  exact regularSeqLe_trans (hbptRC_leC a d hd_nn hi) hend

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLe_zero_of_ltData {x : RegularSeq}
    (h : regularSeqLtData zeroSeq x) : RegularSeqLe zeroSeq x := by
  have hpos : regularSeqLtProp zeroSeq x := h.toProp
  refine regularSeqNonneg_of_eventual (subSeq_zero_right_eventually x) ?_
  intro hlt
  exact regularSeqLtProp_irrefl zeroSeq
    (regularSeqLtProp_trans zeroSeq x zeroSeq hpos hlt)

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLe_self_add_of_nonneg (x d : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) : RegularSeqLe x (addSeq x d) := by
  have hstep : RegularSeqLe (addSeq x zeroSeq) (addSeq x d) :=
    regularSeqLe_add (regularSeqLe_refl x) hd
  exact regularSeqLe_of_left_eventual
    (relEventually_symm (addSeq x zeroSeq) x (addSeq_zero_right_eventually x)) hstep

/-- Technical lemma used in the public import closure. -/
theorem sigmaScaleC_nonneg {d : RegularSeq}
    (hd_pos : regularSeqLtData zeroSeq d) :
    RegularSeqLe zeroSeq (sigmaScaleC d) :=
  regularSeqLe_zero_of_ltData (half_scale_pos_dataC (half_scale_pos_dataC hd_pos))

/-- Technical lemma used in the public import closure. -/
theorem slot_hauC (a d : CReal) (hd_nn : RegularSeqNonneg d)
    (hd_pos : regularSeqLtData zeroSeq d) (j : Nat) :
    RegularSeqLe a (addSeq (bptRC a d j) (sigmaScaleC d)) :=
  regularSeqLe_trans (ha_bptRC a d hd_nn j)
    (regularSeqLe_self_add_of_nonneg (bptRC a d j) (sigmaScaleC d)
      (sigmaScaleC_nonneg hd_pos))

/-- Technical lemma used in the public import closure. -/
theorem slot_hvbC {a b d : CReal} (hd_nn : RegularSeqNonneg d)
    (hd_pos : regularSeqLtData zeroSeq d) (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) {j : Nat} (hj1 : j + 1 ≤ 2 ^ e) :
    RegularSeqLe (subSeq (bptRC a d (j + 1)) (sigmaScaleC d)) b :=
  regularSeqLe_trans
    (regularSeqLe_sub_right_self_of_nonneg (bptRC a d (j + 1)) (sigmaScaleC d)
      (sigmaScaleC_nonneg hd_pos))
    (hbptRC_b hd_nn e hdeq hj1)

/-- Technical lemma used in the public import closure. -/
def SlotC {a b : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (d : CReal) (K : Nat) (i : Nat) (g : P.Code) : Prop :=
  g ∈ P.F ∧
  (i = 0 → g = P.oneCode) ∧
  (i = K + 1 → g = P.zeroCode) ∧
  (∀ (_hi0 : 0 < i) (_hiK : i ≤ K),
    (∀ t, RegularSeqLe a t → RegularSeqLe t (addSeq (bptRC a d (i - 1)) (sigmaScaleC d)) →
      P.embed g t ≈ CReal.zero) ∧
    (∀ t, RegularSeqLe (subSeq (bptRC a d i) (sigmaScaleC d)) t → RegularSeqLe t b →
      P.embed g t ≈ CReal.one))

/-- Technical lemma used in the public import closure. -/
noncomputable def hSlotC {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (i : Nat) : { g : P.Code // SlotC P d (2 ^ e) i g } := by
  by_cases hi0 : i = 0
  · subst i
    exact ⟨P.oneCode, P.has_one, (fun _ => rfl),
      (fun hbad => (Nat.succ_ne_zero (2 ^ e) hbad.symm).elim),
      (fun hpos => absurd hpos (lt_irrefl 0))⟩
  by_cases hiMid : 0 < i ∧ i ≤ 2 ^ e
  · rcases hiMid with ⟨hiPos, hiK⟩
    have hji : i - 1 + 1 = i := by omega
    have hj1 : i - 1 + 1 ≤ 2 ^ e := by rw [hji]; exact hiK
    have hau : RegularSeqLe a (addSeq (bptRC a d (i - 1)) (sigmaScaleC d)) :=
      slot_hauC a d hd_nn hd_pos (i - 1)
    have huv : PosEventuallyData
        (CReal.sub (subSeq (bptRC a d i) (sigmaScaleC d))
          (addSeq (bptRC a d (i - 1)) (sigmaScaleC d))) := by
      have h := gridSlot_lt_dataC (a := a) hd_pos (i - 1)
      rw [hji] at h
      exact h
    have hvb : RegularSeqLe (subSeq (bptRC a d i) (sigmaScaleC d)) b := by
      have h := slot_hvbC hd_nn hd_pos e hdeq (j := i - 1) hj1
      rw [hji] at h
      exact h
    rcases P.separating (addSeq (bptRC a d (i - 1)) (sigmaScaleC d))
        (subSeq (bptRC a d i) (sigmaScaleC d)) hau huv hvb with ⟨g, hg, hgz, hgo⟩
    exact ⟨g, hg, (fun h => (hi0 h).elim),
      (fun hK1 => absurd (hK1 ▸ hiK) (Nat.not_succ_le_self _)), (fun _ _ => ⟨hgz, hgo⟩)⟩
  · exact ⟨P.zeroCode, P.has_zero, (fun h => (hi0 h).elim), (fun _ => rfl),
      (fun hiPos hiK => (hiMid ⟨hiPos, hiK⟩).elim)⟩

/-- Technical lemma used in the public import closure. -/
noncomputable def fC {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) : Nat → P.Code :=
  fun i => (hSlotC P hd_nn hd_pos e hdeq i).val

/-- Technical lemma used in the public import closure. -/
theorem fC_spec {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) (i : Nat) :
    SlotC P d (2 ^ e) i (fC P hd_nn hd_pos e hdeq i) :=
  (hSlotC P hd_nn hd_pos e hdeq i).property

/-- Technical lemma used in the public import closure. -/
theorem fC_mem {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) (i : Nat) :
    fC P hd_nn hd_pos e hdeq i ∈ P.F :=
  (fC_spec P hd_nn hd_pos e hdeq i).1

/-- Technical lemma used in the public import closure. -/
theorem fC_zero {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) :
    fC P hd_nn hd_pos e hdeq 0 = P.oneCode :=
  (fC_spec P hd_nn hd_pos e hdeq 0).2.1 rfl

/-- Technical lemma used in the public import closure. -/
theorem fC_last {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) :
    fC P hd_nn hd_pos e hdeq (2 ^ e + 1) = P.zeroCode :=
  (fC_spec P hd_nn hd_pos e hdeq (2 ^ e + 1)).2.2.1 rfl

/-- Technical lemma used in the public import closure. -/
theorem fC_left {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (i : Nat) (hi0 : 0 < i) (hiK : i ≤ 2 ^ e) :
    ∀ t, RegularSeqLe a t →
      RegularSeqLe t (addSeq (bptRC a d (i - 1)) (sigmaScaleC d)) →
      P.embed (fC P hd_nn hd_pos e hdeq i) t ≈ CReal.zero :=
  ((fC_spec P hd_nn hd_pos e hdeq i).2.2.2 hi0 hiK).1

/-- Technical lemma used in the public import closure. -/
theorem fC_right {a b d : CReal} {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (i : Nat) (hi0 : 0 < i) (hiK : i ≤ 2 ^ e) :
    ∀ t, RegularSeqLe (subSeq (bptRC a d i) (sigmaScaleC d)) t →
      RegularSeqLe t b →
      P.embed (fC P hd_nn hd_pos e hdeq i) t ≈ CReal.one :=
  ((fC_spec P hd_nn hd_pos e hdeq i).2.2.2 hi0 hiK).2

/-- Technical lemma used in the public import closure. -/
theorem sigmaScaleC_pos_prop {d : CReal} (hd_pos : regularSeqLtData zeroSeq d) :
    regularSeqLtProp CReal.zero (sigmaScaleC d) :=
  (half_scale_pos_dataC (half_scale_pos_dataC hd_pos)).toProp

/-- Technical lemma used in the public import closure. -/
theorem sigmaScaleC_two_lt_d_prop {d : CReal} (hd_pos : regularSeqLtData zeroSeq d) :
    regularSeqLtProp (addSeq (sigmaScaleC d) (sigmaScaleC d)) d :=
  (sigmaScaleC_two_lt_dataC hd_pos).toProp



/-! ### §3 core: hfC_anti / lambda / alpha layer

Imported from `Mathdemo.ScratchAnti`, which built successfully before BSP integration.
This block is the CReal-native mirror of the abstract `hf_anti`, `hlam_anti`,
and `halpha_nn` layer in `BishopSec3_Profile.lean`.
-/

theorem regularSeqLe_zero_of_nonnegC {x : CReal} (hx : RegularSeqNonneg x) :
    RegularSeqLe CReal.zero x := by
  change RegularSeqNonneg (subSeq x CReal.zero)
  exact regularSeqNonneg_of_eventual (subSeq_zero_right_eventually x) hx

/-- If `0 < x`, then `-x < 0`.  Prop-level arithmetic helper for `hfC_anti`. -/
theorem regularSeqLtProp_neg_lt_zeroC {x : CReal}
    (hx : regularSeqLtProp CReal.zero x) :
    regularSeqLtProp (CReal.neg x) CReal.zero := by
  have htmp : regularSeqLtProp
      (CReal.add (CReal.neg x) CReal.zero)
      (CReal.add (CReal.neg x) x) :=
    regularSeqLtProp_add_left (CReal.neg x) CReal.zero x hx
  have hleft : regularSeqLtProp (CReal.neg x)
      (CReal.add (CReal.neg x) x) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (CReal.add_zero (CReal.neg x))) htmp
  exact regularSeqLtProp_of_right_eventual (CReal.add_left_neg x) hleft

/-- If `0 < x`, then `-x < x`. -/
theorem regularSeqLtProp_neg_lt_selfC {x : CReal}
    (hx : regularSeqLtProp CReal.zero x) :
    regularSeqLtProp (CReal.neg x) x :=
  regularSeqLtProp_trans (CReal.neg x) CReal.zero x
    (regularSeqLtProp_neg_lt_zeroC hx) hx

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLtProp_zero_lt_negC {z : CReal}
    (hz : regularSeqLtProp z CReal.zero) :
    regularSeqLtProp CReal.zero (CReal.neg z) := by
  have htmp : regularSeqLtProp
      (CReal.add (CReal.neg z) z)
      (CReal.add (CReal.neg z) CReal.zero) :=
    regularSeqLtProp_add_left (CReal.neg z) z CReal.zero hz
  have hleft : regularSeqLtProp CReal.zero
      (CReal.add (CReal.neg z) CReal.zero) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (CReal.add_left_neg z)) htmp
  exact regularSeqLtProp_of_right_eventual (CReal.add_zero (CReal.neg z)) hleft

/-- Technical lemma used in the public import closure. -/
theorem regularSeqLtProp_abs_split {beta z : CReal}
    (hbeta : regularSeqLtProp CReal.zero beta)
    (h : regularSeqLtProp beta (CReal.abs z)) :
    regularSeqLtProp beta z ∨ regularSeqLtProp beta (CReal.neg z) := by
  have habs_pos : regularSeqLtProp CReal.zero (CReal.abs z) :=
    regularSeqLtProp_trans CReal.zero beta (CReal.abs z) hbeta h
  rcases CReal.lt_or_lt_of_abs_pos_E habs_pos with hzpos | hzneg
  · -- 0 < z : |z| ≈ z
    left
    have hznn : ¬ CReal.ltE z CReal.zero := fun hc =>
      regularSeqLtProp_irrefl CReal.zero
        (regularSeqLtProp_trans CReal.zero z CReal.zero hzpos hc)
    have habs_eq : CReal.abs z ≈ z := CReal.abs_of_nonneg_E hznn
    exact regularSeqLtProp_of_right_eventual habs_eq h
  · -- z < 0 : |z| ≈ neg z
    right
    have h0negz : regularSeqLtProp CReal.zero (CReal.neg z) :=
      regularSeqLtProp_zero_lt_negC hzneg
    have hnegznn : ¬ CReal.ltE (CReal.neg z) CReal.zero := fun hc =>
      regularSeqLtProp_irrefl CReal.zero
        (regularSeqLtProp_trans CReal.zero (CReal.neg z) CReal.zero h0negz hc)
    have h1 : CReal.abs (CReal.neg z) ≈ CReal.neg z :=
      CReal.abs_of_nonneg_E hnegznn
    have h2 : CReal.abs (CReal.neg z) ≈ CReal.abs z := CReal.abs_neg z
    have habs_eq : CReal.abs z ≈ CReal.neg z :=
      Setoid.trans (Setoid.symm h2) h1
    exact regularSeqLtProp_of_right_eventual habs_eq h

/-- The open gap between the right edge of slot `i` and the left edge of slot `j`
for `i < j`: `bptRC i - σ < bptRC (j-1) + σ`.  This is the CReal-native
counterpart of the `hgap` subproof inside abstract `hf_anti`. -/
theorem grid_slot_prop_gapC {a d : CReal}
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    {i j : Nat} (hijlt : i < j) :
    regularSeqLtProp
      (subSeq (bptRC a d i) (sigmaScaleC d))
      (addSeq (bptRC a d (j - 1)) (sigmaScaleC d)) := by
  have hijm : i ≤ j - 1 := by omega
  have hbase : RegularSeqLe (bptRC a d i) (bptRC a d (j - 1)) :=
    hbptRC_leC a d hd_nn hijm
  have hσ : regularSeqLtProp CReal.zero (sigmaScaleC d) :=
    sigmaScaleC_pos_prop hd_pos
  have hnegpos : regularSeqLtProp (CReal.neg (sigmaScaleC d)) (sigmaScaleC d) :=
    regularSeqLtProp_neg_lt_selfC hσ
  have htmp : regularSeqLtProp
      (CReal.add (bptRC a d i) (CReal.neg (sigmaScaleC d)))
      (CReal.add (bptRC a d i) (sigmaScaleC d)) :=
    regularSeqLtProp_add_left (bptRC a d i)
      (CReal.neg (sigmaScaleC d)) (sigmaScaleC d) hnegpos
  have hlocal : regularSeqLtProp
      (subSeq (bptRC a d i) (sigmaScaleC d))
      (CReal.add (bptRC a d i) (sigmaScaleC d)) :=
    regularSeqLtProp_of_left_eventual
      (subSeq_eq_add_neg_eventually (bptRC a d i) (sigmaScaleC d)) htmp
  have hshift : RegularSeqLe
      (CReal.add (bptRC a d i) (sigmaScaleC d))
      (CReal.add (bptRC a d (j - 1)) (sigmaScaleC d)) :=
    regularSeqLe_add hbase (regularSeqLe_refl (sigmaScaleC d))
  exact regularSeqLtProp_of_lt_of_le hlocal hshift

/-- Antitonicity of the separator family `fC`: if `i ≤ j`, then pointwise
`f_j ≤ f_i`.  This is the CReal-native mirror of abstract `hf_anti`
(`BishopSec3_Profile.lean`, around lines 1064--1104). -/
theorem hfC_anti {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (hd_nn : RegularSeqNonneg d)
    (hd_pos : regularSeqLtData zeroSeq d) (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (i j : Nat) (hij : i ≤ j) (hjK1 : j ≤ 2 ^ e + 1) :
    ∀ t, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe
        (P.embed (fC P hd_nn hd_pos e hdeq j) t)
        (P.embed (fC P hd_nn hd_pos e hdeq i) t) := by
  intro t hat htb
  by_cases hi0 : i = 0
  · subst i
    simpa [fC_zero P hd_nn hd_pos e hdeq, P.embed_one]
      using (P.bound (fC P hd_nn hd_pos e hdeq j)
        (fC_mem P hd_nn hd_pos e hdeq j) t hat htb).2
  by_cases hjlast : j = 2 ^ e + 1
  · subst j
    simpa [fC_last P hd_nn hd_pos e hdeq, P.embed_zero]
      using regularSeqLe_zero_of_nonnegC
        ((P.bound (fC P hd_nn hd_pos e hdeq i)
          (fC_mem P hd_nn hd_pos e hdeq i) t hat htb).1)
  by_cases hijEq : i = j
  · subst j
    exact regularSeqLe_refl _
  have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
  have hjK : j ≤ 2 ^ e := by
    have hjlt : j < 2 ^ e + 1 := Nat.lt_of_le_of_ne hjK1 hjlast
    exact Nat.le_of_lt_succ hjlt
  have hijlt : i < j := Nat.lt_of_le_of_ne hij hijEq
  have hjPos : 0 < j := Nat.lt_trans hiPos hijlt
  have hiK : i ≤ 2 ^ e := Nat.le_trans (Nat.le_of_lt hijlt) hjK
  have hgap : regularSeqLtProp
      (subSeq (bptRC a d i) (sigmaScaleC d))
      (addSeq (bptRC a d (j - 1)) (sigmaScaleC d)) :=
    grid_slot_prop_gapC hd_nn hd_pos hijlt
  rcases regularSeqLtProp_cotrans
      (subSeq (bptRC a d i) (sigmaScaleC d))
      (addSeq (bptRC a d (j - 1)) (sigmaScaleC d)) t hgap with htRight | htLeft
  · have hfi : P.embed (fC P hd_nn hd_pos e hdeq i) t ≈ CReal.one :=
      fC_right P hd_nn hd_pos e hdeq i hiPos hiK t
        (regularSeqLe_of_ltPropC htRight) htb
    have hj_le_one : RegularSeqLe
        (P.embed (fC P hd_nn hd_pos e hdeq j) t) CReal.one :=
      (P.bound (fC P hd_nn hd_pos e hdeq j)
        (fC_mem P hd_nn hd_pos e hdeq j) t hat htb).2
    exact regularSeqLe_of_right_eventual (Setoid.symm hfi) hj_le_one
  · have hfj : P.embed (fC P hd_nn hd_pos e hdeq j) t ≈ CReal.zero :=
      fC_left P hd_nn hd_pos e hdeq j hjPos hjK t hat
        (regularSeqLe_of_ltPropC htLeft)
    have hzero_le_i : RegularSeqLe CReal.zero
        (P.embed (fC P hd_nn hd_pos e hdeq i) t) :=
      regularSeqLe_zero_of_nonnegC
        ((P.bound (fC P hd_nn hd_pos e hdeq i)
          (fC_mem P hd_nn hd_pos e hdeq i) t hat htb).1)
    exact regularSeqLe_of_left_eventual hfj hzero_le_i

/-- Lambda sequence attached to the separator family. -/
noncomputable def lamC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (hd_nn : RegularSeqNonneg d)
    (hd_pos : regularSeqLtData zeroSeq d) (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) : Nat → CReal :=
  fun i => P.lambda (fC P hd_nn hd_pos e hdeq i)

/-- Antitonicity of the lambda values, obtained from `P.mono` and `hfC_anti`. -/
theorem hlamC_anti {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (hd_nn : RegularSeqNonneg d)
    (hd_pos : regularSeqLtData zeroSeq d) (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (i j : Nat) (hij : i ≤ j) (hjK1 : j ≤ 2 ^ e + 1) :
    RegularSeqLe
      (lamC P hd_nn hd_pos e hdeq j)
      (lamC P hd_nn hd_pos e hdeq i) := by
  dsimp [lamC]
  exact P.mono (fC P hd_nn hd_pos e hdeq j)
    (fC P hd_nn hd_pos e hdeq i)
    (fC_mem P hd_nn hd_pos e hdeq j)
    (fC_mem P hd_nn hd_pos e hdeq i)
    (hfC_anti P hd_nn hd_pos e hdeq i j hij hjK1)

/-- Width-two lambda drop `alpha_i = lambda_{i-1} - lambda_{i+1}`. -/
noncomputable def alphaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (hd_nn : RegularSeqNonneg d)
    (hd_pos : regularSeqLtData zeroSeq d) (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) : Nat → CReal :=
  fun i => subSeq (lamC P hd_nn hd_pos e hdeq (i - 1))
    (lamC P hd_nn hd_pos e hdeq (i + 1))

/-- Nonnegativity of the two-step lambda drop on interior indices. -/
theorem halphaC_nn {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (hd_nn : RegularSeqNonneg d)
    (hd_pos : regularSeqLtData zeroSeq d) (e : Nat)
    (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (i : Nat) (_hi0 : 0 < i) (hiK : i ≤ 2 ^ e) :
    RegularSeqNonneg (alphaC P hd_nn hd_pos e hdeq i) := by
  have hidx : i - 1 ≤ i + 1 := by
    exact Nat.le_trans (Nat.sub_le i 1) (Nat.le_succ i)
  have hupper : i + 1 ≤ 2 ^ e + 1 := Nat.succ_le_succ hiK
  have hle := hlamC_anti P hd_nn hd_pos e hdeq (i - 1) (i + 1) hidx hupper
  simpa [alphaC, lamC] using hle

/-- The `lamC` endpoint diameter is the profile's one-zero lambda diameter. -/
theorem lemma33LamTotal_equiv_profileDiameterC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e)) :
    CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
      (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
    CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode) := by
  dsimp [lamC]
  rw [fC_zero P hd_nn hd_pos e hdeq]
  rw [fC_last P hd_nn hd_pos e hdeq]

/-- The profile one-zero lambda diameter is nonnegative. -/
theorem lemma33ProfileDiameter_nonnegC {a b : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) :
    RegularSeqNonneg (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode)) := by
  have hle : RegularSeqLe (P.lambda P.zeroCode) (P.lambda P.oneCode) := by
    exact P.mono P.zeroCode P.oneCode P.has_zero P.has_one (by
      intro t hat htb
      rw [P.embed_zero, P.embed_one]
      exact CReal.zero_le_oneC)
  exact hle

#print axioms BishopSec3P.hfC_anti
#print axioms BishopSec3P.hlamC_anti
#print axioms BishopSec3P.halphaC_nn
#print axioms BishopSec3P.lemma33LamTotal_equiv_profileDiameterC
#print axioms BishopSec3P.lemma33ProfileDiameter_nonnegC




/-! ### §3 core: classification / Good / next / selected endpoints layer

Imported from `Mathdemo.ScratchClassify`, which built successfully before BSP integration.
This block follows `hfC_anti / hlamC_anti / halphaC_nn` and mirrors the
classification / Good / next / s / N layer of the abstract `lemma_3_3`.
-/

def lemma33IterC (next : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => next (lemma33IterC next j)

/-- Minimality of `Nat.find`, in the negative form used by the retained-index
construction.  Pure Nat/Bool; no CReal content. -/
theorem lemma33_not_of_lt_findC {p : Nat → Prop} [DecidablePred p]
    (H : ∃ n, p n) {m : Nat} (hm : m < Nat.find H) : ¬ p m := by
  intro hpm
  exact (Nat.not_le_of_lt hm) (Nat.find_min' H hpm)

/--
Data-valued cotransitive classification used by the hardness-4 rewrite.

`false` records the big branch `theta < x`; `true` records the small branch
`x < eps`.  The returned Boolean is data, not a decidable-looking decision of a
proposition.
-/
def lemma33H4_classifyC {theta eps : CReal}
    (h : regularSeqLtData theta eps) (x : CReal) :
    {c : Bool //
      (c = true → regularSeqLtProp x eps) ∧
      (c = false → regularSeqLtProp theta x)} := by
  match regularSeqLtData_cotrans theta eps x h with
  | .inl hbig =>
      refine ⟨false, ?_⟩
      constructor
      · intro hbad
        cases hbad
      · intro _
        exact hbig.toProp
  | .inr hsmall =>
      refine ⟨true, ?_⟩
      constructor
      · intro _
        exact hsmall.toProp
      · intro hbad
        cases hbad

/-- Boolean classification of a nonnegative increment sequence `alpha`. -/
def clsC {theta eps : CReal}
    (htheta_eps : regularSeqLtData theta eps) (alpha : Nat → CReal) : Nat → Bool :=
  fun i => (lemma33H4_classifyC htheta_eps (alpha i)).1

/-- Small-branch accessor for `clsC`. -/
theorem clsC_small {theta eps : CReal}
    (htheta_eps : regularSeqLtData theta eps) (alpha : Nat → CReal)
    (i : Nat) (hci : clsC htheta_eps alpha i = true) :
    regularSeqLtProp (alpha i) eps := by
  change (lemma33H4_classifyC htheta_eps (alpha i)).1 = true at hci
  exact (lemma33H4_classifyC htheta_eps (alpha i)).2.1 hci

/-- Big-branch accessor for `clsC`. -/
theorem clsC_big {theta eps : CReal}
    (htheta_eps : regularSeqLtData theta eps) (alpha : Nat → CReal)
    (i : Nat) (hci : clsC htheta_eps alpha i = false) :
    regularSeqLtProp theta (alpha i) := by
  change (lemma33H4_classifyC htheta_eps (alpha i)).1 = false at hci
  exact (lemma33H4_classifyC htheta_eps (alpha i)).2.2 hci

/-- Retained grid indices: endpoints, small node, or predecessor of a small node. -/
def GoodC (K : Nat) (cls : Nat → Bool) (i : Nat) : Prop :=
  i = 0 ∨ i = K ∨
    (0 < i ∧ i ≤ K ∧ cls i = true) ∨
    (i < K ∧ cls (i + 1) = true)

/-- `GoodC` is decidable because it is built only from Nat comparisons,
Nat equalities, and Bool equalities.  This is needed by `Nat.find` in `nextC`. -/
instance instDecidablePredGoodC (K : Nat) (cls : Nat → Bool) :
    DecidablePred (GoodC K cls) := by
  intro i
  unfold GoodC
  infer_instance

/-- The right endpoint `K` is retained. -/
theorem hGoodKC (K : Nat) (cls : Nat → Bool) : GoodC K cls K := by
  dsimp [GoodC]
  exact Or.inr (Or.inl rfl)

/-- For each `k < K`, at least one retained index lies strictly to the right. -/
theorem hCandC (K : Nat) (cls : Nat → Bool) (k : Nat) (hk : k < K) :
    ∃ i : Nat, k < i ∧ i ≤ K ∧ GoodC K cls i :=
  ⟨K, hk, Nat.le_refl K, hGoodKC K cls⟩

/-- Least retained index strictly to the right of `k`, or `K` outside the range. -/
noncomputable def nextC (K : Nat) (cls : Nat → Bool) : Nat → Nat :=
  fun k => if hk : k < K then Nat.find (hCandC K cls k hk) else K

/-- Specification of `nextC` inside the grid. -/
theorem hnext_specC (K : Nat) (cls : Nat → Bool) (k : Nat) (hk : k < K) :
    k < nextC K cls k ∧ nextC K cls k ≤ K ∧ GoodC K cls (nextC K cls k) := by
  dsimp [nextC]
  rw [dif_pos hk]
  exact Nat.find_spec (hCandC K cls k hk)

/-- Outside the active range, `nextC` is exactly `K`. -/
theorem hnext_eq_KC (K : Nat) (cls : Nat → Bool) (k : Nat) (hk : ¬ k < K) :
    nextC K cls k = K := by
  dsimp [nextC]
  rw [dif_neg hk]

/-- `nextC` never moves past `K`. -/
theorem hnext_leC (K : Nat) (cls : Nat → Bool) (k : Nat) :
    nextC K cls k ≤ K := by
  by_cases hk : k < K
  · exact (hnext_specC K cls k hk).2.1
  · rw [hnext_eq_KC K cls k hk]

/-- Minimality of `nextC`: no retained index lies strictly between `k` and
`nextC K cls k`. -/
theorem hnext_minC (K : Nat) (cls : Nat → Bool) (k m : Nat) (hk : k < K)
    (hkm : k < m) (hmn : m < nextC K cls k) : ¬ GoodC K cls m := by
  have hnle : nextC K cls k ≤ K := (hnext_specC K cls k hk).2.1
  have hmK : m ≤ K := Nat.le_trans (Nat.le_of_lt hmn) hnle
  have hnot : ¬ (k < m ∧ m ≤ K ∧ GoodC K cls m) := by
    dsimp [nextC] at hmn
    rw [dif_pos hk] at hmn
    exact lemma33_not_of_lt_findC (hCandC K cls k hk) hmn
  intro hgm
  exact hnot ⟨hkm, hmK, hgm⟩

/-- Retained-index iteration sequence. -/
noncomputable def sC (K : Nat) (cls : Nat → Bool) : Nat → Nat :=
  lemma33IterC (nextC K cls)

/-- The iteration starts at the left endpoint. -/
theorem hs_zeroC (K : Nat) (cls : Nat → Bool) : sC K cls 0 = 0 := by
  rfl

/-- Successor equation for the retained-index iteration. -/
theorem hs_succC (K : Nat) (cls : Nat → Bool) (j : Nat) :
    sC K cls (j + 1) = nextC K cls (sC K cls j) := by
  rfl

/-- Every retained iterate remains at or before `K`. -/
theorem hs_le_KC (K : Nat) (cls : Nat → Bool) (j : Nat) : sC K cls j ≤ K := by
  induction j with
  | zero =>
      rw [hs_zeroC]
      exact Nat.zero_le K
  | succ j ih =>
      rw [hs_succC]
      exact hnext_leC K cls (sC K cls j)

/-- If the current retained point is not yet `K`, the iteration strictly moves right. -/
theorem hs_stepC (K : Nat) (cls : Nat → Bool) (j : Nat) (hj : sC K cls j < K) :
    sC K cls j < sC K cls (j + 1) := by
  rw [hs_succC]
  exact (hnext_specC K cls (sC K cls j) hj).1

/-- The retained-index iteration eventually dominates the iteration counter. -/
theorem hs_ge_indexC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hjK : j ≤ K) : j ≤ sC K cls j := by
  induction j with
  | zero => exact Nat.zero_le (sC K cls 0)
  | succ j ih =>
      have hjK' : j ≤ K := Nat.le_trans (Nat.le_succ j) hjK
      have hij : j ≤ sC K cls j := ih hjK'
      by_cases hsj : sC K cls j < K
      · have hstrict := hs_stepC K cls j hsj
        omega
      · rw [hs_succC, hnext_eq_KC K cls (sC K cls j) hsj]
        exact hjK

/-- At time `K`, the retained iteration has reached `K`. -/
theorem hs_KC (K : Nat) (cls : Nat → Bool) : sC K cls K = K :=
  Nat.le_antisymm (hs_le_KC K cls K) (hs_ge_indexC K cls K (Nat.le_refl K))

/-- First time when the retained iteration reaches `K`. -/
noncomputable def N_C (K : Nat) (cls : Nat → Bool) : Nat :=
  Nat.find (show ∃ j : Nat, sC K cls j = K from ⟨K, hs_KC K cls⟩)

/-- The first hitting time indeed hits `K`. -/
theorem hs_NC (K : Nat) (cls : Nat → Bool) : sC K cls (N_C K cls) = K := by
  dsimp [N_C]
  exact Nat.find_spec (show ∃ j : Nat, sC K cls j = K from ⟨K, hs_KC K cls⟩)

/-- The first hitting time is at most `K`. -/
theorem hN_le_KC (K : Nat) (cls : Nat → Bool) : N_C K cls ≤ K := by
  by_contra hbad
  have hKN : K < N_C K cls := Nat.lt_of_not_ge hbad
  have hnot : sC K cls K ≠ K := by
    dsimp [N_C] at hKN
    exact lemma33_not_of_lt_findC
      (show ∃ j : Nat, sC K cls j = K from ⟨K, hs_KC K cls⟩) hKN
  exact hnot (hs_KC K cls)

/-- If `K` is positive, then the hitting time is positive. -/
theorem hNposC (K : Nat) (cls : Nat → Bool) (hKpos : 0 < K) :
    0 < N_C K cls := by
  by_contra hbad
  have hNz : N_C K cls = 0 := Nat.eq_zero_of_not_pos hbad
  have : (0 : Nat) = K := by
    simpa [hNz, hs_zeroC] using hs_NC K cls
  omega

/-- Before the hitting time, the retained iteration is still strictly before `K`. -/
theorem hs_lt_K_of_lt_NC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hjN : j < N_C K cls) : sC K cls j < K := by
  have hnot : sC K cls j ≠ K := by
    dsimp [N_C] at hjN
    exact lemma33_not_of_lt_findC
      (show ∃ r : Nat, sC K cls r = K from ⟨K, hs_KC K cls⟩) hjN
  have hle := hs_le_KC K cls j
  omega

/-- The retained iteration is strictly increasing before the hitting time. -/
theorem hs_strictC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hjN : j < N_C K cls) : sC K cls j < sC K cls (j + 1) :=
  hs_stepC K cls j (hs_lt_K_of_lt_NC K cls j hjN)

/-- The next retained endpoint is always Good before the hitting time. -/
theorem hs_good_succC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hjN : j < N_C K cls) : GoodC K cls (sC K cls (j + 1)) := by
  rw [hs_succC]
  exact (hnext_specC K cls (sC K cls j) (hs_lt_K_of_lt_NC K cls j hjN)).2.2

/-- No retained/Good index lies strictly between consecutive retained iterates. -/
theorem hs_no_good_betweenC (K : Nat) (cls : Nat → Bool)
    (j m : Nat) (hjN : j < N_C K cls)
    (hleft : sC K cls j < m) (hright : m < sC K cls (j + 1)) :
    ¬ GoodC K cls m := by
  rw [hs_succC] at hright
  exact hnext_minC K cls (sC K cls j) m
    (hs_lt_K_of_lt_NC K cls j hjN) hleft hright

/-- Consecutive retained right endpoints are positive before the hitting time. -/
theorem hs_endpoint_posC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hjN : j < N_C K cls) : 0 < sC K cls (j + 1) := by
  have h := hs_strictC K cls j hjN
  omega

/-- Retained right endpoints stay at or below `K`. -/
theorem hs_endpoint_le_KC (K : Nat) (cls : Nat → Bool) (j : Nat) :
    sC K cls (j + 1) ≤ K :=
  hs_le_KC K cls (j + 1)

/-- If a retained right endpoint is small, the preceding retained endpoint is
exactly its immediate predecessor. -/
theorem hs_prev_of_smallC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hjN : j < N_C K cls)
    (hSmallEnd : cls (sC K cls (j + 1)) = true) :
    sC K cls (j + 1) = sC K cls j + 1 := by
  have hki := hs_strictC K cls j hjN
  by_contra hbad
  have hgap : sC K cls j + 1 < sC K cls (j + 1) := by omega
  let m : Nat := sC K cls (j + 1) - 1
  have hm_eq : m + 1 = sC K cls (j + 1) := by
    dsimp [m]
    omega
  have hkm : sC K cls j < m := by
    dsimp [m]
    omega
  have hmi : m < sC K cls (j + 1) := by
    dsimp [m]
    omega
  have hmK : m < K := by
    have hiK := hs_endpoint_le_KC K cls j
    dsimp [m]
    omega
  have hGoodm : GoodC K cls m := by
    dsimp [GoodC]
    exact Or.inr (Or.inr
      (Or.inr ⟨hmK, by simpa [hm_eq] using hSmallEnd⟩))
  exact hs_no_good_betweenC K cls j m hjN hkm hmi hGoodm

/-- If a retained right endpoint is big, every crossed original grid index is big. -/
theorem hs_all_bigC (K : Nat) (cls : Nat → Bool)
    (j m : Nat) (hjN : j < N_C K cls)
    (hBigEnd : cls (sC K cls (j + 1)) = false)
    (hleft : sC K cls j < m) (hright : m ≤ sC K cls (j + 1)) :
    cls m = false := by
  by_cases hmi : m = sC K cls (j + 1)
  · subst m
    exact hBigEnd
  · cases hcm : cls m with
    | false => rfl
    | true =>
        have hmlt : m < sC K cls (j + 1) := by omega
        have hmPos : 0 < m := by omega
        have hmK : m ≤ K :=
          Nat.le_trans hright (hs_endpoint_le_KC K cls j)
        have hGoodm : GoodC K cls m := by
          dsimp [GoodC]
          exact Or.inr (Or.inr
            (Or.inl ⟨hmPos, hmK, hcm⟩))
        exact (hs_no_good_betweenC K cls j m hjN hleft hmlt hGoodm).elim




/-! ### §3 core: width / p' witness / beta charge layer

Imported from `Mathdemo.ScratchWidthCharge`, which built successfully before
BSP integration.  This block follows the classification / selected-endpoints
layer and stops before the prefix/telescope total-charge proof.
-/

noncomputable def hpprime_of_gapC {a b d upper : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (k i : Nat) (hki : k < i) (hiK : i ≤ 2 ^ e)
    (hgap : regularSeqLtProp
      (CReal.sub (lamC P hd_nn hd_pos e hdeq k)
        (lamC P hd_nn hd_pos e hdeq (i + 1))) upper) :
    P.p_prime_ltC (bptRC a d k) (bptRC a d i) upper := by
  refine ⟨sigmaScaleC d, sigmaScaleC_pos_prop hd_pos, ?_⟩
  refine ⟨fC P hd_nn hd_pos e hdeq (i + 1),
    fC_mem P hd_nn hd_pos e hdeq (i + 1),
    fC P hd_nn hd_pos e hdeq k,
    fC_mem P hd_nn hd_pos e hdeq k, ?_, ?_, ?_⟩
  · intro t hat _htb htv
    have htv' : RegularSeqLe t (addSeq (bptRC a d i) (sigmaScaleC d)) :=
      regularSeqLe_trans htv
        (CReal.min_le_rightC b (addSeq (bptRC a d i) (sigmaScaleC d)))
    by_cases hi : i = 2 ^ e
    · subst i
      rw [fC_last P hd_nn hd_pos e hdeq]
      simpa [P.embed_zero]
    · have hiLt : i < 2 ^ e := Nat.lt_of_le_of_ne hiK hi
      have hz := fC_left P hd_nn hd_pos e hdeq (i + 1)
        (by omega) (by omega) t hat (by
          rw [Nat.add_sub_cancel]
          exact htv')
      exact hz
  · intro t hat htb hut
    have hbase : RegularSeqLe (CReal.sub (bptRC a d k) (sigmaScaleC d))
        (CReal.max a (CReal.sub (bptRC a d k) (sigmaScaleC d))) :=
      CReal.le_max_rightC a (CReal.sub (bptRC a d k) (sigmaScaleC d))
    have hkt : RegularSeqLe (CReal.sub (bptRC a d k) (sigmaScaleC d)) t :=
      regularSeqLe_trans hbase hut
    by_cases hk : k = 0
    · subst k
      rw [fC_zero P hd_nn hd_pos e hdeq]
      simpa [P.embed_one]
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
      have hkK : k ≤ 2 ^ e := Nat.le_trans (Nat.le_of_lt hki) hiK
      exact fC_right P hd_nn hd_pos e hdeq k hkPos hkK t hkt htb
  · exact hgap

/-- Small retained intervals already satisfy `p' < eps`.

The Boolean small accessor is passed as an argument so this lemma can be used
with either `clsC` or a temporary classification sequence during auxiliary work.
-/
noncomputable def hp_smallC {a b d eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool)
    (hcls_small : ∀ i : Nat, cls i = true →
      regularSeqLtProp (alphaC P hd_nn hd_pos e hdeq i) eps)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hSmallEnd : cls (sC (2 ^ e) cls (j + 1)) = true) :
    P.p_prime_ltC
      (bptRC a d (sC (2 ^ e) cls j))
      (bptRC a d (sC (2 ^ e) cls (j + 1))) eps := by
  have hprev := hs_prev_of_smallC (2 ^ e) cls j hjN hSmallEnd
  have hki := hs_strictC (2 ^ e) cls j hjN
  have hiK := hs_endpoint_le_KC (2 ^ e) cls j
  refine hpprime_of_gapC P hd_nn hd_pos e hdeq
    (sC (2 ^ e) cls j) (sC (2 ^ e) cls (j + 1)) hki hiK ?_
  have halphaSmall := hcls_small (sC (2 ^ e) cls (j + 1)) hSmallEnd
  dsimp [alphaC] at halphaSmall
  rw [hprev] at halphaSmall
  rw [Nat.add_sub_cancel] at halphaSmall
  rw [hprev]
  exact halphaSmall

/-- Big-interval beta charge: `lambda(s_j) - lambda(s_{j+1}+1)`. -/
noncomputable def betaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) : Nat → CReal :=
  fun j => CReal.sub
    (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls j))
    (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls (j + 1) + 1))

/-- The beta charge is nonnegative before the hitting time. -/
theorem hbeta_nnC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqNonneg (betaC P hd_nn hd_pos e hdeq cls j) := by
  have hle : RegularSeqLe
      (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls (j + 1) + 1))
      (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls j)) :=
    hlamC_anti P hd_nn hd_pos e hdeq
      (sC (2 ^ e) cls j)
      (sC (2 ^ e) cls (j + 1) + 1)
      (by
        have hstrict := hs_strictC (2 ^ e) cls j hjN
        omega)
      (by
        have hbnd := hs_le_KC (2 ^ e) cls (j + 1)
        omega)
  dsimp [betaC]
  exact hle

/-- Each retained beta charge is bounded by the total lambda diameter.
This is the CReal analogue of the elementary antitone-lambda estimate used
to feed the approximate floor upper cap. -/
theorem hbeta_totalC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (j : Nat) (_hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (betaC P hd_nn hd_pos e hdeq cls j)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  let K : Nat := 2 ^ e
  have hleft : RegularSeqLe
      (lamC P hd_nn hd_pos e hdeq (sC K cls j))
      (lamC P hd_nn hd_pos e hdeq 0) := by
    exact hlamC_anti P hd_nn hd_pos e hdeq 0 (sC K cls j)
      (Nat.zero_le _) (by
        have hb := hs_le_KC K cls j
        omega)
  have hright : RegularSeqLe
      (lamC P hd_nn hd_pos e hdeq (K + 1))
      (lamC P hd_nn hd_pos e hdeq (sC K cls (j + 1) + 1)) := by
    exact hlamC_anti P hd_nn hd_pos e hdeq
      (sC K cls (j + 1) + 1) (K + 1)
      (by
        have hb := hs_le_KC K cls (j + 1)
        omega)
      (Nat.le_refl _)
  have hstep1 : RegularSeqLe
      (CReal.sub
        (lamC P hd_nn hd_pos e hdeq (sC K cls j))
        (lamC P hd_nn hd_pos e hdeq (sC K cls (j + 1) + 1)))
      (CReal.sub
        (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (sC K cls (j + 1) + 1))) :=
    subSeq_monotone_left_regularSeqLe _ _ _ hleft
  have hstep2 : RegularSeqLe
      (CReal.sub
        (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (sC K cls (j + 1) + 1)))
      (CReal.sub
        (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (K + 1))) :=
    regularSeqLe_subSeq_right _ hright
  simpa [betaC, K] using regularSeqLe_trans hstep1 hstep2

/-- A strict upper bound for `beta_j` gives a `p'` bound for the corresponding
retained interval. -/
noncomputable def hp_B_boundC {a b d upper : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hup : regularSeqLtProp (betaC P hd_nn hd_pos e hdeq cls j) upper) :
    P.p_prime_ltC
      (bptRC a d (sC (2 ^ e) cls j))
      (bptRC a d (sC (2 ^ e) cls (j + 1))) upper := by
  refine hpprime_of_gapC P hd_nn hd_pos e hdeq
    (sC (2 ^ e) cls j) (sC (2 ^ e) cls (j + 1))
    (hs_strictC (2 ^ e) cls j hjN)
    (hs_endpoint_le_KC (2 ^ e) cls j) ?_
  simpa [betaC, Nat.add_assoc] using hup

/-- Big retained intervals: active interval and right endpoint classified big. -/
def BintC (K : Nat) (cls : Nat → Bool) (j : Nat) : Prop :=
  j < N_C K cls ∧ cls (sC K cls (j + 1)) = false

/-- `BintC` is decidable: it is built from Nat comparisons and Bool equality.
This instance is needed by the `if BintC ... then ... else ...` in `chargeC`. -/
noncomputable instance instDecidableBintC (K : Nat) (cls : Nat → Bool) :
    DecidablePred (BintC K cls) := by
  intro j
  unfold BintC
  infer_instance

/-- After a big retained interval, the next retained right endpoint is small. -/
theorem hafter_big_smallC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hj1N : j + 1 < N_C K cls) (hBj : BintC K cls j) :
    cls (sC K cls (j + 2)) = true := by
  have hjN : j < N_C K cls := Nat.lt_trans (Nat.lt_succ_self j) hj1N
  have hiGood := hs_good_succC K cls j hjN
  have hiLtK := hs_lt_K_of_lt_NC K cls (j + 1) hj1N
  have hnextSmall : cls (sC K cls (j + 1) + 1) = true := by
    rcases hiGood with h0 | hK | hSmallCase | hsucc
    · exfalso
      have hstrict := hs_strictC K cls j hjN
      omega
    · exfalso
      omega
    · rw [hBj.2] at hSmallCase
      exact Bool.noConfusion hSmallCase.2.2
    · exact hsucc.2
  have hGoodNext : GoodC K cls (sC K cls (j + 1) + 1) := by
    dsimp [GoodC]
    exact Or.inr (Or.inr
      (Or.inl ⟨by omega, by omega, hnextSmall⟩))
  have hs2 : sC K cls (j + 2) = sC K cls (j + 1) + 1 := by
    have hj2 : j + 2 = (j + 1) + 1 := by omega
    rw [hj2, hs_succC]
    have hle : nextC K cls (sC K cls (j + 1)) ≤ sC K cls (j + 1) + 1 := by
      by_contra hbad
      have hlt : sC K cls (j + 1) + 1 < nextC K cls (sC K cls (j + 1)) :=
        Nat.lt_of_not_ge hbad
      exact hnext_minC K cls (sC K cls (j + 1))
        (sC K cls (j + 1) + 1) hiLtK (Nat.lt_succ_self _) hlt hGoodNext
    have hspec := hnext_specC K cls (sC K cls (j + 1)) hiLtK
    omega
  rw [hs2]
  exact hnextSmall

/-- Big retained intervals are never consecutive. -/
theorem hB_not_consecutiveC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hj1N : j + 1 < N_C K cls) (hBj : BintC K cls j) :
    ¬ BintC K cls (j + 1) := by
  intro hnextB
  have hsmall := hafter_big_smallC K cls j hj1N hBj
  have h2 : cls (sC K cls ((j + 1) + 1)) = false := hnextB.2
  have hidx : (j + 1) + 1 = j + 2 := by omega
  rw [hidx] at h2
  rw [hsmall] at h2
  exact Bool.noConfusion h2

/-- Charge sequence: beta on big intervals, zero otherwise. -/
noncomputable def chargeC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) : Nat → CReal :=
  fun j => if BintC (2 ^ e) cls j then betaC P hd_nn hd_pos e hdeq cls j else CReal.zero

/-- Charge equals beta on a big interval. -/
theorem hcharge_of_BC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (j : Nat) (hBj : BintC (2 ^ e) cls j) :
    chargeC P hd_nn hd_pos e hdeq cls j = betaC P hd_nn hd_pos e hdeq cls j := by
  dsimp [chargeC]
  rw [if_pos hBj]

/-- Charge is zero off big intervals. -/
theorem hcharge_of_notB_C {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (j : Nat) (hBj : ¬ BintC (2 ^ e) cls j) :
    chargeC P hd_nn hd_pos e hdeq cls j = CReal.zero := by
  dsimp [chargeC]
  rw [if_neg hBj]

/-- Charge is nonnegative on every active retained interval. -/
theorem hcharge_nnC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqNonneg (chargeC P hd_nn hd_pos e hdeq cls j) := by
  by_cases hBj : BintC (2 ^ e) cls j
  · rw [hcharge_of_BC P hd_nn hd_pos e hdeq cls j hBj]
    exact hbeta_nnC P hd_nn hd_pos e hdeq cls j hjN
  · rw [hcharge_of_notB_C P hd_nn hd_pos e hdeq cls j hBj]
    exact regularSeqNonneg_of_zero_le (regularSeqLe_refl CReal.zero)




/-! ### §3 core: cursor / prefix / telescope / total charge layer

Imported from `Mathdemo.ScratchChargeTotal`, which built successfully before
BSP integration.  This block proves the prefix/telescope accounting bound
`hcharge_totalC`.
-/

def lemma33PrefixC (x : Nat → CReal) : Nat → CReal
  | 0 => CReal.zero
  | n + 1 => CReal.add (lemma33PrefixC x n) (x n)

@[simp] theorem lemma33PrefixC_zero (x : Nat → CReal) :
    lemma33PrefixC x 0 = CReal.zero := rfl

@[simp] theorem lemma33PrefixC_succ (x : Nat → CReal) (n : Nat) :
    lemma33PrefixC x (n + 1) = CReal.add (lemma33PrefixC x n) (x n) := rfl

/-- `x - x ≈ 0`. -/
theorem sub_self_equiv_zeroC (x : CReal) : CReal.sub x x ≈ CReal.zero := by
  have hq : mkQuot (CReal.sub x x) = mkQuot CReal.zero := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (mkQuot x) - (mkQuot x) = 0
    ring
  exact Quotient.exact hq

/-- `↑(n+1) * x ≈ ↑n * x + x`. -/
theorem natCast_succ_mulC (n : Nat) (x : CReal) :
    CReal.mul (constSeq (Nat.cast (n + 1))) x ≈
      CReal.add (CReal.mul (constSeq (Nat.cast n)) x) x := by
  have hc : constSeq (Nat.cast (n + 1)) ≈
      CReal.add (constSeq (Nat.cast n)) CReal.one := constSeq_natCast_succC n
  calc CReal.mul (constSeq (Nat.cast (n + 1))) x
      ≈ CReal.mul (CReal.add (constSeq (Nat.cast n)) CReal.one) x :=
        CReal.mul_respects_equiv _ _ _ _ hc (Setoid.refl x)
    _ ≈ CReal.add (CReal.mul (constSeq (Nat.cast n)) x) (CReal.mul CReal.one x) :=
        CReal.right_distrib _ _ _
    _ ≈ CReal.add (CReal.mul (constSeq (Nat.cast n)) x) x :=
        CReal.add_respects_equiv _ _ _ _ (Setoid.refl _) (CReal.one_mul x)

/-- If every term in a positive prefix is strictly above `theta`, then the
constant prefix `N * theta` is strictly below the prefix sum. -/
theorem lemma33Prefix_const_ltC (theta : CReal) (u : Nat → CReal) (N : Nat)
    (hN : 0 < N) (h : ∀ j : Nat, j < N → regularSeqLtProp theta (u j)) :
    regularSeqLtProp (CReal.mul (constSeq (Nat.cast N)) theta)
      (lemma33PrefixC u N) := by
  induction N with
  | zero => exfalso; omega
  | succ N ih =>
      by_cases hNz : N = 0
      · subst N
        rw [lemma33PrefixC_succ, lemma33PrefixC_zero]
        have hleft : CReal.mul (constSeq (Nat.cast (0 + 1))) theta ≈ theta := by
          simpa using CReal.one_mul theta
        have hright : CReal.add CReal.zero (u 0) ≈ u 0 := CReal.zero_add (u 0)
        exact regularSeqLtProp_of_left_eventual hleft
          (regularSeqLtProp_of_right_eventual (Setoid.symm hright) (h 0 (by omega)))
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hNz
        have hpre : regularSeqLtProp
            (CReal.mul (constSeq (Nat.cast N)) theta)
            (lemma33PrefixC u N) :=
          ih hNpos (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N)))
        have hlast : regularSeqLtProp theta (u N) := h N (Nat.lt_succ_self N)
        have hs : regularSeqLtProp
            (CReal.add (CReal.mul (constSeq (Nat.cast N)) theta) theta)
            (CReal.add (lemma33PrefixC u N) (u N)) :=
          regularSeqLtProp_add hpre hlast
        exact regularSeqLtProp_of_left_eventual (natCast_succ_mulC N theta) hs

/-- Closed-form grid distance for `bptC`. -/
theorem bptC_sub_generalC (a d : CReal) {k i : Nat} (hki : k ≤ i) :
    CReal.sub (bptC a d i) (bptC a d k) ≈
      CReal.mul (constSeq (Nat.cast (i - k))) d := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hki
  have hr : k + r - k = r := by omega
  rw [hr]
  dsimp [bptC]
  have hc : constSeq (Nat.cast (k + r)) ≈
      CReal.add (constSeq (Nat.cast k)) (constSeq (Nat.cast r)) :=
    constSeq_natCast_addC k r
  have hmul : CReal.mul (constSeq (Nat.cast (k + r))) d ≈
      CReal.add (CReal.mul (constSeq (Nat.cast k)) d)
        (CReal.mul (constSeq (Nat.cast r)) d) := by
    calc CReal.mul (constSeq (Nat.cast (k + r))) d
        ≈ CReal.mul (CReal.add (constSeq (Nat.cast k)) (constSeq (Nat.cast r))) d :=
          CReal.mul_respects_equiv _ _ _ _ hc (Setoid.refl d)
      _ ≈ CReal.add (CReal.mul (constSeq (Nat.cast k)) d)
          (CReal.mul (constSeq (Nat.cast r)) d) :=
          CReal.right_distrib _ _ _
  have hleft : CReal.add a (CReal.mul (constSeq (Nat.cast (k + r))) d) ≈
      CReal.add (CReal.add a (CReal.mul (constSeq (Nat.cast k)) d))
        (CReal.mul (constSeq (Nat.cast r)) d) := by
    calc CReal.add a (CReal.mul (constSeq (Nat.cast (k + r))) d)
        ≈ CReal.add a (CReal.add (CReal.mul (constSeq (Nat.cast k)) d)
            (CReal.mul (constSeq (Nat.cast r)) d)) :=
          CReal.add_respects_equiv _ _ _ _ (Setoid.refl a) hmul
      _ ≈ CReal.add (CReal.add a (CReal.mul (constSeq (Nat.cast k)) d))
          (CReal.mul (constSeq (Nat.cast r)) d) :=
          Setoid.symm (CReal.add_assoc a (CReal.mul (constSeq (Nat.cast k)) d)
            (CReal.mul (constSeq (Nat.cast r)) d))
  have hsub : CReal.sub (CReal.add a (CReal.mul (constSeq (Nat.cast (k + r))) d))
      (CReal.add a (CReal.mul (constSeq (Nat.cast k)) d)) ≈
      CReal.sub
        (CReal.add (CReal.add a (CReal.mul (constSeq (Nat.cast k)) d))
          (CReal.mul (constSeq (Nat.cast r)) d))
        (CReal.add a (CReal.mul (constSeq (Nat.cast k)) d)) :=
    CReal.sub_respects_equiv _ _ _ _ hleft (Setoid.refl _)
  exact Setoid.trans hsub
    (add_sub_cancel_leftC (CReal.add a (CReal.mul (constSeq (Nat.cast k)) d))
      (CReal.mul (constSeq (Nat.cast r)) d))

/-- Closed-form grid distance for the recursive grid `bptRC`. -/
theorem bptRC_sub_generalC (a d : CReal) {k i : Nat} (hki : k ≤ i) :
    CReal.sub (bptRC a d i) (bptRC a d k) ≈
      CReal.mul (constSeq (Nat.cast (i - k))) d := by
  have htransport : CReal.sub (bptRC a d i) (bptRC a d k) ≈
      CReal.sub (bptC a d i) (bptC a d k) :=
    CReal.sub_respects_equiv _ _ _ _ (bptRC_equiv_bptC a d i) (bptRC_equiv_bptC a d k)
  exact Setoid.trans htransport (bptC_sub_generalC a d hki)

/-- Two-step lambda drops telescope. -/
theorem lemma33AlphaPrefix_telescopeC (lam : Nat → CReal) (k ell : Nat) :
    lemma33PrefixC (fun r => CReal.sub (lam (k + r)) (lam (k + r + 2))) ell ≈
      CReal.add (CReal.sub (lam k) (lam (k + ell)))
        (CReal.sub (lam (k + 1)) (lam (k + ell + 1))) := by
  induction ell with
  | zero =>
      rw [lemma33PrefixC_zero]
      have hq : mkQuot
          (CReal.add (CReal.sub (lam k) (lam (k + 0)))
            (CReal.sub (lam (k + 1)) (lam (k + 0 + 1)))) = mkQuot CReal.zero := by
        letI : CommRing CRealQuot :=
          cRealQuotCommRingConcreteWith cRatScalarMulArch
        change ((mkQuot (lam k)) - (mkQuot (lam (k + 0)))) +
            ((mkQuot (lam (k + 1))) - (mkQuot (lam (k + 0 + 1)))) = 0
        ring
      exact Setoid.symm (Quotient.exact hq)
  | succ ell ih =>
      rw [lemma33PrefixC_succ]
      have hstep1 : CReal.add
          (lemma33PrefixC (fun r => CReal.sub (lam (k + r)) (lam (k + r + 2))) ell)
          (CReal.sub (lam (k + ell)) (lam (k + ell + 2))) ≈
        CReal.add
          (CReal.add (CReal.sub (lam k) (lam (k + ell)))
            (CReal.sub (lam (k + 1)) (lam (k + ell + 1))))
          (CReal.sub (lam (k + ell)) (lam (k + ell + 2))) :=
        CReal.add_respects_equiv _ _ _ _ ih (Setoid.refl _)
      have hring : CReal.add
          (CReal.add (CReal.sub (lam k) (lam (k + ell)))
            (CReal.sub (lam (k + 1)) (lam (k + ell + 1))))
          (CReal.sub (lam (k + ell)) (lam (k + ell + 2))) ≈
        CReal.add (CReal.sub (lam k) (lam (k + ell + 1)))
          (CReal.sub (lam (k + 1)) (lam (k + ell + 2))) := by
        have hq : mkQuot (CReal.add
            (CReal.add (CReal.sub (lam k) (lam (k + ell)))
              (CReal.sub (lam (k + 1)) (lam (k + ell + 1))))
            (CReal.sub (lam (k + ell)) (lam (k + ell + 2)))) =
            mkQuot (CReal.add (CReal.sub (lam k) (lam (k + ell + 1)))
              (CReal.sub (lam (k + 1)) (lam (k + ell + 2)))) := by
          letI : CommRing CRealQuot :=
            cRealQuotCommRingConcreteWith cRatScalarMulArch
          change (((mkQuot (lam k)) - (mkQuot (lam (k + ell)))) +
              ((mkQuot (lam (k + 1))) - (mkQuot (lam (k + ell + 1))))) +
              ((mkQuot (lam (k + ell))) - (mkQuot (lam (k + ell + 2)))) =
              ((mkQuot (lam k)) - (mkQuot (lam (k + ell + 1)))) +
              ((mkQuot (lam (k + 1))) - (mkQuot (lam (k + ell + 2))))
          ring
        exact Quotient.exact hq
      have htarget : CReal.add (CReal.sub (lam k) (lam (k + (ell + 1))))
          (CReal.sub (lam (k + 1)) (lam (k + (ell + 1) + 1))) ≈
        CReal.add (CReal.sub (lam k) (lam (k + ell + 1)))
          (CReal.sub (lam (k + 1)) (lam (k + ell + 2))) := by
        have h1 : k + (ell + 1) = k + ell + 1 := by omega
        have h2 : k + ell + 1 + 1 = k + ell + 2 := by omega
        rw [h1, h2]
      exact Setoid.trans hstep1 (Setoid.trans hring (Setoid.symm htarget))

/-- A telescoped two-step alpha prefix is bounded by twice the profile diameter. -/
theorem lemma33AlphaPrefix_le_twoDiameterC (lam : Nat → CReal)
    (lamOne lamZero : CReal) (K k ell : Nat)
    (hupper : ∀ i : Nat, i ≤ K + 1 → RegularSeqLe (lam i) lamOne)
    (hlower : ∀ i : Nat, i ≤ K + 1 → RegularSeqLe lamZero (lam i))
    (hk : k ≤ K + 1) (hkell : k + ell ≤ K + 1)
    (hk1 : k + 1 ≤ K + 1) (hkell1 : k + ell + 1 ≤ K + 1) :
    RegularSeqLe
      (lemma33PrefixC (fun r => CReal.sub (lam (k + r)) (lam (k + r + 2))) ell)
      (CReal.add (CReal.sub lamOne lamZero) (CReal.sub lamOne lamZero)) := by
  let D : CReal := CReal.sub lamOne lamZero
  have htel := lemma33AlphaPrefix_telescopeC lam k ell
  have hgap1a : RegularSeqLe (CReal.sub (lam k) (lam (k + ell)))
      (CReal.sub lamOne (lam (k + ell))) :=
    subSeq_monotone_left_regularSeqLe _ _ _ (hupper k hk)
  have hgap1b : RegularSeqLe (CReal.sub lamOne (lam (k + ell))) D := by
    dsimp [D]
    exact regularSeqLe_subSeq_right _ (hlower (k + ell) hkell)
  have hgap1 : RegularSeqLe (CReal.sub (lam k) (lam (k + ell))) D :=
    regularSeqLe_trans hgap1a hgap1b
  have hgap2a : RegularSeqLe (CReal.sub (lam (k + 1)) (lam (k + ell + 1)))
      (CReal.sub lamOne (lam (k + ell + 1))) :=
    subSeq_monotone_left_regularSeqLe _ _ _ (hupper (k + 1) hk1)
  have hgap2b : RegularSeqLe (CReal.sub lamOne (lam (k + ell + 1))) D := by
    dsimp [D]
    exact regularSeqLe_subSeq_right _ (hlower (k + ell + 1) hkell1)
  have hgap2 : RegularSeqLe (CReal.sub (lam (k + 1)) (lam (k + ell + 1))) D :=
    regularSeqLe_trans hgap2a hgap2b
  have hsum : RegularSeqLe
      (CReal.add (CReal.sub (lam k) (lam (k + ell)))
        (CReal.sub (lam (k + 1)) (lam (k + ell + 1))))
      (CReal.add D D) := regularSeqLe_add hgap1 hgap2
  exact regularSeqLe_of_left_eventual htel (by simpa [D] using hsum)

#print axioms BishopSec3P.sub_self_equiv_zeroC
#print axioms BishopSec3P.natCast_succ_mulC
#print axioms BishopSec3P.lemma33Prefix_const_ltC
#print axioms BishopSec3P.bptC_sub_generalC
#print axioms BishopSec3P.bptRC_sub_generalC
#print axioms BishopSec3P.lemma33AlphaPrefix_telescopeC
#print axioms BishopSec3P.lemma33AlphaPrefix_le_twoDiameterC

/-- `x - x` is nonnegative, via `x - x ≈ 0`. -/
theorem regularSeqLe_zero_sub_selfC (x : CReal) :
    RegularSeqLe CReal.zero (CReal.sub x x) := by
  have hsub : CReal.sub x x ≈ CReal.add x (CReal.neg x) :=
    rel_to_relEventually _ _ (sub_eq_add_neg_raw x x)
  have hzero : CReal.add x (CReal.neg x) ≈ CReal.zero :=
    addSeq_neg_right_eventually x
  have h : CReal.sub x x ≈ CReal.zero := Setoid.trans hsub hzero
  exact regularSeqLe_of_right_eventual (Setoid.symm h)
    (regularSeqLe_refl CReal.zero)

/-- Monotonicity of subtraction in the right argument: `a ≤ b` implies
`c - b ≤ c - a`.

This is the CReal-native mirror of abstract `lemma33_sub_le_sub_left`. -/
theorem regularSeqLe_sub_leftC {a b c : CReal} (h : RegularSeqLe a b) :
    RegularSeqLe (CReal.sub c b) (CReal.sub c a) := by
  change RegularSeqNonneg (subSeq (CReal.sub c a) (CReal.sub c b))
  have hrel : relEventually (subSeq (CReal.sub c a) (CReal.sub c b)) (subSeq b a) := by
    have hq : mkQuot (subSeq (CReal.sub c a) (CReal.sub c b)) = mkQuot (subSeq b a) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      change ((mkQuot c) - (mkQuot a)) - ((mkQuot c) - (mkQuot b)) =
        (mkQuot b) - (mkQuot a)
      ring
    exact Quotient.exact hq
  exact regularSeqNonneg_of_eventual hrel h

/-- Telescope identity `(x - y) + (y - z) ≈ x - z`. -/
theorem sub_add_sub_cancelC (x y z : CReal) :
    CReal.add (CReal.sub x y) (CReal.sub y z) ≈ CReal.sub x z := by
  have hxy : CReal.sub x y ≈ CReal.add x (CReal.neg y) :=
    rel_to_relEventually _ _ (sub_eq_add_neg_raw x y)
  have hyz : CReal.sub y z ≈ CReal.add y (CReal.neg z) :=
    rel_to_relEventually _ _ (sub_eq_add_neg_raw y z)
  have hxz : CReal.sub x z ≈ CReal.add x (CReal.neg z) :=
    rel_to_relEventually _ _ (sub_eq_add_neg_raw x z)
  have h1 : CReal.add (CReal.sub x y) (CReal.sub y z)
      ≈ CReal.add (CReal.add x (CReal.neg y)) (CReal.add y (CReal.neg z)) :=
    CReal.add_respects_equiv _ _ _ _ hxy hyz
  have h2 : CReal.add (CReal.add x (CReal.neg y)) (CReal.add y (CReal.neg z))
      ≈ CReal.add x (CReal.add (CReal.neg y) (CReal.add y (CReal.neg z))) :=
    CReal.add_assoc x (CReal.neg y) (CReal.add y (CReal.neg z))
  have h3 : CReal.add (CReal.neg y) (CReal.add y (CReal.neg z))
      ≈ CReal.add (CReal.add (CReal.neg y) y) (CReal.neg z) :=
    Setoid.symm (CReal.add_assoc (CReal.neg y) y (CReal.neg z))
  have h4 : CReal.add (CReal.add (CReal.neg y) y) (CReal.neg z)
      ≈ CReal.add CReal.zero (CReal.neg z) :=
    CReal.add_respects_equiv _ _ _ _ (addSeq_neg_left_eventually y) (Setoid.refl _)
  have h5 : CReal.add CReal.zero (CReal.neg z) ≈ CReal.neg z :=
    CReal.zero_add (CReal.neg z)
  have hinner : CReal.add (CReal.neg y) (CReal.add y (CReal.neg z))
      ≈ CReal.neg z := Setoid.trans h3 (Setoid.trans h4 h5)
  have h6 : CReal.add x (CReal.add (CReal.neg y) (CReal.add y (CReal.neg z)))
      ≈ CReal.add x (CReal.neg z) :=
    CReal.add_respects_equiv _ _ _ _ (Setoid.refl x) hinner
  exact Setoid.trans h1 (Setoid.trans h2 (Setoid.trans h6 (Setoid.symm hxz)))

/-- Cursor used in the beta-charge telescope.

After a big interval we jump to `s r + 1`; otherwise we stay at `s r`.
-/
noncomputable def cursorC (K : Nat) (cls : Nat → Bool) : Nat → Nat :=
  fun r => if hr : r = 0 then 0
    else if BintC K cls (r - 1) then sC K cls r + 1 else sC K cls r

/-- Cursor starts at zero. -/
theorem hcursor_zeroC (K : Nat) (cls : Nat → Bool) :
    cursorC K cls 0 = 0 := by
  rfl

/-- Cursor after a big interval. -/
theorem hcursor_succ_BC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hBj : BintC K cls j) :
    cursorC K cls (j + 1) = sC K cls (j + 1) + 1 := by
  dsimp [cursorC]
  rw [if_pos hBj]

/-- Cursor after a non-big interval. -/
theorem hcursor_succ_notB_C (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hBj : ¬ BintC K cls j) :
    cursorC K cls (j + 1) = sC K cls (j + 1) := by
  dsimp [cursorC]
  rw [if_neg hBj]

/-- Immediately before a big interval, the cursor is exactly `s j`. -/
theorem hcursor_before_BC (K : Nat) (cls : Nat → Bool)
    (j : Nat) (hjN : j < N_C K cls) (hBj : BintC K cls j) :
    cursorC K cls j = sC K cls j := by
  by_cases hj0 : j = 0
  · subst j
    rw [hcursor_zeroC, hs_zeroC]
  · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
    by_cases hprev : BintC K cls (j - 1)
    · have hnc := hB_not_consecutiveC K cls (j - 1) (by omega) hprev
      have hji : j - 1 + 1 = j := Nat.sub_add_cancel hjPos
      exact (hnc (by rw [hji]; exact hBj)).elim
    · dsimp [cursorC]
      rw [if_neg hj0, if_neg hprev]

/-- If interval `j` is not big, the cursor bound can be advanced to `s(j+1)`.

This is the local monotonicity bridge used by the prefix induction. -/
theorem hcursor_after_smallC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBj : ¬ BintC (2 ^ e) cls j) :
    RegularSeqLe
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (cursorC (2 ^ e) cls j)))
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls (j + 1)))) := by
  by_cases hj0 : j = 0
  · subst j
    rw [hcursor_zeroC]
    have hle : RegularSeqLe
        (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls 1))
        (lamC P hd_nn hd_pos e hdeq 0) :=
      hlamC_anti P hd_nn hd_pos e hdeq 0 (sC (2 ^ e) cls 1)
        (Nat.zero_le _) (by have := hs_le_KC (2 ^ e) cls 1; omega)
    exact regularSeqLe_sub_leftC hle
  · by_cases hprev : BintC (2 ^ e) cls (j - 1)
    · have hjm1N : j - 1 + 1 < N_C (2 ^ e) cls := by omega
      have hSmallEnd : cls (sC (2 ^ e) cls ((j - 1) + 2)) = true :=
        hafter_big_smallC (2 ^ e) cls (j - 1) hjm1N hprev
      have hsimm : sC (2 ^ e) cls (j + 1) = sC (2 ^ e) cls j + 1 := by
        apply hs_prev_of_smallC (2 ^ e) cls j hjN
        have hidx : (j - 1) + 2 = j + 1 := by omega
        rwa [hidx] at hSmallEnd
      have hc : cursorC (2 ^ e) cls j = sC (2 ^ e) cls j + 1 := by
        have hj1 : (j - 1) + 1 = j := by omega
        have hcs := hcursor_succ_BC (2 ^ e) cls (j - 1) hprev
        rwa [hj1] at hcs
      rw [hc, hsimm]
      exact regularSeqLe_refl _
    · have hc : cursorC (2 ^ e) cls j = sC (2 ^ e) cls j := by
        dsimp [cursorC]
        rw [if_neg hj0, if_neg hprev]
      rw [hc]
      have hle : RegularSeqLe
          (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls (j + 1)))
          (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls j)) :=
        hlamC_anti P hd_nn hd_pos e hdeq
          (sC (2 ^ e) cls j) (sC (2 ^ e) cls (j + 1))
          (Nat.le_of_lt (hs_strictC (2 ^ e) cls j hjN))
          (by have := hs_le_KC (2 ^ e) cls (j + 1); omega)
      exact regularSeqLe_sub_leftC hle

/-- Prefix/telescope estimate for the beta-charge sequence. -/
theorem hcharge_prefixC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (r : Nat) (hrN : r ≤ N_C (2 ^ e) cls) :
    RegularSeqLe
      (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls) r)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (cursorC (2 ^ e) cls r))) := by
  induction r with
  | zero =>
      rw [lemma33PrefixC_zero, hcursor_zeroC]
      exact regularSeqLe_zero_sub_selfC (lamC P hd_nn hd_pos e hdeq 0)
  | succ j ih =>
      have hjN : j < N_C (2 ^ e) cls := by omega
      have hpre := ih (Nat.le_of_lt hjN)
      by_cases hBj : BintC (2 ^ e) cls j
      · have hcBefore := hcursor_before_BC (2 ^ e) cls j hjN hBj
        have hcAfter := hcursor_succ_BC (2 ^ e) cls j hBj
        have hch := hcharge_of_BC P hd_nn hd_pos e hdeq cls j hBj
        rw [lemma33PrefixC_succ, hch, hcAfter]
        rw [hcBefore] at hpre
        have hstep : RegularSeqLe
            (CReal.add (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls) j)
              (betaC P hd_nn hd_pos e hdeq cls j))
            (CReal.add
              (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
                (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls j)))
              (betaC P hd_nn hd_pos e hdeq cls j)) :=
          regularSeqLe_add hpre (regularSeqLe_refl _)
        have htel : CReal.add
              (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
                (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls j)))
              (betaC P hd_nn hd_pos e hdeq cls j)
            ≈ CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
                (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls (j + 1) + 1)) := by
          dsimp [betaC]
          exact sub_add_sub_cancelC
            (lamC P hd_nn hd_pos e hdeq 0)
            (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls j))
            (lamC P hd_nn hd_pos e hdeq (sC (2 ^ e) cls (j + 1) + 1))
        exact regularSeqLe_of_right_eventual htel hstep
      · have hcAfter := hcursor_succ_notB_C (2 ^ e) cls j hBj
        have hch := hcharge_of_notB_C P hd_nn hd_pos e hdeq cls j hBj
        rw [lemma33PrefixC_succ, hch, hcAfter]
        have hpre0 : RegularSeqLe
            (CReal.add (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls) j) CReal.zero)
            (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
              (lamC P hd_nn hd_pos e hdeq (cursorC (2 ^ e) cls j))) :=
          regularSeqLe_of_left_eventual
            (CReal.add_zero (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls) j)) hpre
        exact regularSeqLe_trans hpre0
          (hcursor_after_smallC P hd_nn hd_pos e hdeq cls j hjN hBj)

/-- Final cursor is bounded by the final lambda index `K+1`. -/
theorem hcursorN_leC (K : Nat) (cls : Nat → Bool) :
    cursorC K cls (N_C K cls) ≤ K + 1 := by
  by_cases hNz : N_C K cls = 0
  · rw [hNz, hcursor_zeroC]
    omega
  · by_cases hlastB : BintC K cls (N_C K cls - 1)
    · have hc : cursorC K cls (N_C K cls) = sC K cls (N_C K cls) + 1 := by
        have hNm : N_C K cls - 1 + 1 = N_C K cls := by omega
        have hcs := hcursor_succ_BC K cls (N_C K cls - 1) hlastB
        rwa [hNm] at hcs
      rw [hc, hs_NC]
    · have hc : cursorC K cls (N_C K cls) = sC K cls (N_C K cls) := by
        dsimp [cursorC]
        rw [if_neg hNz, if_neg hlastB]
      rw [hc, hs_NC]
      omega

/-- Total beta charge is bounded by the total lambda diameter. -/
theorem hcharge_totalC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) :
    RegularSeqLe
      (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls) (N_C (2 ^ e) cls))
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  have hpref := hcharge_prefixC P hd_nn hd_pos e hdeq cls
    (N_C (2 ^ e) cls) (Nat.le_refl _)
  have hcursorBnd := hcursorN_leC (2 ^ e) cls
  have hlowerCursor : RegularSeqLe
      (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))
      (lamC P hd_nn hd_pos e hdeq (cursorC (2 ^ e) cls (N_C (2 ^ e) cls))) :=
    hlamC_anti P hd_nn hd_pos e hdeq
      (cursorC (2 ^ e) cls (N_C (2 ^ e) cls)) (2 ^ e + 1)
      hcursorBnd (Nat.le_refl _)
  have htail : RegularSeqLe
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (cursorC (2 ^ e) cls (N_C (2 ^ e) cls))))
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) :=
    regularSeqLe_sub_leftC hlowerCursor
  exact regularSeqLe_trans hpref htail




/-! ### §3 core: integer allocation skeleton

Imported from `Mathdemo.ScratchAllocSkeleton`, which built successfully before
BSP integration.  This block provides the Nat allocation prefix, raw allocation
`mrawC`, shifted final allocation `MC`, and the pure Nat sum accounting.
-/

def lemma33PrefixNatC (u : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lemma33PrefixNatC u n + u n

@[simp] theorem lemma33PrefixNatC_zero (u : Nat → Nat) :
    lemma33PrefixNatC u 0 = 0 := rfl

@[simp] theorem lemma33PrefixNatC_succ (u : Nat → Nat) (n : Nat) :
    lemma33PrefixNatC u (n + 1) = lemma33PrefixNatC u n + u n := rfl

/-- Updating the zero-th term by adding `r` adds `r` to every nonempty prefix. -/
theorem lemma33PrefixNatC_update_zero (u : Nat → Nat) (r N : Nat) (hN : 0 < N) :
    lemma33PrefixNatC (fun j => if j = 0 then u j + r else u j) N =
      lemma33PrefixNatC u N + r := by
  cases N with
  | zero => cases hN
  | succ N =>
      induction N with
      | zero =>
          simp [lemma33PrefixNatC, Nat.add_assoc]
      | succ N ih =>
          calc
            lemma33PrefixNatC (fun j => if j = 0 then u j + r else u j) (N + 1 + 1)
                = lemma33PrefixNatC (fun j => if j = 0 then u j + r else u j) (N + 1)
                    + (if N + 1 = 0 then u (N + 1) + r else u (N + 1)) := by
                  rfl
            _ = (lemma33PrefixNatC u (N + 1) + r) + u (N + 1) := by
                  rw [ih (Nat.succ_pos N)]
                  have hNz : N + 1 ≠ 0 := by omega
                  rw [if_neg hNz]
            _ = (lemma33PrefixNatC u (N + 1) + u (N + 1)) + r := by
                  omega
            _ = lemma33PrefixNatC u (N + 1 + 1) + r := by
                  rfl

/-- Raw interval allocation.  Small retained endpoints receive zero; big
endpoints receive the externally supplied approximate floor `afloor j`. -/
noncomputable def mrawC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat) :
    Nat → Nat :=
  fun j =>
    if hj : j < N_C K cls then
      if hSmallEnd : cls (sC K cls (j + 1)) = true then 0 else afloor j
    else 0

/-- Raw allocation is zero on a small retained right endpoint. -/
theorem hmraw_smallC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat)
    (j : Nat) (hjN : j < N_C K cls)
    (hSmallEnd : cls (sC K cls (j + 1)) = true) :
    mrawC K cls afloor j = 0 := by
  dsimp [mrawC]
  rw [if_pos hjN, if_pos hSmallEnd]

/-- Raw allocation is the floor value on a big retained right endpoint. -/
theorem hmraw_bigC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat)
    (j : Nat) (hjN : j < N_C K cls)
    (hBigEnd : cls (sC K cls (j + 1)) = false) :
    mrawC K cls afloor j = afloor j := by
  have hnotSmall : ¬ cls (sC K cls (j + 1)) = true := by
    intro hsmall
    rw [hBigEnd] at hsmall
    exact Bool.noConfusion hsmall
  dsimp [mrawC]
  rw [if_pos hjN, if_neg hnotSmall]

/-- Total raw allocated mass before the final remainder adjustment. -/
noncomputable def mSumC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat) : Nat :=
  lemma33PrefixNatC (mrawC K cls afloor) (N_C K cls)

/-- Final shifted allocation.  The leftover `n - mSum` is absorbed at index 1;
subsequent intervals use the previous raw allocation. -/
noncomputable def MC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat) (n : Nat) :
    Nat → Nat :=
  fun t => if t = 1 then mrawC K cls afloor 0 + (n - mSumC K cls afloor)
    else mrawC K cls afloor (t - 1)

/-- Shift identity for the final allocation. -/
theorem hM_shiftC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat)
    (n j : Nat) :
    MC K cls afloor n (j + 1) =
      if j = 0 then mrawC K cls afloor j + (n - mSumC K cls afloor)
      else mrawC K cls afloor j := by
  by_cases hj0 : j = 0
  · subst j
    rfl
  · have hj1 : j + 1 ≠ 1 := by omega
    dsimp [MC]
    rw [if_neg hj1, if_neg hj0]

/-- The final allocation dominates the raw allocation intervalwise. -/
theorem hM_geC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat)
    (n j : Nat) :
    mrawC K cls afloor j ≤ MC K cls afloor n (j + 1) := by
  rw [hM_shiftC]
  split
  · omega
  · exact Nat.le_refl _

/-- Prefix form of the final allocation sum. -/
theorem hsum_MC_prefixC (K : Nat) (cls : Nat → Bool) (afloor : Nat → Nat)
    (n : Nat) (hNpos : 0 < N_C K cls) (hmSum_le : mSumC K cls afloor ≤ n) :
    lemma33PrefixNatC (fun j => MC K cls afloor n (j + 1)) (N_C K cls) = n := by
  have hfun : (fun j => MC K cls afloor n (j + 1)) =
      (fun j => if j = 0 then
          mrawC K cls afloor j + (n - mSumC K cls afloor)
        else mrawC K cls afloor j) := by
    funext j
    exact hM_shiftC K cls afloor n j
  rw [hfun]
  have hupdate := lemma33PrefixNatC_update_zero
    (mrawC K cls afloor) (n - mSumC K cls afloor) (N_C K cls) hNpos
  rw [hupdate]
  dsimp [mSumC]
  exact Nat.add_sub_of_le hmSum_le

/-- Bridge from raw `p'` bounds to final `M` bounds.

The monotonicity of the numeric bound is supplied as an argument.  This keeps
this brick purely about allocation accounting; the next brick can discharge
`hbound_mono` from `hM_geC`, Nat-cast monotonicity, and nonnegativity of `eps`. -/
noncomputable def hp_final_from_rawC {a b d eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (afloor : Nat → Nat) (n : Nat)
    (hraw : ∀ j : Nat, j < N_C (2 ^ e) cls →
      P.p_prime_ltC
        (bptRC a d (sC (2 ^ e) cls j))
        (bptRC a d (sC (2 ^ e) cls (j + 1)))
        (CReal.mul (constSeq (Nat.cast (mrawC (2 ^ e) cls afloor j + 1))) eps))
    (hbound_mono : ∀ j : Nat,
      RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (mrawC (2 ^ e) cls afloor j + 1))) eps)
        (CReal.mul (constSeq (Nat.cast (MC (2 ^ e) cls afloor n (j + 1) + 1))) eps))
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    P.p_prime_ltC
      (bptRC a d (sC (2 ^ e) cls j))
      (bptRC a d (sC (2 ^ e) cls (j + 1)))
      (CReal.mul (constSeq (Nat.cast (MC (2 ^ e) cls afloor n (j + 1) + 1))) eps) :=
  ProfileC.p_prime_ltC_mono P (hraw j hjN) (hbound_mono j)




/-! ### §3 core: approximate floor interface

Imported from `Mathdemo.ScratchFloorInterface`, which built successfully before
BSP integration.  This block introduces the local approximate-floor data
interface and proves that it feeds through `afloorC`, `mrawC`, and `chargeC`.
-/

structure Lemma33H4ApproxFloorC (theta eps beta : CReal) (cap : Nat) where
  val : Nat
  val_le : val ≤ cap
  lower : RegularSeqLe (CReal.mul (constSeq (Nat.cast val)) theta) beta
  lower_strict : 0 < val →
    regularSeqLtProp (CReal.mul (constSeq (Nat.cast val)) theta) beta
  upper : regularSeqLtProp beta
    (CReal.mul (constSeq (Nat.cast (val + 1))) eps)

/-- The zero Nat coefficient gives a left-hand side equivalent to `0`, hence
it is `≤ 0`.  This is used when a retained endpoint is small and `mraw = 0`. -/
theorem natCast_zero_mul_le_zeroC (theta : CReal) :
    RegularSeqLe (CReal.mul (constSeq (Nat.cast 0)) theta) CReal.zero := by
  have h0 : constSeq (Nat.cast 0) ≈ CReal.zero := constSeq_natCast_zeroC
  have hmul : CReal.mul (constSeq (Nat.cast 0)) theta ≈ CReal.mul CReal.zero theta :=
    CReal.mul_respects_equiv _ _ _ _ h0 (Setoid.refl theta)
  have hzero : CReal.mul CReal.zero theta ≈ CReal.zero := zero_mul_equivC theta
  exact regularSeqLe_of_left_eventual (Setoid.trans hmul hzero)
    (regularSeqLe_refl CReal.zero)

-- The dependent result type contains CReal multiplication and Nat casts; the
-- default heartbeat budget times out during induction elaboration although the
-- produced proof is still hardness-4.
set_option maxHeartbeats 800000 in
/-- CReal-native approximate floor producer, mirroring abstract
`lemma33H4_approxFloor`.  The recursion descends from the supplied cap; the
only data-valued branch is cotransitivity for
`(cap+1) * theta < (cap+1) * eps`. -/
noncomputable def lemma33H4ApproxFloorC_construct (theta eps beta : CReal)
    (htheta_eps : regularSeqLtProp theta eps)
    (hbeta_nn : RegularSeqNonneg beta)
    (cap : Nat)
    (hupper : regularSeqLtProp beta
      (CReal.mul (constSeq (Nat.cast (cap + 1))) eps)) :
    Lemma33H4ApproxFloorC theta eps beta cap := by
  induction cap with
  | zero =>
      refine {
        val := 0,
        val_le := Nat.le_refl 0,
        lower := ?_,
        lower_strict := ?_,
        upper := hupper }
      · exact regularSeqLe_trans (natCast_zero_mul_le_zeroC theta)
          (regularSeqLe_zero_of_nonneg hbeta_nn)
      · intro hbad
        exfalso
        omega
  | succ cap ih =>
      let c : CReal := constSeq (Nat.cast (cap + 1))
      have hc_nat : regularSeqLtProp (constSeq (Nat.cast 0)) c := by
        dsimp [c]
        exact natCast_ltC 0 (cap + 1) (Nat.succ_pos cap)
      have hc : regularSeqLtProp CReal.zero c := by
        exact regularSeqLtProp_of_left_eventual
          (relEventually_symm _ _ constSeq_natCast_zeroC) hc_nat
      have hgap_prop :
          regularSeqLtProp (CReal.mul c theta) (CReal.mul c eps) :=
        mul_lt_mul_of_pos_leftC htheta_eps hc
      have hgap_data :
          regularSeqLtData (CReal.mul c theta) (CReal.mul c eps) := by
        show PosEventuallyData (subSeq (CReal.mul c eps) (CReal.mul c theta))
        exact posEventuallyData_of_strongGaugeC
          (strongGaugeC (posEventually_to_strongC hgap_prop))
      cases regularSeqLtData_cotrans
          (CReal.mul c theta) (CReal.mul c eps) beta hgap_data with
      | inl hbig =>
          refine {
            val := cap + 1,
            val_le := Nat.le_refl (cap + 1),
            lower := ?_,
            lower_strict := ?_,
            upper := hupper }
          · exact regularSeqLe_of_ltPropC hbig.toProp
          · intro _
            exact hbig.toProp
      | inr hsmall =>
          let r := ih hsmall.toProp
          refine {
            val := r.val,
            val_le := Nat.le_trans r.val_le (Nat.le_succ cap),
            lower := r.lower,
            lower_strict := r.lower_strict,
            upper := r.upper }

/-- Construct all local approximate-floor data from a total lambda budget. -/
noncomputable def lemma33ApproxFloorDataC_construct {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (htheta_eps : regularSeqLtProp theta eps)
    (htotal_lt : regularSeqLtProp
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n := by
  intro j hjN
  exact lemma33H4ApproxFloorC_construct theta eps
    (betaC P hd_nn hd_pos e hdeq cls j)
    htheta_eps
    (hbeta_nnC P hd_nn hd_pos e hdeq cls j hjN)
    n
    (regularSeqLtProp_of_le_of_lt
      (hbeta_totalC P hd_nn hd_pos e hdeq cls j hjN)
      htotal_lt)

/-- The floor function extracted from local floor data.  Outside the retained
range it is harmlessly set to zero. -/
noncomputable def afloorC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Nat → Nat :=
  fun j => if hj : j < N_C (2 ^ e) cls then (afloorData j hj).val else 0

/-- Extracted floor values are bounded by the global cap `n`. -/
theorem hafloor_leC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData j ≤ n := by
  dsimp [afloorC]
  rw [dif_pos hjN]
  exact (afloorData j hjN).val_le

/-- Upper bracket for the extracted floor. -/
theorem hafloor_upperC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    regularSeqLtProp (betaC P hd_nn hd_pos e hdeq cls j)
      (CReal.mul
        (constSeq (Nat.cast
          (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData j + 1))) eps) := by
  dsimp [afloorC]
  rw [dif_pos hjN]
  exact (afloorData j hjN).upper

/-- Lower bracket for the extracted floor. -/
theorem hafloor_lowerC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData j))) theta)
      (betaC P hd_nn hd_pos e hdeq cls j) := by
  dsimp [afloorC]
  rw [dif_pos hjN]
  exact (afloorData j hjN).lower

/-- Strict lower bracket when the extracted floor value is positive. -/
theorem hafloor_lower_strictC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hpos : 0 < afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData j) :
    regularSeqLtProp
      (CReal.mul
        (constSeq (Nat.cast
          (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData j))) theta)
      (betaC P hd_nn hd_pos e hdeq cls j) := by
  dsimp [afloorC] at hpos ⊢
  rw [dif_pos hjN] at hpos ⊢
  exact (afloorData j hjN).lower_strict hpos

/-- Upper beta bracket after pushing the floor through `mrawC`. -/
theorem hmraw_upperC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBigEnd : cls (sC (2 ^ e) cls (j + 1)) = false) :
    regularSeqLtProp (betaC P hd_nn hd_pos e hdeq cls j)
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j + 1))) eps) := by
  rw [hmraw_bigC (2 ^ e) cls
    (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j hjN hBigEnd]
  exact hafloor_upperC P hd_nn hd_pos e hdeq cls theta eps n afloorData j hjN

/-- Lower theta bracket after pushing the floor through `mrawC` on a big endpoint. -/
theorem hmraw_lower_big_thetaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBigEnd : cls (sC (2 ^ e) cls (j + 1)) = false) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j))) theta)
      (betaC P hd_nn hd_pos e hdeq cls j) := by
  rw [hmraw_bigC (2 ^ e) cls
    (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j hjN hBigEnd]
  exact hafloor_lowerC P hd_nn hd_pos e hdeq cls theta eps n afloorData j hjN

/-- Strict lower theta bracket for positive raw allocation on a big endpoint. -/
theorem hmraw_lower_strict_big_thetaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBigEnd : cls (sC (2 ^ e) cls (j + 1)) = false)
    (hpos : 0 < mrawC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j) :
    regularSeqLtProp
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j))) theta)
      (betaC P hd_nn hd_pos e hdeq cls j) := by
  rw [hmraw_bigC (2 ^ e) cls
    (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j hjN hBigEnd] at hpos ⊢
  exact hafloor_lower_strictC P hd_nn hd_pos e hdeq cls theta eps n afloorData j hjN hpos

/-- Raw theta allocation is bounded by the interval charge. -/
theorem hmraw_charge_thetaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j))) theta)
      (chargeC P hd_nn hd_pos e hdeq cls j) := by
  cases hEnd : cls (sC (2 ^ e) cls (j + 1)) with
  | true =>
      have hm := hmraw_smallC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j hjN hEnd
      have hnotB : ¬ BintC (2 ^ e) cls j := by
        intro hBint
        have h2 : cls (sC (2 ^ e) cls (j + 1)) = false := hBint.2
        rw [hEnd] at h2
        exact Bool.noConfusion h2
      rw [hm, hcharge_of_notB_C P hd_nn hd_pos e hdeq cls j hnotB]
      exact natCast_zero_mul_le_zeroC theta
  | false =>
      have hBint : BintC (2 ^ e) cls j := ⟨hjN, hEnd⟩
      rw [hcharge_of_BC P hd_nn hd_pos e hdeq cls j hBint]
      exact hmraw_lower_big_thetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData j hjN hEnd

/-- If the raw allocation is positive, the raw theta allocation is strictly
below the interval charge. -/
theorem hmraw_charge_strict_thetaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hpos : 0 < mrawC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j) :
    regularSeqLtProp
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j))) theta)
      (chargeC P hd_nn hd_pos e hdeq cls j) := by
  cases hEnd : cls (sC (2 ^ e) cls (j + 1)) with
  | true =>
      have hm := hmraw_smallC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j hjN hEnd
      rw [hm] at hpos
      exfalso
      omega
  | false =>
      have hBint : BintC (2 ^ e) cls j := ⟨hjN, hEnd⟩
      rw [hcharge_of_BC P hd_nn hd_pos e hdeq cls j hBint]
      exact hmraw_lower_strict_big_thetaC P hd_nn hd_pos e hdeq cls theta eps n
        afloorData j hjN hEnd hpos




/-! ### §3 core: raw theta prefix bound

Imported from `Mathdemo.ScratchRawPrefixBound`, which built successfully before
BSP integration.  This block lifts intervalwise raw theta-charge estimates to
a CReal prefix bound and connects it to `hcharge_totalC`.
-/

theorem lemma33PrefixC_mono (x y : Nat → CReal) (n : Nat)
    (hxy : ∀ j : Nat, j < n → RegularSeqLe (x j) (y j)) :
    RegularSeqLe (lemma33PrefixC x n) (lemma33PrefixC y n) := by
  induction n with
  | zero =>
      rw [lemma33PrefixC_zero, lemma33PrefixC_zero]
      exact regularSeqLe_refl CReal.zero
  | succ n ih =>
      rw [lemma33PrefixC_succ, lemma33PrefixC_succ]
      have hpref :
          RegularSeqLe (lemma33PrefixC x n) (lemma33PrefixC y n) :=
        ih (by
          intro j hj
          exact hxy j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      have hterm : RegularSeqLe (x n) (y n) := hxy n (Nat.lt_succ_self n)
      exact regularSeqLe_add hpref hterm

/-- Raw theta term associated to the raw allocation. -/
noncomputable def rawThetaTermC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Nat → CReal :=
  fun j =>
    CReal.mul
      (constSeq (Nat.cast
        (mrawC (2 ^ e) cls
          (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j)))
      theta

/-- Intervalwise raw theta-charge, lifted to a prefix inequality. -/
theorem hmraw_charge_prefix_thetaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) :
    RegularSeqLe
      (lemma33PrefixC
        (rawThetaTermC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        (N_C (2 ^ e) cls))
      (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls)
        (N_C (2 ^ e) cls)) := by
  refine lemma33PrefixC_mono
    (rawThetaTermC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
    (chargeC P hd_nn hd_pos e hdeq cls)
    (N_C (2 ^ e) cls) ?_
  intro j hjN
  dsimp [rawThetaTermC]
  exact hmraw_charge_thetaC P hd_nn hd_pos e hdeq cls theta eps n
    afloorData j hjN

/-- Raw theta prefix is bounded by the total lambda diameter. -/
theorem hmraw_charge_prefix_totalC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) :
    RegularSeqLe
      (lemma33PrefixC
        (rawThetaTermC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        (N_C (2 ^ e) cls))
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  exact regularSeqLe_trans
    (hmraw_charge_prefix_thetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
    (hcharge_totalC P hd_nn hd_pos e hdeq cls)




/-! ### §3 core: mSum / theta bridge interface

Imported from `Mathdemo.ScratchMSumThetaBridge`, which built successfully before
BSP integration.  This block names the raw-theta prefix and the scaled raw
allocation, packages their equivalence as `MSumThetaBridgeC`, and derives the
scaled raw allocation bound from that bridge.
-/

noncomputable def rawThetaPrefixC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : CReal :=
  lemma33PrefixC
    (rawThetaTermC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
    (N_C (2 ^ e) cls)

/-- The CReal expression `(mSumC ... : CReal) * theta`. -/
noncomputable def mSumThetaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : CReal :=
  CReal.mul
    (constSeq (Nat.cast
      (mSumC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData))))
    theta

/-- Bridge asserting that the CReal prefix of raw theta terms is the same
CReal number as `(mSumC ... : CReal) * theta`.

The next brick should construct this bridge by induction on the prefix and
Nat-cast algebra. -/
structure MSumThetaBridgeC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Prop where
  equiv_prefix :
    rawThetaPrefixC P hd_nn hd_pos e hdeq cls theta eps n afloorData ≈
      mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData

/-- The raw total allocation, scaled by `theta`, is bounded by the total
lambda diameter, provided the Nat/CReal prefix bridge is available. -/
theorem hmSum_scale_thetaC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (bridge : MSumThetaBridgeC P hd_nn hd_pos e hdeq cls theta eps n afloorData) :
    RegularSeqLe
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  have htot : RegularSeqLe
      (rawThetaPrefixC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
    dsimp [rawThetaPrefixC]
    exact hmraw_charge_prefix_totalC P hd_nn hd_pos e hdeq cls theta eps n afloorData
  exact regularSeqLe_of_left_eventual (Setoid.symm bridge.equiv_prefix) htot

/-- Same bound with `mSumThetaC` unfolded. -/
theorem hmSum_scale_theta_unfoldC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (bridge : MSumThetaBridgeC P hd_nn hd_pos e hdeq cls theta eps n afloorData) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mSumC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData))))
        theta)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  simpa [mSumThetaC] using
    hmSum_scale_thetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData bridge




/-! ### §3 core: mSum / theta bridge construction

Imported from `Mathdemo.ScratchMSumThetaConstruct`, which built successfully
before BSP integration.  This block constructs the Nat/CReal prefix bridge and
removes the bridge parameter from the scaled raw allocation bound.
-/

theorem natCast_zero_mul_equiv_zeroC (theta : CReal) :
    CReal.mul (constSeq (Nat.cast 0)) theta ≈ CReal.zero := by
  have h0 : constSeq (Nat.cast 0) ≈ CReal.zero := constSeq_natCast_zeroC
  have hmul : CReal.mul (constSeq (Nat.cast 0)) theta ≈
      CReal.mul CReal.zero theta :=
    CReal.mul_respects_equiv _ _ _ _ h0 (Setoid.refl theta)
  exact Setoid.trans hmul (zero_mul_equivC theta)

/-- One step of Nat-cast scalar addition under multiplication by `theta`. -/
theorem rawThetaStep_equivC (m n : Nat) (theta : CReal) :
    CReal.add
      (CReal.mul (constSeq (Nat.cast m)) theta)
      (CReal.mul (constSeq (Nat.cast n)) theta) ≈
    CReal.mul (constSeq (Nat.cast (m + n))) theta := by
  have hconst : constSeq (Nat.cast (m + n)) ≈
      CReal.add (constSeq (Nat.cast m)) (constSeq (Nat.cast n)) :=
    constSeq_natCast_addC m n
  have hmul : CReal.mul (constSeq (Nat.cast (m + n))) theta ≈
      CReal.mul
        (CReal.add (constSeq (Nat.cast m)) (constSeq (Nat.cast n))) theta :=
    CReal.mul_respects_equiv _ _ _ _ hconst (Setoid.refl theta)
  have hdist : CReal.mul
        (CReal.add (constSeq (Nat.cast m)) (constSeq (Nat.cast n))) theta ≈
      CReal.add
        (CReal.mul (constSeq (Nat.cast m)) theta)
        (CReal.mul (constSeq (Nat.cast n)) theta) :=
    CReal.right_distrib (constSeq (Nat.cast m)) (constSeq (Nat.cast n)) theta
  exact Setoid.symm (Setoid.trans hmul hdist)

/-- The CReal prefix of raw theta terms is equivalent to the Nat prefix,
cast to CReal and multiplied by `theta`. -/
theorem lemma33PrefixC_rawTheta_equiv_natC (u : Nat → Nat) (theta : CReal)
    (N : Nat) :
    lemma33PrefixC
      (fun j => CReal.mul (constSeq (Nat.cast (u j))) theta) N ≈
    CReal.mul (constSeq (Nat.cast (lemma33PrefixNatC u N))) theta := by
  induction N with
  | zero =>
      rw [lemma33PrefixC_zero, lemma33PrefixNatC_zero]
      exact Setoid.symm (natCast_zero_mul_equiv_zeroC theta)
  | succ N ih =>
      rw [lemma33PrefixC_succ, lemma33PrefixNatC_succ]
      have hprefix :
          CReal.add
            (lemma33PrefixC
              (fun j => CReal.mul (constSeq (Nat.cast (u j))) theta) N)
            (CReal.mul (constSeq (Nat.cast (u N))) theta) ≈
          CReal.add
            (CReal.mul (constSeq (Nat.cast (lemma33PrefixNatC u N))) theta)
            (CReal.mul (constSeq (Nat.cast (u N))) theta) :=
        CReal.add_respects_equiv _ _ _ _ ih (Setoid.refl _)
      have hstep :
          CReal.add
            (CReal.mul (constSeq (Nat.cast (lemma33PrefixNatC u N))) theta)
            (CReal.mul (constSeq (Nat.cast (u N))) theta) ≈
          CReal.mul
            (constSeq (Nat.cast (lemma33PrefixNatC u N + u N))) theta :=
        rawThetaStep_equivC (lemma33PrefixNatC u N) (u N) theta
      exact Setoid.trans hprefix hstep

/-- Construction of the bridge introduced in `ScratchMSumThetaBridge`. -/
theorem mSumThetaBridge_of_prefixC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) :
    MSumThetaBridgeC P hd_nn hd_pos e hdeq cls theta eps n afloorData := by
  constructor
  dsimp [rawThetaPrefixC, mSumThetaC, rawThetaTermC, mSumC]
  exact lemma33PrefixC_rawTheta_equiv_natC
    (mrawC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData))
    theta
    (N_C (2 ^ e) cls)

/-- Scaled raw allocation bound, with the prefix bridge constructed internally. -/
theorem hmSum_scale_theta_constructedC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) :
    RegularSeqLe
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  exact hmSum_scale_thetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData
    (mSumThetaBridge_of_prefixC P hd_nn hd_pos e hdeq cls theta eps n afloorData)

/-- Same bound with `mSumThetaC` unfolded. -/
theorem hmSum_scale_theta_constructed_unfoldC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mSumC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData))))
        theta)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  simpa [mSumThetaC] using
    hmSum_scale_theta_constructedC P hd_nn hd_pos e hdeq cls theta eps n afloorData




/-! ### §3 core: mSum budget criterion

Imported from `Mathdemo.ScratchMSumLeCriterion`, which built successfully
before BSP integration.  This block isolates the CReal-to-Nat cancellation
criterion and feeds it into the final Nat allocation accounting.
-/

structure MSumLeCriterionC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Prop where
  le_of_scaled_bound :
    RegularSeqLe
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) →
    mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n

/-- The raw Nat sum is within budget, once the CReal-to-Nat criterion is
available. -/
theorem hmSum_le_from_criterionC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (criterion : MSumLeCriterionC P hd_nn hd_pos e hdeq cls theta eps n afloorData) :
    mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n := by
  exact criterion.le_of_scaled_bound
    (hmSum_scale_theta_constructedC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData)

/-- Final shifted allocation sums to `n`, once the CReal-to-Nat criterion is
available. -/
theorem hsum_MC_from_criterionC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (criterion : MSumLeCriterionC P hd_nn hd_pos e hdeq cls theta eps n afloorData) :
    lemma33PrefixNatC
      (fun j => MC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        n (j + 1))
      (N_C (2 ^ e) cls) = n := by
  exact hsum_MC_prefixC (2 ^ e) cls
    (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
    n
    (hNposC (2 ^ e) cls (Nat.pow_pos (Nat.succ_pos 1) : 0 < 2 ^ e))
    (hmSum_le_from_criterionC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData criterion)

/-- A named remainder after the raw allocation.  This is harmless before the
criterion is constructed, and will be used by the final packaging layer. -/
noncomputable def remC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Nat :=
  n - mSumC (2 ^ e) cls
    (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)

/-- The remainder unfolding is just the Nat subtraction defining `MC`. -/
theorem remC_eqC {a b d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) :
    remC P hd_nn hd_pos e hdeq cls theta eps n afloorData =
      n - mSumC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) := rfl




/-! ### §3 core: mSum bad-case contradiction shell

Imported from `Mathdemo.ScratchMSumLeConstruct`, which built successfully
before BSP integration.  This block packages the bad-case contradiction needed
to turn the scaled CReal budget into the Nat bound `mSumC ≤ n`.
-/

theorem nat_succ_le_of_not_leC {m n : Nat} (h : ¬ m ≤ n) : n + 1 ≤ m := by
  omega

/-- If `m ≤ n` fails for natural numbers, then `m` is positive. -/
theorem nat_pos_of_not_leC {m n : Nat} (h : ¬ m ≤ n) : 0 < m := by
  omega

/-- Failed raw-budget bound gives the successor lower bound for `mSumC`. -/
theorem hmSum_bad_succ_leC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hbad : ¬ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) :
    n + 1 ≤ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) := by
  exact nat_succ_le_of_not_leC hbad

/-- Failed raw-budget bound gives positivity of `mSumC`. -/
theorem hmSum_bad_posC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hbad : ¬ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) :
    0 < mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) := by
  exact nat_pos_of_not_leC hbad

/-- The remaining bad-case contradiction data for the `mSumC ≤ n` step.

Here `D` is the total lambda drop
`lamC 0 - lamC (2^e+1)`.  If `mSumC ≤ n` fails, the previous prefix/floor
work should yield a strict upper estimate `mSumThetaC < D`, while the concrete
choice of `theta` as the `(n+1)`-budget unit should yield `D ≤ mSumThetaC`.
This structure isolates exactly those two estimates. -/
structure MSumLeContradictionDataC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Prop where
  strict_of_bad :
    (¬ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) →
    regularSeqLtProp
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)))
  lower_of_bad :
    (¬ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) →
    RegularSeqLe
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)))
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)

/-- Construct the earlier `MSumLeCriterionC` from the two bad-case estimates.

This version avoids `by_cases` and uses the concrete `Decidable` instance for
Nat inequalities, keeping the declaration free of `selector-style construction`.
-/
def mSumLeCriterion_of_contradictionC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (badData : MSumLeContradictionDataC
      P hd_nn hd_pos e hdeq cls theta eps n afloorData) :
    MSumLeCriterionC P hd_nn hd_pos e hdeq cls theta eps n afloorData := by
  refine ⟨?_⟩
  intro _hscaled
  have hdec : Decidable
      (mSumC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) :=
    inferInstance
  cases hdec with
  | isTrue hle =>
      exact hle
  | isFalse hbad =>
      have hstrict := badData.strict_of_bad hbad
      have hlower := badData.lower_of_bad hbad
      exact (regularSeqLtProp_irrefl
        (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        (regularSeqLtProp_of_lt_of_le hstrict hlower)).elim

/-- Once the bad-case contradiction data is available, the raw Nat sum is
within budget. -/
theorem hmSum_le_from_contradictionC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (badData : MSumLeContradictionDataC
      P hd_nn hd_pos e hdeq cls theta eps n afloorData) :
    mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n := by
  exact hmSum_le_from_criterionC P hd_nn hd_pos e hdeq cls theta eps n
    afloorData
    (mSumLeCriterion_of_contradictionC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData badData)

/-- Final allocation sum obtained from the bad-case contradiction package. -/
theorem hsum_MC_from_contradictionC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (badData : MSumLeContradictionDataC
      P hd_nn hd_pos e hdeq cls theta eps n afloorData) :
    lemma33PrefixNatC
      (fun j => MC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        n (j + 1))
      (N_C (2 ^ e) cls) = n := by
  exact hsum_MC_from_criterionC P hd_nn hd_pos e hdeq cls theta eps n
    afloorData
    (mSumLeCriterion_of_contradictionC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData badData)




/-! ### §3 core: strict upper half of the mSum bad-case contradiction

Imported from `Mathdemo.ScratchMSumLeBadStrict`, which built successfully
before BSP integration.  This block proves that a failed raw Nat budget bound
forces the scaled raw allocation strictly below the total lambda drop.
-/

theorem regularSeqLtProp_add_rightC {a b c : CReal}
    (h : regularSeqLtProp a b) :
    regularSeqLtProp (CReal.add a c) (CReal.add b c) := by
  have hleft : regularSeqLtProp (CReal.add c a) (CReal.add c b) :=
    regularSeqLtProp_add_left c a b h
  have hstep : regularSeqLtProp (CReal.add a c) (CReal.add c b) :=
    regularSeqLtProp_of_left_eventual (CReal.add_comm a c) hleft
  exact regularSeqLtProp_of_right_eventual (CReal.add_comm c b) hstep

/-- If a Nat prefix sum is positive, one term in the prefix is positive. -/
theorem lemma33PrefixNatC_exists_pos_of_pos (u : Nat → Nat) (N : Nat)
    (hpos : 0 < lemma33PrefixNatC u N) :
    ∃ j : Nat, j < N ∧ 0 < u j := by
  induction N with
  | zero =>
      simp [lemma33PrefixNatC] at hpos
  | succ N ih =>
      rw [lemma33PrefixNatC_succ] at hpos
      by_cases hpref : 0 < lemma33PrefixNatC u N
      · rcases ih hpref with ⟨j, hjN, hjpos⟩
        exact ⟨j, Nat.lt_trans hjN (Nat.lt_succ_self N), hjpos⟩
      · have hpref0 : lemma33PrefixNatC u N = 0 := by omega
        have hterm : 0 < u N := by omega
        exact ⟨N, Nat.lt_succ_self N, hterm⟩

/-- Finite CReal prefixes are strict if they are termwise `≤` and at least one
term is strict. -/
theorem lemma33PrefixC_lt_of_le_of_exists_lt (x y : Nat → CReal) (N : Nat)
    (hle : ∀ j : Nat, j < N → RegularSeqLe (x j) (y j))
    (hstrict : ∃ j : Nat, j < N ∧ regularSeqLtProp (x j) (y j)) :
    regularSeqLtProp (lemma33PrefixC x N) (lemma33PrefixC y N) := by
  induction N with
  | zero =>
      rcases hstrict with ⟨j, hjN, _hjstrict⟩
      exact False.elim (Nat.not_lt_zero j hjN)
  | succ N ih =>
      rw [lemma33PrefixC_succ, lemma33PrefixC_succ]
      rcases hstrict with ⟨j, hjNsucc, hjstrict⟩
      have hjLe : j ≤ N := Nat.le_of_lt_succ hjNsucc
      rcases Nat.lt_or_eq_of_le hjLe with hjN | hjEq
      · have hpref_strict :
            regularSeqLtProp (lemma33PrefixC x N) (lemma33PrefixC y N) :=
          ih
            (by
              intro k hkN
              exact hle k (Nat.lt_trans hkN (Nat.lt_succ_self N)))
            ⟨j, hjN, hjstrict⟩
        have hterm_le : RegularSeqLe (x N) (y N) :=
          hle N (Nat.lt_succ_self N)
        have hfirst :
            RegularSeqLe
              (CReal.add (lemma33PrefixC x N) (x N))
              (CReal.add (lemma33PrefixC x N) (y N)) :=
          regularSeqLe_add
            (regularSeqLe_refl (lemma33PrefixC x N)) hterm_le
        have hsecond :
            regularSeqLtProp
              (CReal.add (lemma33PrefixC x N) (y N))
              (CReal.add (lemma33PrefixC y N) (y N)) :=
          regularSeqLtProp_add_rightC (c := y N) hpref_strict
        exact regularSeqLtProp_of_le_of_lt hfirst hsecond
      · subst j
        have hpref_le :
            RegularSeqLe (lemma33PrefixC x N) (lemma33PrefixC y N) :=
          lemma33PrefixC_mono x y N
            (by
              intro k hkN
              exact hle k (Nat.lt_trans hkN (Nat.lt_succ_self N)))
        have hfirst :
            RegularSeqLe
              (CReal.add (lemma33PrefixC x N) (x N))
              (CReal.add (lemma33PrefixC y N) (x N)) :=
          regularSeqLe_add hpref_le (regularSeqLe_refl (x N))
        have hsecond :
            regularSeqLtProp
              (CReal.add (lemma33PrefixC y N) (x N))
              (CReal.add (lemma33PrefixC y N) (y N)) :=
          regularSeqLtProp_add_left
            (lemma33PrefixC y N) (x N) (y N) hjstrict
        exact regularSeqLtProp_of_le_of_lt hfirst hsecond


/-- A positive raw Nat sum gives a strict raw-theta prefix bound against the
charge prefix. -/
theorem hmraw_charge_prefix_strict_thetaC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hpos : 0 < mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)) :
    regularSeqLtProp
      (lemma33PrefixC
        (rawThetaTermC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        (N_C (2 ^ e) cls))
      (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls)
        (N_C (2 ^ e) cls)) := by
  have hprefix_pos :
      0 < lemma33PrefixNatC
        (mrawC (2 ^ e) cls
          (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData))
        (N_C (2 ^ e) cls) := by
    simpa [mSumC] using hpos
  rcases lemma33PrefixNatC_exists_pos_of_pos
      (mrawC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData))
      (N_C (2 ^ e) cls) hprefix_pos with
    ⟨j0, hj0N, hj0pos⟩
  refine lemma33PrefixC_lt_of_le_of_exists_lt
    (rawThetaTermC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
    (chargeC P hd_nn hd_pos e hdeq cls)
    (N_C (2 ^ e) cls) ?_ ?_
  · intro j hjN
    dsimp [rawThetaTermC]
    exact hmraw_charge_thetaC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData j hjN
  · refine ⟨j0, hj0N, ?_⟩
    dsimp [rawThetaTermC]
    exact hmraw_charge_strict_thetaC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData j0 hj0N hj0pos

/-- The strict upper half of the bad-case contradiction: if the raw Nat budget
fails, then the scaled raw allocation is strictly below the total lambda drop. -/
theorem hmSumTheta_strict_total_of_badC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hbad : ¬ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) :
    regularSeqLtProp
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  have hpos : 0 < mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) :=
    hmSum_bad_posC P hd_nn hd_pos e hdeq cls theta eps n afloorData hbad
  have hprefStrict :
      regularSeqLtProp
        (rawThetaPrefixC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        (lemma33PrefixC (chargeC P hd_nn hd_pos e hdeq cls)
          (N_C (2 ^ e) cls)) := by
    dsimp [rawThetaPrefixC]
    exact hmraw_charge_prefix_strict_thetaC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData hpos
  have hrawTotal :
      regularSeqLtProp
        (rawThetaPrefixC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
          (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) :=
    regularSeqLtProp_of_lt_of_le hprefStrict
      (hcharge_totalC P hd_nn hd_pos e hdeq cls)
  have hbridge :=
    mSumThetaBridge_of_prefixC P hd_nn hd_pos e hdeq cls theta eps n afloorData
  exact regularSeqLtProp_of_left_eventual (Setoid.symm hbridge.equiv_prefix)
    hrawTotal

/-- Same strict upper estimate, packaged as the first field required by
`MSumLeContradictionDataC`. -/
theorem mSumLeContradiction_strict_of_badC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) :
    (¬ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) →
    regularSeqLtProp
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1))) := by
  intro hbad
  exact hmSumTheta_strict_total_of_badC P hd_nn hd_pos e hdeq cls theta eps n
    afloorData hbad




/-! ### §3 core: lower half of the mSum bad-case contradiction

Imported from `Mathdemo.ScratchMSumLeBadLower`, which built successfully
before BSP integration.  This block proves the lower half of the bad-case
contradiction and closes the route to `mSumC ≤ n`.
-/

theorem hmSumTheta_lower_of_badC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
      CReal.mul (constSeq (Nat.cast (n + 1))) theta)
    (hbad : ¬ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n) :
    RegularSeqLe
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)))
      (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData) := by
  have hsucc : n + 1 ≤ mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) :=
    hmSum_bad_succ_leC P hd_nn hd_pos e hdeq cls theta eps n afloorData hbad
  have hnat :
      RegularSeqLe
        (constSeq (Nat.cast (n + 1)))
        (constSeq (Nat.cast
          (mSumC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)))) :=
    natCast_leC (n + 1)
      (mSumC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)) hsucc
  have hmul :
      RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (n + 1))) theta)
        (CReal.mul
          (constSeq (Nat.cast
            (mSumC (2 ^ e) cls
              (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData))))
          theta) :=
    regularSeqLe_mul_right_of_nonnegC hnat htheta_nn
  have hmul' :
      RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (n + 1))) theta)
        (mSumThetaC P hd_nn hd_pos e hdeq cls theta eps n afloorData) := by
    simpa [mSumThetaC] using hmul
  exact regularSeqLe_of_left_eventual htheta_budget hmul'

/-- Assemble the full bad-case contradiction package from the strict upper
estimate of the previous brick and the lower estimate of this brick. -/
def mSumLeContradictionData_of_bad_boundsC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
      CReal.mul (constSeq (Nat.cast (n + 1))) theta) :
    MSumLeContradictionDataC
      P hd_nn hd_pos e hdeq cls theta eps n afloorData := by
  refine ⟨?_, ?_⟩
  · intro hbad
    exact mSumLeContradiction_strict_of_badC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData hbad
  · intro hbad
    exact hmSumTheta_lower_of_badC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData htheta_nn htheta_budget hbad

/-- With the two concrete theta-budget facts, the raw Nat allocation is within
budget.  This closes the `mSumC ≤ n` route. -/
theorem hmSum_le_from_bad_boundsC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
      CReal.mul (constSeq (Nat.cast (n + 1))) theta) :
    mSumC (2 ^ e) cls
      (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) ≤ n := by
  exact hmSum_le_from_contradictionC P hd_nn hd_pos e hdeq cls theta eps n
    afloorData
    (mSumLeContradictionData_of_bad_boundsC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData htheta_nn htheta_budget)

/-- The final shifted allocation sums to `n`, using the completed bad-case
contradiction route. -/
theorem hsum_MC_from_bad_boundsC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta eps : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
      CReal.mul (constSeq (Nat.cast (n + 1))) theta) :
    lemma33PrefixNatC
      (fun j => MC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        n (j + 1))
      (N_C (2 ^ e) cls) = n := by
  exact hsum_MC_from_contradictionC P hd_nn hd_pos e hdeq cls theta eps n
    afloorData
    (mSumLeContradictionData_of_bad_boundsC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData htheta_nn htheta_budget)




/-! ### §3 core: final p'-bound package

Imported from `Mathdemo.ScratchFinalPBound`, which built successfully before
BSP integration.  This block transports raw p'-bounds through the final
allocation shift and packages the final Nat allocation sum with intervalwise
p'-bounds.
-/

theorem regularSeqLe_eps_to_one_mulC (eps : CReal) :
    RegularSeqLe eps (CReal.mul (constSeq (Nat.cast (0 + 1))) eps) := by
  have hone : CReal.mul (constSeq (Nat.cast (0 + 1))) eps ≈ eps := by
    simpa using CReal.one_mul eps
  exact regularSeqLe_of_right_eventual (Setoid.symm hone)
    (regularSeqLe_refl eps)

/-- Raw p'-bound before the final remainder shift. -/
noncomputable def hp_rawC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hcls_small : ∀ i : Nat, cls i = true →
      regularSeqLtProp (alphaC P hd_nn hd_pos e hdeq i) eps)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    P.p_prime_ltC
      (bptRC a d (sC (2 ^ e) cls j))
      (bptRC a d (sC (2 ^ e) cls (j + 1)))
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j + 1)))
        eps) := by
  cases hEnd : cls (sC (2 ^ e) cls (j + 1)) with
  | true =>
      have hsmall := hp_smallC P hd_nn hd_pos e hdeq cls hcls_small j hjN hEnd
      have hm := hmraw_smallC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j hjN hEnd
      have hwiden :
          RegularSeqLe eps
            (CReal.mul
              (constSeq (Nat.cast
                (mrawC (2 ^ e) cls
                  (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j + 1)))
              eps) := by
        rw [hm]
        simpa using regularSeqLe_eps_to_one_mulC eps
      exact ProfileC.p_prime_ltC_mono P hsmall hwiden
  | false =>
      exact hp_B_boundC P hd_nn hd_pos e hdeq cls j hjN
        (hmraw_upperC P hd_nn hd_pos e hdeq cls theta eps n afloorData j hjN hEnd)

/-- Monotonicity of the p'-bound coefficient from raw allocation to final
shifted allocation. -/
theorem hbound_mono_finalC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (heps_nn : RegularSeqNonneg eps)
    (j : Nat) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j + 1)))
        eps)
      (CReal.mul
        (constSeq (Nat.cast
          (MC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
            n (j + 1) + 1)))
        eps) := by
  have hnat :
      mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j + 1 ≤
      MC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
            n (j + 1) + 1 := by
    exact Nat.succ_le_succ
      (hM_geC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) n j)
  exact regularSeqLe_mul_right_of_nonnegC
    (natCast_leC
      (mrawC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) j + 1)
      (MC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
            n (j + 1) + 1)
      hnat)
    heps_nn

/-- Final p'-bound after absorbing the remainder into `MC`. -/
noncomputable def hp_finalC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hcls_small : ∀ i : Nat, cls i = true →
      regularSeqLtProp (alphaC P hd_nn hd_pos e hdeq i) eps)
    (heps_nn : RegularSeqNonneg eps)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    P.p_prime_ltC
      (bptRC a d (sC (2 ^ e) cls j))
      (bptRC a d (sC (2 ^ e) cls (j + 1)))
      (CReal.mul
        (constSeq (Nat.cast
          (MC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
            n (j + 1) + 1)))
        eps) :=
  hp_final_from_rawC P hd_nn hd_pos e hdeq cls
    (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData) n
    (hp_rawC P hd_nn hd_pos e hdeq cls theta n afloorData hcls_small)
    (hbound_mono_finalC P hd_nn hd_pos e hdeq cls theta n afloorData heps_nn)
    j hjN

/-- Final allocation sum paired with final p'-bounds.  This is the data the
next width/packaging brick will feed into `SubdivisionData`. -/
structure FinalPBoundPackC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) where
  sum_MC :
    lemma33PrefixNatC
      (fun j => MC (2 ^ e) cls
        (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
        n (j + 1))
      (N_C (2 ^ e) cls) = n
  p_final : ∀ j : Nat, j < N_C (2 ^ e) cls →
    P.p_prime_ltC
      (bptRC a d (sC (2 ^ e) cls j))
      (bptRC a d (sC (2 ^ e) cls (j + 1)))
      (CReal.mul
        (constSeq (Nat.cast
          (MC (2 ^ e) cls
            (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
            n (j + 1) + 1)))
        eps)

/-- Build the final p'-bound package from the completed bad-bound route. -/
noncomputable def finalPBoundPackC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hcls_small : ∀ i : Nat, cls i = true →
      regularSeqLtProp (alphaC P hd_nn hd_pos e hdeq i) eps)
    (heps_nn : RegularSeqNonneg eps)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
      CReal.mul (constSeq (Nat.cast (n + 1))) theta) :
    FinalPBoundPackC P hd_nn hd_pos e hdeq cls theta n afloorData :=
  ⟨hsum_MC_from_bad_boundsC P hd_nn hd_pos e hdeq cls theta eps n
      afloorData htheta_nn htheta_budget,
    hp_finalC P hd_nn hd_pos e hdeq cls theta n afloorData hcls_small heps_nn⟩

/-- Profile lambda diameter used in the concrete theta choice for Lemma 3.3. -/
noncomputable def lemma33DiameterC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) : CReal :=
  CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode)

/-- Concrete theta choice: profile diameter divided by `n+1`. -/
noncomputable def lemma33ThetaForProfileC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) : CReal :=
  lemma33ThetaC (lemma33DiameterC P) n

theorem lemma33ThetaForProfile_nonnegC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) :
    RegularSeqNonneg (lemma33ThetaForProfileC P n) := by
  simpa [lemma33ThetaForProfileC, lemma33DiameterC] using
    (lemma33Theta_nonnegC (D := lemma33DiameterC P) (n := n)
      (lemma33ProfileDiameter_nonnegC P))

theorem lemma33ThetaForProfile_lt_epsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    regularSeqLtProp (lemma33ThetaForProfileC P n) eps := by
  simpa [lemma33ThetaForProfileC] using
    (lemma33Theta_lt_epsC (D := lemma33DiameterC P) (eps := eps) (n := n) hD_eps)

noncomputable def lemma33ThetaForProfileDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    regularSeqLtData (lemma33ThetaForProfileC P n) eps := by
  change PosEventuallyData (subSeq eps (lemma33ThetaForProfileC P n))
  exact posEventuallyData_of_strongGaugeC
    (strongGaugeC (posEventually_to_strongC
      (lemma33ThetaForProfile_lt_epsC P n hD_eps)))

theorem lemma33ThetaForProfile_budgetC {a b d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat) :
    CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
      CReal.mul (constSeq (Nat.cast (n + 1))) (lemma33ThetaForProfileC P n) := by
  exact Setoid.trans
    (lemma33LamTotal_equiv_profileDiameterC P hd_nn hd_pos e hdeq)
    (by
      simpa [lemma33ThetaForProfileC, lemma33DiameterC] using
        (lemma33Theta_budgetC (lemma33DiameterC P) n))

theorem lemma33LamTotal_lt_profileBudgetC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    regularSeqLtProp
      (CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps) := by
  exact regularSeqLtProp_of_left_eventual
    (lemma33LamTotal_equiv_profileDiameterC P hd_nn hd_pos e hdeq) hD_eps

/-- Concrete classification obtained from the profile theta choice. -/
noncomputable def lemma33ClsForProfileC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) : Nat → Bool :=
  clsC (lemma33ThetaForProfileDataC P n hD_eps)
    (alphaC P hd_nn hd_pos e hdeq)

theorem lemma33ClsForProfile_smallC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (i : Nat) (hci : lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps i = true) :
    regularSeqLtProp (alphaC P hd_nn hd_pos e hdeq i) eps := by
  exact clsC_small (lemma33ThetaForProfileDataC P n hD_eps)
    (alphaC P hd_nn hd_pos e hdeq) i hci

/-- Concrete approximate-floor data obtained from the profile theta choice. -/
noncomputable def lemma33AfloorDataForProfileC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    (j : Nat) → j < N_C (2 ^ e) (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps) →
      Lemma33H4ApproxFloorC (lemma33ThetaForProfileC P n) eps
        (betaC P hd_nn hd_pos e hdeq
          (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps) j) n :=
  lemma33ApproxFloorDataC_construct P hd_nn hd_pos e hdeq
    (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps)
    (lemma33ThetaForProfileC P n) n
    (lemma33ThetaForProfile_lt_epsC P n hD_eps)
    (lemma33LamTotal_lt_profileBudgetC P hd_nn hd_pos e hdeq n hD_eps)

/-- Concrete final p-bound pack obtained from the profile theta choice. -/
noncomputable def lemma33FinalPBoundPackC_construct {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat) (heps_nn : RegularSeqNonneg eps)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    FinalPBoundPackC P hd_nn hd_pos e hdeq
      (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps)
      (lemma33ThetaForProfileC P n) n
      (lemma33AfloorDataForProfileC P hd_nn hd_pos e hdeq n hD_eps) :=
  finalPBoundPackC P hd_nn hd_pos e hdeq
    (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps)
    (lemma33ThetaForProfileC P n) n
    (lemma33AfloorDataForProfileC P hd_nn hd_pos e hdeq n hD_eps)
    (lemma33ClsForProfile_smallC P hd_nn hd_pos e hdeq n hD_eps)
    heps_nn
    (lemma33ThetaForProfile_nonnegC P n)
    (lemma33ThetaForProfile_budgetC P hd_nn hd_pos e hdeq n)

#print axioms BishopSec3P.lemma33DiameterC
#print axioms BishopSec3P.lemma33ThetaForProfileC
#print axioms BishopSec3P.lemma33ThetaForProfile_nonnegC
#print axioms BishopSec3P.lemma33ThetaForProfile_lt_epsC
#print axioms BishopSec3P.lemma33ThetaForProfileDataC
#print axioms BishopSec3P.lemma33ThetaForProfile_budgetC
#print axioms BishopSec3P.lemma33LamTotal_lt_profileBudgetC
#print axioms BishopSec3P.lemma33ClsForProfileC
#print axioms BishopSec3P.lemma33ClsForProfile_smallC
#print axioms BishopSec3P.lemma33AfloorDataForProfileC
#print axioms BishopSec3P.lemma33FinalPBoundPackC_construct

/-- If `total ≈ (n+1) * theta`, then `2(n+1) * theta ≈ total + total`. -/
theorem lemma33DoubleThetaBudgetC (total theta : CReal) (n : Nat)
    (hbudget : total ≈ CReal.mul (constSeq (Nat.cast (n + 1))) theta) :
    CReal.mul (constSeq (Nat.cast (2 * (n + 1)))) theta ≈
      CReal.add total total := by
  have hnatEq : 2 * (n + 1) = (n + 1) + (n + 1) := by omega
  have hnat : constSeq (Nat.cast (2 * (n + 1))) ≈
      CReal.add (constSeq (Nat.cast (n + 1))) (constSeq (Nat.cast (n + 1))) := by
    rw [hnatEq]
    exact constSeq_natCast_addC (n + 1) (n + 1)
  calc CReal.mul (constSeq (Nat.cast (2 * (n + 1)))) theta
      ≈ CReal.mul (CReal.add (constSeq (Nat.cast (n + 1)))
          (constSeq (Nat.cast (n + 1)))) theta :=
        CReal.mul_respects_equiv _ _ _ _ hnat (Setoid.refl theta)
    _ ≈ CReal.add (CReal.mul (constSeq (Nat.cast (n + 1))) theta)
        (CReal.mul (constSeq (Nat.cast (n + 1))) theta) :=
        CReal.right_distrib _ _ _
    _ ≈ CReal.add total total :=
        CReal.add_respects_equiv _ _ _ _ (Setoid.symm hbudget) (Setoid.symm hbudget)

/-- Retained-interval width bound, CReal port of Lemma 3.3 Step 7(a). -/
theorem lemma33RetainedWidthC {a b d delta small : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (hcls_big : ∀ i : Nat, cls i = false →
      regularSeqLtProp theta (alphaC P hd_nn hd_pos e hdeq i))
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (2 ^ e + 1)) ≈
      CReal.mul (constSeq (Nat.cast (n + 1))) theta)
    (hd_small_le : RegularSeqLe d small)
    (hsmall_nn : RegularSeqNonneg small)
    (hLsmall : RegularSeqLe
      (CReal.mul (constSeq (Nat.cast (2 * (n + 1)))) small) delta)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (CReal.sub (bptRC a d (sC (2 ^ e) cls (j + 1)))
        (bptRC a d (sC (2 ^ e) cls j)))
      delta := by
  let K : Nat := 2 ^ e
  let L : Nat := 2 * (n + 1)
  let k : Nat := sC K cls j
  let i : Nat := sC K cls (j + 1)
  have hki : k < i := by
    simpa [K, k, i] using hs_strictC K cls j hjN
  have hiK : i ≤ K := by
    simpa [K, i] using hs_endpoint_le_KC K cls j
  have hdist : CReal.sub (bptRC a d i) (bptRC a d k) ≈
      CReal.mul (constSeq (Nat.cast (i - k))) d :=
    bptRC_sub_generalC a d (Nat.le_of_lt hki)
  by_cases hshort : i - k ≤ L
  · have hcast : RegularSeqLe (constSeq (Nat.cast (i - k))) (constSeq (Nat.cast L)) :=
      natCast_leC (i - k) L hshort
    have h1 : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (i - k))) d)
        (CReal.mul (constSeq (Nat.cast (i - k))) small) :=
      regularSeqLe_mul_left_of_nonnegC hd_small_le (natCast_nonnegC (i - k))
    have h2 : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (i - k))) small)
        (CReal.mul (constSeq (Nat.cast L)) small) :=
      regularSeqLe_mul_right_of_nonnegC hcast hsmall_nn
    have h3 : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (i - k))) d) delta :=
      regularSeqLe_trans (regularSeqLe_trans h1 h2) (by simpa [L] using hLsmall)
    exact regularSeqLe_of_left_eventual (by simpa [K, k, i] using hdist) h3
  · have hlong : L < i - k := Nat.lt_of_not_ge hshort
    have hBigEnd : cls i = false := by
      cases hci : cls i with
      | false => rfl
      | true =>
          have hprev := hs_prev_of_smallC K cls j hjN hci
          exfalso
          dsimp [L, k, i] at hlong hprev
          omega
    let ell : Nat := i - k
    have hellPos : 0 < ell := by dsimp [ell]; omega
    have hAllBig : ∀ r : Nat, r < ell → cls (k + r + 1) = false := by
      intro r hr
      exact hs_all_bigC K cls j (k + r + 1) hjN hBigEnd (by omega) (by
        dsimp [ell] at hr
        omega)
    have hAllTheta : ∀ r : Nat, r < ell →
        regularSeqLtProp theta
          (CReal.sub (lamC P hd_nn hd_pos e hdeq (k + r))
            (lamC P hd_nn hd_pos e hdeq (k + r + 2))) := by
      intro r hr
      have hraw := hcls_big (k + r + 1) (hAllBig r hr)
      have hsub : k + r + 1 - 1 = k + r := by omega
      have hadd : k + r + 1 + 1 = k + r + 2 := by omega
      simpa [alphaC, K, hsub, hadd] using hraw
    have hlower : regularSeqLtProp
        (CReal.mul (constSeq (Nat.cast ell)) theta)
        (lemma33PrefixC
          (fun r => CReal.sub (lamC P hd_nn hd_pos e hdeq (k + r))
            (lamC P hd_nn hd_pos e hdeq (k + r + 2))) ell) :=
      lemma33Prefix_const_ltC theta
        (fun r => CReal.sub (lamC P hd_nn hd_pos e hdeq (k + r))
          (lamC P hd_nn hd_pos e hdeq (k + r + 2))) ell hellPos hAllTheta
    have hLell : RegularSeqLe (constSeq (Nat.cast L)) (constSeq (Nat.cast ell)) :=
      natCast_leC L ell (Nat.le_of_lt hlong)
    have hscale : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast L)) theta)
        (CReal.mul (constSeq (Nat.cast ell)) theta) :=
      regularSeqLe_mul_right_of_nonnegC hLell htheta_nn
    have hLtheta_lt : regularSeqLtProp
        (CReal.mul (constSeq (Nat.cast L)) theta)
        (lemma33PrefixC
          (fun r => CReal.sub (lamC P hd_nn hd_pos e hdeq (k + r))
            (lamC P hd_nn hd_pos e hdeq (k + r + 2))) ell) :=
      regularSeqLtProp_of_le_of_lt hscale hlower
    let total : CReal := CReal.sub (lamC P hd_nn hd_pos e hdeq 0)
      (lamC P hd_nn hd_pos e hdeq (K + 1))
    have hbudgetK : total ≈ CReal.mul (constSeq (Nat.cast (n + 1))) theta := by
      dsimp [total, K]
      exact htheta_budget
    have hdouble : CReal.mul (constSeq (Nat.cast L)) theta ≈ CReal.add total total := by
      dsimp [L]
      exact lemma33DoubleThetaBudgetC total theta n hbudgetK
    have htwo_lower : regularSeqLtProp (CReal.add total total)
        (lemma33PrefixC
          (fun r => CReal.sub (lamC P hd_nn hd_pos e hdeq (k + r))
            (lamC P hd_nn hd_pos e hdeq (k + r + 2))) ell) :=
      regularSeqLtProp_of_left_eventual (Setoid.symm hdouble) hLtheta_lt
    have hk_le : k ≤ K + 1 := by
      have hkK := hs_le_KC K cls j
      dsimp [k]
      omega
    have hkell_eq : k + ell = i := by dsimp [ell]; omega
    have hkell_le : k + ell ≤ K + 1 := by
      rw [hkell_eq]
      omega
    have hk1_le : k + 1 ≤ K + 1 := by
      have hkK := hs_le_KC K cls j
      dsimp [k]
      omega
    have hkell1_le : k + ell + 1 ≤ K + 1 := by
      rw [hkell_eq]
      omega
    have hupper : RegularSeqLe
        (lemma33PrefixC
          (fun r => CReal.sub (lamC P hd_nn hd_pos e hdeq (k + r))
            (lamC P hd_nn hd_pos e hdeq (k + r + 2))) ell)
        (CReal.add total total) := by
      have hraw := lemma33AlphaPrefix_le_twoDiameterC
        (lamC P hd_nn hd_pos e hdeq)
        (lamC P hd_nn hd_pos e hdeq 0)
        (lamC P hd_nn hd_pos e hdeq (K + 1))
        K k ell
        (fun r hr =>
          hlamC_anti P hd_nn hd_pos e hdeq 0 r (Nat.zero_le r) (by simpa [K] using hr))
        (fun r hr =>
          hlamC_anti P hd_nn hd_pos e hdeq r (K + 1) (by simpa [K] using hr)
            (Nat.le_refl _))
        hk_le hkell_le hk1_le hkell1_le
      simpa [total, K] using hraw
    have hbad : regularSeqLtProp (CReal.add total total) (CReal.add total total) :=
      regularSeqLtProp_of_lt_of_le htwo_lower hupper
    exact False.elim (regularSeqLtProp_irrefl (CReal.add total total) hbad)

#print axioms BishopSec3P.lemma33DoubleThetaBudgetC
#print axioms BishopSec3P.lemma33RetainedWidthC

theorem lemma33ClsForProfile_bigC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (i : Nat) (hci : lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps i = false) :
    regularSeqLtProp (lemma33ThetaForProfileC P n)
      (alphaC P hd_nn hd_pos e hdeq i) := by
  exact clsC_big (lemma33ThetaForProfileDataC P n hD_eps)
    (alphaC P hd_nn hd_pos e hdeq) i hci




/-! ### §3 core: final Lemma 3.3 package

Imported from `Mathdemo.ScratchWidthAndLemma33Pack`, which built successfully
before BSP integration.  This block packages retained points, final interval
multiplicities, width bounds, final sum, and final p'-bounds into the
CReal-native Lemma 3.3 payload.
-/

noncomputable def lemma33PtsC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Nat → CReal :=
  fun j => bptRC a d (sC (2 ^ e) cls j)

/-- Final interval multiplicity, indexed by the retained interval number. -/
noncomputable def lemma33MCWeightC {a b d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) : Nat → Nat :=
  fun j => MC (2 ^ e) cls
    (afloorC P hd_nn hd_pos e hdeq cls theta eps n afloorData)
    n (j + 1)

/-- Packaged `lemma_3_3C` subdivision payload. -/
structure Lemma33PackC {a b d eps delta : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n) where
  N_pos : 0 < N_C (2 ^ e) cls
  pts_zero :
    lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData 0 ≈ a
  pts_N :
    lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData
      (N_C (2 ^ e) cls) ≈ b
  pts_strict : ∀ j : Nat, j < N_C (2 ^ e) cls →
    regularSeqLtProp
      (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData j)
      (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData (j + 1))
  width_le : ∀ j : Nat, j < N_C (2 ^ e) cls →
    RegularSeqLe
      (CReal.sub
        (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData (j + 1))
        (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData j))
      delta
  sum_M :
    lemma33PrefixNatC
      (lemma33MCWeightC P hd_nn hd_pos e hdeq cls theta n afloorData)
      (N_C (2 ^ e) cls) = n
  p_prime_cond : ∀ j : Nat, j < N_C (2 ^ e) cls →
    P.p_prime_ltC
      (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData j)
      (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData (j + 1))
      (CReal.mul
        (constSeq (Nat.cast
          (lemma33MCWeightC P hd_nn hd_pos e hdeq cls theta n afloorData j + 1)))
        eps)

/-- Build the final `lemma_3_3C` package from endpoint/width data and the
already-completed final p'-bound package. -/
noncomputable def lemma33PackC {a b d eps delta : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (hpts_zero :
      lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData 0 ≈ a)
    (hpts_N :
      lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData
        (N_C (2 ^ e) cls) ≈ b)
    (hpts_strict : ∀ j : Nat, j < N_C (2 ^ e) cls →
      regularSeqLtProp
        (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData j)
        (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData (j + 1)))
    (hwidth : ∀ j : Nat, j < N_C (2 ^ e) cls →
      RegularSeqLe
        (CReal.sub
          (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData (j + 1))
          (lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData j))
        delta)
    (finalPack :
      FinalPBoundPackC P hd_nn hd_pos e hdeq cls theta n afloorData) :
    Lemma33PackC (delta := delta) P hd_nn hd_pos e hdeq cls theta n afloorData := by
  refine {
    N_pos := ?_,
    pts_zero := hpts_zero,
    pts_N := hpts_N,
    pts_strict := hpts_strict,
    width_le := hwidth,
    sum_M := ?_,
    p_prime_cond := ?_
  }
  · exact hNposC (2 ^ e) cls
      (Nat.pow_pos (Nat.succ_pos 1) : 0 < 2 ^ e)
  · simpa [lemma33MCWeightC] using finalPack.sum_MC
  · intro j hjN
    simpa [lemma33PtsC, lemma33MCWeightC] using finalPack.p_final j hjN




/-! ### §3 bridge: Lemma 3.3 result object for Lemma 3.4

Imported from `Mathdemo.ScratchLemma34CBridge`, which built successfully before
BSP integration.  This block repackages the final Lemma 3.3 payload into a
result object convenient for the Lemma 3.4 tower layer.
-/

structure Lemma33ResultC {a b : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) (eps delta : CReal) where
  N : Nat
  N_pos : 0 < N
  pts : Nat → CReal
  pts_zero : pts 0 ≈ a
  pts_N : pts N ≈ b
  pts_strict : ∀ i : Nat, i < N →
    regularSeqLtProp (pts i) (pts (i + 1))
  width_le : ∀ i : Nat, i < N →
    RegularSeqLe (CReal.sub (pts (i + 1)) (pts i)) delta
  M : Nat → Nat
  sum_M : lemma33PrefixNatC M N = n
  p_prime_cond : ∀ i : Nat, i < N →
    P.p_prime_ltC (pts i) (pts (i + 1))
      (CReal.mul (constSeq (Nat.cast (M i + 1))) eps)

/-- Turn the already-packaged final Lemma 3.3 payload into the exported result
object used by the upcoming Lemma 3.4 tower layer. -/
noncomputable def lemma33ResultC_of_packC {a b d eps delta : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (cls : Nat → Bool) (theta : CReal) (n : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaC P hd_nn hd_pos e hdeq cls j) n)
    (pack : Lemma33PackC (delta := delta)
      P hd_nn hd_pos e hdeq cls theta n afloorData) :
    Lemma33ResultC P n eps delta where
  N := N_C (2 ^ e) cls
  N_pos := pack.N_pos
  pts := lemma33PtsC P hd_nn hd_pos e hdeq cls theta n afloorData
  pts_zero := pack.pts_zero
  pts_N := pack.pts_N
  pts_strict := pack.pts_strict
  width_le := pack.width_le
  M := lemma33MCWeightC P hd_nn hd_pos e hdeq cls theta n afloorData
  sum_M := pack.sum_M
  p_prime_cond := pack.p_prime_cond

/-- Concrete Lemma 3.3 pack once the dyadic mesh is known small enough. -/
noncomputable def lemma33PackC_construct {a b d eps delta small : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat) (heps_nn : RegularSeqNonneg eps)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (hd_small_le : RegularSeqLe d small)
    (hsmall_nn : RegularSeqNonneg small)
    (hLsmall : RegularSeqLe
      (CReal.mul (constSeq (Nat.cast (2 * (n + 1)))) small) delta) :
    Lemma33PackC (delta := delta) P hd_nn hd_pos e hdeq
      (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps)
      (lemma33ThetaForProfileC P n) n
      (lemma33AfloorDataForProfileC P hd_nn hd_pos e hdeq n hD_eps) := by
  let cls := lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps
  let theta := lemma33ThetaForProfileC P n
  let afloorData := lemma33AfloorDataForProfileC P hd_nn hd_pos e hdeq n hD_eps
  refine lemma33PackC P hd_nn hd_pos e hdeq cls theta n afloorData ?_ ?_ ?_ ?_ ?_
  · dsimp [lemma33PtsC, cls, theta, afloorData]
    rw [hs_zeroC]
    exact Setoid.trans (bptRC_equiv_bptC a d 0) (bptC_zeroC a d)
  · dsimp [lemma33PtsC, cls, theta, afloorData]
    rw [hs_NC]
    exact Setoid.trans (bptRC_equiv_bptC a d (2 ^ e)) (bptC_KC e hdeq)
  · intro j hjN
    dsimp [lemma33PtsC, cls, theta, afloorData]
    have hki := hs_strictC (2 ^ e)
      (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps) j hjN
    have hltC : regularSeqLtProp
        (bptC a d (sC (2 ^ e)
          (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps) j))
        (bptC a d (sC (2 ^ e)
          (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps) (j + 1))) :=
      bptC_ltC hd_pos.toProp hki
    exact regularSeqLtProp_of_left_eventual
      (bptRC_equiv_bptC a d (sC (2 ^ e)
        (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps) j))
      (regularSeqLtProp_of_right_eventual
        (Setoid.symm (bptRC_equiv_bptC a d (sC (2 ^ e)
          (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps) (j + 1)))) hltC)
  · intro j hjN
    dsimp [lemma33PtsC, cls, theta, afloorData]
    exact lemma33RetainedWidthC P hd_nn hd_pos e hdeq
      (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps)
      (lemma33ThetaForProfileC P n) n
      (lemma33ClsForProfile_bigC P hd_nn hd_pos e hdeq n hD_eps)
      (lemma33ThetaForProfile_nonnegC P n)
      (lemma33ThetaForProfile_budgetC P hd_nn hd_pos e hdeq n)
      hd_small_le hsmall_nn hLsmall j hjN
  · exact lemma33FinalPBoundPackC_construct P hd_nn hd_pos e hdeq n heps_nn hD_eps

/-- Concrete Lemma 3.3 result once the dyadic mesh is known small enough. -/
noncomputable def lemma33ResultC_construct {a b d eps delta small : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub b a) (halfPow e))
    (n : Nat) (heps_nn : RegularSeqNonneg eps)
    (hD_eps : regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (hd_small_le : RegularSeqLe d small)
    (hsmall_nn : RegularSeqNonneg small)
    (hLsmall : RegularSeqLe
      (CReal.mul (constSeq (Nat.cast (2 * (n + 1)))) small) delta) :
    Lemma33ResultC P n eps delta :=
  lemma33ResultC_of_packC P hd_nn hd_pos e hdeq
    (lemma33ClsForProfileC P hd_nn hd_pos e hdeq n hD_eps)
    (lemma33ThetaForProfileC P n) n
    (lemma33AfloorDataForProfileC P hd_nn hd_pos e hdeq n hD_eps)
    (lemma33PackC_construct P hd_nn hd_pos e hdeq n heps_nn hD_eps
      hd_small_le hsmall_nn hLsmall)

#print axioms BishopSec3P.lemma33ClsForProfile_bigC
#print axioms BishopSec3P.lemma33PackC_construct
#print axioms BishopSec3P.lemma33ResultC_construct




/-! ### §3 Lemma 3.4 CReal-native result payload

Imported from `Mathdemo.ScratchLemma34CResultPayload`, which built successfully
before BSP integration.  This block fixes the CReal-native result API for the
later Lemma 3.4 tower construction.
-/

structure Lemma34LocalC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (t : Fin n → CReal) (beta : CReal) where
  gamma : CReal
  gamma_pos : regularSeqLtProp zeroSeq gamma
  local_bound : ∀ t_pt : CReal,
    RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
        (∀ i : Fin n,
          regularSeqLtProp beta
            (CReal.abs (CReal.sub t_pt (t i)))) →
          P.p_ltC
            (CReal.max a (CReal.sub t_pt gamma))
            (CReal.min b (CReal.add t_pt gamma))
            eps

/-- CReal-native result object for Lemma 3.4.

This mirrors the generic `BishopC.lemma_3_4` return shape, but packages the
dependent Sigma tower as named structures so that the later CReal-native tower
construction has a stable target API.
-/
structure Lemma34ResultC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) where
  t : Fin n → CReal
  t_bounds : ∀ i : Fin n, RegularSeqLe a (t i) ∧ RegularSeqLe (t i) b
  local_prop : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      Lemma34LocalC (a := a) (b := b) (eps := eps) (hab := hab) P n t beta




/-! ### §3 Lemma 3.4 CReal-native tower payload

Imported from `Mathdemo.ScratchLemma34CTowerPayload`, which built successfully
before BSP integration.  This block fixes the CReal-native tower/refinement
API for the later Lemma 3.4 construction.
-/

noncomputable def lemma34WidthScaleC (a b : CReal) (k : Nat) : CReal :=
  CReal.mul (CReal.sub b a) (halfPow k)

/-- One finite level of the CReal-native Lemma 3.4 nested interval tower. -/
structure Lemma34TowerC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) (k : Nat) where
  segL : Fin n → CReal
  segR : Fin n → CReal
  seg_proper : ∀ j : Fin n,
    RegularSeqLe a (segL j) ∧
      regularSeqLtProp (segL j) (segR j) ∧
        RegularSeqLe (segR j) b
  seg_width : ∀ j : Fin n,
    RegularSeqLe
      (CReal.sub (segR j) (segL j))
      (lemma34WidthScaleC a b k)

/-- CReal-native refinement relation between consecutive Lemma 3.4 tower levels. -/
structure Lemma34RefinesC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k)
    (T1 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1)) where
  left_mono : ∀ j : Fin n, RegularSeqLe (T0.segL j) (T1.segL j)
  right_mono : ∀ j : Fin n, RegularSeqLe (T1.segR j) (T0.segR j)




/-! ### §3 Lemma 3.4 CReal-native tower sequence skeleton

Imported from `Mathdemo.ScratchLemma34CTowerSeqSkeleton`, which built
successfully before BSP integration.  This block fixes the tower sequence,
refinement, and endpoint-sequence API for the later Lemma 3.4 construction.
-/

noncomputable def lemma34TowerSeqC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext }) :
    (k : Nat) →
      Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k
  | 0 => T0
  | k + 1 => (step k (lemma34TowerSeqC P n T0 step k)).val

/-- Consecutive levels of `lemma34TowerSeqC` refine each other. -/
noncomputable def lemma34TowerSeq_refinesC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (k : Nat) :
    Lemma34RefinesC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k
      (lemma34TowerSeqC P n T0 step k)
      (lemma34TowerSeqC P n T0 step (k + 1)) :=
  (step k (lemma34TowerSeqC P n T0 step k)).property

/-- Left endpoint sequence of one tower column. -/
noncomputable def lemma34LeftSeqC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (k : Nat) : CReal :=
  (lemma34TowerSeqC P n T0 step k).segL j

/-- Right endpoint sequence of one tower column. -/
noncomputable def lemma34RightSeqC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (k : Nat) : CReal :=
  (lemma34TowerSeqC P n T0 step k).segR j




/-! ### §3 Lemma 3.4 CReal-native tower endpoint projections

Imported from `Mathdemo.ScratchLemma34CSeqProjection`, which built successfully
before BSP integration.  This block exposes endpoint bounds, width bounds, and
one-step monotonicity from the tower sequence API.
-/

theorem lemma34TowerSeq_seg_properC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (k : Nat) :
    RegularSeqLe a (lemma34LeftSeqC P n T0 step j k) ∧
      regularSeqLtProp
        (lemma34LeftSeqC P n T0 step j k)
        (lemma34RightSeqC P n T0 step j k) ∧
      RegularSeqLe (lemma34RightSeqC P n T0 step j k) b := by
  simpa [lemma34LeftSeqC, lemma34RightSeqC] using
    (lemma34TowerSeqC P n T0 step k).seg_proper j

theorem lemma34TowerSeq_segment_widthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (CReal.sub
        (lemma34RightSeqC P n T0 step j k)
        (lemma34LeftSeqC P n T0 step j k))
      (lemma34WidthScaleC a b k) := by
  simpa [lemma34LeftSeqC, lemma34RightSeqC] using
    (lemma34TowerSeqC P n T0 step k).seg_width j

theorem lemma34LeftSeq_monoStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (lemma34LeftSeqC P n T0 step j k)
      (lemma34LeftSeqC P n T0 step j (k + 1)) := by
  simpa [lemma34LeftSeqC] using
    (lemma34TowerSeq_refinesC P n T0 step k).left_mono j

theorem lemma34RightSeq_antitoneStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (lemma34RightSeqC P n T0 step j (k + 1))
      (lemma34RightSeqC P n T0 step j k) := by
  simpa [lemma34RightSeqC] using
    (lemma34TowerSeq_refinesC P n T0 step k).right_mono j

/-- Technical lemma used in the public import closure. -/
theorem lemma34LeftSeq_monoC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) : ∀ {p q : Nat}, p ≤ q →
      RegularSeqLe
        (lemma34LeftSeqC P n T0 step j p)
        (lemma34LeftSeqC P n T0 step j q) := by
  intro p q hpq
  induction hpq with
  | refl => exact regularSeqLe_refl _
  | @step m _ ih =>
      exact regularSeqLe_trans ih (lemma34LeftSeq_monoStepC P n T0 step j m)

/-- Technical lemma used in the public import closure. -/
theorem lemma34RightSeq_antitoneC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) : ∀ {p q : Nat}, p ≤ q →
      RegularSeqLe
        (lemma34RightSeqC P n T0 step j q)
        (lemma34RightSeqC P n T0 step j p) := by
  intro p q hpq
  induction hpq with
  | refl => exact regularSeqLe_refl _
  | @step m _ ih =>
      exact regularSeqLe_trans (lemma34RightSeq_antitoneStepC P n T0 step j m) ih

/-- Technical lemma used in the public import closure. -/
theorem lemma34LeftSeq_le_rightSeqC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (m k : Nat) :
    RegularSeqLe
      (lemma34LeftSeqC P n T0 step j m)
      (lemma34RightSeqC P n T0 step j k) := by
  rcases Nat.le_total m k with hmk | hkm
  · exact regularSeqLe_trans
      (lemma34LeftSeq_monoC P n T0 step j hmk)
      (regularSeqLe_of_ltPropC (lemma34TowerSeq_seg_properC P n T0 step j k).2.1)
  · exact regularSeqLe_trans
      (regularSeqLe_of_ltPropC (lemma34TowerSeq_seg_properC P n T0 step j m).2.1)
      (lemma34RightSeq_antitoneC P n T0 step j hkm)

/-- Technical lemma used in the public import closure. -/
theorem lemma34LeftSeq_absSub_le_widthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) (M m k : Nat) (hm : M ≤ m) (hk : M ≤ k) :
    RegularSeqLe
      (absSeq (subSeq (lemma34LeftSeqC P n T0 step j m)
                      (lemma34LeftSeqC P n T0 step j k)))
      (lemma34WidthScaleC a b M) := by
  have hW :
      RegularSeqLe
        (subSeq (lemma34RightSeqC P n T0 step j M)
                (lemma34LeftSeqC P n T0 step j M))
        (lemma34WidthScaleC a b M) :=
    lemma34TowerSeq_segment_widthC P n T0 step j M
  rcases Nat.le_total m k with hmk | hkm
  · have hmk_le : RegularSeqLe (lemma34LeftSeqC P n T0 step j m)
        (lemma34LeftSeqC P n T0 step j k) :=
      lemma34LeftSeq_monoC P n T0 step j hmk
    have hdiff_nonneg :
        RegularSeqLe zeroSeq
          (subSeq (lemma34LeftSeqC P n T0 step j k)
                  (lemma34LeftSeqC P n T0 step j m)) :=
      regularSeqLe_zero_of_nonneg hmk_le
    have habs_rev :
        RegularSeqLe
          (absSeq (subSeq (lemma34LeftSeqC P n T0 step j k)
                          (lemma34LeftSeqC P n T0 step j m)))
          (subSeq (lemma34LeftSeqC P n T0 step j k)
                  (lemma34LeftSeqC P n T0 step j m)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have habs :
        RegularSeqLe
          (absSeq (subSeq (lemma34LeftSeqC P n T0 step j m)
                          (lemma34LeftSeqC P n T0 step j k)))
          (subSeq (lemma34LeftSeqC P n T0 step j k)
                  (lemma34LeftSeqC P n T0 step j m)) :=
      regularSeqLe_of_left_eventual
        (absSeq_subSeq_comm_eventually _ _) habs_rev
    have hA :
        RegularSeqLe
          (subSeq (lemma34LeftSeqC P n T0 step j k)
                  (lemma34LeftSeqC P n T0 step j m))
          (subSeq (lemma34RightSeqC P n T0 step j M)
                  (lemma34LeftSeqC P n T0 step j m)) :=
      subSeq_monotone_left_regularSeqLe _ _ _
        (lemma34LeftSeq_le_rightSeqC P n T0 step j k M)
    have hB :
        RegularSeqLe
          (subSeq (lemma34RightSeqC P n T0 step j M)
                  (lemma34LeftSeqC P n T0 step j m))
          (subSeq (lemma34RightSeqC P n T0 step j M)
                  (lemma34LeftSeqC P n T0 step j M)) :=
      regularSeqLe_subSeq_right _ (lemma34LeftSeq_monoC P n T0 step j hm)
    exact regularSeqLe_trans habs
      (regularSeqLe_trans hA (regularSeqLe_trans hB hW))
  · have hkm_le : RegularSeqLe (lemma34LeftSeqC P n T0 step j k)
        (lemma34LeftSeqC P n T0 step j m) :=
      lemma34LeftSeq_monoC P n T0 step j hkm
    have hdiff_nonneg :
        RegularSeqLe zeroSeq
          (subSeq (lemma34LeftSeqC P n T0 step j m)
                  (lemma34LeftSeqC P n T0 step j k)) :=
      regularSeqLe_zero_of_nonneg hkm_le
    have habs :
        RegularSeqLe
          (absSeq (subSeq (lemma34LeftSeqC P n T0 step j m)
                          (lemma34LeftSeqC P n T0 step j k)))
          (subSeq (lemma34LeftSeqC P n T0 step j m)
                  (lemma34LeftSeqC P n T0 step j k)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have hA :
        RegularSeqLe
          (subSeq (lemma34LeftSeqC P n T0 step j m)
                  (lemma34LeftSeqC P n T0 step j k))
          (subSeq (lemma34RightSeqC P n T0 step j M)
                  (lemma34LeftSeqC P n T0 step j k)) :=
      subSeq_monotone_left_regularSeqLe _ _ _
        (lemma34LeftSeq_le_rightSeqC P n T0 step j m M)
    have hB :
        RegularSeqLe
          (subSeq (lemma34RightSeqC P n T0 step j M)
                  (lemma34LeftSeqC P n T0 step j k))
          (subSeq (lemma34RightSeqC P n T0 step j M)
                  (lemma34LeftSeqC P n T0 step j M)) :=
      regularSeqLe_subSeq_right _ (lemma34LeftSeq_monoC P n T0 step j hk)
    exact regularSeqLe_trans habs
      (regularSeqLe_trans hA (regularSeqLe_trans hB hW))

/-- Technical lemma used in the public import closure. -/
def posEventuallyData_halfPowC (g : Nat) : PosEventuallyData (halfPow g) :=
  ⟨g + 1, 0, fun _n _ => eps_succ_lt_eps g⟩

/-! ### §3 Lemma 3.4 CReal-native limit payload

Imported from `Mathdemo.ScratchLemma34CLimitPayload`, which built successfully
before BSP integration.  This block packages limit points of the CReal-native
tower and exposes their interval bounds.
-/

structure Lemma34LimitDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext }) where
  t : Fin n → CReal
  t_bounds : ∀ j : Fin n, RegularSeqLe a (t j) ∧ RegularSeqLe (t j) b
  left_le_t : ∀ j : Fin n, ∀ k : Nat,
    RegularSeqLe (lemma34LeftSeqC P n T0 step j k) (t j)
  t_le_right : ∀ j : Fin n, ∀ k : Nat,
    RegularSeqLe (t j) (lemma34RightSeqC P n T0 step j k)

/-- The selected limit points of the CReal-native Lemma 3.4 tower. -/
noncomputable def lemma34LimitPointsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step) :
    Fin n → CReal :=
  data.t

theorem lemma34LimitPoints_boundsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (j : Fin n) :
    RegularSeqLe a
      (lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step data j) ∧
      RegularSeqLe
        (lemma34LimitPointsC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step data j)
        b := by
  simpa [lemma34LimitPointsC] using data.t_bounds j

theorem lemma34LimitPoints_left_leC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (lemma34LeftSeqC P n T0 step j k)
      (lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step data j) := by
  simpa [lemma34LimitPointsC] using data.left_le_t j k

theorem lemma34LimitPoints_le_rightC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step data j)
      (lemma34RightSeqC P n T0 step j k) := by
  simpa [lemma34LimitPointsC] using data.t_le_right j k




/-! ### §3 Lemma 3.4 CReal-native result assembly from limit data

Imported from `Mathdemo.ScratchLemma34CResultFromLimit`, which built
successfully before BSP integration.  This block assembles `Lemma34ResultC`
from limit points and local witnesses.
-/

structure Lemma34LocalWitnessesC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) (t : Fin n → CReal) where
  local_at : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      Lemma34LocalC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n t beta

/-- Assemble the CReal-native Lemma 3.4 result from limit points and local
witnesses around those points.

The hard work left after this brick is to construct the local witnesses from
the tower/refinement argument.
-/
noncomputable def lemma34ResultC_of_limitLocalC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (localData : Lemma34LocalWitnessesC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n
      (lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step data)) :
    Lemma34ResultC (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { t :=
      lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step data
    t_bounds := by
      intro j
      exact lemma34LimitPoints_boundsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step data j
    local_prop := by
      intro beta hbeta
      exact localData.local_at beta hbeta }




/-! ### §3 Lemma 3.4 CReal-native construction data envelope

Imported from `Mathdemo.ScratchLemma34CConstructionData`, which built
successfully before BSP integration.  This block packages the full construction
data needed to assemble `Lemma34ResultC`.
-/

structure Lemma34ConstructionDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) where
  T0 : Lemma34TowerC
    (a := a) (b := b) (eps := eps) (hab := hab) P n 0
  step : ∀ k : Nat,
    (T : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
      { Tnext : Lemma34TowerC
          (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
        Lemma34RefinesC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n k T Tnext }
  limitData : Lemma34LimitDataC
    (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step
  localData : Lemma34LocalWitnessesC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n
      (lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step limitData)

/-- Assemble the result from complete construction data. -/
noncomputable def lemma34ResultC_of_constructionDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (data : Lemma34ConstructionDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34ResultC (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma34ResultC_of_limitLocalC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n data.T0 data.step data.limitData data.localData

/-- Lemma 3.4 envelope assuming the complete construction data.

The remaining hard work is to construct `Lemma34ConstructionDataC` from
`heps` and `h_cond`; this wrapper only fixes the final CReal-native API.
-/
noncomputable def lemma_3_4C_of_constructionDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (data : Lemma34ConstructionDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34ResultC (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma34ResultC_of_constructionDataC
    (a := a) (b := b) (eps := eps) (hab := hab) P n data




/-! ### §3 Lemma 3.4 CReal-native column refinement step

Imported from `Mathdemo.ScratchLemma34CColumnRefinement`, which built
successfully before BSP integration.  This block turns per-column refinement
certificates into one-step tower refinement data.
-/

structure Lemma34ColumnRefinementC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n k)
    (j : Fin n) where
  segL_next : CReal
  segR_next : CReal
  seg_proper_next :
    RegularSeqLe a segL_next ∧
      regularSeqLtProp segL_next segR_next ∧
      RegularSeqLe segR_next b
  seg_width_next :
    RegularSeqLe
      (CReal.sub segR_next segL_next)
      (lemma34WidthScaleC a b (k + 1))
  left_mono_next :
    RegularSeqLe (T.segL j) segL_next
  right_mono_next :
    RegularSeqLe segR_next (T.segR j)

/-- Build the next tower level from per-column refinement certificates. -/
noncomputable def lemma34TowerC_of_columnRefinementsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n k)
    (refine : ∀ j : Fin n,
      Lemma34ColumnRefinementC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k T j) :
    Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) :=
  { segL := fun j => (refine j).segL_next
    segR := fun j => (refine j).segR_next
    seg_proper := by
      intro j
      exact (refine j).seg_proper_next
    seg_width := by
      intro j
      exact (refine j).seg_width_next }

/-- The next tower level built from column refinements refines the current one. -/
noncomputable def lemma34RefinesC_of_columnRefinementsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n k)
    (refine : ∀ j : Fin n,
      Lemma34ColumnRefinementC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k T j) :
    Lemma34RefinesC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k T
      (lemma34TowerC_of_columnRefinementsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k T refine) :=
  { left_mono := by
      intro j
      exact (refine j).left_mono_next
    right_mono := by
      intro j
      exact (refine j).right_mono_next }

/-- Package the column-refinement construction as the one-step tower API. -/
noncomputable def lemma34StepC_of_columnRefinementsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n k)
    (refine : ∀ j : Fin n,
      Lemma34ColumnRefinementC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k T j) :
    { Tnext : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
      Lemma34RefinesC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k T Tnext } :=
  ⟨ lemma34TowerC_of_columnRefinementsC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k T refine,
    lemma34RefinesC_of_columnRefinementsC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k T refine ⟩




/-! ### §3 Lemma 3.4 CReal-native refinement family and tower-input assembly

Imported from `Mathdemo.ScratchLemma34CRefinementFamily`, which built
successfully before BSP integration.  This block packages a uniform family of
column refinements into tower-input data and the corresponding Lemma 3.4
envelope.
-/

structure Lemma34RefinementFamilyC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) where
  refine : ∀ k : Nat,
    (T : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
    ∀ j : Fin n,
      Lemma34ColumnRefinementC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k T j

/-- Turn a refinement family into the one-step tower API. -/
noncomputable def lemma34StepC_of_refinementFamilyC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (family : Lemma34RefinementFamilyC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
      { Tnext : Lemma34TowerC
          (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
        Lemma34RefinesC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n k T Tnext } :=
  fun k T =>
    lemma34StepC_of_columnRefinementsC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k T (family.refine k T)

/-- Complete tower-input data before final assembly into
`Lemma34ConstructionDataC`.

This separates the hard construction of `T0`, refinement certificates, limit
data, and local witnesses from the purely formal assembly layer.
-/
structure Lemma34TowerInputDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) where
  T0 : Lemma34TowerC
    (a := a) (b := b) (eps := eps) (hab := hab) P n 0
  refineFamily : Lemma34RefinementFamilyC
    (a := a) (b := b) (eps := eps) (hab := hab) P n
  limitData : Lemma34LimitDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0
      (lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n refineFamily)
  localData : Lemma34LocalWitnessesC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n
      (lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n refineFamily)
          limitData)

/-- Assemble `Lemma34ConstructionDataC` from tower-input data. -/
noncomputable def lemma34ConstructionDataC_of_towerInputDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (input : Lemma34TowerInputDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34ConstructionDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { T0 := input.T0
    step :=
      lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n input.refineFamily
    limitData := input.limitData
    localData := input.localData }

/-- Lemma 3.4 envelope from tower-input data. -/
noncomputable def lemma_3_4C_of_towerInputDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (input : Lemma34TowerInputDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_constructionDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P heps n h_cond
    (lemma34ConstructionDataC_of_towerInputDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n input)




/-! ### §3 Lemma 3.4 CReal-native construction frontier

Imported from `Mathdemo.ScratchLemma34CNativeConstructionFrontier`, which built
successfully before BSP integration.  This block identifies the remaining
native construction datum needed for the final Lemma 3.4 CReal result.
-/

structure Lemma34NativeConstructionDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) where
  input : Lemma34TowerInputDataC
    (a := a) (b := b) (eps := eps) (hab := hab) P n

/-- Extract tower-input data from the remaining native construction frontier. -/
noncomputable def lemma34TowerInputData_of_nativeConstructionDataC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (data : Lemma34NativeConstructionDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P heps n h_cond) :
    Lemma34TowerInputDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  data.input

/-- Lemma 3.4 from the remaining native construction frontier. -/
noncomputable def lemma_3_4C_of_nativeConstructionDataC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (data : Lemma34NativeConstructionDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P heps n h_cond) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_towerInputDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P heps n h_cond
    (lemma34TowerInputData_of_nativeConstructionDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P heps n h_cond data)




/-! ### §3 Lemma 3.4 CReal-native constructor frontier

Imported from `Mathdemo.ScratchLemma34CNativeConstructor`, which built
successfully before BSP integration.  This block packages the exact remaining
Goal B constructor object and its final Lemma 3.4 envelope.
-/

structure Lemma34NativeConstructorC : Type 2 where
  construct :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34NativeConstructionDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond

/-- Final Lemma 3.4 CReal result, assuming a global native constructor. -/
noncomputable def lemma_3_4C_of_nativeConstructorC
    (constructor : Lemma34NativeConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_nativeConstructionDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P heps n h_cond
    (constructor.construct P heps n h_cond)

/-- The exact remaining Goal B frontier: construct a `Lemma34NativeConstructorC`. -/
structure Lemma34GoalBFrontierC : Type 2 where
  constructor : Lemma34NativeConstructorC

/-- Final Lemma 3.4 CReal result from the Goal B frontier object. -/
noncomputable def lemma_3_4C_of_goalBFrontierC
    (frontier : Lemma34GoalBFrontierC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_nativeConstructorC
    frontier.constructor P heps n h_cond




/-! ### §3 Lemma 3.4 CReal-native P3-b local witness payload

Imported from `Mathdemo.ScratchLemma34CP3BPayload`, which built successfully
before BSP integration.  This block packages the CReal-native P3-b data needed
to build local witnesses from limit points.
-/

structure Lemma34TowerOutsideC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n k) where
  gamma : CReal
  gamma_pos : regularSeqLtProp zeroSeq gamma
  outside : ∀ t_pt : CReal,
    RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
        (∀ j : Fin n,
          regularSeqLtProp (T.segR j) t_pt ∨
            regularSeqLtProp t_pt (T.segL j)) →
          P.p_ltC
            (CReal.max a (CReal.sub t_pt gamma))
            (CReal.min b (CReal.add t_pt gamma))
            eps

/-- Choice of a tower level whose positionwise segment widths are below `beta`.

This abstracts the CReal-native analogue of the generic
`lemma34_widthScale_eventually_lt` step.
-/
structure Lemma34WidthChoiceC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (beta : CReal) where
  k : Nat
  width_lt : ∀ j : Fin n,
    regularSeqLtProp
      (CReal.sub
        ((lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step k).segR j)
        ((lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step k).segL j))
      beta

/-- Far-from-limit-points implies outside all level-`k` segments.

This is the CReal-native P3-b geometric criterion.  It is deliberately a
separate certificate: later bricks will prove it from interval nesting,
limit bounds, and the width choice.
-/
structure Lemma34FarOutsideFromLimitC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step) where
  far_outside : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      (choice : Lemma34WidthChoiceC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step beta) →
      ∀ t_pt : CReal,
        RegularSeqLe a t_pt →
          RegularSeqLe t_pt b →
            (∀ i : Fin n,
              regularSeqLtProp beta
                (CReal.abs
                  (CReal.sub t_pt
                    (lemma34LimitPointsC
                      (a := a) (b := b) (eps := eps) (hab := hab)
                      P n T0 step data i)))) →
            ∀ j : Fin n,
              regularSeqLtProp
                ((lemma34TowerSeqC
                  (a := a) (b := b) (eps := eps) (hab := hab)
                  P n T0 step choice.k).segR j)
                t_pt ∨
              regularSeqLtProp
                t_pt
                ((lemma34TowerSeqC
                  (a := a) (b := b) (eps := eps) (hab := hab)
                  P n T0 step choice.k).segL j)

/-- P3-b data sufficient to construct all local witnesses around the limit
points. -/
structure Lemma34P3BDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step) where
  widthChoice : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      Lemma34WidthChoiceC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step beta
  outsideAt : ∀ k : Nat,
    Lemma34TowerOutsideC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k
      (lemma34TowerSeqC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step k)
  farOutside : Lemma34FarOutsideFromLimitC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0 step data

/-- Construct local witnesses from CReal-native P3-b data. -/
noncomputable def lemma34LocalWitnessesC_of_p3bDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (p3b : Lemma34P3BDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step data) :
    Lemma34LocalWitnessesC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n
      (lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step data) :=
  { local_at := by
      intro beta hbeta
      let choice := p3b.widthChoice beta hbeta
      let outData := p3b.outsideAt choice.k
      refine
        { gamma := outData.gamma
          gamma_pos := outData.gamma_pos
          local_bound := ?_ }
      intro t_pt hat htb hfar
      exact outData.outside t_pt hat htb
        (p3b.farOutside.far_outside beta hbeta choice t_pt hat htb hfar) }




/-! ### §3 Lemma 3.4 CReal-native P3-b input assembly

Imported from `Mathdemo.ScratchLemma34CP3BInputAssembly`, which built
successfully before BSP integration.  This block assembles tower-input and
native-construction data from the CReal-native P3-b core payload.
-/

structure Lemma34P3BInputCoreC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) where
  T0 : Lemma34TowerC
    (a := a) (b := b) (eps := eps) (hab := hab) P n 0
  refineFamily : Lemma34RefinementFamilyC
    (a := a) (b := b) (eps := eps) (hab := hab) P n
  limitData : Lemma34LimitDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0
      (lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n refineFamily)
  p3bData : Lemma34P3BDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0
      (lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n refineFamily)
      limitData

/-- Assemble `Lemma34TowerInputDataC` from P3-b input core data. -/
noncomputable def lemma34TowerInputDataC_of_p3bInputCoreC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (core : Lemma34P3BInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34TowerInputDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { T0 := core.T0
    refineFamily := core.refineFamily
    limitData := core.limitData
    localData :=
      lemma34LocalWitnessesC_of_p3bDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n core.T0
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n core.refineFamily)
        core.limitData
        core.p3bData }

/-- Assemble native construction data from P3-b input core data. -/
noncomputable def lemma34NativeConstructionDataC_of_p3bInputCoreC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (core : Lemma34P3BInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34NativeConstructionDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P heps n h_cond :=
  { input :=
      lemma34TowerInputDataC_of_p3bInputCoreC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n core }

/-- Lemma 3.4 envelope from P3-b input core data. -/
noncomputable def lemma_3_4C_of_p3bInputCoreC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (core : Lemma34P3BInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_nativeConstructionDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P heps n h_cond
    (lemma34NativeConstructionDataC_of_p3bInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P heps n h_cond core)




/-! ### §3 Lemma 3.4 CReal-native P3-b core constructor frontier

Imported from `Mathdemo.ScratchLemma34CP3BCoreConstructor`, which built
successfully before BSP integration.  This block sharpens the remaining Goal B
frontier to construction of the P3-b input core.
-/

structure Lemma34P3BInputCoreConstructorC : Type 2 where
  construct :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34P3BInputCoreC
        (a := a) (b := b) (eps := eps) (hab := hab) P n

/-- Convert a P3-b input-core constructor into the previous native constructor. -/
noncomputable def lemma34NativeConstructorC_of_p3bInputCoreConstructorC
    (ctor : Lemma34P3BInputCoreConstructorC) :
    Lemma34NativeConstructorC :=
  { construct := by
      intro a b eps hab P heps n h_cond
      exact
        lemma34NativeConstructionDataC_of_p3bInputCoreC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P heps n h_cond
          (ctor.construct P heps n h_cond) }

/-- Final Lemma 3.4 CReal result from a P3-b input-core constructor. -/
noncomputable def lemma_3_4C_of_p3bInputCoreConstructorC
    (ctor : Lemma34P3BInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_nativeConstructorC
    (lemma34NativeConstructorC_of_p3bInputCoreConstructorC ctor)
    P heps n h_cond

/-- Sharpened Goal B frontier after isolating the P3-b input core. -/
structure Lemma34GoalBFrontierP3BC : Type 2 where
  constructor : Lemma34P3BInputCoreConstructorC

/-- Final Lemma 3.4 CReal result from the sharpened P3-b frontier. -/
noncomputable def lemma_3_4C_of_goalBFrontierP3BC
    (frontier : Lemma34GoalBFrontierP3BC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_p3bInputCoreConstructorC
    frontier.constructor P heps n h_cond




/-! ### §3 Lemma 3.4 CReal-native P3-b piecewise constructor frontier

Imported from `Mathdemo.ScratchLemma34CP3BPieceConstructor`, which built
successfully before BSP integration.  This block decomposes the sharpened
Goal B frontier into the four remaining construction pieces.
-/

structure Lemma34P3BInputCorePieceConstructorC : Type 2 where
  constructT0 :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n 0

  constructRefineFamily :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34RefinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab) P n

  constructLimitData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34LimitDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))

  constructP3BData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34P3BDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))
        (@constructLimitData a b eps hab P heps n h_cond)

/-- Assemble a fixed P3-b input core from the piecewise constructor. -/
noncomputable def lemma34P3BInputCoreC_of_pieceConstructorC
    (pieces : Lemma34P3BInputCorePieceConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34P3BInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { T0 := pieces.constructT0 P heps n h_cond
    refineFamily := pieces.constructRefineFamily P heps n h_cond
    limitData := pieces.constructLimitData P heps n h_cond
    p3bData := pieces.constructP3BData P heps n h_cond }

/-- Convert a piecewise constructor into the P3-b input-core constructor. -/
noncomputable def lemma34P3BInputCoreConstructorC_of_pieceConstructorC
    (pieces : Lemma34P3BInputCorePieceConstructorC) :
    Lemma34P3BInputCoreConstructorC :=
  { construct := by
      intro a b eps hab P heps n h_cond
      exact
        lemma34P3BInputCoreC_of_pieceConstructorC
          pieces P heps n h_cond }

/-- Final Lemma 3.4 CReal result from a piecewise P3-b constructor. -/
noncomputable def lemma_3_4C_of_p3bPieceConstructorC
    (pieces : Lemma34P3BInputCorePieceConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_p3bInputCoreConstructorC
    (lemma34P3BInputCoreConstructorC_of_pieceConstructorC pieces)
    P heps n h_cond




/-! ### §3 Lemma 3.4 CReal-native width choice from width scale

Imported from `Mathdemo.ScratchLemma34CWidthChoiceFromScale`, which built
successfully before BSP integration.  This block reduces P3-b width choice to
eventual smallness of the CReal-native width scale.
-/

structure Lemma34WidthScaleChoiceDataC {a b : CReal} where
  choose : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      { k : Nat // regularSeqLtProp (lemma34WidthScaleC a b k) beta }
  le_lt_trans : ∀ {x y z : CReal},
    RegularSeqLe x y →
      regularSeqLtProp y z →
        regularSeqLtProp x z

/-- Build the P3-b width choice from width-scale choice data. -/
noncomputable def lemma34WidthChoiceC_of_widthScaleChoiceDataC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (scaleChoice : Lemma34WidthScaleChoiceDataC (a := a) (b := b))
    (beta : CReal)
    (hbeta : regularSeqLtProp zeroSeq beta) :
    Lemma34WidthChoiceC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step beta :=
  let chosen := scaleChoice.choose beta hbeta
  { k := chosen.val
    width_lt := by
      intro j
      have hle :
          RegularSeqLe
            (CReal.sub
              ((lemma34TowerSeqC
                (a := a) (b := b) (eps := eps) (hab := hab)
                P n T0 step chosen.val).segR j)
              ((lemma34TowerSeqC
                (a := a) (b := b) (eps := eps) (hab := hab)
                P n T0 step chosen.val).segL j))
            (lemma34WidthScaleC a b chosen.val) := by
        simpa [lemma34LeftSeqC, lemma34RightSeqC] using
          lemma34TowerSeq_segment_widthC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n T0 step j chosen.val
      exact scaleChoice.le_lt_trans hle chosen.property }

/-- A reusable width-choice provider for every positive `beta`. -/
noncomputable def lemma34WidthChoiceProviderC_of_widthScaleChoiceDataC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (scaleChoice : Lemma34WidthScaleChoiceDataC (a := a) (b := b)) :
    ∀ beta : CReal,
      regularSeqLtProp zeroSeq beta →
        Lemma34WidthChoiceC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step beta :=
  fun beta hbeta =>
    lemma34WidthChoiceC_of_widthScaleChoiceDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step scaleChoice beta hbeta




/-! ### §3 Lemma 3.4 CReal-native P3-b data from split pieces

Imported from `Mathdemo.ScratchLemma34CP3BDataFromPieces`, which built
successfully before BSP integration.  This block decomposes the CReal-native
P3-b payload into width-scale choice, outside witnesses, and far-outside
geometry.
-/

structure Lemma34P3BPieceDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (limitData : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step) where
  scaleChoice : Lemma34WidthScaleChoiceDataC (a := a) (b := b)
  outsideAt : ∀ k : Nat,
    Lemma34TowerOutsideC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k
      (lemma34TowerSeqC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step k)
  farOutside : Lemma34FarOutsideFromLimitC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0 step limitData

/-- Assemble `Lemma34P3BDataC` from its three P3-b pieces. -/
noncomputable def lemma34P3BDataC_of_pieceDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (limitData : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (pieces : Lemma34P3BPieceDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData) :
    Lemma34P3BDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData :=
  { widthChoice :=
      lemma34WidthChoiceProviderC_of_widthScaleChoiceDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step pieces.scaleChoice
    outsideAt := pieces.outsideAt
    farOutside := pieces.farOutside }

/-- Core input data where P3-b itself is supplied in split piece form. -/
structure Lemma34P3BPieceInputCoreC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) where
  T0 : Lemma34TowerC
    (a := a) (b := b) (eps := eps) (hab := hab) P n 0
  refineFamily : Lemma34RefinementFamilyC
    (a := a) (b := b) (eps := eps) (hab := hab) P n
  limitData : Lemma34LimitDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0
      (lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n refineFamily)
  p3bPieces : Lemma34P3BPieceDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0
      (lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n refineFamily)
      limitData

/-- Assemble the P3-b input core from split P3-b pieces. -/
noncomputable def lemma34P3BInputCoreC_of_pieceInputCoreC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (core : Lemma34P3BPieceInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n) :
    Lemma34P3BInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { T0 := core.T0
    refineFamily := core.refineFamily
    limitData := core.limitData
    p3bData :=
      lemma34P3BDataC_of_pieceDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n core.T0
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n core.refineFamily)
        core.limitData
        core.p3bPieces }




/-! ### §3 Lemma 3.4 CReal-native six-piece P3-b constructor frontier

Imported from `Mathdemo.ScratchLemma34CP3BPieceInputCoreConstructor`, which built
successfully before BSP integration.  This block sharpens the remaining
frontier to six construction pieces: base tower, refinement family, limit data,
width-scale choice, outside witnesses, and far-outside geometry.
-/

structure Lemma34P3BPieceInputCoreConstructorC : Type 2 where
  constructT0 :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n 0

  constructRefineFamily :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34RefinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab) P n

  constructLimitData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34LimitDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))

  constructScaleChoice :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34WidthScaleChoiceDataC (a := a) (b := b)

  constructOutsideAt :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat),
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructT0 a b eps hab P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n
            (@constructRefineFamily a b eps hab P heps n h_cond))
          k)

  constructFarOutside :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34FarOutsideFromLimitC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))
        (@constructLimitData a b eps hab P heps n h_cond)

/-- Assemble split P3-b piece data from the six-piece constructor. -/
noncomputable def lemma34P3BPieceDataC_of_pieceInputCoreConstructorC
    (ctor : Lemma34P3BPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34P3BPieceDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n
      (ctor.constructT0 (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond)
      (lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (ctor.constructRefineFamily
          (a := a) (b := b) (eps := eps) (hab := hab)
          P heps n h_cond))
      (ctor.constructLimitData
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond) :=
  { scaleChoice :=
      ctor.constructScaleChoice
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    outsideAt := by
      intro k
      exact
        ctor.constructOutsideAt
          (a := a) (b := b) (eps := eps) (hab := hab)
          P heps n h_cond k
    farOutside :=
      ctor.constructFarOutside
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond }

/-- Assemble a P3-b piece input core from the six-piece constructor. -/
noncomputable def lemma34P3BPieceInputCoreC_of_pieceInputCoreConstructorC
    (ctor : Lemma34P3BPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34P3BPieceInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { T0 :=
      ctor.constructT0
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    refineFamily :=
      ctor.constructRefineFamily
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    limitData :=
      ctor.constructLimitData
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    p3bPieces :=
      lemma34P3BPieceDataC_of_pieceInputCoreConstructorC
        ctor P heps n h_cond }

/-- Convert the six-piece constructor into the P3-b input-core constructor. -/
noncomputable def lemma34P3BInputCoreConstructorC_of_pieceInputCoreConstructorC
    (ctor : Lemma34P3BPieceInputCoreConstructorC) :
    Lemma34P3BInputCoreConstructorC :=
  { construct := by
      intro a b eps hab P heps n h_cond
      exact
        lemma34P3BInputCoreC_of_pieceInputCoreC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34P3BPieceInputCoreC_of_pieceInputCoreConstructorC
            ctor P heps n h_cond) }

/-- Final Lemma 3.4 CReal result from the six-piece constructor. -/
noncomputable def lemma_3_4C_of_p3bPieceInputCoreConstructorC
    (ctor : Lemma34P3BPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_p3bInputCoreConstructorC
    (lemma34P3BInputCoreConstructorC_of_pieceInputCoreConstructorC ctor)
    P heps n h_cond




/-! ### §3 Lemma 3.4 CReal-native width-scale eventual smallness frontier

Imported from `Mathdemo.ScratchLemma34CWidthScaleEventualSmall`, which built
successfully before BSP integration.  This block reduces the width-choice part
of P3-b to eventual smallness of the CReal-native width scale.
-/

structure Lemma34WidthScaleEventualSmallC {a b : CReal} where
  choose : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      { k : Nat // regularSeqLtProp (lemma34WidthScaleC a b k) beta }

/-- Fill the order-composition field of `Lemma34WidthScaleChoiceDataC` from
the already live CReal order API.

After this, the only remaining data is the eventual-smallness chooser.
-/
noncomputable def lemma34WidthScaleChoiceDataC_of_eventualSmallC
    {a b : CReal}
    (eventual : Lemma34WidthScaleEventualSmallC (a := a) (b := b)) :
    Lemma34WidthScaleChoiceDataC (a := a) (b := b) :=
  { choose := eventual.choose
    le_lt_trans := by
      intro x y z hxy hyz
      exact regularSeqLtProp_of_le_of_lt hxy hyz }

/-- Width choice provider directly from eventual-smallness of the width scale. -/
noncomputable def lemma34WidthChoiceProviderC_of_eventualSmallC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (eventual : Lemma34WidthScaleEventualSmallC (a := a) (b := b)) :
    ∀ beta : CReal,
      regularSeqLtProp zeroSeq beta →
        Lemma34WidthChoiceC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step beta :=
  lemma34WidthChoiceProviderC_of_widthScaleChoiceDataC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0 step
    (lemma34WidthScaleChoiceDataC_of_eventualSmallC
      (a := a) (b := b) eventual)

/-- P3-b piece data where the width-choice field is supplied by eventual
smallness rather than the larger `Lemma34WidthScaleChoiceDataC`.
-/
structure Lemma34P3BPieceDataFromEventualC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (limitData : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step) where
  eventualSmall : Lemma34WidthScaleEventualSmallC (a := a) (b := b)
  outsideAt : ∀ k : Nat,
    Lemma34TowerOutsideC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k
      (lemma34TowerSeqC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step k)
  farOutside : Lemma34FarOutsideFromLimitC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0 step limitData

/-- Convert the eventual-smallness version of P3-b pieces to the previous
split P3-b piece data.
-/
noncomputable def lemma34P3BPieceDataC_of_eventualSmallPiecesC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (limitData : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (pieces : Lemma34P3BPieceDataFromEventualC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData) :
    Lemma34P3BPieceDataC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData :=
  { scaleChoice :=
      lemma34WidthScaleChoiceDataC_of_eventualSmallC
        (a := a) (b := b) pieces.eventualSmall
    outsideAt := pieces.outsideAt
    farOutside := pieces.farOutside }




/-! ### §3 Lemma 3.4 CReal-native eventual-smallness P3-b constructor frontier

Imported from `Mathdemo.ScratchLemma34CP3BEventualPieceConstructor`, which built
successfully before BSP integration.  This block sharpens the six-piece
frontier by replacing the width-scale-choice component with eventual
smallness of the CReal-native width scale.
-/

structure Lemma34P3BEventualPieceInputCoreConstructorC : Type 2 where
  constructT0 :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n 0

  constructRefineFamily :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34RefinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab) P n

  constructLimitData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34LimitDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))

  constructEventualSmall :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34WidthScaleEventualSmallC (a := a) (b := b)

  constructOutsideAt :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat),
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructT0 a b eps hab P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n
            (@constructRefineFamily a b eps hab P heps n h_cond))
          k)

  constructFarOutside :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34FarOutsideFromLimitC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))
        (@constructLimitData a b eps hab P heps n h_cond)

/-- Assemble eventual-smallness P3-b piece data from the sharpened constructor. -/
noncomputable def lemma34P3BPieceDataFromEventualC_of_eventualPieceConstructorC
    (ctor : Lemma34P3BEventualPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34P3BPieceDataFromEventualC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n
      (ctor.constructT0
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond)
      (lemma34StepC_of_refinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (ctor.constructRefineFamily
          (a := a) (b := b) (eps := eps) (hab := hab)
          P heps n h_cond))
      (ctor.constructLimitData
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond) :=
  { eventualSmall :=
      ctor.constructEventualSmall
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    outsideAt := by
      intro k
      exact
        ctor.constructOutsideAt
          (a := a) (b := b) (eps := eps) (hab := hab)
          P heps n h_cond k
    farOutside :=
      ctor.constructFarOutside
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond }

/-- Assemble a split P3-b input core from the eventual-smallness constructor. -/
noncomputable def lemma34P3BPieceInputCoreC_of_eventualPieceConstructorC
    (ctor : Lemma34P3BEventualPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34P3BPieceInputCoreC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { T0 :=
      ctor.constructT0
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    refineFamily :=
      ctor.constructRefineFamily
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    limitData :=
      ctor.constructLimitData
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond
    p3bPieces :=
      lemma34P3BPieceDataC_of_eventualSmallPiecesC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (ctor.constructT0
          (a := a) (b := b) (eps := eps) (hab := hab)
          P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (ctor.constructRefineFamily
            (a := a) (b := b) (eps := eps) (hab := hab)
            P heps n h_cond))
        (ctor.constructLimitData
          (a := a) (b := b) (eps := eps) (hab := hab)
          P heps n h_cond)
        (lemma34P3BPieceDataFromEventualC_of_eventualPieceConstructorC
          ctor P heps n h_cond) }

/-- Convert the eventual-smallness constructor into the P3-b input-core constructor. -/
noncomputable def lemma34P3BInputCoreConstructorC_of_eventualPieceConstructorC
    (ctor : Lemma34P3BEventualPieceInputCoreConstructorC) :
    Lemma34P3BInputCoreConstructorC :=
  { construct := by
      intro a b eps hab P heps n h_cond
      exact
        lemma34P3BInputCoreC_of_pieceInputCoreC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34P3BPieceInputCoreC_of_eventualPieceConstructorC
            ctor P heps n h_cond) }

/-- Final Lemma 3.4 CReal result from the eventual-smallness constructor. -/
noncomputable def lemma_3_4C_of_p3bEventualPieceConstructorC
    (ctor : Lemma34P3BEventualPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_p3bInputCoreConstructorC
    (lemma34P3BInputCoreConstructorC_of_eventualPieceConstructorC ctor)
    P heps n h_cond




/-! ### §3 Lemma 3.4 CReal-native width-scale from dyadic gauge

Imported from `Mathdemo.ScratchLemma34CWidthScaleFromDyadicGauge`, which built
successfully before BSP integration.  This block reduces width-scale eventual
smallness to a positive dyadic-gauge chooser.
-/

structure Lemma34PositiveDyadicGaugeChoiceC : Type 1 where
  choose : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      { j : Nat // regularSeqLtProp (halfPow j) beta }

/-- Absorb the coefficient `(b-a)` into a later dyadic scale.

Given a positive dyadic gauge chooser, the CReal-native width scale
`(b-a) * halfPow k` is eventually below every positive `beta`.
-/
noncomputable def lemma34WidthScaleEventualSmallC_of_positiveDyadicGaugeChoiceC
    (gauge : Lemma34PositiveDyadicGaugeChoiceC)
    {a b : CReal} :
    Lemma34WidthScaleEventualSmallC (a := a) (b := b) :=
  { choose := by
      intro beta hbeta
      let chosen := gauge.choose beta hbeta
      let k : Nat := chosen.val + CReal.mulArchBound (CReal.sub b a)
      refine ⟨k, ?_⟩
      have hbase :
          RegularSeqLe
            (CReal.mul (halfPow k) (CReal.sub b a))
            (halfPow chosen.val) := by
        simpa [k] using
          halfPow_mul_archBound_le (CReal.sub b a) chosen.val
      have hcomm :
          relEventually
            (CReal.mul (CReal.sub b a) (halfPow k))
            (CReal.mul (halfPow k) (CReal.sub b a)) :=
        CReal.mul_comm (CReal.sub b a) (halfPow k)
      have hle :
          RegularSeqLe
            (CReal.mul (CReal.sub b a) (halfPow k))
            (halfPow chosen.val) :=
        regularSeqLe_of_left_eventual hcomm hbase
      show regularSeqLtProp
        (lemma34WidthScaleC a b k) beta
      simpa [lemma34WidthScaleC] using
        regularSeqLtProp_of_le_of_lt hle chosen.property }

/-- The width-choice provider directly from the dyadic-gauge chooser. -/
noncomputable def lemma34WidthChoiceProviderC_of_positiveDyadicGaugeChoiceC
    (gauge : Lemma34PositiveDyadicGaugeChoiceC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext }) :
    ∀ beta : CReal,
      regularSeqLtProp zeroSeq beta →
        Lemma34WidthChoiceC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step beta :=
  lemma34WidthChoiceProviderC_of_eventualSmallC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0 step
    (lemma34WidthScaleEventualSmallC_of_positiveDyadicGaugeChoiceC
      gauge)

/-- P3-b piece data where the width part is supplied by the dyadic-gauge
chooser directly.
-/
structure Lemma34P3BPieceDataFromGaugeC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (limitData : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step) where
  gauge : Lemma34PositiveDyadicGaugeChoiceC
  outsideAt : ∀ k : Nat,
    Lemma34TowerOutsideC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n k
      (lemma34TowerSeqC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n T0 step k)
  farOutside : Lemma34FarOutsideFromLimitC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0 step limitData

/-- Convert dyadic-gauge P3-b pieces into eventual-smallness P3-b pieces. -/
noncomputable def lemma34P3BPieceDataFromEventualC_of_gaugePiecesC
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (limitData : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (pieces : Lemma34P3BPieceDataFromGaugeC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData) :
    Lemma34P3BPieceDataFromEventualC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData :=
  { eventualSmall :=
      lemma34WidthScaleEventualSmallC_of_positiveDyadicGaugeChoiceC
        pieces.gauge
    outsideAt := pieces.outsideAt
    farOutside := pieces.farOutside }




/-! ### §3 Lemma 3.4 CReal-native positive dyadic gauge from data positivity

Imported from `Mathdemo.ScratchLemma34CPositiveDyadicGaugeFromData`, which built
successfully before BSP integration.  This block closes the DATA-positive
dyadic gauge chooser and isolates the remaining Prop-to-DATA positivity bridge.
-/

structure Lemma34PositiveDyadicGaugeDataChoiceC : Type 1 where
  chooseData : ∀ beta : CReal,
    PosEventuallyData beta →
      { j : Nat // regularSeqLtProp (halfPow j) beta }

/-- Standard dyadic gauge chooser from DATA positivity. -/
noncomputable def lemma34PositiveDyadicGaugeDataChoiceC_standard :
    Lemma34PositiveDyadicGaugeDataChoiceC :=
  { chooseData := by
      intro beta hbeta
      let arch := regularSeqArchimedeanPositiveData hbeta
      refine ⟨arch.1, ?_⟩
      have hlt : regularSeqLtProp (constSeq (eps arch.1)) beta := by
        first
        | exact regularSeqLtData_to_prop _ _ arch.2
        | exact regularSeqLtData_to_prop arch.2
      first
      | simpa [halfPow] using hlt
      | exact hlt }

/-- Remaining Prop-to-DATA positivity bridge for the dyadic gauge chooser.

This is deliberately separated: the previous probe showed that the live API
does not provide a direct `regularSeqLtProp → PosEventuallyData` conversion.
-/
structure Lemma34PositiveDyadicGaugePropToDataC : Type 1 where
  toPosData : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      PosEventuallyData beta

/-- Build the full positive dyadic gauge chooser from the Prop-to-DATA bridge. -/
noncomputable def lemma34PositiveDyadicGaugeChoiceC_of_propToDataC
    (bridge : Lemma34PositiveDyadicGaugePropToDataC) :
    Lemma34PositiveDyadicGaugeChoiceC :=
  { choose := by
      intro beta hbeta
      exact
        lemma34PositiveDyadicGaugeDataChoiceC_standard.chooseData
          beta
          (bridge.toPosData beta hbeta) }

/-- Width-scale eventual smallness from the remaining Prop-to-DATA positivity
bridge.
-/
noncomputable def lemma34WidthScaleEventualSmallC_of_propToDataC
    (bridge : Lemma34PositiveDyadicGaugePropToDataC)
    {a b : CReal} :
    Lemma34WidthScaleEventualSmallC (a := a) (b := b) :=
  lemma34WidthScaleEventualSmallC_of_positiveDyadicGaugeChoiceC
    (lemma34PositiveDyadicGaugeChoiceC_of_propToDataC bridge)

/-- Gauge-piece P3-b data from the remaining Prop-to-DATA positivity bridge. -/
noncomputable def lemma34P3BPieceDataFromEventualC_of_propToDataGaugePiecesC
    (bridge : Lemma34PositiveDyadicGaugePropToDataC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (limitData : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (outsideAt : ∀ k : Nat,
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step k))
    (farOutside : Lemma34FarOutsideFromLimitC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData) :
    Lemma34P3BPieceDataFromEventualC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step limitData :=
  { eventualSmall :=
      lemma34WidthScaleEventualSmallC_of_propToDataC
        (a := a) (b := b) bridge
    outsideAt := outsideAt
    farOutside := farOutside }




/-! ### §3 Lemma 3.4 CReal-native Prop-to-DATA P3-b constructor frontier

Imported from `Mathdemo.ScratchLemma34CP3BPropToDataPieceConstructor`, which built
successfully before BSP integration.  This block sharpens the width component
to the single remaining Prop-to-DATA positivity bridge.
-/

structure Lemma34P3BPropToDataPieceInputCoreConstructorC : Type 2 where
  constructT0 :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n 0

  constructRefineFamily :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34RefinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab) P n

  constructLimitData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34LimitDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))

  constructPropToData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34PositiveDyadicGaugePropToDataC

  constructOutsideAt :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat),
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructT0 a b eps hab P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n
            (@constructRefineFamily a b eps hab P heps n h_cond))
          k)

  constructFarOutside :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34FarOutsideFromLimitC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (@constructT0 a b eps hab P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))
        (@constructLimitData a b eps hab P heps n h_cond)

/-- Convert the Prop-to-DATA piece constructor into the previous
eventual-smallness constructor.
-/
noncomputable def lemma34P3BEventualPieceInputCoreConstructorC_of_propToDataPieceConstructorC
    (ctor : Lemma34P3BPropToDataPieceInputCoreConstructorC) :
    Lemma34P3BEventualPieceInputCoreConstructorC :=
  { constructT0 := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructT0 P heps n h_cond
    constructRefineFamily := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructRefineFamily P heps n h_cond
    constructLimitData := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructLimitData P heps n h_cond
    constructEventualSmall := by
      intro a b eps hab P heps n h_cond
      exact
        lemma34WidthScaleEventualSmallC_of_propToDataC
          (a := a) (b := b)
          (ctor.constructPropToData P heps n h_cond)
    constructOutsideAt := by
      intro a b eps hab P heps n h_cond k
      exact ctor.constructOutsideAt P heps n h_cond k
    constructFarOutside := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructFarOutside P heps n h_cond }

/-- Final Lemma 3.4 CReal result from the Prop-to-DATA piece constructor. -/
noncomputable def lemma_3_4C_of_p3bPropToDataPieceConstructorC
    (ctor : Lemma34P3BPropToDataPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_p3bEventualPieceConstructorC
    (lemma34P3BEventualPieceInputCoreConstructorC_of_propToDataPieceConstructorC ctor)
    P heps n h_cond




/-! ### §3 Lemma 3.4 CReal-native direct base tower T0

Imported from `Mathdemo.ScratchLemma34CT0Direct`, which built successfully
before BSP integration.  This block closes the base tower `T0` component and
sharpens the remaining P3-b constructor frontier to the five non-T0 pieces.
-/

noncomputable def lemma34T0C_direct
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34TowerC
      (a := a) (b := b) (eps := eps) (hab := hab) P n 0 :=
  { segL := fun _ => a
    segR := fun _ => b
    seg_proper := by
      intro j
      refine ⟨?_, ?_, ?_⟩
      · first
        | exact regularSeqLe_refl a
        | exact regularSeqLe_refl
      · exact hab
      · first
        | exact regularSeqLe_refl b
        | exact regularSeqLe_refl
    seg_width := by
      intro j
      have hrefl : RegularSeqLe (CReal.sub b a) (CReal.sub b a) := by
        first
        | exact regularSeqLe_refl (CReal.sub b a)
        | exact regularSeqLe_refl
      -- `halfPow 0` is the CReal dyadic unit.  Transport the reflexive
      -- width bound across multiplication by that unit.
      first
      | simpa [lemma34WidthScaleC, halfPow] using hrefl
      | have hmul :
            relEventually
              (CReal.mul (CReal.sub b a) (halfPow 0))
              (CReal.sub b a) := by
            simpa [halfPow] using CReal.mul_one (CReal.sub b a)
        have hsymm :
            relEventually
              (CReal.sub b a)
              (CReal.mul (CReal.sub b a) (halfPow 0)) :=
          relEventually_symm
            (CReal.mul (CReal.sub b a) (halfPow 0))
            (CReal.sub b a)
            hmul
        have hrefl_mul :
            RegularSeqLe
              (CReal.mul (CReal.sub b a) (halfPow 0))
              (CReal.mul (CReal.sub b a) (halfPow 0)) := by
          first
          | exact regularSeqLe_refl (CReal.mul (CReal.sub b a) (halfPow 0))
          | exact regularSeqLe_refl
        have hle :
            RegularSeqLe
              (CReal.sub b a)
              (CReal.mul (CReal.sub b a) (halfPow 0)) :=
          regularSeqLe_of_left_eventual hsymm hrefl_mul
        simpa [lemma34WidthScaleC] using hle }

/-- Base tower outside witness, matching the source proof's initial
`F_1 = {[a,b]}` case.  The positivity assumption on `n` is essential:
with no segment (`n=0`) the outside premise is vacuous. -/
noncomputable def lemma34T0OutsideC_direct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34TowerOutsideC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n 0
      (lemma34T0C_direct
        (a := a) (b := b) (eps := eps) (hab := hab)
        P heps n h_cond) :=
  { gamma := CReal.one
    gamma_pos := CReal.one_pos_E
    outside := by
      intro t_pt hat htb hout
      let j0 : Fin n := ⟨0, hn⟩
      have hseg := hout j0
      have hFalse : False := by
        rcases hseg with hbt | hta
        · exact regularSeqLe_not_lt_reverse_prop htb hbt
        · exact regularSeqLe_not_lt_reverse_prop hat hta
      exact False.elim hFalse }

/-- P3-b constructor with the T0 field removed, since T0 is now direct. -/
structure Lemma34P3BNoT0PieceInputCoreConstructorC : Type 2 where
  constructRefineFamily :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34RefinementFamilyC
        (a := a) (b := b) (eps := eps) (hab := hab) P n

  constructLimitData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34LimitDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (lemma34T0C_direct P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))

  constructPropToData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34PositiveDyadicGaugePropToDataC

  constructOutsideAt :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat),
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34T0C_direct P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n
            (@constructRefineFamily a b eps hab P heps n h_cond))
          k)

  constructFarOutside :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34FarOutsideFromLimitC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (lemma34T0C_direct P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (@constructRefineFamily a b eps hab P heps n h_cond))
        (@constructLimitData a b eps hab P heps n h_cond)

/-- Reinsert the direct T0 into the previous Prop-to-DATA constructor interface. -/
noncomputable def lemma34P3BPropToDataPieceInputCoreConstructorC_of_noT0ConstructorC
    (ctor : Lemma34P3BNoT0PieceInputCoreConstructorC) :
    Lemma34P3BPropToDataPieceInputCoreConstructorC :=
  { constructT0 := by
      intro a b eps hab P heps n h_cond
      exact lemma34T0C_direct P heps n h_cond
    constructRefineFamily := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructRefineFamily P heps n h_cond
    constructLimitData := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructLimitData P heps n h_cond
    constructPropToData := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructPropToData P heps n h_cond
    constructOutsideAt := by
      intro a b eps hab P heps n h_cond k
      exact ctor.constructOutsideAt P heps n h_cond k
    constructFarOutside := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructFarOutside P heps n h_cond }

/-- Final Lemma 3.4 CReal result from the no-T0 constructor. -/
noncomputable def lemma_3_4C_of_p3bNoT0PieceConstructorC
    (ctor : Lemma34P3BNoT0PieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_p3bPropToDataPieceConstructorC
    (lemma34P3BPropToDataPieceInputCoreConstructorC_of_noT0ConstructorC ctor)
    P heps n h_cond




/-! ### §3 Lemma 3.4 CReal-native refinement family from column provider

Imported from `Mathdemo.ScratchLemma34CRefinementFamilyFromColumnProvider`,
which built successfully before BSP integration.  This block reduces the
refinement-family component to a uniform one-column refinement provider.
-/

structure Lemma34ColumnRefinementProviderC : Type 2 where
  refine :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat)
      (T : Lemma34TowerC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k)
      (j : Fin n),
      Lemma34ColumnRefinementC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k T j

/-- Bundle the one-column refinement provider into a refinement family. -/
noncomputable def lemma34RefinementFamilyC_of_columnRefinementProviderC
    (provider : Lemma34ColumnRefinementProviderC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34RefinementFamilyC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { refine := by
      intro k T j
      exact provider.refine P heps n h_cond k T j }

/-- No-T0/no-refineFamily constructor frontier.

After this assembly, `refineFamily` itself is no longer a separate task:
the remaining refinement obstruction is exactly `Lemma34ColumnRefinementProviderC`.
-/
structure Lemma34P3BNoT0NoRefineFamilyPieceInputCoreConstructorC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC

  constructLimitData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34LimitDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (lemma34T0C_direct P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34RefinementFamilyC_of_columnRefinementProviderC
            (a := a) (b := b) (eps := eps) (hab := hab)
            columnProvider P heps n h_cond))

  constructPropToData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34PositiveDyadicGaugePropToDataC

  constructOutsideAt :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat),
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34T0C_direct P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n
            (lemma34RefinementFamilyC_of_columnRefinementProviderC
              (a := a) (b := b) (eps := eps) (hab := hab)
              columnProvider P heps n h_cond))
          k)

  constructFarOutside :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34FarOutsideFromLimitC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (lemma34T0C_direct P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34RefinementFamilyC_of_columnRefinementProviderC
            (a := a) (b := b) (eps := eps) (hab := hab)
            columnProvider P heps n h_cond))
        (@constructLimitData a b eps hab P heps n h_cond)

/-- Reinsert the refinement family constructed from the column provider. -/
noncomputable def lemma34P3BNoT0PieceInputCoreConstructorC_of_noRefineFamilyConstructorC
    (ctor : Lemma34P3BNoT0NoRefineFamilyPieceInputCoreConstructorC) :
    Lemma34P3BNoT0PieceInputCoreConstructorC :=
  { constructRefineFamily := by
      intro a b eps hab P heps n h_cond
      exact
        lemma34RefinementFamilyC_of_columnRefinementProviderC
          (a := a) (b := b) (eps := eps) (hab := hab)
          ctor.columnProvider P heps n h_cond
    constructLimitData := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructLimitData P heps n h_cond
    constructPropToData := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructPropToData P heps n h_cond
    constructOutsideAt := by
      intro a b eps hab P heps n h_cond k
      exact ctor.constructOutsideAt P heps n h_cond k
    constructFarOutside := by
      intro a b eps hab P heps n h_cond
      exact ctor.constructFarOutside P heps n h_cond }

/-- Final Lemma 3.4 CReal result from the no-refineFamily constructor. -/
noncomputable def lemma_3_4C_of_p3bNoRefineFamilyPieceConstructorC
    (ctor : Lemma34P3BNoT0NoRefineFamilyPieceInputCoreConstructorC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma_3_4C_of_p3bNoT0PieceConstructorC
    (lemma34P3BNoT0PieceInputCoreConstructorC_of_noRefineFamilyConstructorC ctor)
    P heps n h_cond




/-! Technical auxiliary material for the public import closure. -/

/-- DATA-beta unconditional width-scale eventual smallness chooser.
The gauge comes DIRECTLY from DATA positivity, so NO frontier is needed. -/
noncomputable def lemma34WidthScaleEventualSmallDataC_standard {a b : CReal} :
    ∀ beta : CReal, PosEventuallyData beta →
      { k : Nat // regularSeqLtProp (lemma34WidthScaleC a b k) beta } := by
  intro beta hdata
  let chosen := lemma34PositiveDyadicGaugeDataChoiceC_standard.chooseData beta hdata
  let k : Nat := chosen.val + CReal.mulArchBound (CReal.sub b a)
  refine ⟨k, ?_⟩
  have hbase :
      RegularSeqLe
        (CReal.mul (halfPow k) (CReal.sub b a))
        (halfPow chosen.val) := by
    simpa [k] using
      halfPow_mul_archBound_le (CReal.sub b a) chosen.val
  have hcomm :
      relEventually
        (CReal.mul (CReal.sub b a) (halfPow k))
        (CReal.mul (halfPow k) (CReal.sub b a)) :=
    CReal.mul_comm (CReal.sub b a) (halfPow k)
  have hle :
      RegularSeqLe
        (CReal.mul (CReal.sub b a) (halfPow k))
        (halfPow chosen.val) :=
    regularSeqLe_of_left_eventual hcomm hbase
  change regularSeqLtProp (lemma34WidthScaleC a b k) beta
  simpa [lemma34WidthScaleC] using
    regularSeqLtProp_of_le_of_lt hle chosen.property

/-- Technical lemma used in the public import closure. -/
noncomputable def lemma34LeftSeqCauchyDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) :
    CRealRepSequenceCauchyData
      (fun k => lemma34LeftSeqC P n T0 step j k) :=
  { cmod := fun g =>
      (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
        (halfPow g) (posEventuallyData_halfPowC g)).val
    close_eventually := fun g m₂ n₂ hm hn => by
      have hK :
          regularSeqLtProp
            (lemma34WidthScaleC a b
              (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
                (halfPow g) (posEventuallyData_halfPowC g)).val)
            (halfPow g) :=
        (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
          (halfPow g) (posEventuallyData_halfPowC g)).property
      have hcm :
          RegularSeqLe
            (absSeq (subSeq (lemma34LeftSeqC P n T0 step j m₂)
                            (lemma34LeftSeqC P n T0 step j n₂)))
            (lemma34WidthScaleC a b
              (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
                (halfPow g) (posEventuallyData_halfPowC g)).val) :=
        lemma34LeftSeq_absSub_le_widthC P n T0 step j _ m₂ n₂ hm hn
      have hlt :
          regularSeqLtProp
            (absSeq (subSeq (lemma34LeftSeqC P n T0 step j m₂)
                            (lemma34LeftSeqC P n T0 step j n₂)))
            (halfPow g) :=
        regularSeqLtProp_of_le_of_lt hcm hK
      exact repCloseAtGauge_of_absGap _ _ g hlt }

/-- Rep-carrying limit of the tower's left-endpoint sequence (choice-free). -/
noncomputable def lemma34LimitReprC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (j : Fin n) :
    CRealRepLimitData (fun k => lemma34LeftSeqC P n T0 step j k) :=
  CReal.complete_repCarrying_data _ (lemma34LeftSeqCauchyDataC P n T0 step j)

/-- Generic construction of the limit-data record for the Lemma 3.4 tower, for
ANY `T0`/`step`.  This is what `Lemma34DataFrontierC.constructLimitData`
specializes to.  Choice-free. -/
noncomputable def lemma34LimitDataC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext }) :
    Lemma34LimitDataC (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step :=
  { t := fun j => (lemma34LimitReprC P n T0 step j).limit
    t_bounds := fun j =>
      ⟨ repLimitData_ge_of_eventually_ge (lemma34LimitReprC P n T0 step j) a 0
          (fun m _ => (lemma34TowerSeq_seg_properC P n T0 step j m).1),
        repLimitData_le_of_eventually_le (lemma34LimitReprC P n T0 step j) b 0
          (fun m _ => regularSeqLe_trans
            (lemma34LeftSeq_le_rightSeqC P n T0 step j m 0)
            (lemma34TowerSeq_seg_properC P n T0 step j 0).2.2) ⟩
    left_le_t := fun j k₀ =>
      repLimitData_ge_of_eventually_ge (lemma34LimitReprC P n T0 step j)
        (lemma34LeftSeqC P n T0 step j k₀) k₀
        (fun _m hm => lemma34LeftSeq_monoC P n T0 step j hm)
    t_le_right := fun j k₀ =>
      repLimitData_le_of_eventually_le (lemma34LimitReprC P n T0 step j)
        (lemma34RightSeqC P n T0 step j k₀) 0
        (fun m _ => lemma34LeftSeq_le_rightSeqC P n T0 step j m k₀) }

/-- Algebraic eventual equality `z + (x - z) ≈ x`, used to cancel the common
right endpoint in strict inequalities. -/
theorem add_sub_cancel_right_eventualC (x z : CReal) :
    CReal.add z (CReal.sub x z) ≈ x := by
  have hq : mkQuot (CReal.add z (CReal.sub x z)) = mkQuot x := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (mkQuot z) + ((mkQuot x) - (mkQuot z)) = mkQuot x
    ring
  exact Quotient.exact hq

/-- Algebraic eventual equality `-(z) + (z - y) ≈ -y`. -/
theorem neg_add_sub_left_eventualC (z y : CReal) :
    CReal.add (CReal.neg z) (CReal.sub z y) ≈ CReal.neg y := by
  have hq :
      mkQuot (CReal.add (CReal.neg z) (CReal.sub z y)) =
        mkQuot (CReal.neg y) := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (-(mkQuot z)) + ((mkQuot z) - (mkQuot y)) = -(mkQuot y)
    ring
  exact Quotient.exact hq

/-- Algebraic eventual equality `(x + y) + (-y) ≈ x`. -/
theorem add_add_neg_right_eventualC (x y : CReal) :
    CReal.add (CReal.add x y) (CReal.neg y) ≈ x := by
  have hq :
      mkQuot (CReal.add (CReal.add x y) (CReal.neg y)) = mkQuot x := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change ((mkQuot x) + (mkQuot y)) + (-(mkQuot y)) = mkQuot x
    ring
  exact Quotient.exact hq

/-- Algebraic eventual equality `(x + y) + (-x) ≈ y`. -/
theorem add_add_neg_left_eventualC (x y : CReal) :
    CReal.add (CReal.add x y) (CReal.neg x) ≈ y := by
  have hq :
      mkQuot (CReal.add (CReal.add x y) (CReal.neg x)) = mkQuot y := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change ((mkQuot x) + (mkQuot y)) + (-(mkQuot x)) = mkQuot y
    ring
  exact Quotient.exact hq

/-- Algebraic eventual equality `-(x-y) ≈ y-x`. -/
theorem neg_sub_eventualC (x y : CReal) :
    CReal.neg (CReal.sub x y) ≈ CReal.sub y x := by
  have hq :
      mkQuot (CReal.neg (CReal.sub x y)) = mkQuot (CReal.sub y x) := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (-((mkQuot x) - (mkQuot y))) = (mkQuot y) - (mkQuot x)
    ring
  exact Quotient.exact hq

/-- Strict cancellation of a common right-subtracted term:
`x-z < y-z → x < y`. -/
theorem regularSeqLtProp_add_sub_cancel_rightC {x y z : CReal}
    (h : regularSeqLtProp (CReal.sub x z) (CReal.sub y z)) :
    regularSeqLtProp x y := by
  have hadd :
      regularSeqLtProp
        (CReal.add z (CReal.sub x z))
        (CReal.add z (CReal.sub y z)) :=
    regularSeqLtProp_add_left z (CReal.sub x z) (CReal.sub y z) h
  have hleft :
      regularSeqLtProp x (CReal.add z (CReal.sub y z)) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (add_sub_cancel_right_eventualC x z)) hadd
  exact regularSeqLtProp_of_right_eventual
    (add_sub_cancel_right_eventualC y z) hleft

/-- Strict cancellation for a common left minuend:
`z-y < z-x → x < y`. -/
theorem regularSeqLtProp_sub_left_cancel_revC {x y z : CReal}
    (h : regularSeqLtProp (CReal.sub z y) (CReal.sub z x)) :
    regularSeqLtProp x y := by
  have hneg_raw :
      regularSeqLtProp
        (CReal.add (CReal.neg z) (CReal.sub z y))
        (CReal.add (CReal.neg z) (CReal.sub z x)) :=
    regularSeqLtProp_add_left (CReal.neg z)
      (CReal.sub z y) (CReal.sub z x) h
  have hneg_left :
      regularSeqLtProp (CReal.neg y)
        (CReal.add (CReal.neg z) (CReal.sub z x)) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (neg_add_sub_left_eventualC z y)) hneg_raw
  have hneg :
      regularSeqLtProp (CReal.neg y) (CReal.neg x) :=
    regularSeqLtProp_of_right_eventual
      (neg_add_sub_left_eventualC z x) hneg_left
  have hadd :
      regularSeqLtProp
        (CReal.add (CReal.add x y) (CReal.neg y))
        (CReal.add (CReal.add x y) (CReal.neg x)) :=
    regularSeqLtProp_add_left (CReal.add x y)
      (CReal.neg y) (CReal.neg x) hneg
  have hleft :
      regularSeqLtProp x
        (CReal.add (CReal.add x y) (CReal.neg x)) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (add_add_neg_right_eventualC x y)) hadd
  exact regularSeqLtProp_of_right_eventual
    (add_add_neg_left_eventualC x y) hleft

/-- Generic construction of the `far_outside` geometry from limit data.

This is the final paragraph of source Lemma 3.4 in CReal-native form: once a
tower level has width below `beta`, a point whose distance from every limit
point is above `beta` cannot lie in any level-`k` segment. -/
noncomputable def lemma34FarOutsideFromLimitC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step) :
    Lemma34FarOutsideFromLimitC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step data :=
  { far_outside := by
      intro beta hbeta choice t_pt _hat _htb hfar j
      let Tseq :=
        lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step choice.k
      let L : CReal := Tseq.segL j
      let R : CReal := Tseq.segR j
      let tj : CReal :=
        lemma34LimitPointsC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n T0 step data j
      have hL_t : RegularSeqLe L tj := by
        simpa [L, tj, Tseq, lemma34LeftSeqC, lemma34LimitPointsC] using
          data.left_le_t j choice.k
      have ht_R : RegularSeqLe tj R := by
        simpa [R, tj, Tseq, lemma34RightSeqC, lemma34LimitPointsC] using
          data.t_le_right j choice.k
      have hwidth : regularSeqLtProp (CReal.sub R L) beta := by
        simpa [R, L, Tseq] using choice.width_lt j
      have hfarj :
          regularSeqLtProp beta (CReal.abs (CReal.sub t_pt tj)) := by
        simpa [tj] using hfar j
      rcases regularSeqLtProp_abs_split hbeta hfarj with hright | hleft
      · left
        have hRt_le_width : RegularSeqLe (CReal.sub R tj) (CReal.sub R L) :=
          regularSeqLe_sub_leftC (a := L) (b := tj) (c := R) hL_t
        have hRt_lt_beta : regularSeqLtProp (CReal.sub R tj) beta :=
          regularSeqLtProp_of_le_of_lt hRt_le_width hwidth
        have hRt_lt_tpt :
            regularSeqLtProp (CReal.sub R tj) (CReal.sub t_pt tj) :=
          regularSeqLtProp_trans (CReal.sub R tj) beta (CReal.sub t_pt tj)
            hRt_lt_beta hright
        have hR_tpt : regularSeqLtProp R t_pt :=
          regularSeqLtProp_add_sub_cancel_rightC hRt_lt_tpt
        simpa [R, Tseq] using hR_tpt
      · right
        have htL_le_width : RegularSeqLe (CReal.sub tj L) (CReal.sub R L) := by
          change RegularSeqLe (subSeq tj L) (subSeq R L)
          exact subSeq_monotone_left_regularSeqLe tj R L ht_R
        have htL_lt_beta : regularSeqLtProp (CReal.sub tj L) beta :=
          regularSeqLtProp_of_le_of_lt htL_le_width hwidth
        have hleft_sub : regularSeqLtProp beta (CReal.sub tj t_pt) :=
          regularSeqLtProp_of_right_eventual (neg_sub_eventualC t_pt tj) hleft
        have htL_lt_tpt :
            regularSeqLtProp (CReal.sub tj L) (CReal.sub tj t_pt) :=
          regularSeqLtProp_trans (CReal.sub tj L) beta (CReal.sub tj t_pt)
            htL_lt_beta hleft_sub
        have htpt_L : regularSeqLtProp t_pt L :=
          regularSeqLtProp_sub_left_cancel_revC htL_lt_tpt
        simpa [L, Tseq] using htpt_L }

/-- DATA positivity refines the Prop strict order `0 < x` used by `far_outside`.
`regularSeqLtProp zeroSeq x = PosEventually (subSeq x zeroSeq)`, and
`subSeq x zeroSeq ≈ x`, so this is the harmless DATA→Prop direction. -/
theorem regularSeqLtProp_zero_of_posEventuallyData {x : RegularSeq}
    (h : PosEventuallyData x) : regularSeqLtProp zeroSeq x :=
  posEventually_respects x (subSeq x zeroSeq)
    (relEventually_symm (subSeq x zeroSeq) x (subSeq_zero_right_eventually x))
    h.toProp

/-- DATA-beta width-choice provider, built from the beta-free tower geometry
(`T0`, `step`) and the unconditional DATA width chooser.  NO frontier. -/
noncomputable def lemma34WidthChoiceProviderDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab) P n k T Tnext }) :
    ∀ beta : CReal, PosEventuallyData beta →
      Lemma34WidthChoiceC
        (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step beta :=
  fun beta hdata =>
    let ch := lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b) beta hdata
    { k := ch.val
      width_lt := fun j =>
        regularSeqLtProp_of_le_of_lt
          ((lemma34TowerSeqC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n T0 step ch.val).seg_width j)
          ch.property }

/-- CReal-native DATA-beta result object for Lemma 3.4.

Same as `Lemma34ResultC` but the local witnesses are indexed by DATA
positivity `PosEventuallyData beta`, which the CReal port supplies choice-free. -/
structure Lemma34ResultDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) where
  t : Fin n → CReal
  t_bounds : ∀ i : Fin n, RegularSeqLe a (t i) ∧ RegularSeqLe (t i) b
  local_data : ∀ beta : CReal, PosEventuallyData beta →
    Lemma34LocalC (a := a) (b := b) (eps := eps) (hab := hab) P n t beta

/-- Build the DATA-beta Lemma 3.4 result from the beta-free geometry
(`T0`, `step`, `data`, `outsideAt`, `farOutside`).  This does NOT use
`constructPropToData`: the gauge is supplied by `lemma34WidthChoiceProviderDataC`,
and `far_outside` receives its `0 < beta` from the DATA→Prop bridge. -/
noncomputable def lemma34ResultDataC_of_limitOutsideC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (T0 : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n 0)
    (step : ∀ k : Nat,
      (T : Lemma34TowerC (a := a) (b := b) (eps := eps) (hab := hab) P n k) →
        { Tnext : Lemma34TowerC
            (a := a) (b := b) (eps := eps) (hab := hab) P n (k + 1) //
          Lemma34RefinesC
            (a := a) (b := b) (eps := eps) (hab := hab) P n k T Tnext })
    (data : Lemma34LimitDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step)
    (outsideAt : ∀ k : Nat,
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab) P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step k))
    (farOutside : Lemma34FarOutsideFromLimitC
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step data) :
    Lemma34ResultDataC (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  { t :=
      lemma34LimitPointsC
        (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step data
    t_bounds := fun j =>
      lemma34LimitPoints_boundsC
        (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step data j
    local_data := fun beta hdata =>
      let choice :=
        lemma34WidthChoiceProviderDataC
          (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step beta hdata
      let outData := outsideAt choice.k
      { gamma := outData.gamma
        gamma_pos := outData.gamma_pos
        local_bound := fun t_pt hat htb hfar =>
          outData.outside t_pt hat htb
            (farOutside.far_outside beta
              (regularSeqLtProp_zero_of_posEventuallyData hdata)
              choice t_pt hat htb hfar) } }

/-! ### §3 Lemma 3.4 DATA-beta frontier and reducer

DATA-beta counterpart of `Lemma34P3BNoT0NoRefineFamilyPieceInputCoreConstructorC`
(BSP §3), dropping `constructPropToData` and producing `Lemma34ResultDataC`.
The Prop→DATA obstruction disappears: the gauge is supplied by
`lemma34ResultDataC_of_limitOutsideC` from the beta-free geometry only.
-/

/-- DATA-beta frontier for Lemma 3.4: the four beta-free construction pieces,
with NO `constructPropToData`. -/
structure Lemma34DataFrontierC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC

  constructLimitData :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34LimitDataC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (lemma34T0C_direct P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34RefinementFamilyC_of_columnRefinementProviderC
            (a := a) (b := b) (eps := eps) (hab := hab)
            columnProvider P heps n h_cond))

  constructOutsideAt :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat),
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34T0C_direct P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n
            (lemma34RefinementFamilyC_of_columnRefinementProviderC
              (a := a) (b := b) (eps := eps) (hab := hab)
              columnProvider P heps n h_cond))
          k)

  constructFarOutside :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps)),
      Lemma34FarOutsideFromLimitC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n
        (lemma34T0C_direct P heps n h_cond)
        (lemma34StepC_of_refinementFamilyC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34RefinementFamilyC_of_columnRefinementProviderC
            (a := a) (b := b) (eps := eps) (hab := hab)
            columnProvider P heps n h_cond))
        (@constructLimitData a b eps hab P heps n h_cond)

/-- Final DATA-beta Lemma 3.4 result from the DATA frontier.
No Prop→DATA obstruction: the gauge comes from `lemma34ResultDataC_of_limitOutsideC`. -/
noncomputable def lemma_3_4DataC_of_dataFrontierC
    (ctor : Lemma34DataFrontierC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  lemma34ResultDataC_of_limitOutsideC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n
    (lemma34T0C_direct P heps n h_cond)
    (lemma34StepC_of_refinementFamilyC
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n
      (lemma34RefinementFamilyC_of_columnRefinementProviderC
        (a := a) (b := b) (eps := eps) (hab := hab)
        ctor.columnProvider P heps n h_cond))
    (ctor.constructLimitData P heps n h_cond)
    (fun k => ctor.constructOutsideAt P heps n h_cond k)
    (ctor.constructFarOutside P heps n h_cond)

/-- Reduced DATA-beta frontier for Lemma 3.4 after landing the generic
`constructLimitData` and `constructFarOutside` bricks.

Remaining honest work:
* `columnProvider`: the counting-layer producer.
* `constructOutsideAt`: the source proof's P2b-beta `sigma/outside` clause.
-/
structure Lemma34DataFrontierRemainingC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC

  constructOutsideAt :
    ∀ {a b eps : CReal}
      {hab : regularSeqLtProp a b}
      (P : ProfileC a b hab)
      (heps : regularSeqLtProp zeroSeq eps)
      (n : Nat)
      (h_cond :
        regularSeqLtProp
          (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
          (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
      (k : Nat),
      Lemma34TowerOutsideC
        (a := a) (b := b) (eps := eps) (hab := hab)
        P n k
        (lemma34TowerSeqC
          (a := a) (b := b) (eps := eps) (hab := hab)
          P n
          (lemma34T0C_direct P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC
            (a := a) (b := b) (eps := eps) (hab := hab)
            P n
            (lemma34RefinementFamilyC_of_columnRefinementProviderC
              (a := a) (b := b) (eps := eps) (hab := hab)
              columnProvider P heps n h_cond))
          k)

/-- Final DATA-beta Lemma 3.4 result from the reduced remaining frontier.
The two generic pieces are supplied by `lemma34LimitDataC_construct` and
`lemma34FarOutsideFromLimitC_construct`. -/
noncomputable def lemma_3_4DataC_of_remainingFrontierC
    (ctor : Lemma34DataFrontierRemainingC)
    {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC
      (a := a) (b := b) (eps := eps) (hab := hab) P n :=
  let T0 :=
    lemma34T0C_direct
      (a := a) (b := b) (eps := eps) (hab := hab) P heps n h_cond
  let family :=
    lemma34RefinementFamilyC_of_columnRefinementProviderC
      (a := a) (b := b) (eps := eps) (hab := hab)
      ctor.columnProvider P heps n h_cond
  let step :=
    lemma34StepC_of_refinementFamilyC
      (a := a) (b := b) (eps := eps) (hab := hab) P n family
  let data :=
    lemma34LimitDataC_construct
      (a := a) (b := b) (eps := eps) (hab := hab) P n T0 step
  lemma34ResultDataC_of_limitOutsideC
    (a := a) (b := b) (eps := eps) (hab := hab)
    P n T0 step data
    (fun k => ctor.constructOutsideAt P heps n h_cond k)
    (lemma34FarOutsideFromLimitC_construct
      (a := a) (b := b) (eps := eps) (hab := hab)
      P n T0 step data)


/-- Source-faithful positive-`n` version of the remaining frontier.

The paper states Lemma 3.4 for `n >= 1`.  This positive-`n` variant keeps
that hypothesis explicit; it is the usable target for the outside geometry
because the outside premise over `Fin 0` is vacuous. -/
structure Lemma34DataFrontierRemainingPosC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC
  constructOutsideAt :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      0 < n →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      Lemma34TowerOutsideC P n k
        (lemma34TowerSeqC P n
          (lemma34T0C_direct P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC P n
            (lemma34RefinementFamilyC_of_columnRefinementProviderC
              columnProvider P heps n h_cond))
          k)

/-- Reducer for the source-faithful positive-`n` frontier. -/
noncomputable def lemma_3_4DataC_of_remainingFrontierPosC
    (ctor : Lemma34DataFrontierRemainingPosC) {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n := by
  let T0 : Lemma34TowerC P n 0 := lemma34T0C_direct P heps n h_cond
  let family : Lemma34RefinementFamilyC P n :=
    lemma34RefinementFamilyC_of_columnRefinementProviderC
      ctor.columnProvider P heps n h_cond
  let step := lemma34StepC_of_refinementFamilyC P n family
  have data : Lemma34LimitDataC P n T0 step :=
    lemma34LimitDataC_construct P n T0 step
  exact lemma34ResultDataC_of_limitOutsideC P n T0 step data
    (fun k => ctor.constructOutsideAt P heps n hn h_cond k)
    (lemma34FarOutsideFromLimitC_construct P n T0 step data)

/-- Frontier split for `constructOutsideAt`: it is enough to preserve an
outside witness across one refinement step.  The base case is supplied by
`lemma34T0OutsideC_direct`, hence the explicit `0 < n` hypothesis. -/
structure Lemma34OutsideStepProviderC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC
  preserve :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      0 < n →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      let family : Lemma34RefinementFamilyC P n :=
        lemma34RefinementFamilyC_of_columnRefinementProviderC
          columnProvider P heps n h_cond
      let step := lemma34StepC_of_refinementFamilyC P n family
      (k : Nat) →
      (T : Lemma34TowerC P n k) →
      Lemma34TowerOutsideC P n k T →
      Lemma34TowerOutsideC P n (k + 1) (step k T).val

/-- Iterate a one-step outside-preservation provider along the tower sequence. -/
noncomputable def lemma34TowerSeqOutsideC_of_outsideStepProviderC
    (provider : Lemma34OutsideStepProviderC) {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (k : Nat) :
    let T0 : Lemma34TowerC P n 0 := lemma34T0C_direct P heps n h_cond
    let family : Lemma34RefinementFamilyC P n :=
      lemma34RefinementFamilyC_of_columnRefinementProviderC
        provider.columnProvider P heps n h_cond
    let step := lemma34StepC_of_refinementFamilyC P n family
    Lemma34TowerOutsideC P n k (lemma34TowerSeqC P n T0 step k) := by
  induction k with
  | zero =>
      exact lemma34T0OutsideC_direct P heps n hn h_cond
  | succ k ih =>
      exact provider.preserve P heps n hn h_cond k
        (lemma34TowerSeqC P n
          (lemma34T0C_direct P heps n h_cond)
          (lemma34StepC_of_refinementFamilyC P n
            (lemma34RefinementFamilyC_of_columnRefinementProviderC
              provider.columnProvider P heps n h_cond))
          k)
        ih

/-- Package a one-step outside-preservation provider as the positive-`n`
remaining frontier. -/
noncomputable def lemma34DataFrontierRemainingPosC_of_outsideStepProviderC
    (provider : Lemma34OutsideStepProviderC) :
    Lemma34DataFrontierRemainingPosC where
  columnProvider := provider.columnProvider
  constructOutsideAt := by
    intro a b eps hab P heps n hn h_cond k
    exact lemma34TowerSeqOutsideC_of_outsideStepProviderC
      provider P heps n hn h_cond k

/-- Source-faithful reducer from the one-step outside-preservation frontier. -/
noncomputable def lemma_3_4DataC_of_outsideStepProviderC
    (provider : Lemma34OutsideStepProviderC) {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_remainingFrontierPosC (eps := eps)
    (lemma34DataFrontierRemainingPosC_of_outsideStepProviderC provider)
    P heps n hn h_cond

/-! ### §3 P2b-beta finite radius collection primitives -/

/-- Fprevious a finite list with `CReal.min`, using `seed` for the empty list.

This mirrors abstract `lemma34_foldMin`; in P2b-beta the seed is the parent
outside radius. -/
def lemma34FoldMinC (seed : CReal) : List CReal → CReal
  | [] => seed
  | x :: xs => CReal.min x (lemma34FoldMinC seed xs)

/-- The finite folded minimum is below its seed. -/
theorem lemma34FoldMin_le_seedC (seed : CReal) :
    ∀ xs : List CReal, RegularSeqLe (lemma34FoldMinC seed xs) seed
  | [] => regularSeqLe_refl seed
  | _ :: xs =>
      regularSeqLe_trans
        (CReal.min_le_rightC _ _)
        (lemma34FoldMin_le_seedC seed xs)

/-- The finite folded minimum is below every member of the list. -/
theorem lemma34FoldMin_le_memC (seed : CReal) {xs : List CReal} {x : CReal}
    (h : x ∈ xs) : RegularSeqLe (lemma34FoldMinC seed xs) x := by
  induction xs with
  | nil =>
      cases h
  | cons y ys ih =>
      have hOr : x = y ∨ x ∈ ys := List.mem_cons.mp h
      rcases hOr with hxy | hxs
      · rw [hxy]
        exact CReal.min_le_leftC y (lemma34FoldMinC seed ys)
      · exact regularSeqLe_trans
          (CReal.min_le_rightC y (lemma34FoldMinC seed ys))
          (ih hxs)

/-- A finite folded minimum of positive values with a positive seed is positive. -/
theorem lemma34FoldMin_posC (seed : CReal) :
    ∀ xs : List CReal,
      regularSeqLtProp CReal.zero seed →
      (∀ x : CReal, x ∈ xs → regularSeqLtProp CReal.zero x) →
      regularSeqLtProp CReal.zero (lemma34FoldMinC seed xs)
  | [], hseed, _ => hseed
  | x :: xs, hseed, hxs =>
      min_posC
        (hxs x (by simp))
        (lemma34FoldMin_posC seed xs hseed
          (fun y hy => hxs y (by simp [hy])))

/-- Finite radius choice used in P2b-beta: one positive radius below the
parent radius and every collected discarded-cell radius. -/
structure Lemma34FiniteRadiusChoiceC (seed : CReal) (radii : List CReal) : Type where
  sigma : CReal
  sigma_pos : regularSeqLtProp CReal.zero sigma
  sigma_le_seed : RegularSeqLe sigma seed
  sigma_le_mem : ∀ r : CReal, r ∈ radii → RegularSeqLe sigma r

/-- Standard finite radius choice by folded `CReal.min`. -/
def lemma34FiniteRadiusChoiceC_standard (seed : CReal) (radii : List CReal)
    (hseed : regularSeqLtProp CReal.zero seed)
    (hradii : ∀ r : CReal, r ∈ radii → regularSeqLtProp CReal.zero r) :
    Lemma34FiniteRadiusChoiceC seed radii :=
  { sigma := lemma34FoldMinC seed radii
    sigma_pos := lemma34FoldMin_posC seed radii hseed hradii
    sigma_le_seed := lemma34FoldMin_le_seedC seed radii
    sigma_le_mem := fun r hr => lemma34FoldMin_le_memC seed hr }

/-- Right monotonicity of presented `max`: `x <= y -> max a x <= max a y`. -/
theorem CReal.max_right_monoC {a x y : CReal} (hxy : RegularSeqLe x y) :
    RegularSeqLe (CReal.max a x) (CReal.max a y) :=
  CReal.max_leC
    (CReal.le_max_leftC a y)
    (regularSeqLe_trans hxy (CReal.le_max_rightC a y))

/-- Right monotonicity of presented `min`: `x <= y -> min b x <= min b y`. -/
theorem CReal.min_right_monoC {b x y : CReal} (hxy : RegularSeqLe x y) :
    RegularSeqLe (CReal.min b x) (CReal.min b y) :=
  CReal.le_minC
    (CReal.min_le_leftC b x)
    (regularSeqLe_trans (CReal.min_le_rightC b x) hxy)

/-- Shrink a symmetric `p_ltC` neighbourhood from radius `gamma` to a smaller
radius `sigma`. -/
def ProfileC.p_ltC_shrink_gamma {a b : CReal} {hab : regularSeqLtProp a b}
    (PC : ProfileC a b hab) {t gamma sigma eps : CReal}
    (h : PC.p_ltC
      (CReal.max a (CReal.sub t gamma))
      (CReal.min b (CReal.add t gamma)) eps)
    (hsigma : RegularSeqLe sigma gamma) :
    PC.p_ltC
      (CReal.max a (CReal.sub t sigma))
      (CReal.min b (CReal.add t sigma)) eps := by
  have hleft_sub : RegularSeqLe (CReal.sub t gamma) (CReal.sub t sigma) :=
    regularSeqLe_sub_leftC (a := sigma) (b := gamma) (c := t) hsigma
  have hright_add : RegularSeqLe (CReal.add t sigma) (CReal.add t gamma) :=
    regularSeqLe_add (regularSeqLe_refl t) hsigma
  exact PC.p_ltC_subset h
    (CReal.max_right_monoC (a := a) hleft_sub)
    (CReal.min_right_monoC (b := b) hright_add)

/-- Type-valued cover data for one outside-preservation step.

For a point outside all successor segments, the data must either provide the
previous outside premise or a direct local `p_ltC` witness at the finite-radius
choice.  This avoids eliminating a Prop-level disjunction into the Type-valued
`p_ltC` target. -/
structure Lemma34OutsideStepCoverC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T)
    (Tnext : Lemma34TowerC (eps := eps) P n (k + 1)) : Type 2 where
  radii : List CReal
  radii_pos : ∀ r : CReal, r ∈ radii → regularSeqLtProp CReal.zero r
  sigma : CReal
  sigma_pos : regularSeqLtProp CReal.zero sigma
  sigma_le_previous : RegularSeqLe sigma oldOut.gamma
  sigma_le_mem : ∀ r : CReal, r ∈ radii → RegularSeqLe sigma r
  cover :
    ∀ t_pt : CReal,
      RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
      (∀ j : Fin n,
        regularSeqLtProp (Tnext.segR j) t_pt ∨
          regularSeqLtProp t_pt (Tnext.segL j)) →
      PSum
        (∀ j : Fin n,
          regularSeqLtProp (T.segR j) t_pt ∨
            regularSeqLtProp t_pt (T.segL j))
        (P.p_ltC
          (CReal.max a (CReal.sub t_pt sigma))
          (CReal.min b (CReal.add t_pt sigma))
          eps)

/-- Realize a Type-valued one-step cover as an actual successor outside
witness.  The old-outside branch is shrunk to the finite radius choice. -/
noncomputable def lemma34OutsideStepPreserveC_of_coverC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T)
    {Tnext : Lemma34TowerC (eps := eps) P n (k + 1)}
    (coverData : Lemma34OutsideStepCoverC (eps := eps) P n k T oldOut Tnext) :
    Lemma34TowerOutsideC (eps := eps) P n (k + 1) Tnext :=
  { gamma := coverData.sigma
    gamma_pos := coverData.sigma_pos
    outside := by
      intro t_pt hat htb hnew
      cases coverData.cover t_pt hat htb hnew with
      | inl hprevious =>
          exact P.p_ltC_shrink_gamma
            (oldOut.outside t_pt hat htb hprevious)
            coverData.sigma_le_previous
      | inr hlocal =>
          exact hlocal }

/-- Provider for the remaining P2b-beta locatedness split.  This is stronger
than `Lemma34OutsideStepProviderC`, but source-faithful: the old-radius branch
is handled generically, while the provider only supplies the constructive
cover split for discarded cells. -/
structure Lemma34OutsideCoverProviderC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC
  cover :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      0 < n →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      let family : Lemma34RefinementFamilyC P n :=
        lemma34RefinementFamilyC_of_columnRefinementProviderC
          columnProvider P heps n h_cond
      let step := lemma34StepC_of_refinementFamilyC P n family
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T) →
      Lemma34OutsideStepCoverC (eps := eps) P n k T oldOut (step k T).val

/-- A cover provider yields the one-step outside-preservation provider. -/
noncomputable def lemma34OutsideStepProviderC_of_coverProviderC
    (provider : Lemma34OutsideCoverProviderC) :
    Lemma34OutsideStepProviderC where
  columnProvider := provider.columnProvider
  preserve := by
    intro a b eps hab P heps n hn h_cond family step k T oldOut
    exact lemma34OutsideStepPreserveC_of_coverC P n k T oldOut
      (provider.cover P heps n hn h_cond k T oldOut)

/-- Source-faithful reducer from the P2b-beta cover provider. -/
noncomputable def lemma_3_4DataC_of_outsideCoverProviderC
    (provider : Lemma34OutsideCoverProviderC) {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_outsideStepProviderC
    (lemma34OutsideStepProviderC_of_coverProviderC provider)
    P heps n hn h_cond

/-- Generic finite-list PSum scan used by the P2b-beta locatedness split.
Either some element supplies a witness `W`, or all elements satisfy `Q`. -/
def lemma34ScanListPSC {α W : Type*} (Q : α → Prop) :
    (xs : List α) →
    (∀ y, y ∈ xs → PSum W (Q y)) →
    PSum W (∀ y, y ∈ xs → Q y)
  | [], _ =>
      .inr (by
        intro y hy
        have hfalse : False := by simpa using hy
        exact hfalse.elim)
  | y :: ys, hloc =>
      match hloc y (by simp) with
      | .inl w =>
          .inl w
      | .inr hy =>
          match lemma34ScanListPSC (W := W) Q ys
              (fun z hz => hloc z (List.mem_cons_of_mem y hz)) with
          | .inl w =>
              .inl w
          | .inr hys =>
              .inr (by
                intro z hz
                simp only [List.mem_cons] at hz
                rcases hz with rfl | hz
                · exact hy
                · exact hys z hz)

/-- Cell scan over the first `N+1` consecutive CReal cells.  Either some cell
supplies a witness `W`, or the point lies strictly to the right of the final
endpoint / strictly to the left of the initial endpoint. -/
def lemma34H4ScanCellsSuccC
    (pts : Nat → CReal) (x : CReal) {W : Type*} :
    (N : Nat) →
    (∀ i : Nat, i < Nat.succ N →
      PSum W
        (PSum
          (regularSeqLtProp (pts (i + 1)) x)
          (regularSeqLtProp x (pts i)))) →
    PSum W
      (PSum
        (regularSeqLtProp (pts (Nat.succ N)) x)
        (regularSeqLtProp x (pts 0)))
  | 0, hcell =>
      hcell 0 (Nat.zero_lt_succ 0)
  | Nat.succ N, hcell =>
      match lemma34H4ScanCellsSuccC (W := W) pts x N
          (fun i hi =>
            hcell i
              (Nat.lt_trans hi
                (Nat.lt_succ_self (Nat.succ N)))) with
      | .inl w =>
          .inl w
      | .inr (.inr hleft) =>
          .inr (.inr hleft)
      | .inr (.inl hright) =>
          match hcell (Nat.succ N)
              (Nat.lt_succ_self (Nat.succ N)) with
          | .inl w =>
              .inl w
          | .inr (.inl hright') =>
              .inr (.inl hright')
          | .inr (.inr hleft') =>
              False.elim
                (regularSeqLtProp_irrefl (pts (Nat.succ N))
                  (regularSeqLtProp_trans
                    (pts (Nat.succ N)) x (pts (Nat.succ N))
                    hright hleft'))

/-- Nonempty wrapper around `lemma34H4ScanCellsSuccC`. -/
def lemma34H4ScanCellsC
    (pts : Nat → CReal) (x : CReal) {W : Type*}
    (N : Nat) (hN : 0 < N)
    (hcell : ∀ i : Nat, i < N →
      PSum W
        (PSum
          (regularSeqLtProp (pts (i + 1)) x)
          (regularSeqLtProp x (pts i)))) :
    PSum W
      (PSum
        (regularSeqLtProp (pts N) x)
        (regularSeqLtProp x (pts 0))) := by
  cases N with
  | zero =>
      exact False.elim ((Nat.not_lt_zero 0) hN)
  | succ N =>
      exact lemma34H4ScanCellsSuccC (W := W) pts x N hcell

/-- Constructive scan over all `Fin n` indices.  Either one index supplies `W`,
or all indices satisfy `Q`. -/
def lemma34ScanFinPSC {W : Type*} :
    (n : Nat) →
    (Q : Fin n → Prop) →
    ((j : Fin n) → PSum W (Q j)) →
    PSum W (∀ j : Fin n, Q j)
  | 0, _Q, _h =>
      .inr (by
        intro j
        exact False.elim ((Nat.not_lt_zero j.1) j.2))
  | Nat.succ n, Q, h =>
      match lemma34ScanFinPSC (W := W) n
          (fun j : Fin n =>
            Q ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self n)⟩)
          (fun j : Fin n =>
            h ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self n)⟩) with
      | .inl w =>
          .inl w
      | .inr hprev =>
          match h ⟨n, Nat.lt_succ_self n⟩ with
          | .inl w =>
              .inl w
          | .inr hlast =>
              .inr (by
                intro j
                have hjle : j.1 ≤ n := Nat.le_of_lt_succ j.2
                rcases Nat.lt_or_eq_of_le hjle with hjlt | hjeq
                · exact hprev ⟨j.1, hjlt⟩
                · have hjlast : j = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hjeq
                  simpa [hjlast] using hlast)

/-- CReal zero-cell collar data for the local P2b-beta branch.

The subset inequalities are the concrete payload needed to shrink the
discarded-cell `p_ltC` witness to the symmetric successor neighbourhood around
`t_pt`.  Later H4 locatedness work only has to produce this collar data. -/
structure Lemma34ZeroCollarC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (sigma t_pt : CReal) : Type where
  left : CReal
  right : CReal
  omega : CReal
  omega_pos : regularSeqLtProp CReal.zero omega
  source :
    P.p_ltC
      (CReal.max a (CReal.sub left omega))
      (CReal.min b (CReal.add right omega))
      eps
  subset_left :
    RegularSeqLe
      (CReal.max a (CReal.sub left omega))
      (CReal.max a (CReal.sub t_pt sigma))
  subset_right :
    RegularSeqLe
      (CReal.min b (CReal.add t_pt sigma))
      (CReal.min b (CReal.add right omega))

/-- Shrink a zero-cell collar witness to the local symmetric neighbourhood. -/
def lemma34ZeroCollar_shrinkC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma t_pt : CReal}
    (W : Lemma34ZeroCollarC (eps := eps) P sigma t_pt) :
    P.p_ltC
      (CReal.max a (CReal.sub t_pt sigma))
      (CReal.min b (CReal.add t_pt sigma))
      eps :=
  P.p_ltC_subset W.source W.subset_left W.subset_right

/-- Variant of one-step cover data whose local branch returns a zero-cell
collar instead of the already-shrunk `p_ltC` witness. -/
structure Lemma34OutsideStepZeroCoverC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T)
    (Tnext : Lemma34TowerC (eps := eps) P n (k + 1)) : Type 2 where
  radii : List CReal
  radii_pos : ∀ r : CReal, r ∈ radii → regularSeqLtProp CReal.zero r
  sigma : CReal
  sigma_pos : regularSeqLtProp CReal.zero sigma
  sigma_le_previous : RegularSeqLe sigma oldOut.gamma
  sigma_le_mem : ∀ r : CReal, r ∈ radii → RegularSeqLe sigma r
  cover :
    ∀ t_pt : CReal,
      RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
      (∀ j : Fin n,
        regularSeqLtProp (Tnext.segR j) t_pt ∨
          regularSeqLtProp t_pt (Tnext.segL j)) →
      PSum
        (∀ j : Fin n,
          regularSeqLtProp (T.segR j) t_pt ∨
            regularSeqLtProp t_pt (T.segL j))
        (Lemma34ZeroCollarC (eps := eps) P sigma t_pt)

/-- A zero-collar cover is an outside-step cover. -/
def lemma34OutsideStepCoverC_of_zeroCoverC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T)
    {Tnext : Lemma34TowerC (eps := eps) P n (k + 1)}
    (Z : Lemma34OutsideStepZeroCoverC (eps := eps) P n k T oldOut Tnext) :
    Lemma34OutsideStepCoverC (eps := eps) P n k T oldOut Tnext where
  radii := Z.radii
  radii_pos := Z.radii_pos
  sigma := Z.sigma
  sigma_pos := Z.sigma_pos
  sigma_le_previous := Z.sigma_le_previous
  sigma_le_mem := Z.sigma_le_mem
  cover := by
    intro t_pt hat htb hnew
    cases Z.cover t_pt hat htb hnew with
    | inl hprevious =>
        exact PSum.inl hprevious
    | inr W =>
        exact PSum.inr (lemma34ZeroCollar_shrinkC P W)

/-- Provider form of the zero-collar H4 obligation. -/
structure Lemma34OutsideZeroCoverProviderC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC
  zeroCover :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      0 < n →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      let family : Lemma34RefinementFamilyC P n :=
        lemma34RefinementFamilyC_of_columnRefinementProviderC
          columnProvider P heps n h_cond
      let step := lemma34StepC_of_refinementFamilyC P n family
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T) →
      Lemma34OutsideStepZeroCoverC (eps := eps) P n k T oldOut (step k T).val

/-- A zero-collar provider yields the outside-cover provider. -/
noncomputable def lemma34OutsideCoverProviderC_of_zeroCoverProviderC
    (provider : Lemma34OutsideZeroCoverProviderC) :
    Lemma34OutsideCoverProviderC where
  columnProvider := provider.columnProvider
  cover := by
    intro a b eps hab P heps n hn h_cond family step k T oldOut
    exact lemma34OutsideStepCoverC_of_zeroCoverC P n k T oldOut
      (provider.zeroCover P heps n hn h_cond k T oldOut)

/-- Source-faithful reducer from the zero-collar H4 provider. -/
noncomputable def lemma_3_4DataC_of_outsideZeroCoverProviderC
    (provider : Lemma34OutsideZeroCoverProviderC) {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_outsideCoverProviderC
    (lemma34OutsideCoverProviderC_of_zeroCoverProviderC provider)
    P heps n hn h_cond

/-- Per-column zero-collar cover data.  For each previous column it either produces
a zero-cell collar or proves the point lies outside that previous column. -/
structure Lemma34OutsideColumnCoverC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T)
    (Tnext : Lemma34TowerC (eps := eps) P n (k + 1)) : Type 2 where
  radii : List CReal
  radii_pos : ∀ r : CReal, r ∈ radii → regularSeqLtProp CReal.zero r
  sigma : CReal
  sigma_pos : regularSeqLtProp CReal.zero sigma
  sigma_le_previous : RegularSeqLe sigma oldOut.gamma
  sigma_le_mem : ∀ r : CReal, r ∈ radii → RegularSeqLe sigma r
  columnCover :
    ∀ t_pt : CReal,
      RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
      (∀ j : Fin n,
        regularSeqLtProp (Tnext.segR j) t_pt ∨
          regularSeqLtProp t_pt (Tnext.segL j)) →
      (j : Fin n) →
      PSum
        (Lemma34ZeroCollarC (eps := eps) P sigma t_pt)
        (regularSeqLtProp (T.segR j) t_pt ∨
          regularSeqLtProp t_pt (T.segL j))

/-- Per-column cover data gives a zero-collar cover for the whole tower. -/
def lemma34OutsideStepZeroCoverC_of_columnCoverC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T)
    {Tnext : Lemma34TowerC (eps := eps) P n (k + 1)}
    (C : Lemma34OutsideColumnCoverC (eps := eps) P n k T oldOut Tnext) :
    Lemma34OutsideStepZeroCoverC (eps := eps) P n k T oldOut Tnext where
  radii := C.radii
  radii_pos := C.radii_pos
  sigma := C.sigma
  sigma_pos := C.sigma_pos
  sigma_le_previous := C.sigma_le_previous
  sigma_le_mem := C.sigma_le_mem
  cover := by
    intro t_pt hat htb hnew
    let Q : Fin n → Prop := fun j =>
      regularSeqLtProp (T.segR j) t_pt ∨
        regularSeqLtProp t_pt (T.segL j)
    cases lemma34ScanFinPSC (W := Lemma34ZeroCollarC (eps := eps) P C.sigma t_pt)
        n Q (fun j => C.columnCover t_pt hat htb hnew j) with
    | inl W =>
        exact PSum.inr W
    | inr hprevious =>
        exact PSum.inl hprevious

/-- Provider form of the per-column H4 obligation. -/
structure Lemma34OutsideColumnCoverProviderC : Type 2 where
  columnProvider : Lemma34ColumnRefinementProviderC
  columnCover :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      0 < n →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      let family : Lemma34RefinementFamilyC P n :=
        lemma34RefinementFamilyC_of_columnRefinementProviderC
          columnProvider P heps n h_cond
      let step := lemma34StepC_of_refinementFamilyC P n family
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T) →
      Lemma34OutsideColumnCoverC (eps := eps) P n k T oldOut (step k T).val

/-- A per-column cover provider yields the zero-collar provider. -/
noncomputable def lemma34OutsideZeroCoverProviderC_of_columnCoverProviderC
    (provider : Lemma34OutsideColumnCoverProviderC) :
    Lemma34OutsideZeroCoverProviderC where
  columnProvider := provider.columnProvider
  zeroCover := by
    intro a b eps hab P heps n hn h_cond family step k T oldOut
    exact lemma34OutsideStepZeroCoverC_of_columnCoverC P n k T oldOut
      (provider.columnCover P heps n hn h_cond k T oldOut)

/-- Source-faithful reducer from the per-column H4 provider. -/
noncomputable def lemma_3_4DataC_of_outsideColumnCoverProviderC
    (provider : Lemma34OutsideColumnCoverProviderC) {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_outsideZeroCoverProviderC
    (lemma34OutsideZeroCoverProviderC_of_columnCoverProviderC provider)
    P heps n hn h_cond

/-- Monotonicity of zero-collar data in the radius around `t_pt`.
If the symmetric radius is shrunk, the same stored cell still covers it. -/
def lemma34ZeroCollar_shrinkRadiusC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {rho sigma t_pt : CReal}
    (W : Lemma34ZeroCollarC (eps := eps) P rho t_pt)
    (hsigma : RegularSeqLe sigma rho) :
    Lemma34ZeroCollarC (eps := eps) P sigma t_pt :=
  { left := W.left
    right := W.right
    omega := W.omega
    omega_pos := W.omega_pos
    source := W.source
    subset_left := by
      have hsub : RegularSeqLe
          (CReal.sub t_pt rho) (CReal.sub t_pt sigma) :=
        regularSeqLe_sub_leftC (a := sigma) (b := rho) (c := t_pt) hsigma
      exact regularSeqLe_trans W.subset_left
        (CReal.max_right_monoC (a := a) hsub)
    subset_right := by
      have hadd : RegularSeqLe
          (CReal.add t_pt sigma) (CReal.add t_pt rho) :=
        regularSeqLe_add (regularSeqLe_refl t_pt) hsigma
      exact regularSeqLe_trans
        (CReal.min_right_monoC (b := b) hadd)
        W.subset_right }

/-- Concrete one-column step data: the same local construction supplies both
the successor segment and the H4/zero-collar outside classification for that
column.  This is the CReal counterpart of the source proof's block-local
`classifyCell/classifyBlock` payload. -/
structure Lemma34ColumnStepDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n) : Type 2 where
  refinement : Lemma34ColumnRefinementC (eps := eps) P n k T j
  radius : CReal
  radius_pos : regularSeqLtProp CReal.zero radius
  cover :
    ∀ t_pt : CReal,
      RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
      (regularSeqLtProp refinement.segR_next t_pt ∨
        regularSeqLtProp t_pt refinement.segL_next) →
      PSum
        (Lemma34ZeroCollarC (eps := eps) P radius t_pt)
        (regularSeqLtProp (T.segR j) t_pt ∨
          regularSeqLtProp t_pt (T.segL j))

/-- Joint column-step provider.  Unlike the earlier split frontiers, this keeps
the refinement endpoints and the outside-cover classification synchronized. -/
structure Lemma34JointColumnStepProviderC : Type 2 where
  columnStep :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnStepDataC (eps := eps) P n k T j

/-- The refinement projection of the joint column-step provider. -/
noncomputable def lemma34ColumnRefinementProviderC_of_jointColumnStepProviderC
    (provider : Lemma34JointColumnStepProviderC) :
    Lemma34ColumnRefinementProviderC where
  refine := by
    intro a b eps hab P heps n h_cond k T j
    exact (provider.columnStep P heps n h_cond k T j).refinement

/-- One synchronized joint step yields the per-column outside-cover object for
the successor tower produced by its own refinement projection. -/
noncomputable def lemma34OutsideColumnCoverC_of_jointColumnStepProviderC
    (provider : Lemma34JointColumnStepProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k T) :
    let columnProvider :=
      lemma34ColumnRefinementProviderC_of_jointColumnStepProviderC provider
    let family : Lemma34RefinementFamilyC (eps := eps) P n :=
      lemma34RefinementFamilyC_of_columnRefinementProviderC
        columnProvider P heps n h_cond
    let step := lemma34StepC_of_refinementFamilyC P n family
    Lemma34OutsideColumnCoverC (eps := eps) P n k T oldOut
      (step k T).val := by
  let columnProvider :=
    lemma34ColumnRefinementProviderC_of_jointColumnStepProviderC provider
  let family : Lemma34RefinementFamilyC (eps := eps) P n :=
    lemma34RefinementFamilyC_of_columnRefinementProviderC
      columnProvider P heps n h_cond
  let step := lemma34StepC_of_refinementFamilyC P n family
  let radii : List CReal :=
    List.ofFn (fun j : Fin n =>
      (provider.columnStep P heps n h_cond k T j).radius)
  have hradii_pos :
      ∀ r : CReal, r ∈ radii → regularSeqLtProp CReal.zero r := by
    intro r hr
    rcases List.mem_ofFn.mp (by simpa [radii] using hr) with ⟨j, rfl⟩
    exact (provider.columnStep P heps n h_cond k T j).radius_pos
  let choice :=
    lemma34FiniteRadiusChoiceC_standard oldOut.gamma radii
      oldOut.gamma_pos hradii_pos
  refine
    { radii := radii
      radii_pos := hradii_pos
      sigma := choice.sigma
      sigma_pos := choice.sigma_pos
      sigma_le_previous := choice.sigma_le_seed
      sigma_le_mem := choice.sigma_le_mem
      columnCover := ?_ }
  intro t_pt hat htb hnew j
  let D := provider.columnStep P heps n h_cond k T j
  have hmem : D.radius ∈ radii := by
    dsimp [radii, D]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  have hsigma_radius : RegularSeqLe choice.sigma D.radius :=
    choice.sigma_le_mem D.radius hmem
  have hnewj :
      regularSeqLtProp D.refinement.segR_next t_pt ∨
        regularSeqLtProp t_pt D.refinement.segL_next := by
    simpa [D, columnProvider, family, step,
      lemma34ColumnRefinementProviderC_of_jointColumnStepProviderC,
      lemma34RefinementFamilyC_of_columnRefinementProviderC,
      lemma34StepC_of_refinementFamilyC,
      lemma34StepC_of_columnRefinementsC,
      lemma34TowerC_of_columnRefinementsC] using hnew j
  cases D.cover t_pt hat htb hnewj with
  | inl W =>
      exact PSum.inl
        (lemma34ZeroCollar_shrinkRadiusC P W hsigma_radius)
  | inr hprevious =>
      exact PSum.inr hprevious

/-- The synchronized joint provider supplies the earlier per-column-cover
provider, but only for the refinement family projected from itself. -/
noncomputable def lemma34OutsideColumnCoverProviderC_of_jointColumnStepProviderC
    (provider : Lemma34JointColumnStepProviderC) :
    Lemma34OutsideColumnCoverProviderC where
  columnProvider :=
    lemma34ColumnRefinementProviderC_of_jointColumnStepProviderC provider
  columnCover := by
    intro a b eps hab P heps n hn h_cond family step k T oldOut
    exact lemma34OutsideColumnCoverC_of_jointColumnStepProviderC
      provider P heps n h_cond k T oldOut

/-- Source-faithful Lemma 3.4 DATA reducer from synchronized concrete
column-step data.  This is the current concrete target for the counting layer:
produce `Lemma34ColumnStepDataC` for each column. -/
noncomputable def lemma_3_4DataC_of_jointColumnStepProviderC
    (provider : Lemma34JointColumnStepProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_outsideColumnCoverProviderC
    (lemma34OutsideColumnCoverProviderC_of_jointColumnStepProviderC provider)
    P heps n hn h_cond

/-- Finite-cell scan payload for one column.  This is the local CReal form of
the H4 block scan: every cell either yields a zero-collar witness, or proves
that the point is strictly to one side of that cell. -/
structure Lemma34ColumnCellScanDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n) : Type 2 where
  refinement : Lemma34ColumnRefinementC (eps := eps) P n k T j
  radius : CReal
  radius_pos : regularSeqLtProp CReal.zero radius
  N : Nat
  N_pos : 0 < N
  pts : Nat → CReal
  pts_zero : pts 0 ≈ T.segL j
  pts_N : pts N ≈ T.segR j
  cellCover :
    ∀ t_pt : CReal,
      RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
      (regularSeqLtProp refinement.segR_next t_pt ∨
        regularSeqLtProp t_pt refinement.segL_next) →
      ∀ i : Nat, i < N →
        PSum
          (Lemma34ZeroCollarC (eps := eps) P radius t_pt)
          (PSum
            (regularSeqLtProp (pts (i + 1)) t_pt)
            (regularSeqLtProp t_pt (pts i)))

/-- Scan the finite cells of one column to obtain synchronized column-step
data.  If no zero-collar is found, the scan places the point outside the
parent column endpoints. -/
def lemma34ColumnStepDataC_of_cellScanC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnCellScanDataC (eps := eps) P n k T j) :
    Lemma34ColumnStepDataC (eps := eps) P n k T j :=
  { refinement := D.refinement
    radius := D.radius
    radius_pos := D.radius_pos
    cover := by
      intro t_pt hat htb hnew
      have hscan :
          PSum
            (Lemma34ZeroCollarC (eps := eps) P D.radius t_pt)
            (PSum
              (regularSeqLtProp (D.pts D.N) t_pt)
              (regularSeqLtProp t_pt (D.pts 0))) :=
        lemma34H4ScanCellsC
          (W := Lemma34ZeroCollarC (eps := eps) P D.radius t_pt)
          D.pts t_pt D.N D.N_pos
          (fun i hi => D.cellCover t_pt hat htb hnew i hi)
      cases hscan with
      | inl W =>
          exact PSum.inl W
      | inr hside =>
          cases hside with
          | inl hright =>
              exact PSum.inr
                (Or.inl
                  (regularSeqLtProp_of_left_eventual
                    (Setoid.symm D.pts_N) hright))
          | inr hleft =>
              exact PSum.inr
                (Or.inr
                  (regularSeqLtProp_of_right_eventual
                    D.pts_zero hleft)) }

/-- Provider form of the finite-cell scan payload. -/
structure Lemma34ColumnCellScanProviderC : Type 2 where
  cellScan :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnCellScanDataC (eps := eps) P n k T j

/-- Finite-cell scan data supplies the synchronized joint column-step provider. -/
noncomputable def lemma34JointColumnStepProviderC_of_cellScanProviderC
    (provider : Lemma34ColumnCellScanProviderC) :
    Lemma34JointColumnStepProviderC where
  columnStep := by
    intro a b eps hab P heps n h_cond k T j
    exact lemma34ColumnStepDataC_of_cellScanC P n k T j
      (provider.cellScan P heps n h_cond k T j)

/-- Source-faithful Lemma 3.4 DATA reducer from finite-cell scan data. -/
noncomputable def lemma_3_4DataC_of_cellScanProviderC
    (provider : Lemma34ColumnCellScanProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_jointColumnStepProviderC
    (lemma34JointColumnStepProviderC_of_cellScanProviderC provider)
    P heps n hn h_cond

/-- Local zero-cell data for one finite cell.  The strict gap tests are carried
as DATA so that the classifier can return a Type-valued `PSum` without
eliminating a Prop-level disjunction. -/
structure Lemma34ZeroCellLocalDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (sigma left right : CReal) : Type 2 where
  omega : CReal
  omega_pos : regularSeqLtProp CReal.zero omega
  source :
    P.p_ltC
      (CReal.max a (CReal.sub left omega))
      (CReal.min b (CReal.add right omega))
      eps
  left_gap : regularSeqLtData (CReal.sub left sigma) left
  right_gap : regularSeqLtData right (CReal.add right sigma)
  subset_left_of_near :
    ∀ t_pt : CReal,
      regularSeqLtProp (CReal.sub left sigma) t_pt →
      RegularSeqLe
        (CReal.max a (CReal.sub left omega))
        (CReal.max a (CReal.sub t_pt sigma))
  subset_right_of_near :
    ∀ t_pt : CReal,
      regularSeqLtProp t_pt (CReal.add right sigma) →
      RegularSeqLe
        (CReal.min b (CReal.add t_pt sigma))
        (CReal.min b (CReal.add right omega))

/-- DATA-cotransitive classifier for a zero cell.  Either the point is already
strictly outside the cell, or the stored profile witness supplies a zero
collar around the point. -/
def lemma34ZeroCellCoverC_of_localDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma left right t_pt : CReal}
    (D : Lemma34ZeroCellLocalDataC (eps := eps) P sigma left right) :
    PSum
      (Lemma34ZeroCollarC (eps := eps) P sigma t_pt)
      (PSum
        (regularSeqLtProp right t_pt)
        (regularSeqLtProp t_pt left)) := by
  cases regularSeqLtData_cotrans
      (CReal.sub left sigma) left t_pt D.left_gap with
  | inr hleft =>
      exact PSum.inr (PSum.inr hleft.toProp)
  | inl hleftNear =>
      cases regularSeqLtData_cotrans
          right (CReal.add right sigma) t_pt D.right_gap with
      | inl hright =>
          exact PSum.inr (PSum.inl hright.toProp)
      | inr hrightNear =>
          exact PSum.inl
            { left := left
              right := right
              omega := D.omega
              omega_pos := D.omega_pos
              source := D.source
              subset_left := D.subset_left_of_near t_pt hleftNear.toProp
              subset_right := D.subset_right_of_near t_pt hrightNear.toProp }

/-- Local positive-cell data: the cell is contained in the successor segment,
and the cell itself has DATA strict properness for cotransitive side selection. -/
structure Lemma34PositiveCellLocalDataC
    (left right nextL nextR : CReal) : Type where
  cell_strict : regularSeqLtData left right
  next_le_left : RegularSeqLe nextL left
  right_le_next : RegularSeqLe right nextR

/-- DATA-cotransitive classifier for a positive cell contained in the successor
segment.  The branch is chosen by cell properness data; the successor-outside
Prop disjunction is used only inside Prop proofs. -/
def lemma34PositiveCellCoverC_of_localDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma left right nextL nextR t_pt : CReal}
    (D : Lemma34PositiveCellLocalDataC left right nextL nextR)
    (hnew :
      regularSeqLtProp nextR t_pt ∨
        regularSeqLtProp t_pt nextL) :
    PSum
      (Lemma34ZeroCollarC (eps := eps) P sigma t_pt)
      (PSum
        (regularSeqLtProp right t_pt)
        (regularSeqLtProp t_pt left)) := by
  cases regularSeqLtData_cotrans left right t_pt D.cell_strict with
  | inl hleft_t =>
      exact PSum.inr (PSum.inl (by
        rcases hnew with hright | hleft
        · exact regularSeqLtProp_of_le_of_lt D.right_le_next hright
        · have ht_left : regularSeqLtProp t_pt left :=
            regularSeqLtProp_of_lt_of_le hleft D.next_le_left
          exact False.elim
            (regularSeqLtProp_irrefl left
              (regularSeqLtProp_trans left t_pt left
                hleft_t.toProp ht_left))))
  | inr ht_right =>
      exact PSum.inr (PSum.inr (by
        rcases hnew with hright | hleft
        · have hright_t : regularSeqLtProp right t_pt :=
            regularSeqLtProp_of_le_of_lt D.right_le_next hright
          exact False.elim
            (regularSeqLtProp_irrefl right
              (regularSeqLtProp_trans right t_pt right
                hright_t ht_right.toProp))
        · exact regularSeqLtProp_of_lt_of_le hleft D.next_le_left))

/-- Local data for one cell: either it is a zero cell with a profile collar, or
it is a positive cell contained in the successor segment. -/
structure Lemma34CellLocalDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (sigma left right nextL nextR : CReal) :
    Type 2 where
  data :
    PSum
      (Lemma34ZeroCellLocalDataC (eps := eps) P sigma left right)
      (Lemma34PositiveCellLocalDataC left right nextL nextR)

/-- Construct the one-cell Type-valued cover from local zero/positive data. -/
def lemma34CellCoverC_of_localDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma left right nextL nextR t_pt : CReal}
    (D : Lemma34CellLocalDataC (eps := eps) P sigma left right nextL nextR)
    (hnew :
      regularSeqLtProp nextR t_pt ∨
        regularSeqLtProp t_pt nextL) :
    PSum
      (Lemma34ZeroCollarC (eps := eps) P sigma t_pt)
      (PSum
        (regularSeqLtProp right t_pt)
        (regularSeqLtProp t_pt left)) := by
  cases D.data with
  | inl Z =>
      exact lemma34ZeroCellCoverC_of_localDataC P Z
  | inr Pos =>
      exact lemma34PositiveCellCoverC_of_localDataC P Pos hnew

/-- Column scan data whose per-cell classifier is supplied in local
zero/positive form rather than as a raw `cellCover` function. -/
structure Lemma34ColumnLocalCellScanDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n) : Type 2 where
  refinement : Lemma34ColumnRefinementC (eps := eps) P n k T j
  radius : CReal
  radius_pos : regularSeqLtProp CReal.zero radius
  N : Nat
  N_pos : 0 < N
  pts : Nat → CReal
  pts_zero : pts 0 ≈ T.segL j
  pts_N : pts N ≈ T.segR j
  cellLocal :
    ∀ i : Nat, i < N →
      Lemma34CellLocalDataC (eps := eps) P radius
        (pts i) (pts (i + 1))
        refinement.segL_next refinement.segR_next

/-- Local zero/positive cell data produces the finite-cell scan payload. -/
def lemma34ColumnCellScanDataC_of_localCellScanC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnLocalCellScanDataC (eps := eps) P n k T j) :
    Lemma34ColumnCellScanDataC (eps := eps) P n k T j :=
  { refinement := D.refinement
    radius := D.radius
    radius_pos := D.radius_pos
    N := D.N
    N_pos := D.N_pos
    pts := D.pts
    pts_zero := D.pts_zero
    pts_N := D.pts_N
    cellCover := by
      intro t_pt _hat _htb hnew i hi
      exact lemma34CellCoverC_of_localDataC P (D.cellLocal i hi) hnew }

/-- Provider form of the local zero/positive finite-cell scan payload. -/
structure Lemma34ColumnLocalCellScanProviderC : Type 2 where
  localCellScan :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnLocalCellScanDataC (eps := eps) P n k T j

/-- Local zero/positive cell-scan data supplies the previous cell-scan
provider. -/
noncomputable def lemma34ColumnCellScanProviderC_of_localCellScanProviderC
    (provider : Lemma34ColumnLocalCellScanProviderC) :
    Lemma34ColumnCellScanProviderC where
  cellScan := by
    intro a b eps hab P heps n h_cond k T j
    exact lemma34ColumnCellScanDataC_of_localCellScanC P n k T j
      (provider.localCellScan P heps n h_cond k T j)

/-- Source-faithful Lemma 3.4 DATA reducer from local zero/positive finite-cell
scan data. -/
noncomputable def lemma_3_4DataC_of_localCellScanProviderC
    (provider : Lemma34ColumnLocalCellScanProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_cellScanProviderC
    (lemma34ColumnCellScanProviderC_of_localCellScanProviderC provider)
    P heps n hn h_cond

/-- Zero-cell local data specialized to an actual `p_prime_ltC` witness.  The
extra fields are exactly the collar arithmetic needed to shrink the p-prime
alpha-neighbourhood to the step radius `sigma`. -/
structure Lemma34ZeroCellPPrimeDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (sigma left right : CReal) : Type 2 where
  pprime : P.p_prime_ltC left right eps
  left_gap : regularSeqLtData (CReal.sub left sigma) left
  right_gap : regularSeqLtData right (CReal.add right sigma)
  subset_left_of_near :
    ∀ t_pt : CReal,
      regularSeqLtProp (CReal.sub left sigma) t_pt →
      RegularSeqLe
        (CReal.max a (CReal.sub left pprime.alpha))
        (CReal.max a (CReal.sub t_pt sigma))
  subset_right_of_near :
    ∀ t_pt : CReal,
      regularSeqLtProp t_pt (CReal.add right sigma) →
      RegularSeqLe
        (CReal.min b (CReal.add t_pt sigma))
        (CReal.min b (CReal.add right pprime.alpha))

/-- Convert a p-prime zero-cell payload into the generic zero-cell local data. -/
def lemma34ZeroCellLocalDataC_of_pprimeDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma left right : CReal}
    (D : Lemma34ZeroCellPPrimeDataC (eps := eps) P sigma left right) :
    Lemma34ZeroCellLocalDataC (eps := eps) P sigma left right :=
  { omega := D.pprime.alpha
    omega_pos := D.pprime.alpha_pos
    source := D.pprime.inner
    left_gap := D.left_gap
    right_gap := D.right_gap
    subset_left_of_near := D.subset_left_of_near
    subset_right_of_near := D.subset_right_of_near }

/-- One cell supplied either by a p-prime zero-cell payload or by positive-cell
successor containment. -/
structure Lemma34CellPPrimeDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (sigma left right nextL nextR : CReal) :
    Type 2 where
  data :
    PSum
      (Lemma34ZeroCellPPrimeDataC (eps := eps) P sigma left right)
      (Lemma34PositiveCellLocalDataC left right nextL nextR)

/-- Convert p-prime/positive cell data into the generic local cell data. -/
def lemma34CellLocalDataC_of_pprimeDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma left right nextL nextR : CReal}
    (D : Lemma34CellPPrimeDataC (eps := eps) P sigma left right nextL nextR) :
    Lemma34CellLocalDataC (eps := eps) P sigma left right nextL nextR := by
  cases D.data with
  | inl Z =>
      exact
        { data := PSum.inl
            (lemma34ZeroCellLocalDataC_of_pprimeDataC P Z) }
  | inr Pos =>
      exact { data := PSum.inr Pos }

/-- Column scan data in the form closest to Lemma 3.3: zero cells carry an
actual p-prime witness, positive cells carry successor containment. -/
structure Lemma34ColumnPPrimeCellScanDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n) : Type 2 where
  refinement : Lemma34ColumnRefinementC (eps := eps) P n k T j
  radius : CReal
  radius_pos : regularSeqLtProp CReal.zero radius
  N : Nat
  N_pos : 0 < N
  pts : Nat → CReal
  pts_zero : pts 0 ≈ T.segL j
  pts_N : pts N ≈ T.segR j
  cellData :
    ∀ i : Nat, i < N →
      Lemma34CellPPrimeDataC (eps := eps) P radius
        (pts i) (pts (i + 1))
        refinement.segL_next refinement.segR_next

/-- Convert p-prime/positive column scan data into local zero/positive scan
data. -/
def lemma34ColumnLocalCellScanDataC_of_pprimeCellScanC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnPPrimeCellScanDataC (eps := eps) P n k T j) :
    Lemma34ColumnLocalCellScanDataC (eps := eps) P n k T j :=
  { refinement := D.refinement
    radius := D.radius
    radius_pos := D.radius_pos
    N := D.N
    N_pos := D.N_pos
    pts := D.pts
    pts_zero := D.pts_zero
    pts_N := D.pts_N
    cellLocal := by
      intro i hi
      exact lemma34CellLocalDataC_of_pprimeDataC P (D.cellData i hi) }

/-- Provider form of p-prime/positive finite-cell scan data. -/
structure Lemma34ColumnPPrimeCellScanProviderC : Type 2 where
  pprimeCellScan :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnPPrimeCellScanDataC (eps := eps) P n k T j

/-- p-prime/positive cell-scan data supplies the local cell-scan provider. -/
noncomputable def lemma34ColumnLocalCellScanProviderC_of_pprimeCellScanProviderC
    (provider : Lemma34ColumnPPrimeCellScanProviderC) :
    Lemma34ColumnLocalCellScanProviderC where
  localCellScan := by
    intro a b eps hab P heps n h_cond k T j
    exact lemma34ColumnLocalCellScanDataC_of_pprimeCellScanC P n k T j
      (provider.pprimeCellScan P heps n h_cond k T j)

/-- Source-faithful Lemma 3.4 DATA reducer from p-prime/positive finite-cell
scan data. -/
noncomputable def lemma_3_4DataC_of_pprimeCellScanProviderC
    (provider : Lemma34ColumnPPrimeCellScanProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_localCellScanProviderC
    (lemma34ColumnLocalCellScanProviderC_of_pprimeCellScanProviderC provider)
    P heps n hn h_cond

/-- Subinterval form of Lemma 3.3 output, suitable for refining one tower
column.  Unlike `Lemma33ResultC`, the endpoints are arbitrary `u,v` inside the
ambient profile interval, while the cell conclusions still use ambient
`P.p_prime_ltC`. -/
structure Lemma33SubResultDataC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (u v : CReal) (m : Nat) : Type 2 where
  N : Nat
  N_pos : 0 < N
  pts : Nat → CReal
  pts_zero : pts 0 ≈ u
  pts_N : pts N ≈ v
  pts_strict_data : ∀ i : Nat, i < N →
    regularSeqLtData (pts i) (pts (i + 1))
  width_le : ∀ i : Nat, i < N →
    RegularSeqLe (CReal.sub (pts (i + 1)) (pts i)) delta
  M : Nat → Nat
  sum_M : lemma33PrefixNatC M N = m
  p_prime_cond : ∀ i : Nat, i < N →
    P.p_prime_ltC (pts i) (pts (i + 1))
      (CReal.mul (constSeq (Nat.cast (M i + 1))) eps)

/-- If the Lemma 3.3 multiplicity of a subinterval cell is zero, its stored
`p'_lt` bound reduces from `(M i + 1) * eps` to `eps`.  This removes the
coefficient-transport burden from the Lemma 3.4 zero-cell frontier. -/
def lemma33SubResult_p_prime_eps_of_M_zeroC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {u v : CReal} {m i : Nat}
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta) P u v m)
    (hi : i < D.N) (hzero : D.M i = 0) :
    P.p_prime_ltC (D.pts i) (D.pts (i + 1)) eps := by
  have hp := D.p_prime_cond i hi
  have hcoeff :
      CReal.mul (constSeq (Nat.cast (D.M i + 1))) eps ≈
        CReal.mul (constSeq (Nat.cast (0 + 1))) eps := by
    rw [hzero]
  have hone : CReal.mul (constSeq (Nat.cast (0 + 1))) eps ≈ eps := by
    simpa using CReal.one_mul eps
  have heq :
      CReal.mul (constSeq (Nat.cast (D.M i + 1))) eps ≈ eps :=
    Setoid.trans hcoeff hone
  have hle :
      RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (D.M i + 1))) eps) eps :=
    regularSeqLe_of_left_eventual heq (regularSeqLe_refl eps)
  exact ProfileC.p_prime_ltC_mono P hp hle

/-- One-column scan data phrased via a subinterval Lemma 3.3 result. -/
structure Lemma34ColumnSubResultCellScanDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n) : Type 2 where
  refinement : Lemma34ColumnRefinementC (eps := eps) P n k T j
  radius : CReal
  radius_pos : regularSeqLtProp CReal.zero radius
  m : Nat
  delta : CReal
  result :
    Lemma33SubResultDataC (eps := eps) (delta := delta)
      P (T.segL j) (T.segR j) m
  cellData :
    ∀ i : Nat, i < result.N →
      Lemma34CellPPrimeDataC (eps := eps) P radius
        (result.pts i) (result.pts (i + 1))
        refinement.segL_next refinement.segR_next

/-- A subinterval Lemma 3.3 result with p-prime/positive cell classification
supplies the p-prime finite-cell scan payload. -/
def lemma34ColumnPPrimeCellScanDataC_of_subResultCellScanC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultCellScanDataC (eps := eps) P n k T j) :
    Lemma34ColumnPPrimeCellScanDataC (eps := eps) P n k T j :=
  { refinement := D.refinement
    radius := D.radius
    radius_pos := D.radius_pos
    N := D.result.N
    N_pos := D.result.N_pos
    pts := D.result.pts
    pts_zero := D.result.pts_zero
    pts_N := D.result.pts_N
    cellData := D.cellData }

/-- Provider form of the subinterval Lemma 3.3/cell-classification payload. -/
structure Lemma34ColumnSubResultCellScanProviderC : Type 2 where
  subResultCellScan :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnSubResultCellScanDataC (eps := eps) P n k T j

/-- Subinterval Lemma 3.3/cell-classification data supplies the p-prime
cell-scan provider. -/
noncomputable def lemma34ColumnPPrimeCellScanProviderC_of_subResultProviderC
    (provider : Lemma34ColumnSubResultCellScanProviderC) :
    Lemma34ColumnPPrimeCellScanProviderC where
  pprimeCellScan := by
    intro a b eps hab P heps n h_cond k T j
    exact lemma34ColumnPPrimeCellScanDataC_of_subResultCellScanC P n k T j
      (provider.subResultCellScan P heps n h_cond k T j)

/-- Source-faithful Lemma 3.4 DATA reducer from subinterval Lemma 3.3
cell-classification data. -/
noncomputable def lemma_3_4DataC_of_subResultCellScanProviderC
    (provider : Lemma34ColumnSubResultCellScanProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_pprimeCellScanProviderC
    (lemma34ColumnPPrimeCellScanProviderC_of_subResultProviderC provider)
    P heps n hn h_cond

/-- The subdivision part of one column step, separated from the cell
classification.  This is the pure "produce the subinterval Lemma 3.3 result"
payload. -/
structure Lemma34ColumnSubResultDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n) : Type 2 where
  refinement : Lemma34ColumnRefinementC (eps := eps) P n k T j
  radius : CReal
  radius_pos : regularSeqLtProp CReal.zero radius
  m : Nat
  delta : CReal
  result :
    Lemma33SubResultDataC (eps := eps) (delta := delta)
      P (T.segL j) (T.segR j) m

/-- Add a cell classifier to a pure subresult payload. -/
def lemma34ColumnSubResultCellScanDataC_of_splitC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j)
    (cellData :
      ∀ i : Nat, i < D.result.N →
        Lemma34CellPPrimeDataC (eps := eps) P D.radius
          (D.result.pts i) (D.result.pts (i + 1))
          D.refinement.segL_next D.refinement.segR_next) :
    Lemma34ColumnSubResultCellScanDataC (eps := eps) P n k T j :=
  { refinement := D.refinement
    radius := D.radius
    radius_pos := D.radius_pos
    m := D.m
    delta := D.delta
    result := D.result
    cellData := cellData }

/-- Provider form split into two responsibilities:
1. produce the column subresult/refinement/radius data;
2. classify each cell of that subresult as zero or positive. -/
structure Lemma34ColumnSubResultSplitProviderC : Type 2 where
  subResult :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnSubResultDataC (eps := eps) P n k T j
  classify :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j) →
      ∀ i : Nat, i < D.result.N →
        Lemma34CellPPrimeDataC (eps := eps) P D.radius
          (D.result.pts i) (D.result.pts (i + 1))
          D.refinement.segL_next D.refinement.segR_next

/-- The split provider supplies the previous combined subresult-cell provider. -/
noncomputable def lemma34ColumnSubResultCellScanProviderC_of_splitProviderC
    (provider : Lemma34ColumnSubResultSplitProviderC) :
    Lemma34ColumnSubResultCellScanProviderC where
  subResultCellScan := by
    intro a b eps hab P heps n h_cond k T j
    let D := provider.subResult P heps n h_cond k T j
    exact lemma34ColumnSubResultCellScanDataC_of_splitC P n k T j D
      (provider.classify P heps n h_cond k T j D)

/-- Source-faithful Lemma 3.4 DATA reducer from the split subresult/classifier
provider. -/
noncomputable def lemma_3_4DataC_of_subResultSplitProviderC
    (provider : Lemma34ColumnSubResultSplitProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_subResultCellScanProviderC
    (lemma34ColumnSubResultCellScanProviderC_of_splitProviderC provider)
    P heps n hn h_cond

/-- Multiplicity-based classifier for the cells of one subresult.  This mirrors
the source proof split: `M i = 0` is a zero cell; `0 < M i` is a positive cell. -/
structure Lemma34ColumnSubResultMultiplicityClassifierC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j) : Type 2 where
  zeroData :
    ∀ i : Nat, (hi : i < D.result.N) →
      D.result.M i = 0 →
      Lemma34ZeroCellPPrimeDataC (eps := eps) P D.radius
        (D.result.pts i) (D.result.pts (i + 1))
  positiveData :
    ∀ i : Nat, (hi : i < D.result.N) →
      0 < D.result.M i →
      Lemma34PositiveCellLocalDataC
        (D.result.pts i) (D.result.pts (i + 1))
        D.refinement.segL_next D.refinement.segR_next

/-- Convert multiplicity-based zero/positive data into the generic p-prime
cell data for one cell. -/
def lemma34CellPPrimeDataC_of_multiplicityC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {n k : Nat}
    {T : Lemma34TowerC (eps := eps) P n k} {j : Fin n}
    {D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j}
    (C : Lemma34ColumnSubResultMultiplicityClassifierC
      (eps := eps) P n k T j D)
    (i : Nat) (hi : i < D.result.N) :
    Lemma34CellPPrimeDataC (eps := eps) P D.radius
      (D.result.pts i) (D.result.pts (i + 1))
      D.refinement.segL_next D.refinement.segR_next := by
  by_cases hzero : D.result.M i = 0
  · exact { data := PSum.inl (C.zeroData i hi hzero) }
  · have hpos : 0 < D.result.M i := Nat.pos_of_ne_zero hzero
    exact { data := PSum.inr (C.positiveData i hi hpos) }

/-- A pure subresult together with a multiplicity classifier supplies the
previous split subresult/cell payload. -/
def lemma34ColumnSubResultCellScanDataC_of_multiplicityC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j)
    (C : Lemma34ColumnSubResultMultiplicityClassifierC
      (eps := eps) P n k T j D) :
    Lemma34ColumnSubResultCellScanDataC (eps := eps) P n k T j :=
  lemma34ColumnSubResultCellScanDataC_of_splitC P n k T j D
    (fun i hi => lemma34CellPPrimeDataC_of_multiplicityC P C i hi)

/-- Provider form of the multiplicity-based frontier. -/
structure Lemma34ColumnSubResultMultiplicityProviderC : Type 2 where
  subResult :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnSubResultDataC (eps := eps) P n k T j
  classify :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j) →
      Lemma34ColumnSubResultMultiplicityClassifierC
        (eps := eps) P n k T j D

/-- Multiplicity-based provider supplies the split subresult/classifier
provider. -/
noncomputable def lemma34ColumnSubResultSplitProviderC_of_multiplicityProviderC
    (provider : Lemma34ColumnSubResultMultiplicityProviderC) :
    Lemma34ColumnSubResultSplitProviderC where
  subResult := by
    intro a b eps hab P heps n h_cond k T j
    exact provider.subResult P heps n h_cond k T j
  classify := by
    intro a b eps hab P heps n h_cond k T j D i hi
    exact lemma34CellPPrimeDataC_of_multiplicityC P
      (provider.classify P heps n h_cond k T j D) i hi

/-- Source-faithful Lemma 3.4 DATA reducer from multiplicity-based subresult
data. -/
noncomputable def lemma_3_4DataC_of_subResultMultiplicityProviderC
    (provider : Lemma34ColumnSubResultMultiplicityProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_subResultSplitProviderC
    (lemma34ColumnSubResultSplitProviderC_of_multiplicityProviderC provider)
    P heps n hn h_cond

/-- The remaining zero-cell payload after the multiplicity-zero p-prime
transport has been made automatic.  This records only the collar arithmetic
around the already determined `pprime.alpha`. -/
structure Lemma34ZeroCellCollarDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (sigma left right : CReal)
    (pprime : P.p_prime_ltC left right eps) : Type 2 where
  left_gap : regularSeqLtData (CReal.sub left sigma) left
  right_gap : regularSeqLtData right (CReal.add right sigma)
  subset_left_of_near :
    ∀ t_pt : CReal,
      regularSeqLtProp (CReal.sub left sigma) t_pt →
      RegularSeqLe
        (CReal.max a (CReal.sub left pprime.alpha))
        (CReal.max a (CReal.sub t_pt sigma))
  subset_right_of_near :
    ∀ t_pt : CReal,
      regularSeqLtProp t_pt (CReal.add right sigma) →
      RegularSeqLe
        (CReal.min b (CReal.add t_pt sigma))
        (CReal.min b (CReal.add right pprime.alpha))

/-- Reattach the automatic p-prime witness to collar data. -/
def lemma34ZeroCellPPrimeDataC_of_collarDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma left right : CReal}
    {pprime : P.p_prime_ltC left right eps}
    (D : Lemma34ZeroCellCollarDataC (eps := eps) P sigma left right pprime) :
    Lemma34ZeroCellPPrimeDataC (eps := eps) P sigma left right :=
  { pprime := pprime
    left_gap := D.left_gap
    right_gap := D.right_gap
    subset_left_of_near := D.subset_left_of_near
    subset_right_of_near := D.subset_right_of_near }

/-- Multiplicity classifier with the zero branch reduced to collar arithmetic.
The `M i = 0` p-prime witness is reconstructed from the subresult by
`lemma33SubResult_p_prime_eps_of_M_zeroC`. -/
structure Lemma34ColumnSubResultZeroCollarClassifierC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j) : Type 2 where
  zeroCollar :
    ∀ i : Nat, (hi : i < D.result.N) →
      (hzero : D.result.M i = 0) →
      Lemma34ZeroCellCollarDataC (eps := eps) P D.radius
        (D.result.pts i) (D.result.pts (i + 1))
        (lemma33SubResult_p_prime_eps_of_M_zeroC P D.result hi hzero)
  positiveData :
    ∀ i : Nat, (hi : i < D.result.N) →
      0 < D.result.M i →
      Lemma34PositiveCellLocalDataC
        (D.result.pts i) (D.result.pts (i + 1))
        D.refinement.segL_next D.refinement.segR_next

/-- A zero-collar classifier supplies the previous multiplicity classifier. -/
def lemma34ColumnSubResultMultiplicityClassifierC_of_zeroCollarC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j)
    (C : Lemma34ColumnSubResultZeroCollarClassifierC
      (eps := eps) P n k T j D) :
    Lemma34ColumnSubResultMultiplicityClassifierC
      (eps := eps) P n k T j D :=
  { zeroData := by
      intro i hi hzero
      exact lemma34ZeroCellPPrimeDataC_of_collarDataC P
        (C.zeroCollar i hi hzero)
    positiveData := C.positiveData }

/-- Provider form after removing the automatic p-prime transport from the
zero branch. -/
structure Lemma34ColumnSubResultZeroCollarProviderC : Type 2 where
  subResult :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnSubResultDataC (eps := eps) P n k T j
  classify :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j) →
      Lemma34ColumnSubResultZeroCollarClassifierC
        (eps := eps) P n k T j D

/-- Zero-collar provider supplies the multiplicity provider. -/
noncomputable def lemma34ColumnSubResultMultiplicityProviderC_of_zeroCollarProviderC
    (provider : Lemma34ColumnSubResultZeroCollarProviderC) :
    Lemma34ColumnSubResultMultiplicityProviderC where
  subResult := by
    intro a b eps hab P heps n h_cond k T j
    exact provider.subResult P heps n h_cond k T j
  classify := by
    intro a b eps hab P heps n h_cond k T j D
    exact lemma34ColumnSubResultMultiplicityClassifierC_of_zeroCollarC
      P n k T j D (provider.classify P heps n h_cond k T j D)

/-- Source-faithful Lemma 3.4 DATA reducer from the zero-collar frontier. -/
noncomputable def lemma_3_4DataC_of_subResultZeroCollarProviderC
    (provider : Lemma34ColumnSubResultZeroCollarProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_subResultMultiplicityProviderC
    (lemma34ColumnSubResultMultiplicityProviderC_of_zeroCollarProviderC provider)
    P heps n hn h_cond

/-- Positive-cell payload after the strictness field is supplied automatically
by the subresult cell strictness.  Only successor-segment containment remains. -/
structure Lemma34PositiveCellContainmentDataC
    (left right nextL nextR : CReal) : Type where
  next_le_left : RegularSeqLe nextL left
  right_le_next : RegularSeqLe right nextR

/-- Reattach DATA strictness to positive-cell containment data. -/
def lemma34PositiveCellLocalDataC_of_containmentC
    {left right nextL nextR : CReal}
    (cell_strict : regularSeqLtData left right)
    (D : Lemma34PositiveCellContainmentDataC left right nextL nextR) :
    Lemma34PositiveCellLocalDataC left right nextL nextR :=
  { cell_strict := cell_strict
    next_le_left := D.next_le_left
    right_le_next := D.right_le_next }

/-- Classifier frontier with both automatic pieces removed:
zero cells still need collar arithmetic, while positive cells only need
successor containment. -/
structure Lemma34ColumnSubResultGeometryClassifierC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j) : Type 2 where
  zeroCollar :
    ∀ i : Nat, (hi : i < D.result.N) →
      (hzero : D.result.M i = 0) →
      Lemma34ZeroCellCollarDataC (eps := eps) P D.radius
        (D.result.pts i) (D.result.pts (i + 1))
        (lemma33SubResult_p_prime_eps_of_M_zeroC P D.result hi hzero)
  positiveContainment :
    ∀ i : Nat, (hi : i < D.result.N) →
      0 < D.result.M i →
      Lemma34PositiveCellContainmentDataC
        (D.result.pts i) (D.result.pts (i + 1))
        D.refinement.segL_next D.refinement.segR_next

/-- Geometry classifier supplies the zero-collar classifier. -/
def lemma34ColumnSubResultZeroCollarClassifierC_of_geometryC
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (T : Lemma34TowerC (eps := eps) P n k) (j : Fin n)
    (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j)
    (G : Lemma34ColumnSubResultGeometryClassifierC
      (eps := eps) P n k T j D) :
    Lemma34ColumnSubResultZeroCollarClassifierC
      (eps := eps) P n k T j D :=
  { zeroCollar := G.zeroCollar
    positiveData := by
      intro i hi hpos
      exact lemma34PositiveCellLocalDataC_of_containmentC
        (D.result.pts_strict_data i hi)
        (G.positiveContainment i hi hpos) }

/-- Provider form after reducing positive cells to containment. -/
structure Lemma34ColumnSubResultGeometryProviderC : Type 2 where
  subResult :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      Lemma34ColumnSubResultDataC (eps := eps) P n k T j
  classify :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      (P : ProfileC a b hab) →
      (heps : regularSeqLtProp zeroSeq eps) →
      (n : Nat) →
      (h_cond : regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) →
      (k : Nat) →
      (T : Lemma34TowerC (eps := eps) P n k) →
      (j : Fin n) →
      (D : Lemma34ColumnSubResultDataC (eps := eps) P n k T j) →
      Lemma34ColumnSubResultGeometryClassifierC
        (eps := eps) P n k T j D

/-- Geometry provider supplies the zero-collar provider. -/
noncomputable def lemma34ColumnSubResultZeroCollarProviderC_of_geometryProviderC
    (provider : Lemma34ColumnSubResultGeometryProviderC) :
    Lemma34ColumnSubResultZeroCollarProviderC where
  subResult := by
    intro a b eps hab P heps n h_cond k T j
    exact provider.subResult P heps n h_cond k T j
  classify := by
    intro a b eps hab P heps n h_cond k T j D
    exact lemma34ColumnSubResultZeroCollarClassifierC_of_geometryC
      P n k T j D (provider.classify P heps n h_cond k T j D)

/-- Source-faithful Lemma 3.4 DATA reducer from the geometry frontier. -/
noncomputable def lemma_3_4DataC_of_subResultGeometryProviderC
    (provider : Lemma34ColumnSubResultGeometryProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond : regularSeqLtProp
      (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma_3_4DataC_of_subResultZeroCollarProviderC
    (lemma34ColumnSubResultZeroCollarProviderC_of_geometryProviderC provider)
    P heps n hn h_cond

/-- CReal-native retained block for the source-faithful Lemma 3.4 tower.
Zero-multiplicity subintervals are not stored as blocks; they are used only in
the outside/collar argument. -/
structure Lemma34BlockC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat) where
  left : CReal
  right : CReal
  mult : Nat
  mult_pos : 0 < mult
  left_bound : RegularSeqLe a left
  proper : regularSeqLtProp left right
  right_bound : RegularSeqLe right b
  width : RegularSeqLe (CReal.sub right left) (lemma34WidthScaleC a b k)
  budget :
    P.p_prime_ltC left right
      (CReal.mul (constSeq (Nat.cast (mult + 1))) eps)

/-- Repeat a retained block according to its positive multiplicity. -/
def Lemma34BlockC.expand {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k) : List (CReal × CReal) :=
  List.replicate B.mult (B.left, B.right)

/-- Total multiplicity of a CReal block family. -/
def lemma34TotalMultiplicityC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k)) : Nat :=
  (blocks.map (fun B => B.mult)).sum

/-- Flatten a CReal block family into the repeated segment enumeration. -/
def lemma34FlattenBlocksC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k)) :
    List (CReal × CReal) :=
  blocks.flatMap (fun B => B.expand)

/-- Monotonicity of the point sequence returned by a subinterval Lemma 3.3
DATA result. -/
theorem lemma33SubResult_pts_le_addC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {u v : CReal} {m : Nat}
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta) P u v m)
    (i q : Nat) (h : i + q ≤ D.N) :
    RegularSeqLe (D.pts i) (D.pts (i + q)) := by
  induction q with
  | zero =>
      simpa using regularSeqLe_refl (D.pts i)
  | succ q ih =>
      have hprev : i + q ≤ D.N := by omega
      have hstepIndex : i + q < D.N := by omega
      have hstep :
          RegularSeqLe (D.pts (i + q)) (D.pts (i + q + 1)) :=
        regularSeqLe_of_ltPropC
          ((D.pts_strict_data (i + q) hstepIndex).toProp)
      exact regularSeqLe_trans (ih hprev)
        (by simpa [Nat.add_assoc] using hstep)

/-- Arbitrary-index monotonicity for a subinterval Lemma 3.3 DATA result. -/
theorem lemma33SubResult_pts_leC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {u v : CReal} {m : Nat}
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta) P u v m)
    {i j : Nat} (hij : i ≤ j) (hjN : j ≤ D.N) :
    RegularSeqLe (D.pts i) (D.pts j) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact lemma33SubResult_pts_le_addC D i q hjN

/-- One positive-multiplicity cell of a subinterval Lemma 3.3 result becomes a
successor-level retained block. -/
def lemma34ChildBlockOfSubResultC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1)))
    (i : Nat) (hi : i < D.N) (hm : 0 < D.M i) :
    Lemma34BlockC (eps := eps) P (k + 1) := by
  have hparentLeft : RegularSeqLe B.left (D.pts i) := by
    have h0 : RegularSeqLe (D.pts 0) (D.pts i) :=
      lemma33SubResult_pts_leC D (Nat.zero_le i) (Nat.le_of_lt hi)
    exact regularSeqLe_of_left_eventual (Setoid.symm D.pts_zero) h0
  have hparentRight : RegularSeqLe (D.pts (i + 1)) B.right := by
    have hN : RegularSeqLe (D.pts (i + 1)) (D.pts D.N) :=
      lemma33SubResult_pts_leC D (by omega) (Nat.le_refl D.N)
    exact regularSeqLe_of_right_eventual D.pts_N hN
  exact
    { left := D.pts i
      right := D.pts (i + 1)
      mult := D.M i
      mult_pos := hm
      left_bound := regularSeqLe_trans B.left_bound hparentLeft
      proper := (D.pts_strict_data i hi).toProp
      right_bound := regularSeqLe_trans hparentRight B.right_bound
      width := regularSeqLe_trans (D.width_le i hi) hdelta
      budget := D.p_prime_cond i hi }

/-- Every child block obtained from a positive subresult cell lies inside its
parent block. -/
theorem lemma34ChildBlockOfSubResult_insideC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1)))
    (i : Nat) (hi : i < D.N) (hm : 0 < D.M i) :
    RegularSeqLe B.left
        (lemma34ChildBlockOfSubResultC B D hdelta i hi hm).left ∧
      RegularSeqLe
        (lemma34ChildBlockOfSubResultC B D hdelta i hi hm).right
        B.right := by
  constructor
  · change RegularSeqLe B.left (D.pts i)
    have h0 : RegularSeqLe (D.pts 0) (D.pts i) :=
      lemma33SubResult_pts_leC D (Nat.zero_le i) (Nat.le_of_lt hi)
    exact regularSeqLe_of_left_eventual (Setoid.symm D.pts_zero) h0
  · change RegularSeqLe (D.pts (i + 1)) B.right
    have hN : RegularSeqLe (D.pts (i + 1)) (D.pts D.N) :=
      lemma33SubResult_pts_leC D (by omega) (Nat.le_refl D.N)
    exact regularSeqLe_of_right_eventual D.pts_N hN

/-- Filter a list of subresult cell indices, retaining exactly the positive
multiplicity cells as successor blocks. -/
def lemma34ChildBlocksOfSubResultC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1))) :
    List Nat → List (Lemma34BlockC (eps := eps) P (k + 1))
  | [] => []
  | i :: is =>
      if hi : i < D.N then
        if hm : 0 < D.M i then
          lemma34ChildBlockOfSubResultC B D hdelta i hi hm ::
            lemma34ChildBlocksOfSubResultC B D hdelta is
        else
          lemma34ChildBlocksOfSubResultC B D hdelta is
      else
        lemma34ChildBlocksOfSubResultC B D hdelta is

/-- Every retained child block from an arbitrary index list lies inside its
parent block. -/
theorem lemma34ChildBlocksOfSubResult_insideC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1)))
    (xs : List Nat)
    {C : Lemma34BlockC (eps := eps) P (k + 1)}
    (hC : C ∈ lemma34ChildBlocksOfSubResultC B D hdelta xs) :
    RegularSeqLe B.left C.left ∧ RegularSeqLe C.right B.right := by
  induction xs with
  | nil =>
      simp [lemma34ChildBlocksOfSubResultC] at hC
  | cons i is ih =>
      by_cases hi : i < D.N
      · by_cases hm : 0 < D.M i
        · simp [lemma34ChildBlocksOfSubResultC, hi, hm] at hC
          rcases hC with hhead | htail
          · subst C
            exact lemma34ChildBlockOfSubResult_insideC B D hdelta i hi hm
          · exact ih htail
        · simp [lemma34ChildBlocksOfSubResultC, hi, hm] at hC
          exact ih hC
      · simp [lemma34ChildBlocksOfSubResultC, hi] at hC
        exact ih hC

/-- Successor blocks contributed by one parent block from a full subresult. -/
def lemma34RefinedBlocksForSubResultC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1))) :
    List (Lemma34BlockC (eps := eps) P (k + 1)) :=
  lemma34ChildBlocksOfSubResultC B D hdelta (List.range D.N)

/-- Every full-refinement child block lies inside its parent block. -/
theorem lemma34RefinedBlocksForSubResult_insideC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1)))
    {C : Lemma34BlockC (eps := eps) P (k + 1)}
    (hC : C ∈ lemma34RefinedBlocksForSubResultC B D hdelta) :
    RegularSeqLe B.left C.left ∧ RegularSeqLe C.right B.right :=
  lemma34ChildBlocksOfSubResult_insideC B D hdelta (List.range D.N) hC

/-- Total multiplicity is additive over block-list append. -/
theorem lemma34TotalMultiplicityC_append {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (xs ys : List (Lemma34BlockC (eps := eps) P k)) :
    lemma34TotalMultiplicityC (xs ++ ys) =
      lemma34TotalMultiplicityC xs + lemma34TotalMultiplicityC ys := by
  simp [lemma34TotalMultiplicityC]

/-- Filtering positive subresult cells commutes with appending the source
index list. -/
theorem lemma34ChildBlocksOfSubResult_appendC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1)))
    (xs ys : List Nat) :
    lemma34ChildBlocksOfSubResultC B D hdelta (xs ++ ys) =
      lemma34ChildBlocksOfSubResultC B D hdelta xs ++
        lemma34ChildBlocksOfSubResultC B D hdelta ys := by
  induction xs with
  | nil =>
      simp [lemma34ChildBlocksOfSubResultC]
  | cons i is ih =>
      by_cases hi : i < D.N
      · by_cases hm : 0 < D.M i
        · simp [lemma34ChildBlocksOfSubResultC, hi, hm, ih]
        · simp [lemma34ChildBlocksOfSubResultC, hi, hm, ih]
      · simp [lemma34ChildBlocksOfSubResultC, hi, ih]

/-- The retained child blocks among the first `m` source cells have total
multiplicity equal to the prefix sum of the subresult multiplicities. -/
theorem lemma34ChildBlocksOfSubResult_total_prefixC
    {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1)))
    (m : Nat) (hm : m ≤ D.N) :
    lemma34TotalMultiplicityC
        (lemma34ChildBlocksOfSubResultC B D hdelta (List.range m)) =
      lemma33PrefixNatC D.M m := by
  revert hm
  induction m with
  | zero =>
      intro _
      simp [lemma34ChildBlocksOfSubResultC, lemma34TotalMultiplicityC]
  | succ m ih =>
      intro hm
      have hmN : m < D.N := by omega
      rw [List.range_succ,
        lemma34ChildBlocksOfSubResult_appendC B D hdelta,
        lemma34TotalMultiplicityC_append, ih (by omega)]
      by_cases hM : 0 < D.M m
      · have hsingle :
          lemma34ChildBlocksOfSubResultC B D hdelta [m] =
            [lemma34ChildBlockOfSubResultC B D hdelta m hmN hM] := by
          simp [lemma34ChildBlocksOfSubResultC, hmN, hM]
        rw [hsingle]
        simp [lemma34TotalMultiplicityC, lemma33PrefixNatC,
          lemma34ChildBlockOfSubResultC]
      · have hMz : D.M m = 0 := Nat.eq_zero_of_not_pos hM
        have hsingle :
          lemma34ChildBlocksOfSubResultC B D hdelta [m] = [] := by
          simp [lemma34ChildBlocksOfSubResultC, hmN, hM]
        rw [hsingle]
        simp [lemma34TotalMultiplicityC, lemma33PrefixNatC, hMz]

/-- The retained child blocks of a full subresult have exactly the parent
block multiplicity. -/
theorem lemma34RefinedBlocksForSubResult_totalC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta :
      RegularSeqLe delta (lemma34WidthScaleC a b (k + 1))) :
    lemma34TotalMultiplicityC
      (lemma34RefinedBlocksForSubResultC B D hdelta) = B.mult := by
  calc
    lemma34TotalMultiplicityC
        (lemma34RefinedBlocksForSubResultC B D hdelta) =
        lemma33PrefixNatC D.M D.N :=
      lemma34ChildBlocksOfSubResult_total_prefixC B D hdelta D.N
        (Nat.le_refl D.N)
    _ = B.mult := D.sum_M

/-- Flattening preserves total multiplicity as list length. -/
theorem lemma34FlattenBlocks_lengthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k)) :
    (lemma34FlattenBlocksC blocks).length =
      lemma34TotalMultiplicityC blocks := by
  induction blocks with
  | nil =>
      simp [lemma34FlattenBlocksC, lemma34TotalMultiplicityC]
  | cons B blocks ih =>
      simp [lemma34FlattenBlocksC, Lemma34BlockC.expand,
        lemma34TotalMultiplicityC, ih]

/-- Flattening commutes with block-list append. -/
theorem lemma34FlattenBlocks_appendC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (xs ys : List (Lemma34BlockC (eps := eps) P k)) :
    lemma34FlattenBlocksC (xs ++ ys) =
      lemma34FlattenBlocksC xs ++ lemma34FlattenBlocksC ys := by
  simp [lemma34FlattenBlocksC]

/-- One parent block together with the relative/subinterval Lemma 3.3 data used
to refine it.  This is the CReal counterpart of the abstract
`lemma34_blockRefinementResult` package. -/
structure Lemma34BlockSubResultDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat)
    (B : Lemma34BlockC (eps := eps) P k) : Type 2 where
  delta : CReal
  result :
    Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult
  delta_le_width :
    RegularSeqLe delta (lemma34WidthScaleC a b (k + 1))

/-- Refined successor blocks contributed by one parent block with its
subresult data. -/
def lemma34RefinedBlocksForDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma34BlockSubResultDataC (eps := eps) P k B) :
    List (Lemma34BlockC (eps := eps) P (k + 1)) :=
  lemma34RefinedBlocksForSubResultC B D.result D.delta_le_width

/-- One-block refinement preserves total multiplicity. -/
theorem lemma34RefinedBlocksForData_totalC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma34BlockSubResultDataC (eps := eps) P k B) :
    lemma34TotalMultiplicityC (lemma34RefinedBlocksForDataC B D) =
      B.mult :=
  lemma34RefinedBlocksForSubResult_totalC B D.result D.delta_le_width

/-- Every one-block refinement child is contained in its parent. -/
theorem lemma34RefinedBlocksForData_insideC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma34BlockSubResultDataC (eps := eps) P k B)
    {C : Lemma34BlockC (eps := eps) P (k + 1)}
    (hC : C ∈ lemma34RefinedBlocksForDataC B D) :
    RegularSeqLe B.left C.left ∧ RegularSeqLe C.right B.right :=
  lemma34RefinedBlocksForSubResult_insideC B D.result D.delta_le_width hC

/-- Refine a whole block list by applying the one-block subresult package to
each retained parent block. -/
def lemma34RefinedBlocksFromListC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    List (Lemma34BlockC (eps := eps) P (k + 1)) :=
  blocks.flatMap (fun B => lemma34RefinedBlocksForDataC B (data B))

/-- Refining every block in a list preserves total multiplicity. -/
theorem lemma34RefinedBlocksFromList_totalC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    lemma34TotalMultiplicityC
        (lemma34RefinedBlocksFromListC blocks data) =
      lemma34TotalMultiplicityC blocks := by
  induction blocks with
  | nil =>
      simp [lemma34RefinedBlocksFromListC, lemma34TotalMultiplicityC]
  | cons B blocks ih =>
      change
        lemma34TotalMultiplicityC
          (lemma34RefinedBlocksForDataC B (data B) ++
            lemma34RefinedBlocksFromListC blocks data) =
        B.mult + lemma34TotalMultiplicityC blocks
      rw [lemma34TotalMultiplicityC_append,
        lemma34RefinedBlocksForData_totalC, ih]

/-- The flattened repeated-segment enumeration of a refined block list has
length equal to the original total multiplicity. -/
theorem lemma34RefinedBlocksFromList_flatten_lengthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    (lemma34FlattenBlocksC
        (lemma34RefinedBlocksFromListC blocks data)).length =
      lemma34TotalMultiplicityC blocks := by
  rw [lemma34FlattenBlocks_lengthC,
    lemma34RefinedBlocksFromList_totalC]

/-- Every member of a repeated singleton list is that singleton value. -/
theorem lemma34EqOfMemReplicateC {A : Type*} {x y : A} {n : Nat}
    (h : y ∈ List.replicate n x) : y = x := by
  induction n with
  | zero =>
      simp at h
  | succ n ih =>
      simp only [List.replicate_succ, List.mem_cons] at h
      rcases h with h | h
      · exact h
      · exact ih h

/-- A flattened repeated segment comes from one stored block. -/
theorem lemma34MemFlattenBlocksC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    {blocks : List (Lemma34BlockC (eps := eps) P k)}
    {I : CReal × CReal}
    (hI : I ∈ lemma34FlattenBlocksC blocks) :
    ∃ B, B ∈ blocks ∧ I = (B.left, B.right) := by
  unfold lemma34FlattenBlocksC at hI
  rcases List.mem_flatMap.mp hI with ⟨B, hB, hIB⟩
  have hEq : I = (B.left, B.right) :=
    lemma34EqOfMemReplicateC
      (by simpa [Lemma34BlockC.expand] using hIB)
  exact ⟨B, hB, hEq⟩

/-- Every flattened segment satisfies ambient bounds and properness. -/
theorem lemma34FlattenBlocks_properC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    {blocks : List (Lemma34BlockC (eps := eps) P k)}
    {I : CReal × CReal}
    (hI : I ∈ lemma34FlattenBlocksC blocks) :
    RegularSeqLe a I.1 ∧ regularSeqLtProp I.1 I.2 ∧
      RegularSeqLe I.2 b := by
  rcases lemma34MemFlattenBlocksC hI with ⟨B, _hB, hEq⟩
  subst I
  exact ⟨B.left_bound, B.proper, B.right_bound⟩

/-- Every flattened segment has the width bound stored in its block level. -/
theorem lemma34FlattenBlocks_widthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    {blocks : List (Lemma34BlockC (eps := eps) P k)}
    {I : CReal × CReal}
    (hI : I ∈ lemma34FlattenBlocksC blocks) :
    RegularSeqLe (CReal.sub I.2 I.1) (lemma34WidthScaleC a b k) := by
  rcases lemma34MemFlattenBlocksC hI with ⟨B, _hB, hEq⟩
  subst I
  exact B.width

/-- Source-faithful block tower, retaining the block list while exposing the
same repeated-segment semantics as the existing `Lemma34TowerC`. -/
structure Lemma34BlockTowerC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat) : Type 2 where
  blocks : List (Lemma34BlockC (eps := eps) P k)
  total_mult : lemma34TotalMultiplicityC blocks = n

/-- Convert a source-faithful block tower into the existing repeated-segment
`Lemma34TowerC` API. -/
noncomputable def lemma34TowerC_of_blockTowerC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n k : Nat)
    (BT : Lemma34BlockTowerC (eps := eps) P n k) :
    Lemma34TowerC (eps := eps) P n k :=
  let segments := lemma34FlattenBlocksC BT.blocks
  have hlen : segments.length = n := by
    dsimp [segments]
    rw [lemma34FlattenBlocks_lengthC, BT.total_mult]
  { segL := fun j => (segments.get ⟨j.1, by rw [hlen]; exact j.2⟩).1
    segR := fun j => (segments.get ⟨j.1, by rw [hlen]; exact j.2⟩).2
    seg_proper := by
      intro j
      have hmem :
          segments.get ⟨j.1, by rw [hlen]; exact j.2⟩ ∈ segments :=
        List.get_mem segments ⟨j.1, by rw [hlen]; exact j.2⟩
      simpa using lemma34FlattenBlocks_properC (blocks := BT.blocks) hmem
    seg_width := by
      intro j
      have hmem :
          segments.get ⟨j.1, by rw [hlen]; exact j.2⟩ ∈ segments :=
        List.get_mem segments ⟨j.1, by rw [hlen]; exact j.2⟩
      simpa using lemma34FlattenBlocks_widthC (blocks := BT.blocks) hmem }

/-- Source-faithful successor step for the block tower: refine every retained
parent block by its subinterval Lemma 3.3 data, and retain only the positive
multiplicity children. -/
def lemma34BlockTowerStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34BlockTowerC (eps := eps) P n (k + 1) :=
  { blocks := lemma34RefinedBlocksFromListC BT.blocks data
    total_mult := by
      rw [lemma34RefinedBlocksFromList_totalC, BT.total_mult] }

/-- The repeated-segment tower obtained after one block step has exactly the
same `n` positions. -/
theorem lemma34BlockTowerStep_segments_lengthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    (lemma34FlattenBlocksC
      (lemma34BlockTowerStepC BT data).blocks).length = n := by
  rw [lemma34FlattenBlocks_lengthC,
    (lemma34BlockTowerStepC BT data).total_mult]

/-- One CReal interval is contained in another, expressed by endpoint order. -/
def lemma34IntervalNestedC (I J : CReal × CReal) : Prop :=
  RegularSeqLe I.1 J.1 ∧ RegularSeqLe J.2 I.2

/-- Positionwise containment of two equal-length CReal segment lists. -/
inductive Lemma34SegmentsRefineC :
    List (CReal × CReal) → List (CReal × CReal) → Prop
  | nil : Lemma34SegmentsRefineC [] []
  | cons {I J : CReal × CReal} {Is Js : List (CReal × CReal)} :
      lemma34IntervalNestedC I J →
      Lemma34SegmentsRefineC Is Js →
      Lemma34SegmentsRefineC (I :: Is) (J :: Js)

/-- Positionwise segment refinement preserves list length. -/
theorem lemma34SegmentsRefine_lengthC {xs ys : List (CReal × CReal)}
    (h : Lemma34SegmentsRefineC xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Concatenation preserves positionwise segment refinement. -/
theorem lemma34SegmentsRefine_appendC
    {xs ys us vs : List (CReal × CReal)}
    (hxy : Lemma34SegmentsRefineC xs ys)
    (huv : Lemma34SegmentsRefineC us vs) :
    Lemma34SegmentsRefineC (xs ++ us) (ys ++ vs) := by
  induction hxy with
  | nil => simpa using huv
  | cons hIJ htail ih =>
      simpa using Lemma34SegmentsRefineC.cons hIJ ih

/-- Read a positionwise containment witness at a common list index. -/
theorem lemma34SegmentsRefine_getC
    {xs ys : List (CReal × CReal)}
    (h : Lemma34SegmentsRefineC xs ys) {i : Nat}
    (hix : i < xs.length) (hiy : i < ys.length) :
    lemma34IntervalNestedC
      (xs.get ⟨i, hix⟩) (ys.get ⟨i, hiy⟩) := by
  induction h generalizing i with
  | nil => exact absurd hix (Nat.not_lt_zero i)
  | cons hIJ htail ih =>
      cases i with
      | zero => exact hIJ
      | succ i =>
          exact ih (Nat.lt_of_succ_lt_succ hix)
            (Nat.lt_of_succ_lt_succ hiy)

/-- If every member of `ys` lies in `I`, repeated copies of `I` refine to
`ys`. -/
theorem lemma34SegmentsRefine_replicateC
    (I : CReal × CReal) (ys : List (CReal × CReal))
    (hmem : ∀ J, J ∈ ys → lemma34IntervalNestedC I J) :
    Lemma34SegmentsRefineC (List.replicate ys.length I) ys := by
  revert hmem
  induction ys with
  | nil =>
      intro _
      exact Lemma34SegmentsRefineC.nil
  | cons J Js ih =>
      intro hmem
      rw [List.length_cons, List.replicate_succ]
      exact Lemma34SegmentsRefineC.cons
        (hmem J (by simp))
        (ih (fun K hK => hmem K (by simp [hK])))

/-- Repeated successor segments from one block refine the repeated parent
block. -/
theorem lemma34RefinedBlocksForData_segmentsRefineC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34SegmentsRefineC B.expand
      (lemma34FlattenBlocksC (lemma34RefinedBlocksForDataC B D)) := by
  let children := lemma34RefinedBlocksForDataC B D
  let childSegments := lemma34FlattenBlocksC children
  have hlen : childSegments.length = B.mult := by
    dsimp [childSegments, children]
    rw [lemma34FlattenBlocks_lengthC, lemma34RefinedBlocksForData_totalC]
  have hnested : ∀ I, I ∈ childSegments →
      lemma34IntervalNestedC (B.left, B.right) I := by
    intro I hI
    dsimp [childSegments, children] at hI
    rcases lemma34MemFlattenBlocksC hI with ⟨C, hC, hEq⟩
    subst I
    exact lemma34RefinedBlocksForData_insideC B D hC
  have href := lemma34SegmentsRefine_replicateC
    (I := (B.left, B.right)) childSegments hnested
  have href' : Lemma34SegmentsRefineC
      (List.replicate B.mult (B.left, B.right)) childSegments := by
    simpa [hlen] using href
  simpa [Lemma34BlockC.expand, childSegments, children] using href'

/-- Flat-mapping one-block refinements gives global positionwise refinement. -/
theorem lemma34RefinedBlocksFromList_segmentsRefineC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34SegmentsRefineC
      (lemma34FlattenBlocksC blocks)
      (lemma34FlattenBlocksC
        (lemma34RefinedBlocksFromListC blocks data)) := by
  induction blocks with
  | nil =>
      simpa [lemma34FlattenBlocksC, lemma34RefinedBlocksFromListC] using
        (Lemma34SegmentsRefineC.nil :
          Lemma34SegmentsRefineC ([] : List (CReal × CReal)) [])
  | cons B blocks ih =>
      change Lemma34SegmentsRefineC
        (B.expand ++ lemma34FlattenBlocksC blocks)
        (lemma34FlattenBlocksC
          (lemma34RefinedBlocksForDataC B (data B) ++
            lemma34RefinedBlocksFromListC blocks data))
      rw [lemma34FlattenBlocks_appendC]
      exact lemma34SegmentsRefine_appendC
        (lemma34RefinedBlocksForData_segmentsRefineC B (data B)) ih

/-- One source-faithful block-tower step refines the flattened segment list. -/
theorem lemma34BlockTowerStep_segmentsRefineC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34SegmentsRefineC
      (lemma34FlattenBlocksC BT.blocks)
      (lemma34FlattenBlocksC (lemma34BlockTowerStepC BT data).blocks) := by
  dsimp [lemma34BlockTowerStepC]
  exact lemma34RefinedBlocksFromList_segmentsRefineC BT.blocks data

/-- The source-faithful block-tower step supplies the existing tower-refinement
API. -/
noncomputable def lemma34RefinesC_of_blockTowerStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34RefinesC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT)
      (lemma34TowerC_of_blockTowerC P n (k + 1)
        (lemma34BlockTowerStepC BT data)) := by
  refine { left_mono := ?_, right_mono := ?_ }
  · intro j
    let oldSegments := lemma34FlattenBlocksC BT.blocks
    let BTnext := lemma34BlockTowerStepC BT data
    let newSegments := lemma34FlattenBlocksC BTnext.blocks
    have hOldLen : oldSegments.length = n := by
      dsimp [oldSegments]
      rw [lemma34FlattenBlocks_lengthC, BT.total_mult]
    have hNewLen : newSegments.length = n := by
      dsimp [newSegments, BTnext]
      exact lemma34BlockTowerStep_segments_lengthC BT data
    have href : Lemma34SegmentsRefineC oldSegments newSegments := by
      dsimp [oldSegments, newSegments, BTnext]
      exact lemma34BlockTowerStep_segmentsRefineC BT data
    have h := lemma34SegmentsRefine_getC href
      (i := j.1)
      (by rw [hOldLen]; exact j.2)
      (by rw [hNewLen]; exact j.2)
    simpa [lemma34TowerC_of_blockTowerC, oldSegments, newSegments, BTnext,
      lemma34IntervalNestedC] using h.1
  · intro j
    let oldSegments := lemma34FlattenBlocksC BT.blocks
    let BTnext := lemma34BlockTowerStepC BT data
    let newSegments := lemma34FlattenBlocksC BTnext.blocks
    have hOldLen : oldSegments.length = n := by
      dsimp [oldSegments]
      rw [lemma34FlattenBlocks_lengthC, BT.total_mult]
    have hNewLen : newSegments.length = n := by
      dsimp [newSegments, BTnext]
      exact lemma34BlockTowerStep_segments_lengthC BT data
    have href : Lemma34SegmentsRefineC oldSegments newSegments := by
      dsimp [oldSegments, newSegments, BTnext]
      exact lemma34BlockTowerStep_segmentsRefineC BT data
    have h := lemma34SegmentsRefine_getC href
      (i := j.1)
      (by rw [hOldLen]; exact j.2)
      (by rw [hNewLen]; exact j.2)
    simpa [lemma34TowerC_of_blockTowerC, oldSegments, newSegments, BTnext,
      lemma34IntervalNestedC] using h.2

/-- A globally recorded zero-multiplicity cell from a block-list refinement. -/
structure Lemma34GlobalZeroCellC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) : Type 2 where
  parent : Lemma34BlockC (eps := eps) P k
  parent_mem : parent ∈ blocks
  index : Nat
  index_lt : index < (data parent).result.N
  charge_zero : (data parent).result.M index = 0

/-- Canonical global zero-cell record. -/
def lemma34GlobalZeroCellOfC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ blocks)
    (i : Nat) (hi : i < (data B).result.N)
    (hz : (data B).result.M i = 0) :
    Lemma34GlobalZeroCellC blocks data :=
  { parent := B
    parent_mem := hB
    index := i
    index_lt := hi
    charge_zero := hz }

/-- Filter an index list, retaining precisely the zero-multiplicity cells of
one parent block, but packaging them as global records. -/
def lemma34GlobalZeroCellsForBlockAuxC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ blocks) :
    List Nat → List (Lemma34GlobalZeroCellC blocks data)
  | [] => []
  | i :: is =>
      if hi : i < (data B).result.N then
        if hz : (data B).result.M i = 0 then
          lemma34GlobalZeroCellOfC blocks data B hB i hi hz ::
            lemma34GlobalZeroCellsForBlockAuxC blocks data B hB is
        else
          lemma34GlobalZeroCellsForBlockAuxC blocks data B hB is
      else
        lemma34GlobalZeroCellsForBlockAuxC blocks data B hB is

/-- All zero-multiplicity cells obtained from a block-list refinement. -/
def lemma34GlobalZeroCellsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    List (Lemma34GlobalZeroCellC blocks data) :=
  blocks.attach.flatMap (fun B =>
    lemma34GlobalZeroCellsForBlockAuxC blocks data B.1 B.2
      (List.range (data B.1).result.N))

/-- A zero-multiplicity cell carries the `p'_lt eps` witness obtained by
coefficient reduction from the subresult cell bound. -/
def lemma34GlobalZeroCellPPrimeC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    {blocks : List (Lemma34BlockC (eps := eps) P k)}
    {data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B}
    (G : Lemma34GlobalZeroCellC blocks data) :
    P.p_prime_ltC
      ((data G.parent).result.pts G.index)
      ((data G.parent).result.pts (G.index + 1))
      eps :=
  lemma33SubResult_p_prime_eps_of_M_zeroC P
    (data G.parent).result G.index_lt G.charge_zero

/-- The positive enlargement radius attached to a global zero cell. -/
def lemma34GlobalZeroCellOmegaC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    {blocks : List (Lemma34BlockC (eps := eps) P k)}
    {data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B}
    (G : Lemma34GlobalZeroCellC blocks data) : CReal :=
  (lemma34GlobalZeroCellPPrimeC G).alpha

/-- The global zero-cell radius is positive. -/
theorem lemma34GlobalZeroCellOmega_posC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    {blocks : List (Lemma34BlockC (eps := eps) P k)}
    {data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B}
    (G : Lemma34GlobalZeroCellC blocks data) :
    regularSeqLtProp CReal.zero (lemma34GlobalZeroCellOmegaC G) :=
  (lemma34GlobalZeroCellPPrimeC G).alpha_pos

/-- Radii of all discarded zero-multiplicity cells in one block-tower step. -/
def lemma34BlockTowerStepRadiiC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) : List CReal :=
  (lemma34GlobalZeroCellsC BT.blocks data).map
    (fun G => lemma34GlobalZeroCellOmegaC G)

/-- Every discarded-cell radius in the block-tower step is positive. -/
theorem lemma34BlockTowerStepRadii_posC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    {r : CReal} (hr : r ∈ lemma34BlockTowerStepRadiiC BT data) :
    regularSeqLtProp CReal.zero r := by
  unfold lemma34BlockTowerStepRadiiC at hr
  rcases List.mem_map.mp hr with ⟨G, _hG, rfl⟩
  exact lemma34GlobalZeroCellOmega_posC G

/-- Successor sigma for a source-faithful block-tower step: finite minimum of
the previous outside radius and all discarded-cell radii. -/
def lemma34BlockTowerStepSigmaValueC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) : CReal :=
  lemma34FoldMinC oldOut.gamma (lemma34BlockTowerStepRadiiC BT data)

/-- Packaged finite-radius data for a block-tower successor step. -/
structure Lemma34BlockTowerStepSigmaC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) : Type 2 where
  radii : List CReal
  radii_pos : ∀ r : CReal, r ∈ radii → regularSeqLtProp CReal.zero r
  sigma : CReal
  sigma_pos : regularSeqLtProp CReal.zero sigma
  sigma_le_previous : RegularSeqLe sigma oldOut.gamma
  sigma_le_mem : ∀ r : CReal, r ∈ radii → RegularSeqLe sigma r

/-- Construct the finite successor sigma data for one block-tower step. -/
def lemma34BlockTowerStepSigmaC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34BlockTowerStepSigmaC BT oldOut data :=
  { radii := lemma34BlockTowerStepRadiiC BT data
    radii_pos := fun r hr => lemma34BlockTowerStepRadii_posC BT data hr
    sigma := lemma34BlockTowerStepSigmaValueC BT oldOut data
    sigma_pos := by
      unfold lemma34BlockTowerStepSigmaValueC
      exact lemma34FoldMin_posC oldOut.gamma
        (lemma34BlockTowerStepRadiiC BT data)
        oldOut.gamma_pos
        (fun r hr => lemma34BlockTowerStepRadii_posC BT data hr)
    sigma_le_previous := by
      unfold lemma34BlockTowerStepSigmaValueC
      exact lemma34FoldMin_le_seedC oldOut.gamma
        (lemma34BlockTowerStepRadiiC BT data)
    sigma_le_mem := by
      intro r hr
      unfold lemma34BlockTowerStepSigmaValueC
      exact lemma34FoldMin_le_memC oldOut.gamma hr }

/-- A positive-length repetition contains its repeated value. -/
theorem lemma34MemReplicateSelfC {A : Type*} (x : A) {n : Nat}
    (hn : 0 < n) : x ∈ List.replicate n x := by
  cases n with
  | zero => exact False.elim ((Nat.not_lt_zero 0) hn)
  | succ n =>
      rw [List.replicate_succ]
      exact List.mem_cons_self

/-- A positive subresult index is retained by the child-block filter. -/
theorem lemma34ChildBlockOfSubResult_mem_auxC {a b eps delta : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma33SubResultDataC (eps := eps) (delta := delta)
      P B.left B.right B.mult)
    (hdelta : RegularSeqLe delta (lemma34WidthScaleC a b (k + 1)))
    {xs : List Nat} {i : Nat}
    (hix : i ∈ xs) (hi : i < D.N) (hm : 0 < D.M i) :
    lemma34ChildBlockOfSubResultC B D hdelta i hi hm ∈
      lemma34ChildBlocksOfSubResultC B D hdelta xs := by
  induction xs with
  | nil => simp at hix
  | cons j js ih =>
      simp only [List.mem_cons] at hix
      rcases hix with rfl | hix
      · simp [lemma34ChildBlocksOfSubResultC, hi, hm]
      · by_cases hj : j < D.N
        · by_cases hjm : 0 < D.M j
          · simp [lemma34ChildBlocksOfSubResultC, hj, hjm, ih hix]
          · simpa [lemma34ChildBlocksOfSubResultC, hj, hjm] using ih hix
        · simpa [lemma34ChildBlocksOfSubResultC, hj] using ih hix

/-- A positive subresult cell occurs in the one-block refined data list. -/
theorem lemma34ChildBlockOfSubResult_mem_forDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (B : Lemma34BlockC (eps := eps) P k)
    (D : Lemma34BlockSubResultDataC (eps := eps) P k B)
    (i : Nat) (hi : i < D.result.N) (hm : 0 < D.result.M i) :
    lemma34ChildBlockOfSubResultC B D.result D.delta_le_width i hi hm ∈
      lemma34RefinedBlocksForDataC B D := by
  unfold lemma34RefinedBlocksForDataC
  unfold lemma34RefinedBlocksForSubResultC
  exact lemma34ChildBlockOfSubResult_mem_auxC B D.result D.delta_le_width
    (List.mem_range.mpr hi) hi hm

/-- A positive subresult cell occurs in the global block-list refinement. -/
theorem lemma34ChildBlockOfSubResult_mem_globalC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    {blocks : List (Lemma34BlockC (eps := eps) P k)}
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ blocks)
    (i : Nat) (hi : i < (data B).result.N)
    (hm : 0 < (data B).result.M i) :
    lemma34ChildBlockOfSubResultC B (data B).result
        (data B).delta_le_width i hi hm ∈
      lemma34RefinedBlocksFromListC blocks data := by
  unfold lemma34RefinedBlocksFromListC
  rw [List.mem_flatMap]
  exact ⟨B, hB,
    lemma34ChildBlockOfSubResult_mem_forDataC B (data B) i hi hm⟩

/-- A positive subresult cell occurs as a repeated successor segment. -/
theorem lemma34PositiveCell_mem_blockStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ BT.blocks)
    (i : Nat) (hi : i < (data B).result.N)
    (hm : 0 < (data B).result.M i) :
    ((data B).result.pts i, (data B).result.pts (i + 1)) ∈
      lemma34FlattenBlocksC (lemma34BlockTowerStepC BT data).blocks := by
  let C := lemma34ChildBlockOfSubResultC B (data B).result
    (data B).delta_le_width i hi hm
  have hC : C ∈ lemma34RefinedBlocksFromListC BT.blocks data := by
    dsimp [C]
    exact lemma34ChildBlockOfSubResult_mem_globalC data B hB i hi hm
  have hpair : ((data B).result.pts i, (data B).result.pts (i + 1)) ∈ C.expand := by
    have hrep := lemma34MemReplicateSelfC
      ((data B).result.pts i, (data B).result.pts (i + 1)) hm
    simpa [C, Lemma34BlockC.expand, lemma34ChildBlockOfSubResultC] using hrep
  unfold lemma34BlockTowerStepC
  unfold lemma34FlattenBlocksC
  rw [List.mem_flatMap]
  exact ⟨C, hC, hpair⟩

/-- If a predicate holds for every `get` position, it holds for every member. -/
theorem lemma34List_forall_get_of_memC {α : Type*}
    (xs : List α) (Q : α → Prop)
    (hget : ∀ j : Fin xs.length, Q (xs.get j))
    {x : α} (hx : x ∈ xs) : Q x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using hget ⟨0, Nat.succ_pos ys.length⟩
      · have htail : ∀ j : Fin ys.length, Q (ys.get j) := by
          intro j
          have h := hget ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩
          simpa using h
        exact ih htail hx

/-- Convert the `Fin n` outside hypothesis for a block tower into a membership
form over the flattened segment list. -/
theorem lemma34BlockTowerStep_outside_of_memC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BTnext : Lemma34BlockTowerC (eps := eps) P n (k + 1))
    {t_pt : CReal} {I : CReal × CReal}
    (hnew : ∀ j : Fin n,
      regularSeqLtProp
          ((lemma34TowerC_of_blockTowerC P n (k + 1) BTnext).segR j)
          t_pt ∨
        regularSeqLtProp t_pt
          ((lemma34TowerC_of_blockTowerC P n (k + 1) BTnext).segL j))
    (hI : I ∈ lemma34FlattenBlocksC BTnext.blocks) :
    regularSeqLtProp I.2 t_pt ∨ regularSeqLtProp t_pt I.1 := by
  let segments := lemma34FlattenBlocksC BTnext.blocks
  have hlen : segments.length = n := by
    dsimp [segments]
    rw [lemma34FlattenBlocks_lengthC, BTnext.total_mult]
  have hget : ∀ j : Fin segments.length,
      regularSeqLtProp (segments.get j).2 t_pt ∨
        regularSeqLtProp t_pt (segments.get j).1 := by
    intro j
    have hjn : j.1 < n := by rw [← hlen]; exact j.2
    have h := hnew ⟨j.1, hjn⟩
    simpa [lemma34TowerC_of_blockTowerC, segments] using h
  exact lemma34List_forall_get_of_memC segments
    (fun I => regularSeqLtProp I.2 t_pt ∨ regularSeqLtProp t_pt I.1)
    hget hI

/-- A positive-multiplicity source cell inherits the successor outside side. -/
theorem lemma34PositiveCellSide_of_blockStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    {t_pt : CReal}
    (hnew : ∀ j : Fin n,
      regularSeqLtProp
          ((lemma34TowerC_of_blockTowerC P n (k + 1)
            (lemma34BlockTowerStepC BT data)).segR j)
          t_pt ∨
        regularSeqLtProp t_pt
          ((lemma34TowerC_of_blockTowerC P n (k + 1)
            (lemma34BlockTowerStepC BT data)).segL j))
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ BT.blocks)
    (i : Nat) (hi : i < (data B).result.N)
    (hm : 0 < (data B).result.M i) :
    regularSeqLtProp ((data B).result.pts (i + 1)) t_pt ∨
      regularSeqLtProp t_pt ((data B).result.pts i) := by
  have hmem := lemma34PositiveCell_mem_blockStepC BT data B hB i hi hm
  exact lemma34BlockTowerStep_outside_of_memC
    (P := P) (n := n) (k := k)
    (lemma34BlockTowerStepC BT data) hnew hmem


/-- Half of a positive CReal is positive. -/
theorem lemma34HalfMul_posC {x : CReal}
    (hx : regularSeqLtProp CReal.zero x) :
    regularSeqLtProp CReal.zero (CReal.mul CReal.half x) := by
  have hmul : regularSeqLtProp
      (CReal.mul CReal.half CReal.zero)
      (CReal.mul CReal.half x) :=
    mul_lt_mul_of_pos_leftC hx CReal.half_pos_E
  exact regularSeqLtProp_of_left_eventual
    (Setoid.symm (mul_zero_equivC CReal.half)) hmul

/-- `half * x` is weakly below positive `x`. -/
theorem lemma34HalfMul_le_selfC {x : CReal}
    (hx : regularSeqLtProp CReal.zero x) :
    RegularSeqLe (CReal.mul CReal.half x) x := by
  have hhalf_pos : regularSeqLtProp CReal.zero (CReal.mul CReal.half x) :=
    lemma34HalfMul_posC hx
  have hlt : regularSeqLtProp (CReal.mul CReal.half x)
      (CReal.add (CReal.mul CReal.half x) (CReal.mul CReal.half x)) :=
    regularSeqLtProp_lt_add_selfC hhalf_pos
  have hle : RegularSeqLe (CReal.mul CReal.half x)
      (CReal.add (CReal.mul CReal.half x) (CReal.mul CReal.half x)) :=
    regularSeqLe_of_ltPropC hlt
  exact regularSeqLe_of_right_eventual (half_mul_add_selfC x) hle

/-- Half-min successor sigma for a source-faithful block-tower step. -/
def lemma34BlockTowerStepHalfSigmaValueC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) : CReal :=
  CReal.mul CReal.half
    (lemma34FoldMinC oldOut.gamma (lemma34BlockTowerStepRadiiC BT data))

/-- Strong finite-radius data: the chosen sigma is half of the finite minimum,
so `sigma + sigma` is below the previous radius and every zero-cell radius. -/
structure Lemma34BlockTowerStepHalfSigmaC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) : Type 2 where
  radii : List CReal
  radii_pos : ∀ r : CReal, r ∈ radii → regularSeqLtProp CReal.zero r
  sigma : CReal
  sigma_pos : regularSeqLtProp CReal.zero sigma
  sigma_le_previous : RegularSeqLe sigma oldOut.gamma
  sigma_le_mem : ∀ r : CReal, r ∈ radii → RegularSeqLe sigma r
  twice_sigma_le_previous : RegularSeqLe (CReal.add sigma sigma) oldOut.gamma
  twice_sigma_le_mem : ∀ r : CReal, r ∈ radii →
    RegularSeqLe (CReal.add sigma sigma) r

/-- Construct the strong half-min successor sigma data. -/
def lemma34BlockTowerStepHalfSigmaC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34BlockTowerStepHalfSigmaC BT oldOut data := by
  let radii := lemma34BlockTowerStepRadiiC BT data
  let rad := lemma34FoldMinC oldOut.gamma radii
  have hrad_pos : regularSeqLtProp CReal.zero rad := by
    dsimp [rad, radii]
    exact lemma34FoldMin_posC oldOut.gamma
      (lemma34BlockTowerStepRadiiC BT data)
      oldOut.gamma_pos
      (fun r hr => lemma34BlockTowerStepRadii_posC BT data hr)
  have hsigma_pos : regularSeqLtProp CReal.zero (CReal.mul CReal.half rad) :=
    lemma34HalfMul_posC hrad_pos
  have hsigma_le_rad : RegularSeqLe (CReal.mul CReal.half rad) rad :=
    lemma34HalfMul_le_selfC hrad_pos
  have htwice_eq : CReal.add (CReal.mul CReal.half rad)
      (CReal.mul CReal.half rad) ≈ rad :=
    half_mul_add_selfC rad
  refine
    { radii := radii
      radii_pos := ?_
      sigma := CReal.mul CReal.half rad
      sigma_pos := hsigma_pos
      sigma_le_previous := ?_
      sigma_le_mem := ?_
      twice_sigma_le_previous := ?_
      twice_sigma_le_mem := ?_ }
  · intro r hr
    dsimp [radii] at hr
    exact lemma34BlockTowerStepRadii_posC BT data hr
  · exact regularSeqLe_trans hsigma_le_rad
      (by
        dsimp [rad, radii]
        exact lemma34FoldMin_le_seedC oldOut.gamma
          (lemma34BlockTowerStepRadiiC BT data))
  · intro r hr
    exact regularSeqLe_trans hsigma_le_rad
      (by
        dsimp [rad, radii]
        exact lemma34FoldMin_le_memC oldOut.gamma hr)
  · exact regularSeqLe_of_left_eventual htwice_eq
      (by
        dsimp [rad, radii]
        exact lemma34FoldMin_le_seedC oldOut.gamma
          (lemma34BlockTowerStepRadiiC BT data))
  · intro r hr
    exact regularSeqLe_of_left_eventual htwice_eq
      (by
        dsimp [rad, radii]
        exact lemma34FoldMin_le_memC oldOut.gamma hr)

/-- Forget the strong half-min package to the weaker outside-cover sigma API. -/
def lemma34BlockTowerStepSigmaC_of_halfSigmaC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    {BT : Lemma34BlockTowerC (eps := eps) P n k}
    {oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT)}
    {data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B}
    (S : Lemma34BlockTowerStepHalfSigmaC BT oldOut data) :
    Lemma34BlockTowerStepSigmaC BT oldOut data :=
  { radii := S.radii
    radii_pos := S.radii_pos
    sigma := S.sigma
    sigma_pos := S.sigma_pos
    sigma_le_previous := S.sigma_le_previous
    sigma_le_mem := S.sigma_le_mem }


/-- Algebra: `-z + (x-y) ≈ x-(y+z)`. -/
theorem lemma34_neg_add_sub_eventualC (x y z : CReal) :
    CReal.add (CReal.neg z) (CReal.sub x y) ≈
      CReal.sub x (CReal.add y z) := by
  have hq : mkQuot (CReal.add (CReal.neg z) (CReal.sub x y)) =
      mkQuot (CReal.sub x (CReal.add y z)) := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (-(mkQuot z)) + ((mkQuot x) - (mkQuot y)) =
      (mkQuot x) - ((mkQuot y) + (mkQuot z))
    ring
  exact Quotient.exact hq

/-- Algebra: `-z + x ≈ x-z`. -/
theorem lemma34_neg_add_eventual_subC (x z : CReal) :
    CReal.add (CReal.neg z) x ≈ CReal.sub x z := by
  have hq : mkQuot (CReal.add (CReal.neg z) x) =
      mkQuot (CReal.sub x z) := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (-(mkQuot z)) + (mkQuot x) = (mkQuot x) - (mkQuot z)
    ring
  exact Quotient.exact hq

/-- Algebra: `z + (x+y) ≈ x+(y+z)`. -/
theorem lemma34_add_left_assoc_right_eventualC (x y z : CReal) :
    CReal.add z (CReal.add x y) ≈ CReal.add x (CReal.add y z) := by
  have hq : mkQuot (CReal.add z (CReal.add x y)) =
      mkQuot (CReal.add x (CReal.add y z)) := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (mkQuot z) + ((mkQuot x) + (mkQuot y)) =
      (mkQuot x) + ((mkQuot y) + (mkQuot z))
    ring
  exact Quotient.exact hq

/-- Left collar arithmetic: from `left-sigma < t` and `sigma+sigma <= omega`,
obtain `left-omega <= t-sigma`. -/
theorem lemma34ZeroCell_subset_leftC {left omega sigma t : CReal}
    (htwice : RegularSeqLe (CReal.add sigma sigma) omega)
    (hnear : regularSeqLtProp (CReal.sub left sigma) t) :
    RegularSeqLe (CReal.sub left omega) (CReal.sub t sigma) := by
  have hleft_le : RegularSeqLe
      (CReal.sub left omega)
      (CReal.sub left (CReal.add sigma sigma)) :=
    regularSeqLe_sub_leftC htwice
  have hraw : regularSeqLtProp
      (CReal.add (CReal.neg sigma) (CReal.sub left sigma))
      (CReal.add (CReal.neg sigma) t) :=
    regularSeqLtProp_add_left (CReal.neg sigma)
      (CReal.sub left sigma) t hnear
  have hstrict1 : regularSeqLtProp
      (CReal.sub left (CReal.add sigma sigma))
      (CReal.add (CReal.neg sigma) t) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (lemma34_neg_add_sub_eventualC left sigma sigma)) hraw
  have hstrict : regularSeqLtProp
      (CReal.sub left (CReal.add sigma sigma))
      (CReal.sub t sigma) :=
    regularSeqLtProp_of_right_eventual
      (lemma34_neg_add_eventual_subC t sigma) hstrict1
  exact regularSeqLe_trans hleft_le (regularSeqLe_of_ltPropC hstrict)

/-- Right collar arithmetic: from `t < right+sigma` and `sigma+sigma <= omega`,
obtain `t+sigma <= right+omega`. -/
theorem lemma34ZeroCell_subset_rightC {right omega sigma t : CReal}
    (htwice : RegularSeqLe (CReal.add sigma sigma) omega)
    (hnear : regularSeqLtProp t (CReal.add right sigma)) :
    RegularSeqLe (CReal.add t sigma) (CReal.add right omega) := by
  have hraw : regularSeqLtProp
      (CReal.add sigma t)
      (CReal.add sigma (CReal.add right sigma)) :=
    regularSeqLtProp_add_left sigma t (CReal.add right sigma) hnear
  have hleft : regularSeqLtProp
      (CReal.add t sigma)
      (CReal.add sigma (CReal.add right sigma)) :=
    regularSeqLtProp_of_left_eventual (CReal.add_comm t sigma) hraw
  have hstrict : regularSeqLtProp
      (CReal.add t sigma)
      (CReal.add right (CReal.add sigma sigma)) :=
    regularSeqLtProp_of_right_eventual
      (lemma34_add_left_assoc_right_eventualC right sigma sigma) hleft
  have hle_mid : RegularSeqLe
      (CReal.add t sigma)
      (CReal.add right (CReal.add sigma sigma)) :=
    regularSeqLe_of_ltPropC hstrict
  have hle_right : RegularSeqLe
      (CReal.add right (CReal.add sigma sigma))
      (CReal.add right omega) :=
    regularSeqLe_add (regularSeqLe_refl right) htwice
  exact regularSeqLe_trans hle_mid hle_right

/-- Build a zero-cell collar from near-side strict inequalities and the strong
half-sigma radius bound. -/
def lemma34ZeroCollarC_of_pprime_nearC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) {sigma left right t_pt : CReal}
    {pprime : P.p_prime_ltC left right eps}
    (htwice : RegularSeqLe (CReal.add sigma sigma) pprime.alpha)
    (hleft : regularSeqLtProp (CReal.sub left sigma) t_pt)
    (hright : regularSeqLtProp t_pt (CReal.add right sigma)) :
    Lemma34ZeroCollarC (eps := eps) P sigma t_pt :=
  { left := left
    right := right
    omega := pprime.alpha
    omega_pos := pprime.alpha_pos
    source := pprime.inner
    subset_left :=
      CReal.max_right_monoC (a := a)
        (lemma34ZeroCell_subset_leftC htwice hleft)
    subset_right :=
      CReal.min_right_monoC (b := b)
        (lemma34ZeroCell_subset_rightC htwice hright) }


/-- Minimal remaining DATA frontier for the source-faithful block route: only
zero-multiplicity cells need a Type-valued cotransitive local cover.  Positive
cells are handled internally from successor membership and DATA strictness. -/
structure Lemma34BlockZeroCellCoverDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (S : Lemma34BlockTowerStepHalfSigmaC BT oldOut data) : Type 2 where
  zeroCover :
    ∀ t_pt : CReal,
      RegularSeqLe a t_pt →
      RegularSeqLe t_pt b →
      (∀ j : Fin n,
        regularSeqLtProp
            ((lemma34TowerC_of_blockTowerC P n (k + 1)
              (lemma34BlockTowerStepC BT data)).segR j)
            t_pt ∨
          regularSeqLtProp t_pt
            ((lemma34TowerC_of_blockTowerC P n (k + 1)
              (lemma34BlockTowerStepC BT data)).segL j)) →
      (B : Lemma34BlockC (eps := eps) P k) →
      B ∈ BT.blocks →
      (i : Nat) →
      (hi : i < (data B).result.N) →
      (hzero : (data B).result.M i = 0) →
      PSum
        (Lemma34ZeroCollarC (eps := eps) P S.sigma t_pt)
        (PSum
          (regularSeqLtProp ((data B).result.pts (i + 1)) t_pt)
          (regularSeqLtProp t_pt ((data B).result.pts i)))

/-- Local cell cover for the block route.  The zero branch is the only supplied
frontier; the positive branch is closed here. -/
def lemma34BlockCellCoverC_of_zeroDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (S : Lemma34BlockTowerStepHalfSigmaC BT oldOut data)
    (Z : Lemma34BlockZeroCellCoverDataC BT oldOut data S)
    (t_pt : CReal)
    (hat : RegularSeqLe a t_pt) (htb : RegularSeqLe t_pt b)
    (hnew : ∀ j : Fin n,
      regularSeqLtProp
          ((lemma34TowerC_of_blockTowerC P n (k + 1)
            (lemma34BlockTowerStepC BT data)).segR j)
          t_pt ∨
        regularSeqLtProp t_pt
          ((lemma34TowerC_of_blockTowerC P n (k + 1)
            (lemma34BlockTowerStepC BT data)).segL j))
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ BT.blocks)
    (i : Nat) (hi : i < (data B).result.N) :
    PSum
      (Lemma34ZeroCollarC (eps := eps) P S.sigma t_pt)
      (PSum
        (regularSeqLtProp ((data B).result.pts (i + 1)) t_pt)
        (regularSeqLtProp t_pt ((data B).result.pts i))) := by
  by_cases hzero : (data B).result.M i = 0
  · exact Z.zeroCover t_pt hat htb hnew B hB i hi hzero
  · have hm : 0 < (data B).result.M i := Nat.pos_of_ne_zero hzero
    have hside := lemma34PositiveCellSide_of_blockStepC
      BT data hnew B hB i hi hm
    let Pos : Lemma34PositiveCellLocalDataC
        ((data B).result.pts i) ((data B).result.pts (i + 1))
        ((data B).result.pts i) ((data B).result.pts (i + 1)) :=
      { cell_strict := (data B).result.pts_strict_data i hi
        next_le_left := regularSeqLe_refl ((data B).result.pts i)
        right_le_next := regularSeqLe_refl ((data B).result.pts (i + 1)) }
    exact lemma34PositiveCellCoverC_of_localDataC
      (eps := eps) P (sigma := S.sigma) Pos hside

/-- Scan all subresult cells of one retained parent block. -/
def lemma34BlockCoverC_of_zeroDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (S : Lemma34BlockTowerStepHalfSigmaC BT oldOut data)
    (Z : Lemma34BlockZeroCellCoverDataC BT oldOut data S)
    (t_pt : CReal)
    (hat : RegularSeqLe a t_pt) (htb : RegularSeqLe t_pt b)
    (hnew : ∀ j : Fin n,
      regularSeqLtProp
          ((lemma34TowerC_of_blockTowerC P n (k + 1)
            (lemma34BlockTowerStepC BT data)).segR j)
          t_pt ∨
        regularSeqLtProp t_pt
          ((lemma34TowerC_of_blockTowerC P n (k + 1)
            (lemma34BlockTowerStepC BT data)).segL j))
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ BT.blocks) :
    PSum
      (Lemma34ZeroCollarC (eps := eps) P S.sigma t_pt)
      (regularSeqLtProp B.right t_pt ∨ regularSeqLtProp t_pt B.left) := by
  let D := data B
  have hscan := lemma34H4ScanCellsC
    (W := Lemma34ZeroCollarC (eps := eps) P S.sigma t_pt)
    D.result.pts t_pt D.result.N D.result.N_pos
    (fun i hi =>
      lemma34BlockCellCoverC_of_zeroDataC
        BT oldOut data S Z t_pt hat htb hnew B hB i hi)
  cases hscan with
  | inl W => exact PSum.inl W
  | inr hside =>
      cases hside with
      | inl hright =>
          exact PSum.inr (Or.inl
            (regularSeqLtProp_of_left_eventual
              (Setoid.symm D.result.pts_N) hright))
      | inr hleft =>
          exact PSum.inr (Or.inr
            (regularSeqLtProp_of_right_eventual
              D.result.pts_zero hleft))

/-- If every retained block is outside a point, then every repeated previous segment
of the tower is outside the point. -/
theorem lemma34OldTowerOutside_of_blockOutsideC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    {t_pt : CReal}
    (hout : ∀ B : Lemma34BlockC (eps := eps) P k,
      B ∈ BT.blocks → regularSeqLtProp B.right t_pt ∨
        regularSeqLtProp t_pt B.left) :
    ∀ j : Fin n,
      regularSeqLtProp
          ((lemma34TowerC_of_blockTowerC P n k BT).segR j) t_pt ∨
        regularSeqLtProp t_pt
          ((lemma34TowerC_of_blockTowerC P n k BT).segL j) := by
  intro j
  let segments := lemma34FlattenBlocksC BT.blocks
  have hlen : segments.length = n := by
    dsimp [segments]
    rw [lemma34FlattenBlocks_lengthC, BT.total_mult]
  have hmem : segments.get ⟨j.1, by rw [hlen]; exact j.2⟩ ∈ segments :=
    List.get_mem segments ⟨j.1, by rw [hlen]; exact j.2⟩
  rcases lemma34MemFlattenBlocksC (blocks := BT.blocks) hmem with
    ⟨B, hB, hEq⟩
  have hBside := hout B hB
  have hgoal :
      regularSeqLtProp (segments.get ⟨j.1, by rw [hlen]; exact j.2⟩).2 t_pt ∨
        regularSeqLtProp t_pt (segments.get ⟨j.1, by rw [hlen]; exact j.2⟩).1 := by
    rw [hEq]
    exact hBside
  simpa [lemma34TowerC_of_blockTowerC, segments] using hgoal

/-- The block-route zero-cell frontier supplies the one-step zero-cover object. -/
def lemma34OutsideStepZeroCoverC_of_blockZeroDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (S : Lemma34BlockTowerStepHalfSigmaC BT oldOut data)
    (Z : Lemma34BlockZeroCellCoverDataC BT oldOut data S) :
    Lemma34OutsideStepZeroCoverC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT)
      oldOut
      (lemma34TowerC_of_blockTowerC P n (k + 1)
        (lemma34BlockTowerStepC BT data)) :=
  { radii := S.radii
    radii_pos := S.radii_pos
    sigma := S.sigma
    sigma_pos := S.sigma_pos
    sigma_le_previous := S.sigma_le_previous
    sigma_le_mem := S.sigma_le_mem
    cover := by
      intro t_pt hat htb hnew
      have hscan := lemma34ScanListPSC
        (W := Lemma34ZeroCollarC (eps := eps) P S.sigma t_pt)
        (fun B : Lemma34BlockC (eps := eps) P k =>
          regularSeqLtProp B.right t_pt ∨ regularSeqLtProp t_pt B.left)
        BT.blocks
        (fun B hB =>
          lemma34BlockCoverC_of_zeroDataC
            BT oldOut data S Z t_pt hat htb hnew B hB)
      cases hscan with
      | inl W => exact PSum.inr W
      | inr hall =>
          exact PSum.inl
            (lemma34OldTowerOutside_of_blockOutsideC BT hall) }


/-- Input data for one source-faithful block-tower outside step. -/
structure Lemma34BlockTowerStepInputC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT)) : Type 2 where
  subData : (B : Lemma34BlockC (eps := eps) P k) →
    Lemma34BlockSubResultDataC (eps := eps) P k B
  halfSigma : Lemma34BlockTowerStepHalfSigmaC BT oldOut subData
  zeroData : Lemma34BlockZeroCellCoverDataC BT oldOut subData halfSigma

/-- Output package for one source-faithful block-tower outside step. -/
structure Lemma34BlockTowerStepPackageC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT)) : Type 2 where
  BTnext : Lemma34BlockTowerC (eps := eps) P n (k + 1)
  refines : Lemma34RefinesC (eps := eps) P n k
    (lemma34TowerC_of_blockTowerC P n k BT)
    (lemma34TowerC_of_blockTowerC P n (k + 1) BTnext)
  outside : Lemma34TowerOutsideC (eps := eps) P n (k + 1)
    (lemma34TowerC_of_blockTowerC P n (k + 1) BTnext)

/-- Realize one source-faithful block-tower step from subresult data and the
minimal zero-cell cover frontier. -/
noncomputable def lemma34BlockTowerStepPackageC_of_inputC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (I : Lemma34BlockTowerStepInputC BT oldOut) :
    Lemma34BlockTowerStepPackageC BT oldOut := by
  let BTnext := lemma34BlockTowerStepC BT I.subData
  let Z : Lemma34OutsideStepZeroCoverC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT)
      oldOut
      (lemma34TowerC_of_blockTowerC P n (k + 1) BTnext) :=
    lemma34OutsideStepZeroCoverC_of_blockZeroDataC
      BT oldOut I.subData I.halfSigma I.zeroData
  let C : Lemma34OutsideStepCoverC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT)
      oldOut
      (lemma34TowerC_of_blockTowerC P n (k + 1) BTnext) :=
    lemma34OutsideStepCoverC_of_zeroCoverC P n k
      (lemma34TowerC_of_blockTowerC P n k BT) oldOut Z
  exact
    { BTnext := BTnext
      refines := lemma34RefinesC_of_blockTowerStepC BT I.subData
      outside := lemma34OutsideStepPreserveC_of_coverC P n k
        (lemma34TowerC_of_blockTowerC P n k BT) oldOut C }

/-- Convenience constructor using the standard half-min sigma package. -/
noncomputable def lemma34BlockTowerStepInputC_standard {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (subData : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (zeroData : Lemma34BlockZeroCellCoverDataC BT oldOut subData
      (lemma34BlockTowerStepHalfSigmaC_construct BT oldOut subData)) :
    Lemma34BlockTowerStepInputC BT oldOut :=
  { subData := subData
    halfSigma := lemma34BlockTowerStepHalfSigmaC_construct BT oldOut subData
    zeroData := zeroData }

/-- A stateful source-faithful block-tower level, carrying both the hidden
block list and the outside witness for its repeated-segment projection. -/
structure Lemma34BlockTowerStateC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} (n k : Nat) : Type 2 where
  eps_pos : regularSeqLtProp zeroSeq eps
  BT : Lemma34BlockTowerC (eps := eps) P n k
  outside : Lemma34TowerOutsideC (eps := eps) P n k
    (lemma34TowerC_of_blockTowerC P n k BT)

/-- Provider for the stateful block-tower route: at each level it supplies the
subresult data and the remaining zero-cell DATA needed by the one-step package.
-/
structure Lemma34BlockTowerStepInputProviderC : Type 2 where
  input :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      {P : ProfileC a b hab} → {n k : Nat} →
      (S : Lemma34BlockTowerStateC (eps := eps) (P := P) n k) →
      Lemma34BlockTowerStepInputC S.BT S.outside

/-- One stateful source-faithful block-tower step. -/
noncomputable def lemma34BlockTowerStateStepC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (S : Lemma34BlockTowerStateC (eps := eps) (P := P) n k) :
    Lemma34BlockTowerStateC (eps := eps) (P := P) n (k + 1) := by
  let I := provider.input S
  let pkg := lemma34BlockTowerStepPackageC_of_inputC S.BT S.outside I
  exact
    { eps_pos := S.eps_pos
      BT := pkg.BTnext
      outside := pkg.outside }

/-- The stateful block-tower step refines the previous repeated-segment tower.
-/
noncomputable def lemma34BlockTowerStateStep_refinesC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (S : Lemma34BlockTowerStateC (eps := eps) (P := P) n k) :
    Lemma34RefinesC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k S.BT)
      (lemma34TowerC_of_blockTowerC P n (k + 1)
        (lemma34BlockTowerStateStepC provider S).BT) := by
  let I := provider.input S
  let pkg := lemma34BlockTowerStepPackageC_of_inputC S.BT S.outside I
  simpa [lemma34BlockTowerStateStepC, I, pkg] using pkg.refines

/-- The source-faithful block-tower state sequence obtained by iterating the
stateful one-step package. -/
noncomputable def lemma34BlockTowerStateSeqC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (S0 : Lemma34BlockTowerStateC (eps := eps) (P := P) n 0) :
    (k : Nat) → Lemma34BlockTowerStateC (eps := eps) (P := P) n k
  | 0 => S0
  | k + 1 => lemma34BlockTowerStateStepC provider
      (lemma34BlockTowerStateSeqC provider S0 k)

/-- Consecutive repeated-segment projections of the source-faithful block tower
refine each other. -/
noncomputable def lemma34BlockTowerStateSeq_refinesC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (S0 : Lemma34BlockTowerStateC (eps := eps) (P := P) n 0)
    (k : Nat) :
    Lemma34RefinesC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k
        (lemma34BlockTowerStateSeqC provider S0 k).BT)
      (lemma34TowerC_of_blockTowerC P n (k + 1)
        (lemma34BlockTowerStateSeqC provider S0 (k + 1)).BT) := by
  simpa [lemma34BlockTowerStateSeqC] using
    lemma34BlockTowerStateStep_refinesC provider
      (lemma34BlockTowerStateSeqC provider S0 k)

/-- Step-free tower-sequence API.  This is the bridge needed for the stateful
block route, where the hidden block list cannot be recovered from an arbitrary
`Lemma34TowerC` argument. -/
structure Lemma34TowerSeqDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat) : Type 2 where
  T : (k : Nat) → Lemma34TowerC (eps := eps) P n k
  refines : ∀ k : Nat, Lemma34RefinesC (eps := eps) P n k
    (T k) (T (k + 1))

/-- Forget the hidden block lists of a stateful block-tower sequence while
retaining the repeated-segment tower sequence and its refinement certificates.
-/
noncomputable def lemma34TowerSeqDataC_of_blockTowerStateSeqC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (S0 : Lemma34BlockTowerStateC (eps := eps) (P := P) n 0) :
    Lemma34TowerSeqDataC (eps := eps) P n :=
  { T := fun k =>
      lemma34TowerC_of_blockTowerC P n k
        (lemma34BlockTowerStateSeqC provider S0 k).BT
    refines := fun k =>
      lemma34BlockTowerStateSeq_refinesC provider S0 k }

/-- Initial whole-interval `p'` budget obtained directly from the Lemma 3.4
hypothesis `lambda(1)-lambda(0) < (n+1) eps`. -/
def lemma34InitialPPrimeABC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (n : Nat)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    P.p_prime_ltC a b
      (CReal.mul (constSeq (Nat.cast (n + 1))) eps) :=
  { alpha := CReal.one
    alpha_pos := CReal.one_pos_E
    inner :=
      { f1 := P.zeroCode
        f1_mem := P.has_zero
        f2 := P.oneCode
        f2_mem := P.has_one
        cond1 := by
          intro t _hat _htb _htv
          simpa [P.embed_zero]
        cond2 := by
          intro t _hat _htb _hut
          simpa [P.embed_one]
        gap := h_cond } }

/-- The source-faithful initial block: one whole interval `[a,b]` carrying
multiplicity `n`. -/
noncomputable def lemma34InitialBlockC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34BlockC (eps := eps) P 0 :=
  { left := a
    right := b
    mult := n
    mult_pos := hn
    left_bound := regularSeqLe_refl a
    proper := hab
    right_bound := regularSeqLe_refl b
    width := by
      simpa using
        (lemma34T0C_direct P heps n h_cond).seg_width ⟨0, hn⟩
    budget := lemma34InitialPPrimeABC P n h_cond }

/-- Initial source-faithful block tower: a singleton block list whose
multiplicity expands to the `n` repeated whole-interval columns. -/
noncomputable def lemma34InitialBlockTowerC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34BlockTowerC (eps := eps) P n 0 :=
  { blocks := [lemma34InitialBlockC P heps n hn h_cond]
    total_mult := by
      simp [lemma34TotalMultiplicityC, lemma34InitialBlockC] }

/-- The repeated-segment projection of the initial block tower is outside
trivially, exactly as the direct base tower is: any point in `[a,b]` cannot lie
strictly outside the unique whole-interval block. -/
noncomputable def lemma34InitialBlockTowerOutsideC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34TowerOutsideC (eps := eps) P n 0
      (lemma34TowerC_of_blockTowerC P n 0
        (lemma34InitialBlockTowerC P heps n hn h_cond)) :=
  { gamma := CReal.one
    gamma_pos := CReal.one_pos_E
    outside := by
      intro t_pt hat htb hout
      let j0 : Fin n := ⟨0, hn⟩
      have hseg := hout j0
      have hL :
          (lemma34TowerC_of_blockTowerC P n 0
            (lemma34InitialBlockTowerC P heps n hn h_cond)).segL j0 = a := by
        simp [lemma34TowerC_of_blockTowerC, lemma34InitialBlockTowerC,
          lemma34InitialBlockC, lemma34FlattenBlocksC, Lemma34BlockC.expand,
          lemma34TotalMultiplicityC, j0]
      have hR :
          (lemma34TowerC_of_blockTowerC P n 0
            (lemma34InitialBlockTowerC P heps n hn h_cond)).segR j0 = b := by
        simp [lemma34TowerC_of_blockTowerC, lemma34InitialBlockTowerC,
          lemma34InitialBlockC, lemma34FlattenBlocksC, Lemma34BlockC.expand,
          lemma34TotalMultiplicityC, j0]
      have hFalse : False := by
        rcases hseg with hbt | hta
        · exact regularSeqLe_not_lt_reverse_prop htb (by simpa [hR] using hbt)
        · exact regularSeqLe_not_lt_reverse_prop hat (by simpa [hL] using hta)
      exact False.elim hFalse }

/-- Initial state for the source-faithful block-tower route. -/
noncomputable def lemma34InitialBlockTowerStateC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34BlockTowerStateC (eps := eps) (P := P) n 0 :=
  { eps_pos := heps
    BT := lemma34InitialBlockTowerC P heps n hn h_cond
    outside := lemma34InitialBlockTowerOutsideC P heps n hn h_cond }

/-- The step-free tower sequence obtained from the source-faithful block route
from the canonical initial whole-interval block state. -/
noncomputable def lemma34InitialBlockTowerSeqDataC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34TowerSeqDataC (eps := eps) P n :=
  lemma34TowerSeqDataC_of_blockTowerStateSeqC provider
    (lemma34InitialBlockTowerStateC P heps n hn h_cond)

/-- Outside witnesses at every level of a source-faithful block-tower state
sequence. -/
noncomputable def lemma34BlockTowerStateSeq_outsideC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (S0 : Lemma34BlockTowerStateC (eps := eps) (P := P) n 0)
    (k : Nat) :
    Lemma34TowerOutsideC (eps := eps) P n k
      ((lemma34TowerSeqDataC_of_blockTowerStateSeqC provider S0).T k) := by
  simpa [lemma34TowerSeqDataC_of_blockTowerStateSeqC] using
    (lemma34BlockTowerStateSeqC provider S0 k).outside

/-- Outside witnesses at every level of the canonical initial block route. -/
noncomputable def lemma34InitialBlockTowerSeqOutsideC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps))
    (k : Nat) :
    Lemma34TowerOutsideC (eps := eps) P n k
      ((lemma34InitialBlockTowerSeqDataC provider P heps n hn h_cond).T k) :=
  lemma34BlockTowerStateSeq_outsideC provider
    (lemma34InitialBlockTowerStateC P heps n hn h_cond) k

/-- Left endpoint sequence for the step-free tower-sequence API. -/
noncomputable def lemma34SeqDataLeftSeqC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (k : Nat) : CReal :=
  (seq.T k).segL j

/-- Right endpoint sequence for the step-free tower-sequence API. -/
noncomputable def lemma34SeqDataRightSeqC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (k : Nat) : CReal :=
  (seq.T k).segR j

/-- One-step monotonicity of left endpoints for a step-free tower sequence. -/
theorem lemma34SeqDataLeftSeq_monoStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (lemma34SeqDataLeftSeqC seq j k)
      (lemma34SeqDataLeftSeqC seq j (k + 1)) := by
  simpa [lemma34SeqDataLeftSeqC] using (seq.refines k).left_mono j

/-- One-step antitonicity of right endpoints for a step-free tower sequence. -/
theorem lemma34SeqDataRightSeq_antitoneStepC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (lemma34SeqDataRightSeqC seq j (k + 1))
      (lemma34SeqDataRightSeqC seq j k) := by
  simpa [lemma34SeqDataRightSeqC] using (seq.refines k).right_mono j

/-- Endpoint properness for a step-free tower sequence. -/
theorem lemma34SeqData_seg_properC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (k : Nat) :
    RegularSeqLe a (lemma34SeqDataLeftSeqC seq j k) ∧
      regularSeqLtProp
        (lemma34SeqDataLeftSeqC seq j k)
        (lemma34SeqDataRightSeqC seq j k) ∧
      RegularSeqLe (lemma34SeqDataRightSeqC seq j k) b := by
  simpa [lemma34SeqDataLeftSeqC, lemma34SeqDataRightSeqC] using
    (seq.T k).seg_proper j

/-- Width bound for a step-free tower sequence. -/
theorem lemma34SeqData_segment_widthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (k : Nat) :
    RegularSeqLe
      (CReal.sub
        (lemma34SeqDataRightSeqC seq j k)
        (lemma34SeqDataLeftSeqC seq j k))
      (lemma34WidthScaleC a b k) := by
  simpa [lemma34SeqDataLeftSeqC, lemma34SeqDataRightSeqC] using
    (seq.T k).seg_width j

/-- Full monotonicity of the left-endpoint sequence for a step-free tower
sequence. -/
theorem lemma34SeqDataLeftSeq_monoC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) : ∀ {p q : Nat}, p ≤ q →
      RegularSeqLe
        (lemma34SeqDataLeftSeqC seq j p)
        (lemma34SeqDataLeftSeqC seq j q) := by
  intro p q hpq
  induction hpq with
  | refl => exact regularSeqLe_refl _
  | @step m _ ih =>
      exact regularSeqLe_trans ih (lemma34SeqDataLeftSeq_monoStepC seq j m)

/-- Full antitonicity of the right-endpoint sequence for a step-free tower
sequence. -/
theorem lemma34SeqDataRightSeq_antitoneC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) : ∀ {p q : Nat}, p ≤ q →
      RegularSeqLe
        (lemma34SeqDataRightSeqC seq j q)
        (lemma34SeqDataRightSeqC seq j p) := by
  intro p q hpq
  induction hpq with
  | refl => exact regularSeqLe_refl _
  | @step m _ ih =>
      exact regularSeqLe_trans (lemma34SeqDataRightSeq_antitoneStepC seq j m) ih

/-- Nested-interval sandwich for a step-free tower sequence: every left endpoint
is below every right endpoint, at arbitrary levels. -/
theorem lemma34SeqDataLeftSeq_le_rightSeqC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (m k : Nat) :
    RegularSeqLe
      (lemma34SeqDataLeftSeqC seq j m)
      (lemma34SeqDataRightSeqC seq j k) := by
  rcases Nat.le_total m k with hmk | hkm
  · exact regularSeqLe_trans
      (lemma34SeqDataLeftSeq_monoC seq j hmk)
      (regularSeqLe_of_ltPropC (lemma34SeqData_seg_properC seq j k).2.1)
  · exact regularSeqLe_trans
      (regularSeqLe_of_ltPropC (lemma34SeqData_seg_properC seq j m).2.1)
      (lemma34SeqDataRightSeq_antitoneC seq j hkm)

/-- Cauchy modulus for the left-endpoint sequence of a step-free tower
sequence. -/
theorem lemma34SeqDataLeftSeq_absSub_le_widthC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) (M m k : Nat) (hm : M ≤ m) (hk : M ≤ k) :
    RegularSeqLe
      (absSeq (subSeq (lemma34SeqDataLeftSeqC seq j m)
                      (lemma34SeqDataLeftSeqC seq j k)))
      (lemma34WidthScaleC a b M) := by
  have hW :
      RegularSeqLe
        (subSeq (lemma34SeqDataRightSeqC seq j M)
                (lemma34SeqDataLeftSeqC seq j M))
        (lemma34WidthScaleC a b M) :=
    lemma34SeqData_segment_widthC seq j M
  rcases Nat.le_total m k with hmk | hkm
  · have hmk_le : RegularSeqLe (lemma34SeqDataLeftSeqC seq j m)
        (lemma34SeqDataLeftSeqC seq j k) :=
      lemma34SeqDataLeftSeq_monoC seq j hmk
    have hdiff_nonneg :
        RegularSeqLe zeroSeq
          (subSeq (lemma34SeqDataLeftSeqC seq j k)
                  (lemma34SeqDataLeftSeqC seq j m)) :=
      regularSeqLe_zero_of_nonneg hmk_le
    have habs_rev :
        RegularSeqLe
          (absSeq (subSeq (lemma34SeqDataLeftSeqC seq j k)
                          (lemma34SeqDataLeftSeqC seq j m)))
          (subSeq (lemma34SeqDataLeftSeqC seq j k)
                  (lemma34SeqDataLeftSeqC seq j m)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have habs :
        RegularSeqLe
          (absSeq (subSeq (lemma34SeqDataLeftSeqC seq j m)
                          (lemma34SeqDataLeftSeqC seq j k)))
          (subSeq (lemma34SeqDataLeftSeqC seq j k)
                  (lemma34SeqDataLeftSeqC seq j m)) :=
      regularSeqLe_of_left_eventual
        (absSeq_subSeq_comm_eventually _ _) habs_rev
    have hA :
        RegularSeqLe
          (subSeq (lemma34SeqDataLeftSeqC seq j k)
                  (lemma34SeqDataLeftSeqC seq j m))
          (subSeq (lemma34SeqDataRightSeqC seq j M)
                  (lemma34SeqDataLeftSeqC seq j m)) :=
      subSeq_monotone_left_regularSeqLe _ _ _
        (lemma34SeqDataLeftSeq_le_rightSeqC seq j k M)
    have hB :
        RegularSeqLe
          (subSeq (lemma34SeqDataRightSeqC seq j M)
                  (lemma34SeqDataLeftSeqC seq j m))
          (subSeq (lemma34SeqDataRightSeqC seq j M)
                  (lemma34SeqDataLeftSeqC seq j M)) :=
      regularSeqLe_subSeq_right _ (lemma34SeqDataLeftSeq_monoC seq j hm)
    exact regularSeqLe_trans habs
      (regularSeqLe_trans hA (regularSeqLe_trans hB hW))
  · have hkm_le : RegularSeqLe (lemma34SeqDataLeftSeqC seq j k)
        (lemma34SeqDataLeftSeqC seq j m) :=
      lemma34SeqDataLeftSeq_monoC seq j hkm
    have hdiff_nonneg :
        RegularSeqLe zeroSeq
          (subSeq (lemma34SeqDataLeftSeqC seq j m)
                  (lemma34SeqDataLeftSeqC seq j k)) :=
      regularSeqLe_zero_of_nonneg hkm_le
    have habs :
        RegularSeqLe
          (absSeq (subSeq (lemma34SeqDataLeftSeqC seq j m)
                          (lemma34SeqDataLeftSeqC seq j k)))
          (subSeq (lemma34SeqDataLeftSeqC seq j m)
                  (lemma34SeqDataLeftSeqC seq j k)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have hA :
        RegularSeqLe
          (subSeq (lemma34SeqDataLeftSeqC seq j m)
                  (lemma34SeqDataLeftSeqC seq j k))
          (subSeq (lemma34SeqDataRightSeqC seq j M)
                  (lemma34SeqDataLeftSeqC seq j k)) :=
      subSeq_monotone_left_regularSeqLe _ _ _
        (lemma34SeqDataLeftSeq_le_rightSeqC seq j m M)
    have hB :
        RegularSeqLe
          (subSeq (lemma34SeqDataRightSeqC seq j M)
                  (lemma34SeqDataLeftSeqC seq j k))
          (subSeq (lemma34SeqDataRightSeqC seq j M)
                  (lemma34SeqDataLeftSeqC seq j M)) :=
      regularSeqLe_subSeq_right _ (lemma34SeqDataLeftSeq_monoC seq j hk)
    exact regularSeqLe_trans habs
      (regularSeqLe_trans hA (regularSeqLe_trans hB hW))

/-- Cauchy datum for the left-endpoint sequence of a step-free tower sequence.
-/
noncomputable def lemma34SeqDataLeftSeqCauchyDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) :
    CRealRepSequenceCauchyData
      (fun k => lemma34SeqDataLeftSeqC seq j k) :=
  { cmod := fun g =>
      (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
        (halfPow g) (posEventuallyData_halfPowC g)).val
    close_eventually := fun g m₂ n₂ hm hn => by
      have hK :
          regularSeqLtProp
            (lemma34WidthScaleC a b
              (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
                (halfPow g) (posEventuallyData_halfPowC g)).val)
            (halfPow g) :=
        (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
          (halfPow g) (posEventuallyData_halfPowC g)).property
      have hcm :
          RegularSeqLe
            (absSeq (subSeq (lemma34SeqDataLeftSeqC seq j m₂)
                            (lemma34SeqDataLeftSeqC seq j n₂)))
            (lemma34WidthScaleC a b
              (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
                (halfPow g) (posEventuallyData_halfPowC g)).val) :=
        lemma34SeqDataLeftSeq_absSub_le_widthC seq j _ m₂ n₂ hm hn
      have hlt :
          regularSeqLtProp
            (absSeq (subSeq (lemma34SeqDataLeftSeqC seq j m₂)
                            (lemma34SeqDataLeftSeqC seq j n₂)))
            (halfPow g) :=
        regularSeqLtProp_of_le_of_lt hcm hK
      exact repCloseAtGauge_of_absGap _ _ g hlt }

/-- Rep-carrying limit of a step-free tower sequence's left endpoints. -/
noncomputable def lemma34SeqDataLimitReprC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (j : Fin n) :
    CRealRepLimitData (fun k => lemma34SeqDataLeftSeqC seq j k) :=
  CReal.complete_repCarrying_data _ (lemma34SeqDataLeftSeqCauchyDataC seq j)

/-- Limit-data record for a step-free tower sequence. -/
structure Lemma34SeqLimitDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n) : Type 2 where
  t : Fin n → CReal
  t_bounds : ∀ j : Fin n, RegularSeqLe a (t j) ∧ RegularSeqLe (t j) b
  left_le_t : ∀ j : Fin n, ∀ k : Nat,
    RegularSeqLe (lemma34SeqDataLeftSeqC seq j k) (t j)
  t_le_right : ∀ j : Fin n, ∀ k : Nat,
    RegularSeqLe (t j) (lemma34SeqDataRightSeqC seq j k)

/-- Construct step-free limit data by Cauchy completeness of nested intervals.
-/
noncomputable def lemma34SeqLimitDataC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n) :
    Lemma34SeqLimitDataC seq :=
  { t := fun j => (lemma34SeqDataLimitReprC seq j).limit
    t_bounds := fun j =>
      ⟨ repLimitData_ge_of_eventually_ge (lemma34SeqDataLimitReprC seq j) a 0
          (fun m _ => (lemma34SeqData_seg_properC seq j m).1),
        repLimitData_le_of_eventually_le (lemma34SeqDataLimitReprC seq j) b 0
          (fun m _ => regularSeqLe_trans
            (lemma34SeqDataLeftSeq_le_rightSeqC seq j m 0)
            (lemma34SeqData_seg_properC seq j 0).2.2) ⟩
    left_le_t := fun j k₀ =>
      repLimitData_ge_of_eventually_ge (lemma34SeqDataLimitReprC seq j)
        (lemma34SeqDataLeftSeqC seq j k₀) k₀
        (fun _m hm => lemma34SeqDataLeftSeq_monoC seq j hm)
    t_le_right := fun j k₀ =>
      repLimitData_le_of_eventually_le (lemma34SeqDataLimitReprC seq j)
        (lemma34SeqDataRightSeqC seq j k₀) 0
        (fun m _ => lemma34SeqDataLeftSeq_le_rightSeqC seq j m k₀) }

/-- Limit points selected from step-free limit data. -/
noncomputable def lemma34SeqLimitPointsC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    {seq : Lemma34TowerSeqDataC (eps := eps) P n}
    (data : Lemma34SeqLimitDataC seq) : Fin n → CReal :=
  data.t

/-- Width choice for a step-free tower sequence. -/
structure Lemma34SeqWidthChoiceC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (beta : CReal) where
  k : Nat
  width_lt : ∀ j : Fin n,
    regularSeqLtProp
      (CReal.sub ((seq.T k).segR j) ((seq.T k).segL j))
      beta

/-- DATA-beta width-choice provider for a step-free tower sequence. -/
noncomputable def lemma34SeqWidthChoiceProviderDataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n) :
    ∀ beta : CReal, PosEventuallyData beta →
      Lemma34SeqWidthChoiceC seq beta :=
  fun beta hdata =>
    let ch := lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b) beta hdata
    { k := ch.val
      width_lt := fun j =>
        regularSeqLtProp_of_le_of_lt
          ((seq.T ch.val).seg_width j)
          ch.property }

/-- Step-free far-outside geometry from limit data. -/
structure Lemma34SeqFarOutsideFromLimitC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (data : Lemma34SeqLimitDataC seq) where
  far_outside : ∀ beta : CReal,
    regularSeqLtProp zeroSeq beta →
      (choice : Lemma34SeqWidthChoiceC seq beta) →
      ∀ t_pt : CReal,
        RegularSeqLe a t_pt →
          RegularSeqLe t_pt b →
            (∀ i : Fin n,
              regularSeqLtProp beta
                (CReal.abs
                  (CReal.sub t_pt (lemma34SeqLimitPointsC data i)))) →
            ∀ j : Fin n,
              regularSeqLtProp ((seq.T choice.k).segR j) t_pt ∨
                regularSeqLtProp t_pt ((seq.T choice.k).segL j)

/-- Generic construction of step-free far-outside geometry from nested limit
data. -/
noncomputable def lemma34SeqFarOutsideFromLimitC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (data : Lemma34SeqLimitDataC seq) :
    Lemma34SeqFarOutsideFromLimitC seq data :=
  { far_outside := by
      intro beta hbeta choice t_pt _hat _htb hfar j
      let Tseq := seq.T choice.k
      let L : CReal := Tseq.segL j
      let R : CReal := Tseq.segR j
      let tj : CReal := lemma34SeqLimitPointsC data j
      have hL_t : RegularSeqLe L tj := by
        simpa [L, tj, Tseq, lemma34SeqDataLeftSeqC, lemma34SeqLimitPointsC]
          using data.left_le_t j choice.k
      have ht_R : RegularSeqLe tj R := by
        simpa [R, tj, Tseq, lemma34SeqDataRightSeqC, lemma34SeqLimitPointsC]
          using data.t_le_right j choice.k
      have hwidth : regularSeqLtProp (CReal.sub R L) beta := by
        simpa [R, L, Tseq] using choice.width_lt j
      have hfarj :
          regularSeqLtProp beta (CReal.abs (CReal.sub t_pt tj)) := by
        simpa [tj] using hfar j
      rcases regularSeqLtProp_abs_split hbeta hfarj with hright | hleft
      · left
        have hRt_le_width : RegularSeqLe (CReal.sub R tj) (CReal.sub R L) :=
          regularSeqLe_sub_leftC (a := L) (b := tj) (c := R) hL_t
        have hRt_lt_beta : regularSeqLtProp (CReal.sub R tj) beta :=
          regularSeqLtProp_of_le_of_lt hRt_le_width hwidth
        have hRt_lt_tpt :
            regularSeqLtProp (CReal.sub R tj) (CReal.sub t_pt tj) :=
          regularSeqLtProp_trans (CReal.sub R tj) beta (CReal.sub t_pt tj)
            hRt_lt_beta hright
        have hR_tpt : regularSeqLtProp R t_pt :=
          regularSeqLtProp_add_sub_cancel_rightC hRt_lt_tpt
        simpa [R, Tseq] using hR_tpt
      · right
        have htL_le_width : RegularSeqLe (CReal.sub tj L) (CReal.sub R L) := by
          change RegularSeqLe (subSeq tj L) (subSeq R L)
          exact subSeq_monotone_left_regularSeqLe tj R L ht_R
        have htL_lt_beta : regularSeqLtProp (CReal.sub tj L) beta :=
          regularSeqLtProp_of_le_of_lt htL_le_width hwidth
        have hleft_sub : regularSeqLtProp beta (CReal.sub tj t_pt) :=
          regularSeqLtProp_of_right_eventual (neg_sub_eventualC t_pt tj) hleft
        have htL_lt_tpt :
            regularSeqLtProp (CReal.sub tj L) (CReal.sub tj t_pt) :=
          regularSeqLtProp_trans (CReal.sub tj L) beta (CReal.sub tj t_pt)
            htL_lt_beta hleft_sub
        have htpt_L : regularSeqLtProp t_pt L :=
          regularSeqLtProp_sub_left_cancel_revC htL_lt_tpt
        simpa [L, Tseq] using htpt_L }

/-- Build the DATA-beta Lemma 3.4 result from a step-free tower sequence,
its limit data, per-level outside witnesses, and beta-free far-outside geometry.
-/
noncomputable def lemma34ResultDataC_of_seqLimitOutsideC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n : Nat}
    (seq : Lemma34TowerSeqDataC (eps := eps) P n)
    (data : Lemma34SeqLimitDataC seq)
    (outsideAt : ∀ k : Nat,
      Lemma34TowerOutsideC (eps := eps) P n k (seq.T k))
    (farOutside : Lemma34SeqFarOutsideFromLimitC seq data) :
    Lemma34ResultDataC (eps := eps) P n :=
  { t := lemma34SeqLimitPointsC data
    t_bounds := fun j => data.t_bounds j
    local_data := fun beta hdata =>
      let choice := lemma34SeqWidthChoiceProviderDataC seq beta hdata
      let outData := outsideAt choice.k
      { gamma := outData.gamma
        gamma_pos := outData.gamma_pos
        local_bound := fun t_pt hat htb hfar =>
          outData.outside t_pt hat htb
            (farOutside.far_outside beta
              (regularSeqLtProp_zero_of_posEventuallyData hdata)
              choice t_pt hat htb hfar) } }

/-- Final reducer for the canonical source-faithful block route: a stateful
block-step input provider supplies a complete DATA-beta Lemma 3.4 result. -/
noncomputable def lemma34ResultDataC_of_initialBlockRouteC
    (provider : Lemma34BlockTowerStepInputProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  let seq := lemma34InitialBlockTowerSeqDataC provider P heps n hn h_cond
  let data := lemma34SeqLimitDataC_construct seq
  lemma34ResultDataC_of_seqLimitOutsideC seq data
    (lemma34InitialBlockTowerSeqOutsideC provider P heps n hn h_cond)
    (lemma34SeqFarOutsideFromLimitC_construct seq data)

/-- Block-route subresult provider: at every state and for every retained
block, supply the subinterval Lemma 3.3 DATA used for the next refinement. -/
structure Lemma34BlockTowerSubDataProviderC : Type 2 where
  subData :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      {P : ProfileC a b hab} → {n k : Nat} →
      (S : Lemma34BlockTowerStateC (eps := eps) (P := P) n k) →
      (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B

/-- Remaining block-route zero-cover provider after the subresult DATA is
separated out.  The half-min sigma is supplied by the standard constructor. -/
structure Lemma34BlockTowerZeroCoverProviderC
    (subProvider : Lemma34BlockTowerSubDataProviderC) : Type 2 where
  zeroData :
    {a b eps : CReal} → {hab : regularSeqLtProp a b} →
      {P : ProfileC a b hab} → {n k : Nat} →
      (S : Lemma34BlockTowerStateC (eps := eps) (P := P) n k) →
      Lemma34BlockZeroCellCoverDataC S.BT S.outside
        (subProvider.subData S)
        (lemma34BlockTowerStepHalfSigmaC_construct
          S.BT S.outside (subProvider.subData S))

/-- Assemble the original stateful block-step input provider from separated
subresult and zero-cover providers. -/
noncomputable def lemma34BlockTowerStepInputProviderC_of_zeroCoverProviderC
    (subProvider : Lemma34BlockTowerSubDataProviderC)
    (zeroProvider : Lemma34BlockTowerZeroCoverProviderC subProvider) :
    Lemma34BlockTowerStepInputProviderC where
  input := by
    intro a b eps hab P n k S
    exact lemma34BlockTowerStepInputC_standard S.BT S.outside
      (subProvider.subData S)
      (zeroProvider.zeroData S)

/-- Final block-route reducer in decomposed frontier form.  At this point the
only inputs are subinterval Lemma 3.3 DATA for retained blocks and the
zero-cell cover DATA for zero-multiplicity cells. -/
noncomputable def lemma34ResultDataC_of_blockTowerZeroCoverProviderC
    (subProvider : Lemma34BlockTowerSubDataProviderC)
    (zeroProvider : Lemma34BlockTowerZeroCoverProviderC subProvider)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma34ResultDataC_of_initialBlockRouteC
    (lemma34BlockTowerStepInputProviderC_of_zeroCoverProviderC
      subProvider zeroProvider)
    P heps n hn h_cond

/-- Prop-level `x < x + sigma` from Prop-level positivity of `sigma`.
This is the zero-cell cover analogue of the DATA sigma-gap atom, but avoids
the choice-blocked Prop-to-DATA conversion. -/
theorem regularSeqLtProp_self_add_sigmaC {sigma : CReal} (x : CReal)
    (hsigma : regularSeqLtProp CReal.zero sigma) :
    regularSeqLtProp x (CReal.add x sigma) := by
  have hraw : regularSeqLtProp
      (CReal.add x CReal.zero) (CReal.add x sigma) :=
    regularSeqLtProp_add_left x CReal.zero sigma hsigma
  exact regularSeqLtProp_of_left_eventual
    (Setoid.symm (CReal.add_zero x)) hraw

/-- Prop-level `x - sigma < x` from Prop-level positivity of `sigma`.
This is enough for Prop-cotransitive zero-cell cover construction. -/
theorem regularSeqLtProp_sub_sigma_selfC {sigma : CReal} (x : CReal)
    (hsigma : regularSeqLtProp CReal.zero sigma) :
    regularSeqLtProp (CReal.sub x sigma) x := by
  have hraw : regularSeqLtProp
      (CReal.add (CReal.sub x sigma) CReal.zero)
      (CReal.add (CReal.sub x sigma) sigma) :=
    regularSeqLtProp_add_left (CReal.sub x sigma) CReal.zero sigma hsigma
  have hleft : regularSeqLtProp
      (CReal.sub x sigma)
      (CReal.add (CReal.sub x sigma) sigma) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (CReal.add_zero (CReal.sub x sigma))) hraw
  have hright_eq : CReal.add (CReal.sub x sigma) sigma ≈ x :=
    Setoid.trans (CReal.add_comm (CReal.sub x sigma) sigma)
      (add_sub_cancel_right_eventualC x sigma)
  exact regularSeqLtProp_of_right_eventual hright_eq hleft

/-- Upgrade a Prop-valued strict representative inequality to DATA.
The bridge is the existing choice-free strong-gauge extraction
`posEventually_to_strongC`/`strongGaugeC`; no choice-selection is used. -/
def regularSeqLtData_of_ltPropC {x y : CReal}
    (h : regularSeqLtProp x y) : regularSeqLtData x y := by
  show PosEventuallyData (subSeq y x)
  exact posEventuallyData_of_strongGaugeC
    (strongGaugeC (posEventually_to_strongC h))

/-- A packaged zero cell from a parent block occurs in the auxiliary zero-cell
list for any source index list containing its index. -/
theorem lemma34GlobalZeroCellOf_mem_auxC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ blocks)
    {xs : List Nat} {i : Nat}
    (hix : i ∈ xs) (hi : i < (data B).result.N)
    (hz : (data B).result.M i = 0) :
    lemma34GlobalZeroCellOfC blocks data B hB i hi hz ∈
      lemma34GlobalZeroCellsForBlockAuxC blocks data B hB xs := by
  induction xs with
  | nil =>
      simp at hix
  | cons j js ih =>
      simp only [List.mem_cons] at hix
      rcases hix with rfl | hix
      · simp [lemma34GlobalZeroCellsForBlockAuxC, hi, hz]
      · by_cases hj : j < (data B).result.N
        · by_cases hzj : (data B).result.M j = 0
          · simp [lemma34GlobalZeroCellsForBlockAuxC, hj, hzj, ih hix]
          · simpa [lemma34GlobalZeroCellsForBlockAuxC, hj, hzj] using ih hix
        · simpa [lemma34GlobalZeroCellsForBlockAuxC, hj] using ih hix

/-- A packaged zero cell occurs in the global zero-cell list. -/
theorem lemma34GlobalZeroCellOf_memC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {k : Nat}
    (blocks : List (Lemma34BlockC (eps := eps) P k))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ blocks)
    (i : Nat) (hi : i < (data B).result.N)
    (hz : (data B).result.M i = 0) :
    lemma34GlobalZeroCellOfC blocks data B hB i hi hz ∈
      lemma34GlobalZeroCellsC blocks data := by
  unfold lemma34GlobalZeroCellsC
  rw [List.mem_flatMap]
  refine ⟨⟨B, hB⟩, ?_, ?_⟩
  · simp
  · exact lemma34GlobalZeroCellOf_mem_auxC blocks data B hB
      (List.mem_range.mpr hi) hi hz

/-- The radius of a packaged zero cell occurs in the block-step radius list. -/
theorem lemma34GlobalZeroCellOmega_mem_radiiC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B)
    (B : Lemma34BlockC (eps := eps) P k) (hB : B ∈ BT.blocks)
    (i : Nat) (hi : i < (data B).result.N)
    (hz : (data B).result.M i = 0) :
    lemma34GlobalZeroCellOmegaC
        (lemma34GlobalZeroCellOfC BT.blocks data B hB i hi hz) ∈
      lemma34BlockTowerStepRadiiC BT data := by
  unfold lemma34BlockTowerStepRadiiC
  exact List.mem_map.mpr
    ⟨ lemma34GlobalZeroCellOfC BT.blocks data B hB i hi hz,
      lemma34GlobalZeroCellOf_memC BT.blocks data B hB i hi hz,
      rfl ⟩

/-- Construct the block-route zero-cell cover.  The branch selection uses
DATA-cotransitivity; DATA gaps are obtained from the Prop sigma positivity via
the existing strong-gauge Prop-to-DATA bridge. -/
def lemma34BlockZeroCellCoverDataC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (BT : Lemma34BlockTowerC (eps := eps) P n k)
    (oldOut : Lemma34TowerOutsideC (eps := eps) P n k
      (lemma34TowerC_of_blockTowerC P n k BT))
    (data : (B : Lemma34BlockC (eps := eps) P k) →
      Lemma34BlockSubResultDataC (eps := eps) P k B) :
    Lemma34BlockZeroCellCoverDataC BT oldOut data
      (lemma34BlockTowerStepHalfSigmaC_construct BT oldOut data) :=
  { zeroCover := by
      intro t_pt hat htb hnew B hB i hi hzero
      let S := lemma34BlockTowerStepHalfSigmaC_construct BT oldOut data
      let G := lemma34GlobalZeroCellOfC BT.blocks data B hB i hi hzero
      let pprime := lemma34GlobalZeroCellPPrimeC G
      let left : CReal := (data B).result.pts i
      let right : CReal := (data B).result.pts (i + 1)
      have hleft_gap_prop :
          regularSeqLtProp (CReal.sub left S.sigma) left :=
        regularSeqLtProp_sub_sigma_selfC left S.sigma_pos
      have hleft_gap :
          regularSeqLtData (CReal.sub left S.sigma) left :=
        regularSeqLtData_of_ltPropC hleft_gap_prop
      cases regularSeqLtData_cotrans
          (CReal.sub left S.sigma) left t_pt hleft_gap with
      | inr ht_left =>
          exact PSum.inr (PSum.inr (by simpa [left] using ht_left.toProp))
      | inl hleftNear =>
          have hright_gap_prop :
              regularSeqLtProp right (CReal.add right S.sigma) :=
            regularSeqLtProp_self_add_sigmaC right S.sigma_pos
          have hright_gap :
              regularSeqLtData right (CReal.add right S.sigma) :=
            regularSeqLtData_of_ltPropC hright_gap_prop
          cases regularSeqLtData_cotrans
              right (CReal.add right S.sigma) t_pt hright_gap with
          | inl hright_out =>
              exact PSum.inr
                (PSum.inl (by simpa [right] using hright_out.toProp))
          | inr hrightNear =>
              have hr0 :
                  lemma34GlobalZeroCellOmegaC G ∈
                    lemma34BlockTowerStepRadiiC BT data := by
                dsimp [G]
                exact lemma34GlobalZeroCellOmega_mem_radiiC
                  BT data B hB i hi hzero
              have hr :
                  lemma34GlobalZeroCellOmegaC G ∈ S.radii := by
                dsimp [S]
                simpa [lemma34BlockTowerStepHalfSigmaC_construct] using hr0
              have htwice0 :
                  RegularSeqLe (CReal.add S.sigma S.sigma)
                    (lemma34GlobalZeroCellOmegaC G) :=
                S.twice_sigma_le_mem (lemma34GlobalZeroCellOmegaC G) hr
              have htwice :
                  RegularSeqLe (CReal.add S.sigma S.sigma) pprime.alpha := by
                simpa [pprime, G, lemma34GlobalZeroCellOmegaC] using htwice0
              exact PSum.inl
                (lemma34ZeroCollarC_of_pprime_nearC
                  (eps := eps) P (sigma := S.sigma) (left := left)
                  (right := right) (t_pt := t_pt) (pprime := pprime)
                  htwice hleftNear.toProp hrightNear.toProp) }

/-- The block-route zero-cover provider is automatic once the retained-block
subresult provider is supplied. -/
noncomputable def lemma34BlockTowerZeroCoverProviderC_construct
    (subProvider : Lemma34BlockTowerSubDataProviderC) :
    Lemma34BlockTowerZeroCoverProviderC subProvider where
  zeroData := by
    intro a b eps hab P n k S
    exact lemma34BlockZeroCellCoverDataC_construct
      S.BT S.outside (subProvider.subData S)

/-- Final block-route reducer with only the retained-block subresult frontier
remaining.  The zero-cell cover is constructed internally. -/
noncomputable def lemma34ResultDataC_of_blockTowerSubDataProviderC
    (subProvider : Lemma34BlockTowerSubDataProviderC)
    {a b eps : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma34ResultDataC_of_blockTowerZeroCoverProviderC
    subProvider
    (lemma34BlockTowerZeroCoverProviderC_construct subProvider)
    P heps n hn h_cond


/- Relative CReal-native Lemma 3.3 and retained-block subData provider.
   Generated from ScratchRelSlotC after successful auxiliary build. -/

/-- Relative slot predicate for the CReal-native relative Lemma 3.3 route.
The endpoint codes are supplied by the ambient `p'` budget witness. -/
def SlotRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (e : Nat) (z1 z0 : P.Code)
    (i : Nat) (g : P.Code) : Prop :=
  g ∈ P.F ∧
  (i = 0 → g = z1) ∧
  (i = 2 ^ e + 1 → g = z0) ∧
  (∀ (_hi0 : 0 < i) (_hiK : i ≤ 2 ^ e),
    (∀ t, RegularSeqLe a t →
      RegularSeqLe t (addSeq (bptRC u d (i - 1)) (sigmaScaleC d)) →
      P.embed g t ≈ CReal.zero) ∧
    (∀ t, RegularSeqLe (subSeq (bptRC u d i) (sigmaScaleC d)) t →
      RegularSeqLe t b →
      P.embed g t ≈ CReal.one))

noncomputable def hSlotRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (i : Nat) : { g : P.Code // SlotRelC (u := u) (v := v) (d := d) P e z1 z0 i g } := by
  by_cases hi0 : i = 0
  · subst i
    exact ⟨z1, hz1F, (fun _ => rfl),
      (fun hbad => (Nat.succ_ne_zero (2 ^ e) hbad.symm).elim),
      (fun hpos => absurd hpos (lt_irrefl 0))⟩
  by_cases hiMid : 0 < i ∧ i ≤ 2 ^ e
  · rcases hiMid with ⟨hiPos, hiK⟩
    have hji : i - 1 + 1 = i := by omega
    have hj1 : i - 1 + 1 ≤ 2 ^ e := by rw [hji]; exact hiK
    have hau0 : RegularSeqLe u (addSeq (bptRC u d (i - 1)) (sigmaScaleC d)) :=
      slot_hauC u d hd_nn hd_pos (i - 1)
    have hau : RegularSeqLe a (addSeq (bptRC u d (i - 1)) (sigmaScaleC d)) :=
      regularSeqLe_trans hu hau0
    have huv : PosEventuallyData
        (CReal.sub (subSeq (bptRC u d i) (sigmaScaleC d))
          (addSeq (bptRC u d (i - 1)) (sigmaScaleC d))) := by
      have h := gridSlot_lt_dataC (a := u) hd_pos (i - 1)
      rw [hji] at h
      exact h
    have hvb0 : RegularSeqLe (subSeq (bptRC u d i) (sigmaScaleC d)) v := by
      have h := slot_hvbC (a := u) (b := v) hd_nn hd_pos e hdeq (j := i - 1) hj1
      rw [hji] at h
      exact h
    have hvb : RegularSeqLe (subSeq (bptRC u d i) (sigmaScaleC d)) b :=
      regularSeqLe_trans hvb0 hv
    rcases P.separating (addSeq (bptRC u d (i - 1)) (sigmaScaleC d))
        (subSeq (bptRC u d i) (sigmaScaleC d)) hau huv hvb with ⟨g, hg, hgz, hgo⟩
    exact ⟨g, hg, (fun h => (hi0 h).elim),
      (fun hK1 => absurd (hK1 ▸ hiK) (Nat.not_succ_le_self _)),
      (fun _ _ => ⟨hgz, hgo⟩)⟩
  · exact ⟨z0, hz0F, (fun h => (hi0 h).elim), (fun _ => rfl),
      (fun hiPos hiK => (hiMid ⟨hiPos, hiK⟩).elim)⟩

noncomputable def fRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) : Nat → P.Code :=
  fun i => (hSlotRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i).val

theorem fRelC_spec {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) (i : Nat) :
    SlotRelC (u := u) (v := v) (d := d) P e z1 z0 i (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) :=
  (hSlotRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i).property

theorem fRelC_mem {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) (i : Nat) :
    fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i ∈ P.F :=
  (fRelC_spec P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i).1

theorem fRelC_zero {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) :
    fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0 = z1 :=
  (fRelC_spec P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0).2.1 rfl

theorem fRelC_last {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) :
    fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1) = z0 :=
  (fRelC_spec P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)).2.2.1 rfl

theorem fRelC_left {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (i : Nat) (hi0 : 0 < i) (hiK : i ≤ 2 ^ e) :
    ∀ t, RegularSeqLe a t →
      RegularSeqLe t (addSeq (bptRC u d (i - 1)) (sigmaScaleC d)) →
      P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t ≈ CReal.zero :=
  ((fRelC_spec P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i).2.2.2 hi0 hiK).1

theorem fRelC_right {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (i : Nat) (hi0 : 0 < i) (hiK : i ≤ 2 ^ e) :
    ∀ t, RegularSeqLe (subSeq (bptRC u d i) (sigmaScaleC d)) t →
      RegularSeqLe t b →
      P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t ≈ CReal.one :=
  ((fRelC_spec P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i).2.2.2 hi0 hiK).2


theorem fRelC_le_top {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (j : Nat) (hj : j ≤ 2 ^ e + 1) :
    ∀ t, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t)
        (P.embed z1 t) := by
  intro t hat htb
  by_cases hj0 : j = 0
  · subst j
    rw [fRelC_zero P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
    exact regularSeqLe_refl _
  by_cases hjlast : j = 2 ^ e + 1
  · subst j
    rw [fRelC_last P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
    exact hz0_le_z1 t hat htb
  have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
  have hjK : j ≤ 2 ^ e := by omega
  have him1 : j - 1 ≤ 2 ^ e := by omega
  have hbase : RegularSeqLe u (bptRC u d (j - 1)) :=
    ha_bptRC u d hd_nn (j - 1)
  have hsig : regularSeqLtProp (bptRC u d (j - 1))
      (addSeq (bptRC u d (j - 1)) (sigmaScaleC d)) :=
    regularSeqLtProp_self_add_sigmaC (bptRC u d (j - 1))
      (sigmaScaleC_pos_prop hd_pos)
  have hgap : regularSeqLtProp u
      (addSeq (bptRC u d (j - 1)) (sigmaScaleC d)) :=
    regularSeqLtProp_of_le_of_lt hbase hsig
  rcases regularSeqLtProp_cotrans u
      (addSeq (bptRC u d (j - 1)) (sigmaScaleC d)) t hgap with hut | htleft
  · have hz1 : P.embed z1 t ≈ CReal.one :=
      hz1_one_from_u t hat htb (regularSeqLe_of_ltPropC hut)
    have hf_le_one : RegularSeqLe
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t)
        CReal.one :=
      (P.bound (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j)
        (fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t hat htb).2
    exact regularSeqLe_of_right_eventual (Setoid.symm hz1) hf_le_one
  · have hfz : P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t
        ≈ CReal.zero :=
      fRelC_left P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j hjPos hjK
        t hat (regularSeqLe_of_ltPropC htleft)
    have hzero_le_z1 : RegularSeqLe CReal.zero (P.embed z1 t) :=
      regularSeqLe_zero_of_nonnegC ((P.bound z1 hz1F t hat htb).1)
    exact regularSeqLe_of_left_eventual hfz hzero_le_z1

theorem z0_le_fRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (i : Nat) (hi : i ≤ 2 ^ e + 1) :
    ∀ t, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe
        (P.embed z0 t)
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t) := by
  intro t hat htb
  by_cases hi0 : i = 0
  · subst i
    rw [fRelC_zero P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
    exact hz0_le_z1 t hat htb
  by_cases hilast : i = 2 ^ e + 1
  · subst i
    rw [fRelC_last P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
    exact regularSeqLe_refl _
  have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
  have hiK : i ≤ 2 ^ e := by omega
  have hsub_lt : regularSeqLtProp
      (subSeq (bptRC u d i) (sigmaScaleC d)) (bptRC u d i) :=
    regularSeqLtProp_sub_sigma_selfC (bptRC u d i) (sigmaScaleC_pos_prop hd_pos)
  have hbi : RegularSeqLe (bptRC u d i) v :=
    hbptRC_b (a := u) (b := v) hd_nn e hdeq hiK
  have hgap : regularSeqLtProp
      (subSeq (bptRC u d i) (sigmaScaleC d)) v :=
    regularSeqLtProp_of_lt_of_le hsub_lt hbi
  rcases regularSeqLtProp_cotrans
      (subSeq (bptRC u d i) (sigmaScaleC d)) v t hgap with hright | htv
  · have hfi : P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t
        ≈ CReal.one :=
      fRelC_right P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i hiPos hiK
        t (regularSeqLe_of_ltPropC hright) htb
    have hz0_le_one : RegularSeqLe (P.embed z0 t) CReal.one :=
      (P.bound z0 hz0F t hat htb).2
    exact regularSeqLe_of_right_eventual (Setoid.symm hfi) hz0_le_one
  · have hz0 : P.embed z0 t ≈ CReal.zero :=
      hz0_zero_to_v t hat htb (regularSeqLe_of_ltPropC htv)
    have hzero_le_f : RegularSeqLe CReal.zero
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t) :=
      regularSeqLe_zero_of_nonnegC
        ((P.bound (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i)
          (fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t hat htb).1)
    exact regularSeqLe_of_left_eventual hz0 hzero_le_f

theorem hfRelC_anti {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (i j : Nat) (hij : i ≤ j) (hjK1 : j ≤ 2 ^ e + 1) :
    ∀ t, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t)
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t) := by
  intro t hat htb
  by_cases hi0 : i = 0
  · subst i
    rw [fRelC_zero P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
    exact fRelC_le_top P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_le_z1 j hjK1 t hat htb
  by_cases hjlast : j = 2 ^ e + 1
  · subst j
    rw [fRelC_last P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
    exact z0_le_fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz0_zero_to_v hz0_le_z1 i (Nat.le_trans hij (Nat.le_refl _)) t hat htb
  by_cases hijEq : i = j
  · subst j
    exact regularSeqLe_refl _
  have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
  have hjK : j ≤ 2 ^ e := by
    have hjlt : j < 2 ^ e + 1 := Nat.lt_of_le_of_ne hjK1 hjlast
    exact Nat.le_of_lt_succ hjlt
  have hijlt : i < j := Nat.lt_of_le_of_ne hij hijEq
  have hjPos : 0 < j := Nat.lt_trans hiPos hijlt
  have hiK : i ≤ 2 ^ e := Nat.le_trans (Nat.le_of_lt hijlt) hjK
  have hgap : regularSeqLtProp
      (subSeq (bptRC u d i) (sigmaScaleC d))
      (addSeq (bptRC u d (j - 1)) (sigmaScaleC d)) :=
    grid_slot_prop_gapC hd_nn hd_pos hijlt
  rcases regularSeqLtProp_cotrans
      (subSeq (bptRC u d i) (sigmaScaleC d))
      (addSeq (bptRC u d (j - 1)) (sigmaScaleC d)) t hgap with htRight | htLeft
  · have hfi : P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t
        ≈ CReal.one :=
      fRelC_right P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i hiPos hiK
        t (regularSeqLe_of_ltPropC htRight) htb
    have hj_le_one : RegularSeqLe
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t)
        CReal.one :=
      (P.bound (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j)
        (fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t hat htb).2
    exact regularSeqLe_of_right_eventual (Setoid.symm hfi) hj_le_one
  · have hfj : P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j) t
        ≈ CReal.zero :=
      fRelC_left P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j hjPos hjK
        t hat (regularSeqLe_of_ltPropC htLeft)
    have hzero_le_i : RegularSeqLe CReal.zero
        (P.embed (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t) :=
      regularSeqLe_zero_of_nonnegC
        ((P.bound (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i)
          (fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) t hat htb).1)
    exact regularSeqLe_of_left_eventual hfj hzero_le_i

noncomputable def lamRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) : Nat → CReal :=
  fun i => P.lambda (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i)

theorem hlamRelC_anti {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (i j : Nat) (hij : i ≤ j) (hjK1 : j ≤ 2 ^ e + 1) :
    RegularSeqLe
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j)
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) := by
  dsimp [lamRelC]
  exact P.mono
    (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j)
    (fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i)
    (fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F j)
    (fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i)
    (hfRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 i j hij hjK1)

noncomputable def alphaRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) : Nat → CReal :=
  fun i => CReal.sub
    (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (i - 1))
    (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (i + 1))

theorem halphaRelC_nn {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (i : Nat) (_hi0 : 0 < i) (hiK : i ≤ 2 ^ e) :
    RegularSeqNonneg (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) := by
  have hidx : i - 1 ≤ i + 1 := Nat.le_trans (Nat.sub_le i 1) (Nat.le_succ i)
  have hupper : i + 1 ≤ 2 ^ e + 1 := Nat.succ_le_succ hiK
  have hle := hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
    hz1_one_from_u hz0_zero_to_v hz0_le_z1 (i - 1) (i + 1) hidx hupper
  simpa [alphaRelC, lamRelC] using hle


noncomputable def hpprimeRel_of_gapC {a b u v d upper rho : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (CReal.max a (CReal.sub u rho)) t →
        P.embed z1 t ≈ CReal.one)
    (hz0_zero_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t (CReal.min b (CReal.add v rho)) →
        P.embed z0 t ≈ CReal.zero)
    (hsigma_rho : RegularSeqLe (sigmaScaleC d) rho)
    (k i : Nat) (hki : k < i) (hiK : i ≤ 2 ^ e)
    (hgap : regularSeqLtProp
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F k)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (i + 1))) upper) :
    P.p_prime_ltC (bptRC u d k) (bptRC u d i) upper := by
  refine ⟨sigmaScaleC d, sigmaScaleC_pos_prop hd_pos, ?_⟩
  refine ⟨fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (i + 1),
    fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (i + 1),
    fRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F k,
    fRelC_mem P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F k, ?_, ?_, ?_⟩
  · intro t hat htb htv
    have htv' : RegularSeqLe t (addSeq (bptRC u d i) (sigmaScaleC d)) :=
      regularSeqLe_trans htv
        (CReal.min_le_rightC b (addSeq (bptRC u d i) (sigmaScaleC d)))
    by_cases hi : i = 2 ^ e
    · subst i
      rw [fRelC_last P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
      have hbptv : RegularSeqLe (bptRC u d (2 ^ e)) v :=
        hbptRC_b (a := u) (b := v) hd_nn e hdeq (Nat.le_refl _)
      have hadd : RegularSeqLe
          (addSeq (bptRC u d (2 ^ e)) (sigmaScaleC d))
          (CReal.add v rho) :=
        regularSeqLe_add hbptv hsigma_rho
      have htvrho : RegularSeqLe t (CReal.add v rho) :=
        regularSeqLe_trans htv' hadd
      have htmin : RegularSeqLe t (CReal.min b (CReal.add v rho)) :=
        CReal.le_minC htb htvrho
      exact hz0_zero_inner t hat htb htmin
    · have hiLt : i < 2 ^ e := Nat.lt_of_le_of_ne hiK hi
      have hz := fRelC_left P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        (i + 1) (by omega) (by omega) t hat (by
          rw [Nat.add_sub_cancel]
          exact htv')
      exact hz
  · intro t hat htb hut
    have hbase : RegularSeqLe (CReal.sub (bptRC u d k) (sigmaScaleC d))
        (CReal.max a (CReal.sub (bptRC u d k) (sigmaScaleC d))) :=
      CReal.le_max_rightC a (CReal.sub (bptRC u d k) (sigmaScaleC d))
    have hkt : RegularSeqLe (CReal.sub (bptRC u d k) (sigmaScaleC d)) t :=
      regularSeqLe_trans hbase hut
    by_cases hk : k = 0
    · subst k
      rw [fRelC_zero P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
      have hbpt0 : bptRC u d 0 ≈ u :=
        Setoid.trans (bptRC_equiv_bptC u d 0) (bptC_zeroC u d)
      have hsubeq : CReal.sub (bptRC u d 0) (sigmaScaleC d) ≈
          CReal.sub u (sigmaScaleC d) :=
        CReal.sub_respects_equiv _ _ _ _ hbpt0 (Setoid.refl (sigmaScaleC d))
      have huσ_t : RegularSeqLe (CReal.sub u (sigmaScaleC d)) t :=
        regularSeqLe_of_left_eventual (Setoid.symm hsubeq) hkt
      have hurho_uσ : RegularSeqLe (CReal.sub u rho) (CReal.sub u (sigmaScaleC d)) :=
        regularSeqLe_sub_leftC hsigma_rho
      have hurho_t : RegularSeqLe (CReal.sub u rho) t :=
        regularSeqLe_trans hurho_uσ huσ_t
      have hmax_t : RegularSeqLe (CReal.max a (CReal.sub u rho)) t :=
        CReal.max_leC hat hurho_t
      exact hz1_one_inner t hat htb hmax_t
    · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
      have hkK : k ≤ 2 ^ e := Nat.le_trans (Nat.le_of_lt hki) hiK
      exact fRelC_right P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        k hkPos hkK t hkt htb
  · exact hgap

noncomputable def betaRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) : Nat → CReal :=
  fun j => CReal.sub
    (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (sC (2 ^ e) cls j))
    (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      (sC (2 ^ e) cls (j + 1) + 1))

/-- Relative beta charge is nonnegative before the retained-index hitting time. -/
theorem hbetaRel_nnC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqNonneg (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  have hle : RegularSeqLe
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        (sC (2 ^ e) cls (j + 1) + 1))
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        (sC (2 ^ e) cls j)) :=
    hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1
      (sC (2 ^ e) cls j)
      (sC (2 ^ e) cls (j + 1) + 1)
      (by
        have hstrict := hs_strictC (2 ^ e) cls j hjN
        omega)
      (by
        have hbnd := hs_le_KC (2 ^ e) cls (j + 1)
        omega)
  dsimp [betaRelC]
  exact hle

/-- Each relative retained beta charge is bounded by the relative endpoint
lambda diameter. -/
theorem hbetaRel_totalC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (j : Nat) (_hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j)
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
  let K : Nat := 2 ^ e
  have hleft : RegularSeqLe
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (sC K cls j))
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0) := by
    exact hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1
      0 (sC K cls j) (Nat.zero_le _) (by
        have hb := hs_le_KC K cls j
        omega)
  have hright : RegularSeqLe
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (K + 1))
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        (sC K cls (j + 1) + 1)) := by
    exact hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1
      (sC K cls (j + 1) + 1) (K + 1)
      (by
        have hb := hs_le_KC K cls (j + 1)
        omega)
      (Nat.le_refl _)
  have hstep1 : RegularSeqLe
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (sC K cls j))
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (sC K cls (j + 1) + 1)))
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (sC K cls (j + 1) + 1))) :=
    subSeq_monotone_left_regularSeqLe _ _ _ hleft
  have hstep2 : RegularSeqLe
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (sC K cls (j + 1) + 1)))
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (K + 1))) :=
    regularSeqLe_subSeq_right _ hright
  simpa [betaRelC, K] using regularSeqLe_trans hstep1 hstep2

/-- Relative small retained interval: a small endpoint alpha gives the
ambient `p'` bound for the corresponding relative retained interval. -/
noncomputable def hp_smallRelC {a b u v d eps rho : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (CReal.max a (CReal.sub u rho)) t →
        P.embed z1 t ≈ CReal.one)
    (hz0_zero_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t (CReal.min b (CReal.add v rho)) →
        P.embed z0 t ≈ CReal.zero)
    (hsigma_rho : RegularSeqLe (sigmaScaleC d) rho)
    (cls : Nat → Bool)
    (hcls_small : ∀ i : Nat, cls i = true →
      regularSeqLtProp
        (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) eps)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hSmallEnd : cls (sC (2 ^ e) cls (j + 1)) = true) :
    P.p_prime_ltC
      (bptRC u d (sC (2 ^ e) cls j))
      (bptRC u d (sC (2 ^ e) cls (j + 1))) eps := by
  have hprev := hs_prev_of_smallC (2 ^ e) cls j hjN hSmallEnd
  have hki := hs_strictC (2 ^ e) cls j hjN
  have hiK := hs_endpoint_le_KC (2 ^ e) cls j
  refine hpprimeRel_of_gapC P hu hv hd_nn hd_pos e hdeq
    z1 z0 hz1F hz0F hz1_one_inner hz0_zero_inner hsigma_rho
    (sC (2 ^ e) cls j) (sC (2 ^ e) cls (j + 1)) hki hiK ?_
  have halphaSmall := hcls_small (sC (2 ^ e) cls (j + 1)) hSmallEnd
  dsimp [alphaRelC] at halphaSmall
  rw [hprev] at halphaSmall
  rw [Nat.add_sub_cancel] at halphaSmall
  rw [hprev]
  exact halphaSmall

/-- Relative big retained interval: a strict beta bound gives the ambient
`p'` bound for the corresponding relative retained interval. -/
noncomputable def hp_B_boundRelC {a b u v d upper rho : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (CReal.max a (CReal.sub u rho)) t →
        P.embed z1 t ≈ CReal.one)
    (hz0_zero_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t (CReal.min b (CReal.add v rho)) →
        P.embed z0 t ≈ CReal.zero)
    (hsigma_rho : RegularSeqLe (sigmaScaleC d) rho)
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hup : regularSeqLtProp
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) upper) :
    P.p_prime_ltC
      (bptRC u d (sC (2 ^ e) cls j))
      (bptRC u d (sC (2 ^ e) cls (j + 1))) upper := by
  refine hpprimeRel_of_gapC P hu hv hd_nn hd_pos e hdeq
    z1 z0 hz1F hz0F hz1_one_inner hz0_zero_inner hsigma_rho
    (sC (2 ^ e) cls j) (sC (2 ^ e) cls (j + 1))
    (hs_strictC (2 ^ e) cls j hjN)
    (hs_endpoint_le_KC (2 ^ e) cls j) ?_
  simpa [betaRelC, Nat.add_assoc] using hup

/-- Relative charge sequence: beta on big intervals, zero otherwise. -/
noncomputable def chargeRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) : Nat → CReal :=
  fun j =>
    if BintC (2 ^ e) cls j then
      betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j
    else
      CReal.zero

theorem hchargeRel_of_BC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (j : Nat) (hBj : BintC (2 ^ e) cls j) :
    chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j =
      betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j := by
  dsimp [chargeRelC]
  rw [if_pos hBj]

theorem hchargeRel_of_notB_C {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (j : Nat) (hBj : ¬ BintC (2 ^ e) cls j) :
    chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j = CReal.zero := by
  dsimp [chargeRelC]
  rw [if_neg hBj]

theorem hchargeRel_nnC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqNonneg (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  by_cases hBj : BintC (2 ^ e) cls j
  · rw [hchargeRel_of_BC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j hBj]
    exact hbetaRel_nnC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls j hjN
  · rw [hchargeRel_of_notB_C P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j hBj]
    exact regularSeqNonneg_of_zero_le (regularSeqLe_refl CReal.zero)

theorem hcursor_after_smallRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBj : ¬ BintC (2 ^ e) cls j) :
    RegularSeqLe
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (cursorC (2 ^ e) cls j)))
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (sC (2 ^ e) cls (j + 1)))) := by
  by_cases hj0 : j = 0
  · subst j
    rw [hcursor_zeroC]
    have hle : RegularSeqLe
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (sC (2 ^ e) cls 1))
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0) :=
      hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        hz1_one_from_u hz0_zero_to_v hz0_le_z1
        0 (sC (2 ^ e) cls 1) (Nat.zero_le _) (by
          have := hs_le_KC (2 ^ e) cls 1
          omega)
    exact regularSeqLe_sub_leftC hle
  · by_cases hprev : BintC (2 ^ e) cls (j - 1)
    · have hjm1N : j - 1 + 1 < N_C (2 ^ e) cls := by omega
      have hSmallEnd : cls (sC (2 ^ e) cls ((j - 1) + 2)) = true :=
        hafter_big_smallC (2 ^ e) cls (j - 1) hjm1N hprev
      have hsimm : sC (2 ^ e) cls (j + 1) = sC (2 ^ e) cls j + 1 := by
        apply hs_prev_of_smallC (2 ^ e) cls j hjN
        have hidx : (j - 1) + 2 = j + 1 := by omega
        rwa [hidx] at hSmallEnd
      have hc : cursorC (2 ^ e) cls j = sC (2 ^ e) cls j + 1 := by
        have hj1 : (j - 1) + 1 = j := by omega
        have hcs := hcursor_succ_BC (2 ^ e) cls (j - 1) hprev
        rwa [hj1] at hcs
      rw [hc, hsimm]
      exact regularSeqLe_refl _
    · have hc : cursorC (2 ^ e) cls j = sC (2 ^ e) cls j := by
        dsimp [cursorC]
        rw [if_neg hj0, if_neg hprev]
      rw [hc]
      have hle : RegularSeqLe
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
            (sC (2 ^ e) cls (j + 1)))
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
            (sC (2 ^ e) cls j)) :=
        hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          hz1_one_from_u hz0_zero_to_v hz0_le_z1
          (sC (2 ^ e) cls j) (sC (2 ^ e) cls (j + 1))
          (Nat.le_of_lt (hs_strictC (2 ^ e) cls j hjN))
          (by
            have := hs_le_KC (2 ^ e) cls (j + 1)
            omega)
      exact regularSeqLe_sub_leftC hle

/-- Prefix/telescope estimate for the relative charge sequence. -/
theorem hchargeRel_prefixC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (r : Nat) (hrN : r ≤ N_C (2 ^ e) cls) :
    RegularSeqLe
      (lemma33PrefixC (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls) r)
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (cursorC (2 ^ e) cls r))) := by
  induction r with
  | zero =>
      rw [lemma33PrefixC_zero, hcursor_zeroC]
      exact regularSeqLe_zero_sub_selfC
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
  | succ j ih =>
      have hjN : j < N_C (2 ^ e) cls := by omega
      have hpre := ih (Nat.le_of_lt hjN)
      by_cases hBj : BintC (2 ^ e) cls j
      · have hcBefore := hcursor_before_BC (2 ^ e) cls j hjN hBj
        have hcAfter := hcursor_succ_BC (2 ^ e) cls j hBj
        have hch := hchargeRel_of_BC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j hBj
        rw [lemma33PrefixC_succ, hch, hcAfter]
        rw [hcBefore] at hpre
        have hstep : RegularSeqLe
            (CReal.add
              (lemma33PrefixC
                (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls) j)
              (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j))
            (CReal.add
              (CReal.sub
                (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
                (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
                  (sC (2 ^ e) cls j)))
              (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j)) :=
          regularSeqLe_add hpre (regularSeqLe_refl _)
        have htel : CReal.add
              (CReal.sub
                (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
                (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
                  (sC (2 ^ e) cls j)))
              (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j)
            ≈ CReal.sub
                (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
                (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
                  (sC (2 ^ e) cls (j + 1) + 1)) := by
          dsimp [betaRelC]
          exact sub_add_sub_cancelC
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
              (sC (2 ^ e) cls j))
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
              (sC (2 ^ e) cls (j + 1) + 1))
        exact regularSeqLe_of_right_eventual htel hstep
      · have hcAfter := hcursor_succ_notB_C (2 ^ e) cls j hBj
        have hch := hchargeRel_of_notB_C P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j hBj
        rw [lemma33PrefixC_succ, hch, hcAfter]
        have hpre0 : RegularSeqLe
            (CReal.add
              (lemma33PrefixC
                (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls) j)
              CReal.zero)
            (CReal.sub
              (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
              (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
                (cursorC (2 ^ e) cls j))) :=
          regularSeqLe_of_left_eventual
            (CReal.add_zero
              (lemma33PrefixC
                (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls) j)) hpre
        exact regularSeqLe_trans hpre0
          (hcursor_after_smallRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
            hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls j hjN hBj)

/-- Total relative beta charge is bounded by the relative endpoint lambda
diameter. -/
theorem hchargeRel_totalC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) :
    RegularSeqLe
      (lemma33PrefixC (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls)
        (N_C (2 ^ e) cls))
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
  have hpref := hchargeRel_prefixC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
    hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls
    (N_C (2 ^ e) cls) (Nat.le_refl _)
  have hcursorBnd := hcursorN_leC (2 ^ e) cls
  have hlowerCursor : RegularSeqLe
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        (cursorC (2 ^ e) cls (N_C (2 ^ e) cls))) :=
    hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1
      (cursorC (2 ^ e) cls (N_C (2 ^ e) cls)) (2 ^ e + 1)
      hcursorBnd (Nat.le_refl _)
  have htail : RegularSeqLe
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          (cursorC (2 ^ e) cls (N_C (2 ^ e) cls))))
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) :=
    regularSeqLe_sub_leftC hlowerCursor
  exact regularSeqLe_trans hpref htail

/-- Relative lambda total is the gap of the two endpoint codes supplied by the
ambient `p'` witness. -/
theorem lemma33RelLamTotal_equiv_gapC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F) :
    CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))
      ≈ CReal.sub (P.lambda z1) (P.lambda z0) := by
  dsimp [lamRelC]
  rw [fRelC_zero P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]
  rw [fRelC_last P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F]

theorem lemma33RelLamTotal_nonnegC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t)) :
    RegularSeqNonneg
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
  have hle : RegularSeqLe (P.lambda z0) (P.lambda z1) :=
    P.mono z0 z1 hz0F hz1F hz0_le_z1
  exact regularSeqNonneg_of_eventual
    (lemma33RelLamTotal_equiv_gapC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F)
    hle

noncomputable def lemma33ThetaRelC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (m : Nat) : CReal :=
  lemma33ThetaC
    (CReal.sub
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
    m

theorem lemma33ThetaRel_nonnegC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (m : Nat) :
    RegularSeqNonneg
      (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) := by
  exact lemma33Theta_nonnegC
    (D := CReal.sub
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
    (n := m)
    (lemma33RelLamTotal_nonnegC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz0_le_z1)

theorem lemma33ThetaRel_lt_epsC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (m : Nat)
    (hD_eps :
      regularSeqLtProp
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
        (CReal.mul (constSeq (Nat.cast (m + 1))) eps)) :
    regularSeqLtProp
      (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) eps := by
  simpa [lemma33ThetaRelC] using
    (lemma33Theta_lt_epsC
      (D := CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
      (eps := eps) (n := m) hD_eps)

noncomputable def lemma33ThetaRelDataC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (m : Nat)
    (hD_eps :
      regularSeqLtProp
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
        (CReal.mul (constSeq (Nat.cast (m + 1))) eps)) :
    regularSeqLtData
      (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) eps :=
  regularSeqLtData_of_ltPropC
    (lemma33ThetaRel_lt_epsC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)

theorem lemma33ThetaRel_budgetC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (m : Nat) :
    CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))
      ≈ CReal.mul (constSeq (Nat.cast (m + 1)))
        (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) := by
  exact lemma33Theta_budgetC
    (CReal.sub
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
    m

noncomputable def lemma33ClsRelC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (m : Nat)
    (hD_eps :
      regularSeqLtProp
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
        (CReal.mul (constSeq (Nat.cast (m + 1))) eps)) : Nat → Bool :=
  clsC (lemma33ThetaRelDataC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
    (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F)

theorem lemma33ClsRel_smallC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (m : Nat)
    (hD_eps :
      regularSeqLtProp
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
        (CReal.mul (constSeq (Nat.cast (m + 1))) eps))
    (i : Nat) (hci : lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps i = true) :
    regularSeqLtProp
      (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) eps := by
  exact clsC_small
    (lemma33ThetaRelDataC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
    (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F) i hci

theorem lemma33ClsRel_bigC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (m : Nat)
    (hD_eps :
      regularSeqLtProp
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
        (CReal.mul (constSeq (Nat.cast (m + 1))) eps))
    (i : Nat) (hci : lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps i = false) :
    regularSeqLtProp
      (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m)
      (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) := by
  exact clsC_big
    (lemma33ThetaRelDataC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
    (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F) i hci

/-- Relative approximate-floor data from the relative total lambda budget. -/
noncomputable def lemma33ApproxFloorDataRelC_construct {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta : CReal) (m : Nat)
    (htheta_eps : regularSeqLtProp theta eps)
    (htotal_lt :
      regularSeqLtProp
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
        (CReal.mul (constSeq (Nat.cast (m + 1))) eps)) :
    (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m := by
  intro j hjN
  exact lemma33H4ApproxFloorC_construct theta eps
    (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j)
    htheta_eps
    (hbetaRel_nnC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls j hjN)
    m
    (regularSeqLtProp_of_le_of_lt
      (hbetaRel_totalC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls j hjN)
      htotal_lt)

noncomputable def afloorRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    Nat → Nat :=
  fun j => if hj : j < N_C (2 ^ e) cls then (afloorData j hj).val else 0

theorem hafloorRel_leC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j ≤ m := by
  dsimp [afloorRelC]
  rw [dif_pos hjN]
  exact (afloorData j hjN).val_le

theorem hafloorRel_upperC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    regularSeqLtProp
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j)
      (CReal.mul
        (constSeq (Nat.cast
          (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j + 1))) eps) := by
  dsimp [afloorRelC]
  rw [dif_pos hjN]
  exact (afloorData j hjN).upper

theorem hafloorRel_lowerC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j))) theta)
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  dsimp [afloorRelC]
  rw [dif_pos hjN]
  exact (afloorData j hjN).lower

theorem hafloorRel_lower_strictC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hpos : 0 <
      afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j) :
    regularSeqLtProp
      (CReal.mul
        (constSeq (Nat.cast
          (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j))) theta)
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  dsimp [afloorRelC] at hpos ⊢
  rw [dif_pos hjN] at hpos ⊢
  exact (afloorData j hjN).lower_strict hpos

theorem hmrawRel_upperC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBigEnd : cls (sC (2 ^ e) cls (j + 1)) = false) :
    regularSeqLtProp
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j)
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j + 1))) eps) := by
  rw [hmraw_bigC (2 ^ e) cls
    (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j hjN hBigEnd]
  exact hafloorRel_upperC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j hjN

theorem hmrawRel_lower_big_thetaC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBigEnd : cls (sC (2 ^ e) cls (j + 1)) = false) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j))) theta)
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  rw [hmraw_bigC (2 ^ e) cls
    (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j hjN hBigEnd]
  exact hafloorRel_lowerC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j hjN

theorem hmrawRel_lower_strict_big_thetaC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hBigEnd : cls (sC (2 ^ e) cls (j + 1)) = false)
    (hpos : 0 < mrawC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j) :
    regularSeqLtProp
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j))) theta)
      (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  rw [hmraw_bigC (2 ^ e) cls
    (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j hjN hBigEnd] at hpos ⊢
  exact hafloorRel_lower_strictC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j hjN hpos

theorem hmrawRel_charge_thetaC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j))) theta)
      (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  cases hEnd : cls (sC (2 ^ e) cls (j + 1)) with
  | true =>
      have hm := hmraw_smallC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j hjN hEnd
      have hnotB : ¬ BintC (2 ^ e) cls j := by
        intro hBint
        have h2 : cls (sC (2 ^ e) cls (j + 1)) = false := hBint.2
        rw [hEnd] at h2
        exact Bool.noConfusion h2
      rw [hm, hchargeRel_of_notB_C P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j hnotB]
      exact natCast_zero_mul_le_zeroC theta
  | false =>
      have hBint : BintC (2 ^ e) cls j := ⟨hjN, hEnd⟩
      rw [hchargeRel_of_BC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j hBint]
      exact hmrawRel_lower_big_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData j hjN hEnd

theorem hmrawRel_charge_strict_thetaC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls)
    (hpos : 0 < mrawC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j) :
    regularSeqLtProp
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j))) theta)
      (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) := by
  cases hEnd : cls (sC (2 ^ e) cls (j + 1)) with
  | true =>
      have hm := hmraw_smallC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j hjN hEnd
      rw [hm] at hpos
      exfalso
      omega
  | false =>
      have hBint : BintC (2 ^ e) cls j := ⟨hjN, hEnd⟩
      rw [hchargeRel_of_BC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j hBint]
      exact hmrawRel_lower_strict_big_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m
        afloorData j hjN hEnd hpos

noncomputable def rawThetaTermRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    Nat → CReal :=
  fun j =>
    CReal.mul
      (constSeq (Nat.cast
        (mrawC (2 ^ e) cls
          (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j)))
      theta

theorem hmrawRel_charge_prefix_thetaC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    RegularSeqLe
      (lemma33PrefixC
        (rawThetaTermRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        (N_C (2 ^ e) cls))
      (lemma33PrefixC
        (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls)
        (N_C (2 ^ e) cls)) := by
  refine lemma33PrefixC_mono
    (rawThetaTermRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
    (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls)
    (N_C (2 ^ e) cls) ?_
  intro j hjN
  dsimp [rawThetaTermRelC]
  exact hmrawRel_charge_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m
    afloorData j hjN

theorem hmrawRel_charge_prefix_totalC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    RegularSeqLe
      (lemma33PrefixC
        (rawThetaTermRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        (N_C (2 ^ e) cls))
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
  exact regularSeqLe_trans
    (hmrawRel_charge_prefix_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
    (hchargeRel_totalC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls)

noncomputable def rawThetaPrefixRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    CReal :=
  lemma33PrefixC
    (rawThetaTermRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
    (N_C (2 ^ e) cls)

noncomputable def mSumThetaRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    CReal :=
  CReal.mul
    (constSeq (Nat.cast
      (mSumC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData))))
    theta

structure MSumThetaBridgeRelC {a b u v d : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) : Prop where
  equiv_prefix :
    rawThetaPrefixRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData ≈
      mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData

theorem mSumThetaBridgeRel_of_prefixC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    MSumThetaBridgeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData := by
  constructor
  dsimp [rawThetaPrefixRelC, mSumThetaRelC, rawThetaTermRelC, mSumC]
  exact lemma33PrefixC_rawTheta_equiv_natC
    (mrawC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData))
    theta
    (N_C (2 ^ e) cls)

theorem hmSumRel_scale_thetaC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (bridge : MSumThetaBridgeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) :
    RegularSeqLe
      (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
  have htot : RegularSeqLe
      (rawThetaPrefixRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
    dsimp [rawThetaPrefixRelC]
    exact hmrawRel_charge_prefix_totalC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls theta eps m afloorData
  exact regularSeqLe_of_left_eventual (Setoid.symm bridge.equiv_prefix) htot

theorem hmSumRel_scale_theta_constructedC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    RegularSeqLe
      (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
  exact hmSumRel_scale_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
    hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls theta eps m afloorData
    (mSumThetaBridgeRel_of_prefixC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)

structure MSumLeContradictionDataRelC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) : Prop where
  strict_of_bad :
    (¬ mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) ≤ m) →
    regularSeqLtProp
      (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
  lower_of_bad :
    (¬ mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) ≤ m) →
    RegularSeqLe
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
      (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)

def mSumLeCriterionRel_of_contradictionC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (badData : MSumLeContradictionDataRelC
      P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) :
    mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) ≤ m := by
  have hdec : Decidable
      (mSumC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) ≤ m) :=
    inferInstance
  cases hdec with
  | isTrue hle =>
      exact hle
  | isFalse hbad =>
      have hstrict := badData.strict_of_bad hbad
      have hlower := badData.lower_of_bad hbad
      exact (regularSeqLtProp_irrefl
        (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        (regularSeqLtProp_of_lt_of_le hstrict hlower)).elim

theorem hsum_MCRel_from_contradictionC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (badData : MSumLeContradictionDataRelC
      P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) :
    lemma33PrefixNatC
      (fun j => MC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        m (j + 1))
      (N_C (2 ^ e) cls) = m := by
  exact hsum_MC_prefixC (2 ^ e) cls
    (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
    m
    (hNposC (2 ^ e) cls (Nat.pow_pos (Nat.succ_pos 1) : 0 < 2 ^ e))
    (mSumLeCriterionRel_of_contradictionC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      cls theta eps m afloorData badData)

theorem hmrawRel_charge_prefix_strict_thetaC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (hpos : 0 < mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)) :
    regularSeqLtProp
      (lemma33PrefixC
        (rawThetaTermRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        (N_C (2 ^ e) cls))
      (lemma33PrefixC
        (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls)
        (N_C (2 ^ e) cls)) := by
  have hprefix_pos :
      0 < lemma33PrefixNatC
        (mrawC (2 ^ e) cls
          (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData))
        (N_C (2 ^ e) cls) := by
    simpa [mSumC] using hpos
  rcases lemma33PrefixNatC_exists_pos_of_pos
      (mrawC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData))
      (N_C (2 ^ e) cls) hprefix_pos with
    ⟨j0, hj0N, hj0pos⟩
  refine lemma33PrefixC_lt_of_le_of_exists_lt
    (rawThetaTermRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
    (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls)
    (N_C (2 ^ e) cls) ?_ ?_
  · intro j hjN
    dsimp [rawThetaTermRelC]
    exact hmrawRel_charge_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m
      afloorData j hjN
  · refine ⟨j0, hj0N, ?_⟩
    dsimp [rawThetaTermRelC]
    exact hmrawRel_charge_strict_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m
      afloorData j0 hj0N hj0pos

theorem hmSumThetaRel_strict_total_of_badC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (hbad : ¬ mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) ≤ m) :
    regularSeqLtProp
      (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) := by
  have hpos : 0 < mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) :=
    nat_pos_of_not_leC hbad
  have hprefStrict :
      regularSeqLtProp
        (rawThetaPrefixRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        (lemma33PrefixC
          (chargeRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls)
          (N_C (2 ^ e) cls)) := by
    dsimp [rawThetaPrefixRelC]
    exact hmrawRel_charge_prefix_strict_thetaC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m
      afloorData hpos
  have hrawTotal :
      regularSeqLtProp
        (rawThetaPrefixRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))) :=
    regularSeqLtProp_of_lt_of_le hprefStrict
      (hchargeRel_totalC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls)
  have hbridge :=
    mSumThetaBridgeRel_of_prefixC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData
  exact regularSeqLtProp_of_left_eventual (Setoid.symm hbridge.equiv_prefix)
    hrawTotal

theorem hmSumThetaRel_lower_of_badC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))
        ≈ CReal.mul (constSeq (Nat.cast (m + 1))) theta)
    (hbad : ¬ mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) ≤ m) :
    RegularSeqLe
      (CReal.sub
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
      (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) := by
  have hsucc : m + 1 ≤ mSumC (2 ^ e) cls
      (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) :=
    nat_succ_le_of_not_leC hbad
  have hnat :
      RegularSeqLe
        (constSeq (Nat.cast (m + 1)))
        (constSeq (Nat.cast
          (mSumC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)))) :=
    natCast_leC (m + 1)
      (mSumC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)) hsucc
  have hmul :
      RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (m + 1))) theta)
        (CReal.mul
          (constSeq (Nat.cast
            (mSumC (2 ^ e) cls
              (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData))))
          theta) :=
    regularSeqLe_mul_right_of_nonnegC hnat htheta_nn
  have hmul' :
      RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (m + 1))) theta)
        (mSumThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) := by
    simpa [mSumThetaRelC] using hmul
  exact regularSeqLe_of_left_eventual htheta_budget hmul'

def mSumLeContradictionDataRel_of_bad_boundsC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))
        ≈ CReal.mul (constSeq (Nat.cast (m + 1))) theta) :
    MSumLeContradictionDataRelC
      P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData := by
  refine ⟨?_, ?_⟩
  · intro hbad
    exact hmSumThetaRel_strict_total_of_badC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls theta eps m afloorData hbad
  · intro hbad
    exact hmSumThetaRel_lower_of_badC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      cls theta eps m afloorData htheta_nn htheta_budget hbad

theorem hsum_MCRel_from_bad_boundsC {a b u v d : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta eps : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))
        ≈ CReal.mul (constSeq (Nat.cast (m + 1))) theta) :
    lemma33PrefixNatC
      (fun j => MC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
        m (j + 1))
      (N_C (2 ^ e) cls) = m := by
  exact hsum_MCRel_from_contradictionC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
    cls theta eps m afloorData
    (mSumLeContradictionDataRel_of_bad_boundsC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls theta eps m afloorData
      htheta_nn htheta_budget)

noncomputable def hp_rawRelC {a b u v d eps rho : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (CReal.max a (CReal.sub u rho)) t →
        P.embed z1 t ≈ CReal.one)
    (hz0_zero_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t (CReal.min b (CReal.add v rho)) →
        P.embed z0 t ≈ CReal.zero)
    (hsigma_rho : RegularSeqLe (sigmaScaleC d) rho)
    (cls : Nat → Bool) (theta : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (hcls_small : ∀ i : Nat, cls i = true →
      regularSeqLtProp
        (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) eps)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    P.p_prime_ltC
      (bptRC u d (sC (2 ^ e) cls j))
      (bptRC u d (sC (2 ^ e) cls (j + 1)))
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j + 1)))
        eps) := by
  cases hEnd : cls (sC (2 ^ e) cls (j + 1)) with
  | true =>
      have hsmall := hp_smallRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        hz1_one_inner hz0_zero_inner hsigma_rho cls hcls_small j hjN hEnd
      have hm := hmraw_smallC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j hjN hEnd
      have hwiden :
          RegularSeqLe eps
            (CReal.mul
              (constSeq (Nat.cast
                (mrawC (2 ^ e) cls
                  (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j + 1)))
              eps) := by
        rw [hm]
        simpa using regularSeqLe_eps_to_one_mulC eps
      exact ProfileC.p_prime_ltC_mono P hsmall hwiden
  | false =>
      exact hp_B_boundRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        hz1_one_inner hz0_zero_inner hsigma_rho cls j hjN
        (hmrawRel_upperC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
          cls theta eps m afloorData j hjN hEnd)

theorem hbound_mono_finalRelC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (heps_nn : RegularSeqNonneg eps)
    (j : Nat) :
    RegularSeqLe
      (CReal.mul
        (constSeq (Nat.cast
          (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j + 1)))
        eps)
      (CReal.mul
        (constSeq (Nat.cast
          (MC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
            m (j + 1) + 1)))
        eps) := by
  have hnat :
      mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j + 1 ≤
      MC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
            m (j + 1) + 1 := by
    exact Nat.succ_le_succ
      (hM_geC (2 ^ e) cls
        (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) m j)
  exact regularSeqLe_mul_right_of_nonnegC
    (natCast_leC
      (mrawC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData) j + 1)
      (MC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
            m (j + 1) + 1)
      hnat)
    heps_nn

noncomputable def hp_finalRelC {a b u v d eps rho : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (CReal.max a (CReal.sub u rho)) t →
        P.embed z1 t ≈ CReal.one)
    (hz0_zero_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t (CReal.min b (CReal.add v rho)) →
        P.embed z0 t ≈ CReal.zero)
    (hsigma_rho : RegularSeqLe (sigmaScaleC d) rho)
    (cls : Nat → Bool) (theta : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m)
    (hcls_small : ∀ i : Nat, cls i = true →
      regularSeqLtProp
        (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i) eps)
    (heps_nn : RegularSeqNonneg eps)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    P.p_prime_ltC
      (bptRC u d (sC (2 ^ e) cls j))
      (bptRC u d (sC (2 ^ e) cls (j + 1)))
      (CReal.mul
        (constSeq (Nat.cast
          (MC (2 ^ e) cls
            (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
            m (j + 1) + 1)))
        eps) :=
  ProfileC.p_prime_ltC_mono P
    (hp_rawRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_inner hz0_zero_inner hsigma_rho cls theta m afloorData hcls_small j hjN)
    (hbound_mono_finalRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      cls theta m afloorData heps_nn j)

theorem lemma33RetainedWidthRelC {a b u v d delta small : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (cls : Nat → Bool) (theta : CReal) (m : Nat)
    (hcls_big : ∀ i : Nat, cls i = false →
      regularSeqLtProp theta
        (alphaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F i))
    (htheta_nn : RegularSeqNonneg theta)
    (htheta_budget :
      CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1))
        ≈ CReal.mul (constSeq (Nat.cast (m + 1))) theta)
    (hd_small_le : RegularSeqLe d small)
    (hsmall_nn : RegularSeqNonneg small)
    (hLsmall : RegularSeqLe
      (CReal.mul (constSeq (Nat.cast (2 * (m + 1)))) small) delta)
    (j : Nat) (hjN : j < N_C (2 ^ e) cls) :
    RegularSeqLe
      (CReal.sub (bptRC u d (sC (2 ^ e) cls (j + 1)))
        (bptRC u d (sC (2 ^ e) cls j)))
      delta := by
  let K : Nat := 2 ^ e
  let L : Nat := 2 * (m + 1)
  let k : Nat := sC K cls j
  let i : Nat := sC K cls (j + 1)
  have hki : k < i := by
    simpa [K, k, i] using hs_strictC K cls j hjN
  have hiK : i ≤ K := by
    simpa [K, i] using hs_endpoint_le_KC K cls j
  have hdist : CReal.sub (bptRC u d i) (bptRC u d k) ≈
      CReal.mul (constSeq (Nat.cast (i - k))) d :=
    bptRC_sub_generalC u d (Nat.le_of_lt hki)
  by_cases hshort : i - k ≤ L
  · have hcast : RegularSeqLe (constSeq (Nat.cast (i - k))) (constSeq (Nat.cast L)) :=
      natCast_leC (i - k) L hshort
    have h1 : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (i - k))) d)
        (CReal.mul (constSeq (Nat.cast (i - k))) small) :=
      regularSeqLe_mul_left_of_nonnegC hd_small_le (natCast_nonnegC (i - k))
    have h2 : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (i - k))) small)
        (CReal.mul (constSeq (Nat.cast L)) small) :=
      regularSeqLe_mul_right_of_nonnegC hcast hsmall_nn
    have h3 : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (i - k))) d) delta :=
      regularSeqLe_trans (regularSeqLe_trans h1 h2) (by simpa [L] using hLsmall)
    exact regularSeqLe_of_left_eventual (by simpa [K, k, i] using hdist) h3
  · have hlong : L < i - k := Nat.lt_of_not_ge hshort
    have hBigEnd : cls i = false := by
      cases hci : cls i with
      | false => rfl
      | true =>
          have hprev := hs_prev_of_smallC K cls j hjN hci
          exfalso
          dsimp [L, k, i] at hlong hprev
          omega
    let ell : Nat := i - k
    have hellPos : 0 < ell := by dsimp [ell]; omega
    have hAllBig : ∀ r : Nat, r < ell → cls (k + r + 1) = false := by
      intro r hr
      exact hs_all_bigC K cls j (k + r + 1) hjN hBigEnd (by omega) (by
        dsimp [ell] at hr
        omega)
    have hAllTheta : ∀ r : Nat, r < ell →
        regularSeqLtProp theta
          (CReal.sub
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r))
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r + 2))) := by
      intro r hr
      have hraw := hcls_big (k + r + 1) (hAllBig r hr)
      have hsub : k + r + 1 - 1 = k + r := by omega
      have hadd : k + r + 1 + 1 = k + r + 2 := by omega
      simpa [alphaRelC, hsub, hadd] using hraw
    have hlower : regularSeqLtProp
        (CReal.mul (constSeq (Nat.cast ell)) theta)
        (lemma33PrefixC
          (fun r => CReal.sub
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r))
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r + 2))) ell) :=
      lemma33Prefix_const_ltC theta
        (fun r => CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r))
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r + 2))) ell
        hellPos hAllTheta
    have hLell : RegularSeqLe (constSeq (Nat.cast L)) (constSeq (Nat.cast ell)) :=
      natCast_leC L ell (Nat.le_of_lt hlong)
    have hscale : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast L)) theta)
        (CReal.mul (constSeq (Nat.cast ell)) theta) :=
      regularSeqLe_mul_right_of_nonnegC hLell htheta_nn
    have hLtheta_lt : regularSeqLtProp
        (CReal.mul (constSeq (Nat.cast L)) theta)
        (lemma33PrefixC
          (fun r => CReal.sub
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r))
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r + 2))) ell) :=
      regularSeqLtProp_of_le_of_lt hscale hlower
    let total : CReal := CReal.sub
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
      (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (K + 1))
    have hbudgetK : total ≈ CReal.mul (constSeq (Nat.cast (m + 1))) theta := by
      dsimp [total, K]
      exact htheta_budget
    have hdouble : CReal.mul (constSeq (Nat.cast L)) theta ≈ CReal.add total total := by
      dsimp [L]
      exact lemma33DoubleThetaBudgetC total theta m hbudgetK
    have htwo_lower : regularSeqLtProp (CReal.add total total)
        (lemma33PrefixC
          (fun r => CReal.sub
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r))
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r + 2))) ell) :=
      regularSeqLtProp_of_left_eventual (Setoid.symm hdouble) hLtheta_lt
    have hk_le : k ≤ K + 1 := by
      have hkK := hs_le_KC K cls j
      dsimp [k]
      omega
    have hkell_eq : k + ell = i := by dsimp [ell]; omega
    have hkell_le : k + ell ≤ K + 1 := by
      rw [hkell_eq]
      omega
    have hk1_le : k + 1 ≤ K + 1 := by
      have hkK := hs_le_KC K cls j
      dsimp [k]
      omega
    have hkell1_le : k + ell + 1 ≤ K + 1 := by
      rw [hkell_eq]
      omega
    have hupper : RegularSeqLe
        (lemma33PrefixC
          (fun r => CReal.sub
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r))
            (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (k + r + 2))) ell)
        (CReal.add total total) := by
      have hraw := lemma33AlphaPrefix_le_twoDiameterC
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
        (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (K + 1))
        K k ell
        (fun r hr =>
          hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
            hz1_one_from_u hz0_zero_to_v hz0_le_z1
            0 r (Nat.zero_le r) (by simpa [K] using hr))
        (fun r hr =>
          hlamRelC_anti P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
            hz1_one_from_u hz0_zero_to_v hz0_le_z1
            r (K + 1) (by simpa [K] using hr) (Nat.le_refl _))
        hk_le hkell_le hk1_le hkell1_le
      simpa [total, K] using hraw
    have hbad : regularSeqLtProp (CReal.add total total) (CReal.add total total) :=
      regularSeqLtProp_of_lt_of_le htwo_lower hupper
    exact False.elim (regularSeqLtProp_irrefl (CReal.add total total) hbad)

noncomputable def lemma33PtsRelC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    Nat → CReal :=
  fun j => bptRC u d (sC (2 ^ e) cls j)

noncomputable def lemma33MCWeightRelC {a b u v d eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (cls : Nat → Bool) (theta : CReal) (m : Nat)
    (afloorData : (j : Nat) → j < N_C (2 ^ e) cls →
      Lemma33H4ApproxFloorC theta eps
        (betaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls j) m) :
    Nat → Nat :=
  fun j => MC (2 ^ e) cls
    (afloorRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta eps m afloorData)
    m (j + 1)

/-- Relative Lemma 3.3 result once the dyadic mesh is known small enough. -/
noncomputable def lemma33SubResultDataRelC_construct {a b u v d eps delta small rho : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (hu : RegularSeqLe a u) (hv : RegularSeqLe v b)
    (hd_nn : RegularSeqNonneg d) (hd_pos : regularSeqLtData zeroSeq d)
    (e : Nat) (hdeq : d ≈ CReal.mul (CReal.sub v u) (halfPow e))
    (z1 z0 : P.Code) (hz1F : z1 ∈ P.F) (hz0F : z0 ∈ P.F)
    (hz1_one_from_u : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe u t → P.embed z1 t ≈ CReal.one)
    (hz0_zero_to_v : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t v → P.embed z0 t ≈ CReal.zero)
    (hz0_le_z1 : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (P.embed z0 t) (P.embed z1 t))
    (hz1_one_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe (CReal.max a (CReal.sub u rho)) t →
        P.embed z1 t ≈ CReal.one)
    (hz0_zero_inner : ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      RegularSeqLe t (CReal.min b (CReal.add v rho)) →
        P.embed z0 t ≈ CReal.zero)
    (hsigma_rho : RegularSeqLe (sigmaScaleC d) rho)
    (m : Nat) (heps_nn : RegularSeqNonneg eps)
    (hD_eps :
      regularSeqLtProp
        (CReal.sub
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F 0)
          (lamRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F (2 ^ e + 1)))
        (CReal.mul (constSeq (Nat.cast (m + 1))) eps))
    (hd_small_le : RegularSeqLe d small)
    (hsmall_nn : RegularSeqNonneg small)
    (hLsmall : RegularSeqLe
      (CReal.mul (constSeq (Nat.cast (2 * (m + 1)))) small) delta) :
    Lemma33SubResultDataC (eps := eps) (delta := delta) P u v m := by
  let theta := lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m
  let cls := lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps
  let afloorData :=
    lemma33ApproxFloorDataRelC_construct P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1 cls theta m
      (lemma33ThetaRel_lt_epsC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
      hD_eps
  refine
    { N := N_C (2 ^ e) cls
      N_pos := ?_
      pts := lemma33PtsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta m afloorData
      pts_zero := ?_
      pts_N := ?_
      pts_strict_data := ?_
      width_le := ?_
      M := lemma33MCWeightRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F cls theta m afloorData
      sum_M := ?_
      p_prime_cond := ?_ }
  · exact hNposC (2 ^ e) cls
      (Nat.pow_pos (Nat.succ_pos 1) : 0 < 2 ^ e)
  · dsimp [lemma33PtsRelC, cls, theta, afloorData]
    rw [hs_zeroC]
    exact Setoid.trans (bptRC_equiv_bptC u d 0) (bptC_zeroC u d)
  · dsimp [lemma33PtsRelC, cls, theta, afloorData]
    rw [hs_NC]
    exact Setoid.trans (bptRC_equiv_bptC u d (2 ^ e)) (bptC_KC e hdeq)
  · intro j hjN
    dsimp [lemma33PtsRelC, cls, theta, afloorData]
    have hki := hs_strictC (2 ^ e)
      (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps) j hjN
    have hltC : regularSeqLtProp
        (bptC u d (sC (2 ^ e)
          (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps) j))
        (bptC u d (sC (2 ^ e)
          (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps) (j + 1))) :=
      bptC_ltC hd_pos.toProp hki
    have hltR : regularSeqLtProp
        (bptRC u d (sC (2 ^ e)
          (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps) j))
        (bptRC u d (sC (2 ^ e)
          (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps) (j + 1))) :=
      regularSeqLtProp_of_left_eventual
        (bptRC_equiv_bptC u d (sC (2 ^ e)
          (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps) j))
        (regularSeqLtProp_of_right_eventual
          (Setoid.symm (bptRC_equiv_bptC u d (sC (2 ^ e)
            (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps) (j + 1)))) hltC)
    exact regularSeqLtData_of_ltPropC hltR
  · intro j hjN
    dsimp [lemma33PtsRelC, cls, theta, afloorData]
    exact lemma33RetainedWidthRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1
      (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
      (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) m
      (lemma33ClsRel_bigC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
      (lemma33ThetaRel_nonnegC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F hz0_le_z1 m)
      (lemma33ThetaRel_budgetC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m)
      hd_small_le hsmall_nn hLsmall j hjN
  · dsimp [lemma33MCWeightRelC, cls, theta, afloorData]
    exact hsum_MCRel_from_bad_boundsC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_from_u hz0_zero_to_v hz0_le_z1
      (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
      (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) eps m
      (lemma33ApproxFloorDataRelC_construct P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        hz1_one_from_u hz0_zero_to_v hz0_le_z1
        (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
        (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) m
        (lemma33ThetaRel_lt_epsC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
        hD_eps)
      (lemma33ThetaRel_nonnegC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F hz0_le_z1 m)
      (lemma33ThetaRel_budgetC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m)
  · intro j hjN
    dsimp [lemma33PtsRelC, lemma33MCWeightRelC, cls, theta, afloorData]
    exact hp_finalRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
      hz1_one_inner hz0_zero_inner hsigma_rho
      (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
      (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) m
      (lemma33ApproxFloorDataRelC_construct P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F
        hz1_one_from_u hz0_zero_to_v hz0_le_z1
        (lemma33ClsRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
        (lemma33ThetaRelC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m) m
        (lemma33ThetaRel_lt_epsC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
        hD_eps)
      (lemma33ClsRel_smallC P hu hv hd_nn hd_pos e hdeq z1 z0 hz1F hz0F m hD_eps)
      heps_nn j hjN

/-- The sigma scale is bounded by the original mesh. -/
theorem sigmaScaleC_le_selfC {d : CReal}
    (hd_pos : regularSeqLtData zeroSeq d) :
    RegularSeqLe (sigmaScaleC d) d := by
  have hsig_pos : regularSeqLtProp CReal.zero (sigmaScaleC d) :=
    sigmaScaleC_pos_prop hd_pos
  have hsig_lt_twice : regularSeqLtProp (sigmaScaleC d)
      (CReal.add (sigmaScaleC d) (sigmaScaleC d)) :=
    regularSeqLtProp_self_add_sigmaC (sigmaScaleC d) hsig_pos
  have htwice_lt : regularSeqLtProp
      (CReal.add (sigmaScaleC d) (sigmaScaleC d)) d :=
    sigmaScaleC_two_lt_d_prop hd_pos
  exact regularSeqLe_of_ltPropC
    (regularSeqLtProp_trans (sigmaScaleC d)
      (CReal.add (sigmaScaleC d) (sigmaScaleC d)) d
      hsig_lt_twice htwice_lt)

/-- Numerical smallness budget for the relative Lemma 3.3 block route. -/
theorem lemma33Rel_Lsmall0C (delta : CReal) (m : Nat)
    (hdelta_nn : RegularSeqNonneg delta) :
    RegularSeqLe
      (CReal.mul (constSeq (Nat.cast (2 * (m + 1))))
        (CReal.mul (halfPow (m + 2)) delta)) delta := by
  let L : Nat := 2 * (m + 1)
  let T : Nat := 2 ^ (m + 2)
  have hnat : L ≤ T := by
    dsimp [L, T]
    exact BishopC.lemma33H4_two_mul_succ_le_two_pow m
  have hcast : RegularSeqLe (constSeq (Nat.cast L)) (constSeq (Nat.cast T)) :=
    natCast_leC L T hnat
  have hhp_nn : RegularSeqNonneg (halfPow (m + 2)) :=
    regularSeqNonneg_of_zero_le
      (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_halfPow (m + 2)))
  have hsmall0_nn :
      RegularSeqNonneg (CReal.mul (halfPow (m + 2)) delta) :=
    CReal.mul_nonneg_E hhp_nn hdelta_nn
  have hmul : RegularSeqLe
      (CReal.mul (constSeq (Nat.cast L))
        (CReal.mul (halfPow (m + 2)) delta))
      (CReal.mul (constSeq (Nat.cast T))
        (CReal.mul (halfPow (m + 2)) delta)) :=
    regularSeqLe_mul_right_of_nonnegC hcast hsmall0_nn
  have hscalar : (Nat.cast T : Scalar) * eps (m + 2) = 1 := by
    dsimp [T]
    rw [mul_comm]
    exact eps_mul_natCast_twoPow (m + 2)
  have hunit :
      CReal.mul (constSeq (Nat.cast T)) (halfPow (m + 2)) ≈ CReal.one := by
    calc
      CReal.mul (constSeq (Nat.cast T)) (halfPow (m + 2))
          = CReal.mul (constSeq (Nat.cast T)) (constSeq (eps (m + 2))) := rfl
      _ ≈ constSeq ((Nat.cast T : Scalar) * eps (m + 2)) :=
        constSeq_mulC (Nat.cast T) (eps (m + 2))
      _ = CReal.one := by
        rw [hscalar]
        rfl
  have hright : CReal.mul (constSeq (Nat.cast T))
        (CReal.mul (halfPow (m + 2)) delta) ≈ delta := by
    calc
      CReal.mul (constSeq (Nat.cast T)) (CReal.mul (halfPow (m + 2)) delta)
          ≈ CReal.mul
              (CReal.mul (constSeq (Nat.cast T)) (halfPow (m + 2))) delta :=
        Setoid.symm
          (CReal.mul_assoc (constSeq (Nat.cast T)) (halfPow (m + 2)) delta)
      _ ≈ CReal.mul CReal.one delta :=
        CReal.mul_respects_equiv
          (CReal.mul (constSeq (Nat.cast T)) (halfPow (m + 2))) CReal.one
          delta delta hunit (Setoid.refl delta)
      _ ≈ delta := CReal.one_mul delta
  exact regularSeqLe_of_right_eventual hright hmul

/-- Convert DATA `0 < x` to DATA positivity of the representative `x`. -/
def regularSeqLtData_zero_to_posEventuallyC {x : RegularSeq}
    (h : regularSeqLtData zeroSeq x) : PosEventuallyData x :=
  posEventuallyData_of_strongGaugeC
    (strongGaugeC
      (posEventually_to_strongC
        (posEventually_respects (subSeq x zeroSeq) x
          (subSeq_zero_right_eventually x) h.toProp)))

/-- Construct the retained-block Lemma 3.3 DATA required by the block tower. -/
noncomputable def lemma34BlockSubDataC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    {P : ProfileC a b hab} {n k : Nat}
    (S : Lemma34BlockTowerStateC (eps := eps) (P := P) n k)
    (B : Lemma34BlockC (eps := eps) P k) :
    Lemma34BlockSubResultDataC (eps := eps) P k B := by
  let delta : CReal := lemma34WidthScaleC a b (k + 1)
  refine
    { delta := delta
      result := ?_
      delta_le_width := ?_ }
  · rcases B.budget with ⟨rho, hrho, hp⟩
    let small0 : CReal := CReal.mul (halfPow (B.mult + 2)) delta
    let small : CReal := CReal.min small0 rho
    have hdelta_pos : regularSeqLtData zeroSeq delta := by
      dsimp [delta, lemma34WidthScaleC]
      exact CReal.mul_pos_EDC
        (sub_pos_dataC (regularSeqLtData_of_ltPropC hab))
        (regularSeqLtData_zero_halfPowC (k + 1))
    have hdelta_nn : RegularSeqNonneg delta :=
      regularSeqNonneg_of_zero_le (regularSeqLe_zero_of_ltData hdelta_pos)
    have hsmall0_pos : regularSeqLtData zeroSeq small0 := by
      dsimp [small0]
      exact CReal.mul_pos_EDC
        (regularSeqLtData_zero_halfPowC (B.mult + 2)) hdelta_pos
    have hsmall0_pos_prop : regularSeqLtProp zeroSeq small0 :=
      regularSeqLtProp_zero_of_posEventuallyData
        (regularSeqLtData_zero_to_posEventuallyC hsmall0_pos)
    have hsmall_pos : regularSeqLtProp zeroSeq small :=
      min_posC hsmall0_pos_prop hrho
    have hsmall_data : regularSeqLtData zeroSeq small :=
      regularSeqLtData_of_ltPropC hsmall_pos
    have hsmall_nn : RegularSeqNonneg small :=
      regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC hsmall_pos)
    let hsmall_pos_data : PosEventuallyData small :=
      regularSeqLtData_zero_to_posEventuallyC hsmall_data
    let arch := regularSeqArchimedeanPositiveData hsmall_pos_data
    let e : Nat := arch.1 + CReal.mulArchBound (CReal.sub B.right B.left)
    let d : CReal := lemma34WidthScaleC B.left B.right e
    have hdyadic_lt_small : regularSeqLtProp (halfPow arch.1) small := by
      have hlt : regularSeqLtProp (constSeq (BishopCReal.eps arch.1)) small := by
        first
        | exact regularSeqLtData_to_prop _ _ arch.2
        | exact regularSeqLtData_to_prop arch.2
      first
      | simpa [halfPow] using hlt
      | exact hlt
    have hbase :
        RegularSeqLe
          (CReal.mul (halfPow e) (CReal.sub B.right B.left))
          (halfPow arch.1) := by
      simpa [e] using
        halfPow_mul_archBound_le (CReal.sub B.right B.left) arch.1
    have hcomm :
        relEventually
          (CReal.mul (CReal.sub B.right B.left) (halfPow e))
          (CReal.mul (halfPow e) (CReal.sub B.right B.left)) :=
      CReal.mul_comm (CReal.sub B.right B.left) (halfPow e)
    have hle_width :
        RegularSeqLe
          (CReal.mul (CReal.sub B.right B.left) (halfPow e))
          (halfPow arch.1) :=
      regularSeqLe_of_left_eventual hcomm hbase
    have hd_lt_small : regularSeqLtProp d small := by
      dsimp [d, lemma34WidthScaleC]
      exact regularSeqLtProp_of_le_of_lt hle_width hdyadic_lt_small
    have hd_small_le : RegularSeqLe d small :=
      regularSeqLe_of_ltPropC hd_lt_small
    have hd_pos : regularSeqLtData zeroSeq d := by
      dsimp [d, lemma34WidthScaleC]
      exact CReal.mul_pos_EDC
        (sub_pos_dataC (regularSeqLtData_of_ltPropC B.proper))
        (regularSeqLtData_zero_halfPowC e)
    have hd_nn : RegularSeqNonneg d :=
      regularSeqNonneg_of_zero_le (regularSeqLe_zero_of_ltData hd_pos)
    have hdeq :
        d ≈ CReal.mul (CReal.sub B.right B.left) (halfPow e) := by
      rfl
    have hrho_nn : RegularSeqNonneg rho :=
      regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC hrho)
    have hsub_left : RegularSeqLe (CReal.sub B.left rho) B.left :=
      regularSeqLe_sub_right_self_of_nonneg B.left rho
        (regularSeqLe_zero_of_nonneg hrho_nn)
    have hmax_left : RegularSeqLe
        (CReal.max a (CReal.sub B.left rho)) B.left :=
      CReal.max_leC B.left_bound hsub_left
    have hright_le_rho : RegularSeqLe B.right (CReal.add B.right rho) := by
      have hraw : RegularSeqLe
          (CReal.add B.right CReal.zero) (CReal.add B.right rho) :=
        regularSeqLe_add (regularSeqLe_refl B.right)
          (regularSeqLe_of_ltPropC hrho)
      exact regularSeqLe_of_left_eventual
        (Setoid.symm (CReal.add_zero B.right)) hraw
    have hz1_one_from_u :
        ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
          RegularSeqLe B.left t → P.embed hp.f2 t ≈ CReal.one := by
      intro t hat htb hBt
      exact hp.cond2 t hat htb (regularSeqLe_trans hmax_left hBt)
    have hz0_zero_to_v :
        ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
          RegularSeqLe t B.right → P.embed hp.f1 t ≈ CReal.zero := by
      intro t hat htb htB
      exact hp.cond1 t hat htb
        (CReal.le_minC htb (regularSeqLe_trans htB hright_le_rho))
    have hz0_le_z1 :
        ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
          RegularSeqLe (P.embed hp.f1 t) (P.embed hp.f2 t) := by
      intro t hat htb
      rcases regularSeqLtProp_cotrans B.left B.right t B.proper with hLt | htR
      · have h1 : P.embed hp.f2 t ≈ CReal.one :=
          hz1_one_from_u t hat htb (regularSeqLe_of_ltPropC hLt)
        have hz0_le_one : RegularSeqLe (P.embed hp.f1 t) CReal.one :=
          (P.bound hp.f1 hp.f1_mem t hat htb).2
        exact regularSeqLe_of_right_eventual (Setoid.symm h1) hz0_le_one
      · have h0 : P.embed hp.f1 t ≈ CReal.zero :=
          hz0_zero_to_v t hat htb (regularSeqLe_of_ltPropC htR)
        have hzero_le_z1 : RegularSeqLe CReal.zero (P.embed hp.f2 t) :=
          regularSeqLe_zero_of_nonneg
            ((P.bound hp.f2 hp.f2_mem t hat htb).1)
        exact regularSeqLe_of_left_eventual h0 hzero_le_z1
    have hsigma_rho : RegularSeqLe (sigmaScaleC d) rho :=
      regularSeqLe_trans (sigmaScaleC_le_selfC hd_pos)
        (regularSeqLe_trans hd_small_le (CReal.min_le_rightC small0 rho))
    have hsmall_le_small0 : RegularSeqLe small small0 :=
      CReal.min_le_leftC small0 rho
    have hcoeff_nn :
        RegularSeqNonneg (constSeq (Nat.cast (2 * (B.mult + 1)))) :=
      natCast_nonnegC (2 * (B.mult + 1))
    have hmul_small : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (2 * (B.mult + 1)))) small)
        (CReal.mul (constSeq (Nat.cast (2 * (B.mult + 1)))) small0) :=
      regularSeqLe_mul_left_of_nonnegC hsmall_le_small0 hcoeff_nn
    have hLsmall : RegularSeqLe
        (CReal.mul (constSeq (Nat.cast (2 * (B.mult + 1)))) small) delta :=
      regularSeqLe_trans hmul_small
        (lemma33Rel_Lsmall0C delta B.mult hdelta_nn)
    have heps_nn : RegularSeqNonneg eps :=
      regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC S.eps_pos)
    have hD_eps :
        regularSeqLtProp
          (CReal.sub
            (lamRelC P B.left_bound B.right_bound hd_nn hd_pos e hdeq
              hp.f2 hp.f1 hp.f2_mem hp.f1_mem 0)
            (lamRelC P B.left_bound B.right_bound hd_nn hd_pos e hdeq
              hp.f2 hp.f1 hp.f2_mem hp.f1_mem (2 ^ e + 1)))
          (CReal.mul (constSeq (Nat.cast (B.mult + 1))) eps) :=
      regularSeqLtProp_of_left_eventual
        (lemma33RelLamTotal_equiv_gapC P B.left_bound B.right_bound
          hd_nn hd_pos e hdeq hp.f2 hp.f1 hp.f2_mem hp.f1_mem)
        hp.gap
    exact
      lemma33SubResultDataRelC_construct P B.left_bound B.right_bound
        hd_nn hd_pos e hdeq hp.f2 hp.f1 hp.f2_mem hp.f1_mem
        hz1_one_from_u hz0_zero_to_v hz0_le_z1
        hp.cond2 hp.cond1 hsigma_rho B.mult heps_nn hD_eps
        hd_small_le hsmall_nn hLsmall
  · exact regularSeqLe_refl delta

/-- Source-faithful retained-block subresult provider. -/
noncomputable def lemma34BlockTowerSubDataProviderC_construct :
    Lemma34BlockTowerSubDataProviderC where
  subData := by
    intro a b eps hab P n k S B
    exact lemma34BlockSubDataC_construct S B

/-- Frontier-free CReal-native DATA Lemma 3.4 via the block-tower route. -/
noncomputable def lemma34ResultDataC_construct {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma34ResultDataC_of_blockTowerSubDataProviderC
    lemma34BlockTowerSubDataProviderC_construct P heps n hn h_cond

/-- The DATA form of Lemma 3.4. -/
noncomputable def lemma_3_4DataC {a b eps : CReal}
    {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab)
    (heps : regularSeqLtProp zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      regularSeqLtProp
        (CReal.sub (P.lambda P.oneCode) (P.lambda P.zeroCode))
        (CReal.mul (constSeq (Nat.cast (n + 1))) eps)) :
    Lemma34ResultDataC (eps := eps) P n :=
  lemma34ResultDataC_construct P heps n hn h_cond


/-! ### §3 Theorem 3.5 CReal-native smooth-a.e.

CReal/DATA mirror of abstract `BishopSec3_Profile.lean` theorem 3.5.
This block consumes the completed `lemma_3_4DataC` level-by-level, flattens
the finite exceptional families into one choice-free sequence, constructs
`lambdaBar` by CReal representative completeness, and performs the final
epsilon-delta squeeze. -/

/-- CReal-native Theorem 3.5: endpoint gap is nonnegative. -/
theorem lemma35Gap_nonnegC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) :
    RegularSeqNonneg (lemma33DiameterC P) :=
  lemma33ProfileDiameter_nonnegC P

/-- A dyadic Archimedean exponent for the endpoint gap. -/
noncomputable def lemma35ArchExponentC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) : Nat :=
  CReal.mulArchBound (lemma33DiameterC P)

/-- Dyadic powers are nonnegative. -/
theorem twoPow_nonnegC (n : Nat) : RegularSeqNonneg (twoPow n) := by
  induction n with
  | zero =>
      exact regularSeqNonneg_of_zero_le CReal.zero_le_oneC
  | succ n ih =>
      simpa [twoPow] using regularSeqNonneg_add ih ih

/-- `twoPow n` is the constant natural power `2^n`. -/
theorem twoPow_natCastC (n : Nat) :
    twoPow n ≈ constSeq (Nat.cast (2 ^ n) : Scalar) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
        rw [pow_succ]
        omega
      calc
        twoPow (n + 1)
            = CReal.add (twoPow n) (twoPow n) := rfl
        _ ≈ CReal.add (constSeq (Nat.cast (2 ^ n) : Scalar))
              (constSeq (Nat.cast (2 ^ n) : Scalar)) :=
            CReal.add_respects_equiv _ _ _ _ ih ih
        _ ≈ constSeq (Nat.cast (2 ^ n + 2 ^ n) : Scalar) :=
            Setoid.symm (constSeq_natCast_addC (2 ^ n) (2 ^ n))
        _ = constSeq (Nat.cast (2 ^ (n + 1)) : Scalar) := by
            rw [hpow]

/-- The endpoint gap is weakly bounded by the selected dyadic integer. -/
theorem lemma35Gap_le_twoPowC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) :
    RegularSeqLe (lemma33DiameterC P) (twoPow (lemma35ArchExponentC P)) := by
  let D : CReal := lemma33DiameterC P
  let M : Nat := lemma35ArchExponentC P
  have harch : RegularSeqLe (CReal.mul (halfPow (0 + CReal.mulArchBound D)) D) (halfPow 0) :=
    halfPow_mul_archBound_le D 0
  have harch1 : RegularSeqLe (CReal.mul (halfPow M) D) CReal.one := by
    have hM : 0 + CReal.mulArchBound D = M := by
      simp [M, lemma35ArchExponentC, D]
    simpa [hM] using regularSeqLe_of_right_eventual halfPow_zero harch
  have hmul : RegularSeqLe
      (CReal.mul (CReal.mul (halfPow M) D) (twoPow M))
      (CReal.mul CReal.one (twoPow M)) :=
    regularSeqLe_mul_right_of_nonnegC harch1 (twoPow_nonnegC M)
  have hcancel : CReal.mul (halfPow M) (twoPow M) ≈ CReal.one :=
    Setoid.trans (CReal.mul_comm (halfPow M) (twoPow M))
      (twoPow_mul_halfPow M)
  have hleft : CReal.mul (CReal.mul (halfPow M) D) (twoPow M) ≈ D := by
    calc
      CReal.mul (CReal.mul (halfPow M) D) (twoPow M)
          ≈ CReal.mul (halfPow M) (CReal.mul D (twoPow M)) :=
            CReal.mul_assoc (halfPow M) D (twoPow M)
      _ ≈ CReal.mul (halfPow M) (CReal.mul (twoPow M) D) :=
            CReal.mul_respects_equiv _ _ _ _ (Setoid.refl (halfPow M))
              (CReal.mul_comm D (twoPow M))
      _ ≈ CReal.mul (CReal.mul (halfPow M) (twoPow M)) D :=
            Setoid.symm (CReal.mul_assoc (halfPow M) (twoPow M) D)
      _ ≈ CReal.mul CReal.one D :=
            CReal.mul_respects_equiv _ _ _ _ hcancel (Setoid.refl D)
      _ ≈ D := CReal.one_mul D
  have hright : CReal.mul CReal.one (twoPow M) ≈ twoPow M :=
    CReal.one_mul (twoPow M)
  have hD : RegularSeqLe D (twoPow M) :=
    (CReal.le_respects_equiv hleft hright).1 hmul
  simpa [D, M, lemma35ArchExponentC] using hD

/-- Number of exceptional points used at accuracy `halfPow k`. -/
noncomputable def lemma35CountC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat) : Nat :=
  2 ^ lemma35ArchExponentC P * 2 ^ k

/-- Every level has at least one exceptional point. -/
theorem lemma35Count_posC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat) : 0 < lemma35CountC P k := by
  unfold lemma35CountC
  exact Nat.mul_pos
    (Nat.pow_pos (by omega : 0 < 2) : 0 < 2 ^ lemma35ArchExponentC P)
    (Nat.pow_pos (by omega : 0 < 2) : 0 < 2 ^ k)

/-- Main dyadic budget identity for the level count. -/
theorem lemma35Count_mul_halfPowC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat) :
    CReal.mul (constSeq (Nat.cast (lemma35CountC P k) : Scalar)) (halfPow k)
      ≈ twoPow (lemma35ArchExponentC P) := by
  let M : Nat := lemma35ArchExponentC P
  have hscalar :
      (Nat.cast (2 ^ M * 2 ^ k) : Scalar) * eps k =
        (Nat.cast (2 ^ M) : Scalar) := by
    have hcancel : (Nat.cast (2 ^ k) : Scalar) * eps k = 1 := by
      rw [mul_comm]
      exact eps_mul_natCast_twoPow k
    rw [Nat.cast_mul]
    calc
      (Nat.cast (2 ^ M) : Scalar) * Nat.cast (2 ^ k) * eps k
          = (Nat.cast (2 ^ M) : Scalar) * (Nat.cast (2 ^ k) * eps k) := by ring
      _ = (Nat.cast (2 ^ M) : Scalar) * 1 := by rw [hcancel]
      _ = (Nat.cast (2 ^ M) : Scalar) := by ring
  calc
    CReal.mul (constSeq (Nat.cast (lemma35CountC P k) : Scalar)) (halfPow k)
        = CReal.mul (constSeq (Nat.cast (2 ^ M * 2 ^ k) : Scalar)) (constSeq (eps k)) := by
          simp [lemma35CountC, M, halfPow, CReal.epsSeq]
    _ ≈ constSeq ((Nat.cast (2 ^ M * 2 ^ k) : Scalar) * eps k) :=
        constSeq_mulC _ _
    _ = constSeq (Nat.cast (2 ^ M) : Scalar) := by
        rw [hscalar]
    _ ≈ twoPow M := Setoid.symm (twoPow_natCastC M)

/-- Budget required to apply Lemma 3.4 at every dyadic level. -/
theorem lemma35BudgetC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat) :
    regularSeqLtProp (lemma33DiameterC P)
      (CReal.mul (constSeq (Nat.cast (lemma35CountC P k + 1) : Scalar)) (halfPow k)) := by
  have hbase : RegularSeqLe (lemma33DiameterC P) (twoPow (lemma35ArchExponentC P)) :=
    lemma35Gap_le_twoPowC P
  have hcast : regularSeqLtProp
      (constSeq (Nat.cast (lemma35CountC P k) : Scalar))
      (constSeq (Nat.cast (lemma35CountC P k + 1) : Scalar)) :=
    natCast_ltC (lemma35CountC P k) (lemma35CountC P k + 1) (by omega)
  have hscaled : regularSeqLtProp
      (CReal.mul (constSeq (Nat.cast (lemma35CountC P k) : Scalar)) (halfPow k))
      (CReal.mul (constSeq (Nat.cast (lemma35CountC P k + 1) : Scalar)) (halfPow k)) :=
    regularSeqLtProp_mul_right_of_posC hcast (regularSeqLtProp_zero_halfPow k)
  have hscaled' : regularSeqLtProp (twoPow (lemma35ArchExponentC P))
      (CReal.mul (constSeq (Nat.cast (lemma35CountC P k + 1) : Scalar)) (halfPow k)) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (lemma35Count_mul_halfPowC P k)) hscaled
  exact regularSeqLtProp_of_le_of_lt hbase hscaled'

/-- The local small-jump package supplied by Lemma 3.4 at one level. -/
structure Lemma35LocalSmallC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat)
    (points : Fin (lemma35CountC P k) → CReal) (beta : CReal) where
  gamma : CReal
  gamma_pos : regularSeqLtProp CReal.zero gamma
  local_bound : ∀ t : CReal,
    RegularSeqLe a t →
      RegularSeqLe t b →
        (∀ i : Fin (lemma35CountC P k),
          regularSeqLtProp beta
            (CReal.abs (CReal.sub t (points i)))) →
          P.p_ltC
            (CReal.max a (CReal.sub t gamma))
            (CReal.min b (CReal.add t gamma))
            (halfPow k)

/-- All data supplied by Lemma 3.4 at dyadic level `k`. -/
structure Lemma35LevelDataC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat) where
  points : Fin (lemma35CountC P k) → CReal
  bounds : ∀ i, RegularSeqLe a (points i) ∧ RegularSeqLe (points i) b
  local_small :
    ∀ beta : CReal, regularSeqLtProp CReal.zero beta →
      Lemma35LocalSmallC P k points beta

/-- Canonical CReal-native level data, obtained from Lemma 3.4 DATA. -/
noncomputable def lemma35LevelDataC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (k : Nat) : Lemma35LevelDataC P k :=
  let D := lemma_3_4DataC P
    (regularSeqLtProp_zero_halfPow k)
    (lemma35CountC P k)
    (lemma35Count_posC P k)
    (by
      simpa [lemma33DiameterC] using lemma35BudgetC P k)
  { points := D.t
    bounds := D.t_bounds
    local_small := by
      intro beta hbeta
      let L := D.local_data beta
        (regularSeqLtData_zero_to_posEventuallyC
          (regularSeqLtData_of_ltPropC hbeta))
      exact
        { gamma := L.gamma
          gamma_pos := L.gamma_pos
          local_bound := L.local_bound } }

/-- Triangular block size: total slots in Cantor diagonals `d0 .. d0+m-1`. -/
def lemma35BlockSumC : Nat → Nat → Nat
  | _, 0 => 0
  | d0, (m + 1) => (d0 + 1) + lemma35BlockSumC (d0 + 1) m

theorem lemma35BlockSum_geC (m : Nat) :
    ∀ d0, m ≤ lemma35BlockSumC d0 m := by
  induction m with
  | zero => intro d0; exact Nat.zero_le _
  | succ m ih =>
      intro d0
      have h := ih (d0 + 1)
      simp only [lemma35BlockSumC]
      omega

/-- Choice-free diagonal decode (fuel-driven, structural). -/
def lemma35DiagDecodeC : Nat → Nat → Nat → Nat × Nat
  | 0, _, d => (d, 0)
  | (fuel + 1), n, d =>
      if n ≤ d then (d - n, n)
      else lemma35DiagDecodeC fuel (n - (d + 1)) (d + 1)

theorem lemma35DiagDecode_blockSumC (m : Nat) :
    ∀ (fuel d0 r : Nat), r ≤ d0 + m → m < fuel →
      lemma35DiagDecodeC fuel (lemma35BlockSumC d0 m + r) d0 =
        (d0 + m - r, r) := by
  induction m with
  | zero =>
      intro fuel d0 r hr hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [lemma35BlockSumC, lemma35DiagDecodeC]
      rw [if_pos (show (0 : Nat) + r ≤ d0 by omega)]
      congr 1 <;> omega
  | succ m ih =>
      intro fuel d0 r hr hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [lemma35BlockSumC, lemma35DiagDecodeC]
      rw [if_neg (show ¬ (d0 + 1 + lemma35BlockSumC (d0 + 1) m + r ≤ d0) by omega)]
      have hkey :
          d0 + 1 + lemma35BlockSumC (d0 + 1) m + r - (d0 + 1)
            = lemma35BlockSumC (d0 + 1) m + r := by omega
      rw [hkey, ih f (d0 + 1) r (by omega) (by omega)]
      congr 1 <;> omega

/-- Choice-free Cantor encode. -/
def lemma35EncodeC (k j : Nat) : Nat := lemma35BlockSumC 0 (k + j) + j

/-- Choice-free Cantor decode. -/
def lemma35UnpairC (q : Nat) : Nat × Nat := lemma35DiagDecodeC (q + 1) q 0

theorem lemma35Unpair_encodeC (k j : Nat) :
    lemma35UnpairC (lemma35EncodeC k j) = (k, j) := by
  unfold lemma35UnpairC lemma35EncodeC
  have hge : k + j ≤ lemma35BlockSumC 0 (k + j) :=
    lemma35BlockSum_geC (k + j) 0
  rw [lemma35DiagDecode_blockSumC (k + j)
      (lemma35BlockSumC 0 (k + j) + j + 1) 0 j (by omega) (by omega)]
  congr 1 <;> omega

/-- Flatten all finite exceptional families into a single sequence. -/
noncomputable def lemma35ExceptionSeqC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab) :
    Nat → CReal := fun q =>
  let ij := lemma35UnpairC q
  if h : ij.2 < lemma35CountC P ij.1 then
    (lemma35LevelDataC P ij.1).points ⟨ij.2, h⟩
  else
    a

/-- Every level point occurs in the flattened exceptional sequence. -/
theorem lemma35ExceptionSeq_pairC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (k : Nat) (j : Fin (lemma35CountC P k)) :
    lemma35ExceptionSeqC P (lemma35EncodeC k j.1) =
      (lemma35LevelDataC P k).points j := by
  unfold lemma35ExceptionSeqC
  rw [lemma35Unpair_encodeC, dif_pos j.2]

/-- Finite list of distances from `t` to the level-`k` exceptional points. -/
noncomputable def lemma35DistanceListC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (k : Nat) : List CReal :=
  List.ofFn (fun j : Fin (lemma35CountC P k) =>
    CReal.abs (CReal.sub t ((lemma35LevelDataC P k).points j)))

/-- Apartness from the flattened sequence makes every level distance positive. -/
theorem lemma35DistanceList_posC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) :
    ∀ x, x ∈ lemma35DistanceListC P t k →
      regularSeqLtProp CReal.zero x := by
  intro x hx
  have hx' :
      ∃ j : Fin (lemma35CountC P k),
        CReal.abs (CReal.sub t ((lemma35LevelDataC P k).points j)) = x := by
    unfold lemma35DistanceListC at hx
    exact List.mem_ofFn.mp hx
  rcases hx' with ⟨j, rfl⟩
  have h := hT (lemma35EncodeC k j.1)
  rw [lemma35ExceptionSeq_pairC P k j] at h
  exact h

/-- Positive finite minimum of the level distances, with `1` as seed. -/
noncomputable def lemma35MinDistanceC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (k : Nat) : CReal :=
  lemma34FoldMinC CReal.one (lemma35DistanceListC P t k)

/-- The finite minimum is positive away from the exceptional sequence. -/
theorem lemma35MinDistance_posC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) :
    regularSeqLtProp CReal.zero (lemma35MinDistanceC P t k) := by
  unfold lemma35MinDistanceC
  exact lemma34FoldMin_posC CReal.one (lemma35DistanceListC P t k)
    CReal.one_pos_E (lemma35DistanceList_posC P t hT k)

/-- `½*x + ½*x ≈ x`. -/
theorem half_add_self_equivC (x : CReal) :
    CReal.add (CReal.mul CReal.half x) (CReal.mul CReal.half x) ≈ x := by
  calc
    CReal.add (CReal.mul CReal.half x) (CReal.mul CReal.half x)
        ≈ CReal.mul (CReal.add CReal.half CReal.half) x :=
          Setoid.symm (CReal.right_distrib CReal.half CReal.half x)
    _ ≈ CReal.mul CReal.one x :=
          CReal.mul_respects_equiv _ _ _ _ CReal.half_add_half (Setoid.refl x)
    _ ≈ x := CReal.one_mul x

/-- One half of a positive number is strictly smaller than that number. -/
theorem lemma35Half_mul_lt_selfC {x : CReal}
    (hx : regularSeqLtProp CReal.zero x) :
    regularSeqLtProp (CReal.mul CReal.half x) x := by
  have hhalfx_pos : regularSeqLtProp CReal.zero (CReal.mul CReal.half x) :=
    CReal.mul_pos_E CReal.half_pos_E hx
  have hraw : regularSeqLtProp
      (CReal.add (CReal.mul CReal.half x) CReal.zero)
      (CReal.add (CReal.mul CReal.half x) (CReal.mul CReal.half x)) :=
    regularSeqLtProp_add_left
      (CReal.mul CReal.half x) CReal.zero
      (CReal.mul CReal.half x) hhalfx_pos
  have hleft : CReal.mul CReal.half x ≈
      CReal.add (CReal.mul CReal.half x) CReal.zero :=
    Setoid.symm (CReal.add_zero (CReal.mul CReal.half x))
  exact regularSeqLtProp_of_right_eventual (half_add_self_equivC x)
    (regularSeqLtProp_of_left_eventual hleft hraw)

/-- Radius used when applying Lemma 3.4 at one level. -/
noncomputable def lemma35BetaC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (k : Nat) : CReal :=
  CReal.mul CReal.half (lemma35MinDistanceC P t k)

/-- The selected level radius is positive. -/
theorem lemma35Beta_posC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) : regularSeqLtProp CReal.zero (lemma35BetaC P t k) := by
  unfold lemma35BetaC
  exact CReal.mul_pos_E CReal.half_pos_E
    (lemma35MinDistance_posC P t hT k)

/-- The selected radius is strictly below every level distance. -/
theorem lemma35Beta_lt_pointC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) (j : Fin (lemma35CountC P k)) :
    regularSeqLtProp (lemma35BetaC P t k)
      (CReal.abs (CReal.sub t ((lemma35LevelDataC P k).points j))) := by
  have hhalf :
      regularSeqLtProp (lemma35BetaC P t k)
        (lemma35MinDistanceC P t k) := by
    unfold lemma35BetaC
    exact lemma35Half_mul_lt_selfC
      (lemma35MinDistance_posC P t hT k)
  have hmem :
      CReal.abs (CReal.sub t ((lemma35LevelDataC P k).points j)) ∈
        lemma35DistanceListC P t k := by
    apply List.mem_ofFn.mpr
    exact ⟨j, rfl⟩
  have hmin :
      RegularSeqLe (lemma35MinDistanceC P t k)
        (CReal.abs (CReal.sub t ((lemma35LevelDataC P k).points j))) := by
    unfold lemma35MinDistanceC
    exact lemma34FoldMin_le_memC CReal.one hmem
  exact regularSeqLtProp_of_lt_of_le hhalf hmin

/-- T-b output: profile functions witnessing a small jump around `t`. -/
structure Lemma35LocalWitnessC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (t : CReal) (k : Nat) where
  beta : CReal
  beta_pos : regularSeqLtProp CReal.zero beta
  beta_far : ∀ j : Fin (lemma35CountC P k),
    regularSeqLtProp beta
      (CReal.abs (CReal.sub t ((lemma35LevelDataC P k).points j)))
  gamma : CReal
  gamma_pos : regularSeqLtProp CReal.zero gamma
  lower : P.Code
  lower_mem : lower ∈ P.F
  upper : P.Code
  upper_mem : upper ∈ P.F
  lower_zero : ∀ x : CReal, RegularSeqLe a x → RegularSeqLe x b →
    RegularSeqLe x (CReal.add t gamma) →
      P.embed lower x ≈ CReal.zero
  upper_one : ∀ x : CReal, RegularSeqLe a x → RegularSeqLe x b →
    RegularSeqLe (CReal.sub t gamma) x →
      P.embed upper x ≈ CReal.one
  gap_lt : regularSeqLtProp
    (CReal.sub (P.lambda upper) (P.lambda lower)) (halfPow k)

/-- At every level and every point apart from the flattened exceptional
sequence, Lemma 3.4 supplies a positive neighborhood and a profile bracket. -/
noncomputable def lemma35LocalWitnessC_construct {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) : Lemma35LocalWitnessC P t k := by
  let beta : CReal := lemma35BetaC P t k
  have hbeta : regularSeqLtProp CReal.zero beta :=
    lemma35Beta_posC P t hT k
  have hfar : ∀ j : Fin (lemma35CountC P k),
      regularSeqLtProp beta
        (CReal.abs (CReal.sub t ((lemma35LevelDataC P k).points j))) :=
    lemma35Beta_lt_pointC P t hT k
  let S := (lemma35LevelDataC P k).local_small beta hbeta
  have hp :
      P.p_ltC (CReal.max a (CReal.sub t S.gamma))
        (CReal.min b (CReal.add t S.gamma)) (halfPow k) :=
    S.local_bound t hat htb hfar
  exact
    { beta := beta
      beta_pos := hbeta
      beta_far := hfar
      gamma := S.gamma
      gamma_pos := S.gamma_pos
      lower := hp.f1
      lower_mem := hp.f1_mem
      upper := hp.f2
      upper_mem := hp.f2_mem
      lower_zero := by
        intro x hax hxb hxt
        exact hp.cond1 x hax hxb (CReal.le_minC hxb hxt)
      upper_one := by
        intro x hax hxb htx
        exact hp.cond2 x hax hxb (CReal.max_leC hax htx)
      gap_lt := hp.gap }

/-- Canonically chosen T-b witness. -/
noncomputable def lemma35LocalWitnessC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) : Lemma35LocalWitnessC P t k :=
  lemma35LocalWitnessC_construct P t hat htb hT k

/-- Transparent abbreviation for the canonically chosen T-b witnesses. -/
noncomputable def lemma35WitnessSeqC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) : Lemma35LocalWitnessC P t k :=
  lemma35LocalWitnessC P t hat htb hT k

/-- Lower lambda-value at dyadic level `k`. -/
noncomputable def lemma35LowerLambdaC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) : CReal :=
  P.lambda (lemma35WitnessSeqC P t hat htb hT k).lower

/-- Upper lambda-value at dyadic level `k`. -/
noncomputable def lemma35UpperLambdaC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) : CReal :=
  P.lambda (lemma35WitnessSeqC P t hat htb hT k).upper

/-- `(t - gamma₁) + (gamma₁ + gamma₂) ≈ t + gamma₂`. -/
theorem sub_add_gamma_cancelC (t gamma₁ gamma₂ : CReal) :
    CReal.add (CReal.sub t gamma₁) (CReal.add gamma₁ gamma₂) ≈
      CReal.add t gamma₂ := by
  have hq :
      mkQuot (CReal.add (CReal.sub t gamma₁) (CReal.add gamma₁ gamma₂)) =
        mkQuot (CReal.add t gamma₂) := by
    letI : CommRing CRealQuot :=
      cRealQuotCommRingConcreteWith cRatScalarMulArch
    change ((mkQuot t - mkQuot gamma₁) + (mkQuot gamma₁ + mkQuot gamma₂)) =
      mkQuot t + mkQuot gamma₂
    ring
  exact Quotient.exact hq

/-- Cross-level bracket: every lower witness lies below every upper witness. -/
theorem lemma35CrossBracketC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k m : Nat) :
    RegularSeqLe (lemma35LowerLambdaC P t hat htb hT k)
      (lemma35UpperLambdaC P t hat htb hT m) := by
  let Wk : Lemma35LocalWitnessC P t k :=
    lemma35WitnessSeqC P t hat htb hT k
  let Wm : Lemma35LocalWitnessC P t m :=
    lemma35WitnessSeqC P t hat htb hT m
  change RegularSeqLe (P.lambda Wk.lower) (P.lambda Wm.upper)
  apply P.mono Wk.lower Wm.upper Wk.lower_mem Wm.upper_mem
  intro x hax hxb
  have hsum_raw : regularSeqLtProp
      (CReal.add CReal.zero CReal.zero)
      (CReal.add Wm.gamma Wk.gamma) :=
    regularSeqLtProp_add Wm.gamma_pos Wk.gamma_pos
  have hsum : regularSeqLtProp CReal.zero (CReal.add Wm.gamma Wk.gamma) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (CReal.add_zero CReal.zero)) hsum_raw
  have hspan_raw : regularSeqLtProp
      (CReal.add (CReal.sub t Wm.gamma) CReal.zero)
      (CReal.add (CReal.sub t Wm.gamma)
        (CReal.add Wm.gamma Wk.gamma)) :=
    regularSeqLtProp_add_left (CReal.sub t Wm.gamma) CReal.zero
      (CReal.add Wm.gamma Wk.gamma) hsum
  have hspan_left : CReal.sub t Wm.gamma ≈
      CReal.add (CReal.sub t Wm.gamma) CReal.zero :=
    Setoid.symm (CReal.add_zero (CReal.sub t Wm.gamma))
  have hspan_mid : regularSeqLtProp (CReal.sub t Wm.gamma)
      (CReal.add (CReal.sub t Wm.gamma)
        (CReal.add Wm.gamma Wk.gamma)) :=
    regularSeqLtProp_of_left_eventual hspan_left hspan_raw
  have hspan : regularSeqLtProp (CReal.sub t Wm.gamma)
      (CReal.add t Wk.gamma) :=
    regularSeqLtProp_of_right_eventual
      (sub_add_gamma_cancelC t Wm.gamma Wk.gamma) hspan_mid
  rcases regularSeqLtProp_cotrans
      (CReal.sub t Wm.gamma) (CReal.add t Wk.gamma) x hspan with hleft | hright
  · have hu : P.embed Wm.upper x ≈ CReal.one :=
      Wm.upper_one x hax hxb (regularSeqLe_of_ltPropC hleft)
    exact regularSeqLe_of_right_eventual (Setoid.symm hu)
      (P.bound Wk.lower Wk.lower_mem x hax hxb).2
  · have hl : P.embed Wk.lower x ≈ CReal.zero :=
      Wk.lower_zero x hax hxb (regularSeqLe_of_ltPropC hright)
    have hzero_upper : RegularSeqLe CReal.zero (P.embed Wm.upper x) :=
      regularSeqLe_zero_of_nonneg
        (P.bound Wm.upper Wm.upper_mem x hax hxb).1
    exact regularSeqLe_of_left_eventual hl
      hzero_upper

/-- A lower lambda-value at level `m` exceeds that at level `n` by less
than the level-`n` bracket width. -/
theorem lemma35Lower_sub_lt_halfPow_rightC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (m n : Nat) :
    regularSeqLtProp
      (CReal.sub (lemma35LowerLambdaC P t hat htb hT m)
        (lemma35LowerLambdaC P t hat htb hT n))
      (halfPow n) := by
  have hcross := lemma35CrossBracketC P t hat htb hT m n
  have hsub :
      RegularSeqLe
        (CReal.sub (lemma35LowerLambdaC P t hat htb hT m)
          (lemma35LowerLambdaC P t hat htb hT n))
        (CReal.sub (lemma35UpperLambdaC P t hat htb hT n)
          (lemma35LowerLambdaC P t hat htb hT n)) :=
    subSeq_monotone_left_regularSeqLe _ _ _ hcross
  have hgap :
      regularSeqLtProp
        (CReal.sub (lemma35UpperLambdaC P t hat htb hT n)
          (lemma35LowerLambdaC P t hat htb hT n))
        (halfPow n) := by
    simpa [lemma35LowerLambdaC, lemma35UpperLambdaC,
      lemma35WitnessSeqC] using
      (lemma35WitnessSeqC P t hat htb hT n).gap_lt
  exact regularSeqLtProp_of_le_of_lt hsub hgap

/-- Two strict one-sided difference bounds give a strict absolute-value bound. -/
theorem lemma35Abs_sub_lt_of_two_sidedC {x y eps : CReal}
    (heps : regularSeqLtProp CReal.zero eps)
    (hxy : regularSeqLtProp (CReal.sub x y) eps)
    (hyx : regularSeqLtProp (CReal.sub y x) eps) :
    regularSeqLtProp (CReal.abs (CReal.sub x y)) eps := by
  rcases regularSeqLtProp_cotrans CReal.zero eps
      (CReal.abs (CReal.sub x y)) heps with habspos | habslt
  · rcases CReal.lt_or_lt_of_abs_pos_E habspos with hpos | hneg
    · have hnonneg : ¬ CReal.ltE (CReal.sub x y) CReal.zero := fun hc =>
        regularSeqLtProp_irrefl CReal.zero
          (regularSeqLtProp_trans CReal.zero (CReal.sub x y) CReal.zero hpos hc)
      have habs_eq : CReal.abs (CReal.sub x y) ≈ CReal.sub x y :=
        CReal.abs_of_nonneg_E hnonneg
      exact regularSeqLtProp_of_left_eventual habs_eq hxy
    · have h0neg : regularSeqLtProp CReal.zero
          (CReal.neg (CReal.sub x y)) :=
        regularSeqLtProp_zero_lt_negC hneg
      have hnonneg : ¬ CReal.ltE (CReal.neg (CReal.sub x y)) CReal.zero := fun hc =>
        regularSeqLtProp_irrefl CReal.zero
          (regularSeqLtProp_trans CReal.zero
            (CReal.neg (CReal.sub x y)) CReal.zero h0neg hc)
      have h1 : CReal.abs (CReal.neg (CReal.sub x y)) ≈
          CReal.neg (CReal.sub x y) :=
        CReal.abs_of_nonneg_E hnonneg
      have h2 : CReal.abs (CReal.neg (CReal.sub x y)) ≈
          CReal.abs (CReal.sub x y) :=
        CReal.abs_neg (CReal.sub x y)
      have habs_eq : CReal.abs (CReal.sub x y) ≈
          CReal.neg (CReal.sub x y) :=
        Setoid.trans (Setoid.symm h2) h1
      have hneg_eq : CReal.neg (CReal.sub x y) ≈ CReal.sub y x :=
        neg_sub_eventualC x y
      exact regularSeqLtProp_of_left_eventual
        (Setoid.trans habs_eq hneg_eq) hyx
  · exact habslt

/-- The lower lambda-values form a representative Cauchy sequence. -/
noncomputable def lemma35LowerLambdaCauchyDataC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q)))) :
    CRealRepSequenceCauchyData (lemma35LowerLambdaC P t hat htb hT) where
  cmod := fun k => k
  close_eventually := by
    intro k m n hkm hkn
    have hmn :
        regularSeqLtProp
          (CReal.sub (lemma35LowerLambdaC P t hat htb hT m)
            (lemma35LowerLambdaC P t hat htb hT n))
          (halfPow k) :=
      regularSeqLtProp_of_lt_of_le
        (lemma35Lower_sub_lt_halfPow_rightC P t hat htb hT m n)
        (halfPow_antitone_leC hkn)
    have hnm :
        regularSeqLtProp
          (CReal.sub (lemma35LowerLambdaC P t hat htb hT n)
            (lemma35LowerLambdaC P t hat htb hT m))
          (halfPow k) :=
      regularSeqLtProp_of_lt_of_le
        (lemma35Lower_sub_lt_halfPow_rightC P t hat htb hT n m)
        (halfPow_antitone_leC hkm)
    have habs :
        regularSeqLtProp
          (CReal.abs
            (CReal.sub (lemma35LowerLambdaC P t hat htb hT m)
              (lemma35LowerLambdaC P t hat htb hT n)))
          (halfPow k) :=
      lemma35Abs_sub_lt_of_two_sidedC (regularSeqLtProp_zero_halfPow k)
        hmn hnm
    exact repCloseAtGauge_of_absGap
      (lemma35LowerLambdaC P t hat htb hT m)
      (lemma35LowerLambdaC P t hat htb hT n) k
      (by simpa [halfPow, CReal.epsSeq] using habs)

/-- Completeness supplies the candidate `lambdaBar(t)`. -/
noncomputable def lemma35LowerLimitDataC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q)))) :
    CRealRepLimitData (lemma35LowerLambdaC P t hat htb hT) :=
  CReal.complete_repCarrying_data _
    (lemma35LowerLambdaCauchyDataC P t hat htb hT)

/-- The common limiting value used in Theorem 3.5. -/
noncomputable def lemma35LambdaBarC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q)))) : CReal :=
  (lemma35LowerLimitDataC P t hat htb hT).limit

/-- Every lower lambda-value lies weakly below the completed limit. -/
theorem lemma35LowerLambda_le_lambdaBarC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) :
    RegularSeqLe (lemma35LowerLambdaC P t hat htb hT k)
      (lemma35LambdaBarC P t hat htb hT) := by
  let L : Nat → CReal := lemma35LowerLambdaC P t hat htb hT
  let U : Nat → CReal := lemma35UpperLambdaC P t hat htb hT
  let H : CRealRepLimitData L := lemma35LowerLimitDataC P t hat htb hT
  change RegularSeqLe (L k) H.limit
  intro hcounter
  have hpos_order : regularSeqLtProp H.limit (L k) :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hd : regularSeqLtProp CReal.zero (CReal.sub (L k) H.limit) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  have hhalfD : regularSeqLtProp CReal.zero
      (CReal.mul CReal.half (CReal.sub (L k) H.limit)) :=
    CReal.mul_pos_E CReal.half_pos_E hd
  obtain ⟨w, hw⟩ :=
    posC_imp_halfPow_lt hhalfD
  let m : Nat := Nat.max w (H.lmod w)
  have hwm : w ≤ m := Nat.le_max_left _ _
  have hmod : H.lmod w ≤ m := Nat.le_max_right _ _
  have hclose : RepCloseAtGauge (w + 1) (L m) H.limit :=
    H.close w m hmod
  have hLmbar : regularSeqLtProp (CReal.sub (L m) H.limit) (halfPow w) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ w
        (repCloseAtGauge_symm hclose)
  have hkU : RegularSeqLe (L k) (U m) := by
    dsimp [L, U]
    exact lemma35CrossBracketC P t hat htb hT k m
  have hgapm : regularSeqLtProp (CReal.sub (U m) (L m)) (halfPow m) := by
    dsimp [L, U]
    simpa [lemma35LowerLambdaC, lemma35UpperLambdaC,
      lemma35WitnessSeqC] using
      (lemma35WitnessSeqC P t hat htb hT m).gap_lt
  have hgapw : regularSeqLtProp (CReal.sub (U m) (L m)) (halfPow w) :=
    regularSeqLtProp_of_lt_of_le hgapm (halfPow_antitone_leC hwm)
  have hadd : regularSeqLtProp
      (CReal.add (CReal.sub (U m) (L m)) (CReal.sub (L m) H.limit))
      (CReal.add (halfPow w) (halfPow w)) :=
    regularSeqLtProp_add hgapw hLmbar
  have hUmb : regularSeqLtProp (CReal.sub (U m) H.limit)
      (CReal.add (halfPow w) (halfPow w)) :=
    regularSeqLtProp_of_left_eventual
      (Setoid.symm (sub_add_sub_cancelC (U m) (L m) H.limit)) hadd
  have hsub : RegularSeqLe (CReal.sub (L k) H.limit)
      (CReal.sub (U m) H.limit) :=
    subSeq_monotone_left_regularSeqLe _ _ _ hkU
  have hbound : regularSeqLtProp (CReal.sub (L k) H.limit)
      (CReal.add (halfPow w) (halfPow w)) :=
    regularSeqLtProp_of_le_of_lt hsub hUmb
  have htwo : regularSeqLtProp
      (CReal.add (halfPow w) (halfPow w))
      (CReal.add (CReal.mul CReal.half (CReal.sub (L k) H.limit))
        (CReal.mul CReal.half (CReal.sub (L k) H.limit))) :=
    regularSeqLtProp_add hw hw
  have htwoRaw : regularSeqLtProp
      (CReal.add (halfPow w) (halfPow w))
      (CReal.sub (L k) H.limit) :=
    regularSeqLtProp_of_right_eventual
      (half_add_self_equivC (CReal.sub (L k) H.limit)) htwo
  have hloop : regularSeqLtProp
      (CReal.add (halfPow w) (halfPow w))
      (CReal.add (halfPow w) (halfPow w)) :=
    regularSeqLtProp_trans _ _ _ htwoRaw hbound
  exact regularSeqLtProp_irrefl _ hloop

/-- The completed limit lies weakly below every upper lambda-value. -/
theorem lemma35LambdaBar_le_upperLambdaC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ q : Nat,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P q))))
    (k : Nat) :
    RegularSeqLe (lemma35LambdaBarC P t hat htb hT)
      (lemma35UpperLambdaC P t hat htb hT k) := by
  let L : Nat → CReal := lemma35LowerLambdaC P t hat htb hT
  let U : Nat → CReal := lemma35UpperLambdaC P t hat htb hT
  let H : CRealRepLimitData L := lemma35LowerLimitDataC P t hat htb hT
  change RegularSeqLe H.limit (U k)
  intro hcounter
  have hpos_order : regularSeqLtProp (U k) H.limit :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  have hd : regularSeqLtProp CReal.zero (CReal.sub H.limit (U k)) :=
    regularSeqLtProp_zero_lt_sub hpos_order
  obtain ⟨w, hw⟩ := posC_imp_halfPow_lt hd
  let m : Nat := H.lmod w
  have hclose : RepCloseAtGauge (w + 1) (L m) H.limit :=
    H.close w m (Nat.le_refl m)
  have hbarLm : regularSeqLtProp (CReal.sub H.limit (L m)) (halfPow w) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ w hclose
  have hmU : RegularSeqLe (L m) (U k) := by
    dsimp [L, U]
    exact lemma35CrossBracketC P t hat htb hT m k
  have hsub : RegularSeqLe (CReal.sub H.limit (U k))
      (CReal.sub H.limit (L m)) :=
    regularSeqLe_sub_leftC hmU
  have hbound : regularSeqLtProp (CReal.sub H.limit (U k)) (halfPow w) :=
    regularSeqLtProp_of_le_of_lt hsub hbarLm
  have hloop : regularSeqLtProp (halfPow w) (halfPow w) :=
    regularSeqLtProp_trans _ _ _ hw hbound
  exact regularSeqLtProp_irrefl _ hloop

/-- Two-sided subtraction monotonicity:
`a ≤ b` and `c ≤ d` imply `a - d ≤ b - c`. -/
theorem regularSeqLe_sub_subC {a b c d : CReal}
    (hab : RegularSeqLe a b) (hcd : RegularSeqLe c d) :
    RegularSeqLe (CReal.sub a d) (CReal.sub b c) := by
  change RegularSeqNonneg (subSeq (CReal.sub b c) (CReal.sub a d))
  have hsum : RegularSeqNonneg (CReal.add (subSeq b a) (subSeq d c)) :=
    regularSeqNonneg_add hab hcd
  have heq : relEventually
      (subSeq (CReal.sub b c) (CReal.sub a d))
      (CReal.add (subSeq b a) (subSeq d c)) := by
    have hq :
        mkQuot (subSeq (CReal.sub b c) (CReal.sub a d)) =
          mkQuot (CReal.add (subSeq b a) (subSeq d c)) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      change (mkQuot b - mkQuot c) - (mkQuot a - mkQuot d) =
        (mkQuot b - mkQuot a) + (mkQuot d - mkQuot c)
      ring
    exact Quotient.exact hq
  exact regularSeqNonneg_of_eventual heq hsum

/-- Smoothness at a point for CReal-native profiles. -/
def ProfileC.IsSmoothAtC {a b : CReal} {hab : regularSeqLtProp a b}
    (P : ProfileC a b hab) (t : CReal) : Prop :=
  ∃ lambdaBar : CReal,
    ∀ eps : CReal, regularSeqLtProp CReal.zero eps →
      ∃ delta : CReal, regularSeqLtProp CReal.zero delta ∧
        (∀ f : P.Code, f ∈ P.F →
          (∀ x : CReal, RegularSeqLe (CReal.add t delta) x →
            P.embed f x ≈ CReal.one) →
          (∀ x : CReal, RegularSeqLe x (CReal.sub t delta) →
            P.embed f x ≈ CReal.zero) →
          regularSeqLtProp
            (CReal.abs (CReal.sub (P.lambda f) lambdaBar)) eps)

/-- Direct epsilon-delta smoothness data for the concrete `lambdaBar`. -/
noncomputable def thm_3_5_smooth_at_seq_specC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P n)))) :
    ∀ eps : CReal, regularSeqLtProp CReal.zero eps →
      ∃ delta : CReal, regularSeqLtProp CReal.zero delta ∧
        (∀ f : P.Code, f ∈ P.F →
          (∀ x : CReal, RegularSeqLe (CReal.add t delta) x →
            P.embed f x ≈ CReal.one) →
          (∀ x : CReal, RegularSeqLe x (CReal.sub t delta) →
            P.embed f x ≈ CReal.zero) →
          regularSeqLtProp
            (CReal.abs (CReal.sub (P.lambda f)
              (lemma35LambdaBarC P t hat htb hT))) eps) := by
  intro eps heps
  obtain ⟨k, hk⟩ := posC_imp_halfPow_lt heps
  let W : Lemma35LocalWitnessC P t k :=
    lemma35WitnessSeqC P t hat htb hT k
  let delta : CReal := CReal.mul CReal.half W.gamma
  have hδpos : regularSeqLtProp CReal.zero delta := by
    dsimp [delta]
    exact CReal.mul_pos_E CReal.half_pos_E W.gamma_pos
  refine ⟨delta, hδpos, ?_⟩
  intro f hf hf1 hf0
  have hδγ : regularSeqLtProp delta W.gamma := by
    dsimp [delta]
    exact lemma35Half_mul_lt_selfC W.gamma_pos
  have htpδ : regularSeqLtProp
      (CReal.add t delta) (CReal.add t W.gamma) :=
    regularSeqLtProp_add_left t delta W.gamma hδγ
  have hgap_pos : regularSeqLtProp CReal.zero (CReal.sub W.gamma delta) :=
    regularSeqLtProp_zero_lt_sub hδγ
  have htm_raw : regularSeqLtProp
      (CReal.add (CReal.sub t W.gamma) CReal.zero)
      (CReal.add (CReal.sub t W.gamma) (CReal.sub W.gamma delta)) :=
    regularSeqLtProp_add_left (CReal.sub t W.gamma) CReal.zero
      (CReal.sub W.gamma delta) hgap_pos
  have htm_left : CReal.sub t W.gamma ≈
      CReal.add (CReal.sub t W.gamma) CReal.zero :=
    Setoid.symm (CReal.add_zero (CReal.sub t W.gamma))
  have htm_mid : regularSeqLtProp (CReal.sub t W.gamma)
      (CReal.add (CReal.sub t W.gamma) (CReal.sub W.gamma delta)) :=
    regularSeqLtProp_of_left_eventual htm_left htm_raw
  have htmγδ : regularSeqLtProp (CReal.sub t W.gamma) (CReal.sub t delta) :=
    regularSeqLtProp_of_right_eventual
      (sub_add_sub_cancelC t W.gamma delta) htm_mid
  have hlower_le_f : RegularSeqLe (P.lambda W.lower) (P.lambda f) := by
    apply P.mono W.lower f W.lower_mem hf
    intro x hax hxb
    rcases regularSeqLtProp_cotrans
        (CReal.add t delta) (CReal.add t W.gamma) x htpδ with hxr | hxl
    · have hf1x : P.embed f x ≈ CReal.one :=
        hf1 x (regularSeqLe_of_ltPropC hxr)
      exact regularSeqLe_of_right_eventual (Setoid.symm hf1x)
        (P.bound W.lower W.lower_mem x hax hxb).2
    · have hl0 : P.embed W.lower x ≈ CReal.zero :=
        W.lower_zero x hax hxb (regularSeqLe_of_ltPropC hxl)
      have hzero_f : RegularSeqLe CReal.zero (P.embed f x) :=
        regularSeqLe_zero_of_nonneg (P.bound f hf x hax hxb).1
      exact regularSeqLe_of_left_eventual hl0 hzero_f
  have hf_le_upper : RegularSeqLe (P.lambda f) (P.lambda W.upper) := by
    apply P.mono f W.upper hf W.upper_mem
    intro x hax hxb
    rcases regularSeqLtProp_cotrans
        (CReal.sub t W.gamma) (CReal.sub t delta) x htmγδ with hxr | hxl
    · have hu1 : P.embed W.upper x ≈ CReal.one :=
        W.upper_one x hax hxb (regularSeqLe_of_ltPropC hxr)
      exact regularSeqLe_of_right_eventual (Setoid.symm hu1)
        (P.bound f hf x hax hxb).2
    · have hf0x : P.embed f x ≈ CReal.zero :=
        hf0 x (regularSeqLe_of_ltPropC hxl)
      have hzero_upper : RegularSeqLe CReal.zero (P.embed W.upper x) :=
        regularSeqLe_zero_of_nonneg
          (P.bound W.upper W.upper_mem x hax hxb).1
      exact regularSeqLe_of_left_eventual hf0x hzero_upper
  have hlower_le_bar :
      RegularSeqLe (P.lambda W.lower)
        (lemma35LambdaBarC P t hat htb hT) := by
    simpa [W, lemma35LowerLambdaC, lemma35WitnessSeqC] using
      lemma35LowerLambda_le_lambdaBarC P t hat htb hT k
  have hbar_le_upper :
      RegularSeqLe (lemma35LambdaBarC P t hat htb hT)
        (P.lambda W.upper) := by
    simpa [W, lemma35UpperLambdaC, lemma35WitnessSeqC] using
      lemma35LambdaBar_le_upperLambdaC P t hat htb hT k
  have hgapε : regularSeqLtProp
      (CReal.sub (P.lambda W.upper) (P.lambda W.lower)) eps :=
    regularSeqLtProp_trans _ _ _ W.gap_lt hk
  have hxy : regularSeqLtProp
      (CReal.sub (P.lambda f) (lemma35LambdaBarC P t hat htb hT)) eps :=
    regularSeqLtProp_of_le_of_lt
      (regularSeqLe_sub_subC hf_le_upper hlower_le_bar) hgapε
  have hyx : regularSeqLtProp
      (CReal.sub (lemma35LambdaBarC P t hat htb hT) (P.lambda f)) eps :=
    regularSeqLtProp_of_le_of_lt
      (regularSeqLe_sub_subC hbar_le_upper hlower_le_f) hgapε
  exact lemma35Abs_sub_lt_of_two_sidedC heps hxy hyx

/-- Dyadic, data-carrying version of `thm_3_5_smooth_at_seq_specC`.
    This avoids extracting a modulus from a Prop-valued `∃` when downstream
    constructions need an actual `Nat → Nat` modulus. -/
noncomputable def thm_3_5_smooth_at_seq_dyadicSpecDataC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P n))))
    (k : Nat) :
    { delta : CReal //
      regularSeqLtProp CReal.zero delta ∧
        (∀ f : P.Code, f ∈ P.F →
          (∀ x : CReal, RegularSeqLe (CReal.add t delta) x →
            P.embed f x ≈ CReal.one) →
          (∀ x : CReal, RegularSeqLe x (CReal.sub t delta) →
            P.embed f x ≈ CReal.zero) →
          regularSeqLtProp
            (CReal.abs (CReal.sub (P.lambda f)
              (lemma35LambdaBarC P t hat htb hT))) (halfPow k)) } := by
  let W : Lemma35LocalWitnessC P t (k + 1) :=
    lemma35WitnessSeqC P t hat htb hT (k + 1)
  let delta : CReal := CReal.mul CReal.half W.gamma
  have hδpos : regularSeqLtProp CReal.zero delta := by
    dsimp [delta]
    exact CReal.mul_pos_E CReal.half_pos_E W.gamma_pos
  refine ⟨delta, hδpos, ?_⟩
  intro f hf hf1 hf0
  have hδγ : regularSeqLtProp delta W.gamma := by
    dsimp [delta]
    exact lemma35Half_mul_lt_selfC W.gamma_pos
  have htpδ : regularSeqLtProp
      (CReal.add t delta) (CReal.add t W.gamma) :=
    regularSeqLtProp_add_left t delta W.gamma hδγ
  have hgap_pos : regularSeqLtProp CReal.zero (CReal.sub W.gamma delta) :=
    regularSeqLtProp_zero_lt_sub hδγ
  have htm_raw : regularSeqLtProp
      (CReal.add (CReal.sub t W.gamma) CReal.zero)
      (CReal.add (CReal.sub t W.gamma) (CReal.sub W.gamma delta)) :=
    regularSeqLtProp_add_left (CReal.sub t W.gamma) CReal.zero
      (CReal.sub W.gamma delta) hgap_pos
  have htm_left : CReal.sub t W.gamma ≈
      CReal.add (CReal.sub t W.gamma) CReal.zero :=
    Setoid.symm (CReal.add_zero (CReal.sub t W.gamma))
  have htm_mid : regularSeqLtProp (CReal.sub t W.gamma)
      (CReal.add (CReal.sub t W.gamma) (CReal.sub W.gamma delta)) :=
    regularSeqLtProp_of_left_eventual htm_left htm_raw
  have htmγδ : regularSeqLtProp (CReal.sub t W.gamma) (CReal.sub t delta) :=
    regularSeqLtProp_of_right_eventual
      (sub_add_sub_cancelC t W.gamma delta) htm_mid
  have hlower_le_f : RegularSeqLe (P.lambda W.lower) (P.lambda f) := by
    apply P.mono W.lower f W.lower_mem hf
    intro x hax hxb
    rcases regularSeqLtProp_cotrans
        (CReal.add t delta) (CReal.add t W.gamma) x htpδ with hxr | hxl
    · have hf1x : P.embed f x ≈ CReal.one :=
        hf1 x (regularSeqLe_of_ltPropC hxr)
      exact regularSeqLe_of_right_eventual (Setoid.symm hf1x)
        (P.bound W.lower W.lower_mem x hax hxb).2
    · have hl0 : P.embed W.lower x ≈ CReal.zero :=
        W.lower_zero x hax hxb (regularSeqLe_of_ltPropC hxl)
      have hzero_f : RegularSeqLe CReal.zero (P.embed f x) :=
        regularSeqLe_zero_of_nonneg (P.bound f hf x hax hxb).1
      exact regularSeqLe_of_left_eventual hl0 hzero_f
  have hf_le_upper : RegularSeqLe (P.lambda f) (P.lambda W.upper) := by
    apply P.mono f W.upper hf W.upper_mem
    intro x hax hxb
    rcases regularSeqLtProp_cotrans
        (CReal.sub t W.gamma) (CReal.sub t delta) x htmγδ with hxr | hxl
    · have hu1 : P.embed W.upper x ≈ CReal.one :=
        W.upper_one x hax hxb (regularSeqLe_of_ltPropC hxr)
      exact regularSeqLe_of_right_eventual (Setoid.symm hu1)
        (P.bound f hf x hax hxb).2
    · have hf0x : P.embed f x ≈ CReal.zero :=
        hf0 x (regularSeqLe_of_ltPropC hxl)
      have hzero_upper : RegularSeqLe CReal.zero (P.embed W.upper x) :=
        regularSeqLe_zero_of_nonneg
          (P.bound W.upper W.upper_mem x hax hxb).1
      exact regularSeqLe_of_left_eventual hf0x hzero_upper
  have hlower_le_bar :
      RegularSeqLe (P.lambda W.lower)
        (lemma35LambdaBarC P t hat htb hT) := by
    simpa [W, lemma35LowerLambdaC, lemma35WitnessSeqC] using
      lemma35LowerLambda_le_lambdaBarC P t hat htb hT (k + 1)
  have hbar_le_upper :
      RegularSeqLe (lemma35LambdaBarC P t hat htb hT)
        (P.lambda W.upper) := by
    simpa [W, lemma35UpperLambdaC, lemma35WitnessSeqC] using
      lemma35LambdaBar_le_upperLambdaC P t hat htb hT (k + 1)
  have hgapε : regularSeqLtProp
      (CReal.sub (P.lambda W.upper) (P.lambda W.lower)) (halfPow k) :=
    regularSeqLtProp_trans _ _ _ W.gap_lt
      (regularSeqLtProp_halfPow_succ k)
  have hxy : regularSeqLtProp
      (CReal.sub (P.lambda f) (lemma35LambdaBarC P t hat htb hT)) (halfPow k) :=
    regularSeqLtProp_of_le_of_lt
      (regularSeqLe_sub_subC hf_le_upper hlower_le_bar) hgapε
  have hyx : regularSeqLtProp
      (CReal.sub (lemma35LambdaBarC P t hat htb hT) (P.lambda f)) (halfPow k) :=
    regularSeqLtProp_of_le_of_lt
      (regularSeqLe_sub_subC hbar_le_upper hlower_le_f) hgapε
  exact lemma35Abs_sub_lt_of_two_sidedC (regularSeqLtProp_zero_halfPow k) hxy hyx

/-- A point apart from the exceptional sequence is smooth. -/
theorem thm_3_5_smooth_at_seqC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (lemma35ExceptionSeqC P n)))) :
    P.IsSmoothAtC t :=
  ⟨lemma35LambdaBarC P t hat htb hT,
    thm_3_5_smooth_at_seq_specC P t hat htb hT⟩

/-- CReal-native Theorem 3.5: all but countably many points are smooth. -/
theorem thm_3_5_smooth_aeC {a b : CReal}
    {hab : regularSeqLtProp a b} (P : ProfileC a b hab) :
    ∃ T : Nat → CReal, ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      (∀ n,
        regularSeqLtProp CReal.zero
          (CReal.abs (CReal.sub t (T n)))) →
      P.IsSmoothAtC t :=
  ⟨lemma35ExceptionSeqC P,
    fun t hat htb hT => thm_3_5_smooth_at_seqC P t hat htb hT⟩

/-! ### §3 Theorem 3.6 CReal-native entry: endpoint package + smooth apart data -/

/-- CReal-native endpoint package for Theorem 3.6 profile construction.
    We take `alpha=0`, `beta=a/2`, `gamma=b+1`, `delta=gamma+1`. -/
noncomputable def thm36A2_endpointsC {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) :
    Thm36A2EndpointsC a b := by
  let beta : CReal := CReal.mul CReal.half a
  let gamma : CReal := CReal.add b CReal.one
  let delta : CReal := CReal.add gamma CReal.one
  have h0a : regularSeqLtProp CReal.zero a := regularSeqLtProp_zero_of_posData ha
  have h0beta : regularSeqLtProp CReal.zero beta := by
    dsimp [beta]
    exact CReal.mul_pos_E CReal.half_pos_E h0a
  have hbeta_a : regularSeqLtProp beta a := by
    dsimp [beta]
    exact lemma35Half_mul_lt_selfC h0a
  have hbpos : regularSeqLtProp CReal.zero b :=
    regularSeqLtProp_trans CReal.zero a b h0a hab
  have hbgamma : regularSeqLtProp b gamma := by
    dsimp [gamma]
    exact regularSeqLtProp_self_add_sigmaC b CReal.one_pos_E
  have h0gamma : regularSeqLtProp CReal.zero gamma :=
    regularSeqLtProp_trans CReal.zero b gamma hbpos hbgamma
  have hgamma_delta : regularSeqLtProp gamma delta := by
    dsimp [delta]
    exact regularSeqLtProp_self_add_sigmaC gamma CReal.one_pos_E
  exact
    { alpha := CReal.zero
      beta := beta
      gamma := gamma
      delta := delta
      alpha_nonneg := by
        intro h
        exact regularSeqLtProp_irrefl CReal.zero h
      hpos_ba :=
        regularSeqLtData_zero_to_posEventuallyC
          (sub_pos_dataC (regularSeqLtData_of_ltPropC h0beta))
      beta_lt_a := hbeta_a
      b_lt_gamma := hbgamma
      gamma_nonneg := by
        intro h
        exact regularSeqLtProp_irrefl CReal.zero
          (regularSeqLtProp_trans CReal.zero gamma CReal.zero h0gamma h)
      hpos_dg :=
        regularSeqLtData_zero_to_posEventuallyC
          (sub_pos_dataC (regularSeqLtData_of_ltPropC hgamma_delta)) }

/-- The canonical Theorem 3.6 profile attached to an integrable representative. -/
noncomputable def thm36A2_profileDefaultC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) :
    ProfileC a b hab :=
  thm36A2_profileC h hab ha (thm36A2_endpointsC hab ha)

/-- The canonical exceptional sequence for Theorem 3.6 on `(a,b)`. -/
noncomputable def thm36ExceptionSeqC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) : Nat → CReal :=
  lemma35ExceptionSeqC (thm36A2_profileDefaultC h hab ha)

/-- The canonical smooth value `lambdaBar` at an apart point. -/
noncomputable def thm36C_lambdaBarC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : RegularSeqLe a t) (htb : RegularSeqLe t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) : CReal :=
  lemma35LambdaBarC (thm36A2_profileDefaultC h hab ha) t hat htb hT

/-- Theorem 3.6, profile part: the profile attached to `h` is smooth except
    for the countable exceptional sequence supplied by Theorem 3.5. -/
theorem thm_3_6_profile_smooth_aeC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) :
    ∃ T : Nat → CReal, ∀ t : CReal, RegularSeqLe a t → RegularSeqLe t b →
      (∀ n,
        regularSeqLtProp CReal.zero
          (CReal.abs (CReal.sub t (T n)))) →
      (thm36A2_profileDefaultC h hab ha).IsSmoothAtC t :=
  thm_3_5_smooth_aeC (thm36A2_profileDefaultC h hab ha)

/-- Explicit apart-point form used by the level-set part of Theorem 3.6. -/
theorem thm_3_6_forall_apart_smoothC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    (thm36A2_profileDefaultC h hab ha).IsSmoothAtC t :=
  thm_3_5_smooth_at_seqC (thm36A2_profileDefaultC h hab ha) t
    (regularSeqLe_of_ltPropC hat) (regularSeqLe_of_ltPropC htb) hT

/-- Data package for a smooth apart point in the Theorem 3.6 profile. -/
structure Thm36BSmoothPointDataC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) where
  t : CReal
  a_lt_t : regularSeqLtProp a t
  t_lt_b : regularSeqLtProp t b
  apart : ∀ n,
    regularSeqLtProp CReal.zero
      (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))
  smooth : (thm36A2_profileDefaultC h hab ha).IsSmoothAtC t
  lambdaBar : CReal := thm36C_lambdaBarC h hab ha t
    (regularSeqLe_of_ltPropC a_lt_t) (regularSeqLe_of_ltPropC t_lt_b) apart

/-- Build the Theorem 3.6 smooth-point data from an arbitrary apart point. -/
noncomputable def thm36B_smoothPointData_of_apartC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    Thm36BSmoothPointDataC h a b hab ha where
  t := t
  a_lt_t := hat
  t_lt_b := htb
  apart := hT
  smooth := thm_3_6_forall_apart_smoothC h hab ha t hat htb hT

/-! ### §3 Theorem 3.6 D entry: level BSets for the A/B pairs -/

/-- `h` has an absolutely convergent point value at `x`, with sum at least `t`. -/
def thm36D_upperSetC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) : Set X :=
  {x | ∃ (_habs : RepSeriesSum (fun n => CReal.abs ((h.fn n).toFun x)))
      (hx : RepSeriesSum (fun n => (h.fn n).toFun x)),
      RegularSeqLe t hx.sum}

/-- `h` has an absolutely convergent point value at `x`, with sum below `t`. -/
def thm36D_lowerSetC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) : Set X :=
  {x | ∃ (_habs : RepSeriesSum (fun n => CReal.abs ((h.fn n).toFun x)))
      (hx : RepSeriesSum (fun n => (h.fn n).toFun x)),
      regularSeqLtProp hx.sum t}

theorem thm36D_levelSets_disjointC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) :
    ∀ x ∈ thm36D_upperSetC h t, ∀ y ∈ thm36D_lowerSetC h t, x ≠ y := by
  intro x hx y hy hxy
  subst y
  rcases hx with ⟨_habsx, hxsum, hle⟩
  rcases hy with ⟨_habsy, hysum, hlt⟩
  have hsame : hxsum.sum ≈ hysum.sum := repSeriesSum_unique hxsum hysum
  have hltx : regularSeqLtProp hxsum.sum t :=
    regularSeqLtProp_of_left_eventual hsame hlt
  exact regularSeqLtProp_irrefl t (regularSeqLtProp_of_le_of_lt hle hltx)

/-- A-pair level BSet: `({h ≥ t}, {h < t})`. -/
def thm36D_levelBSetC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) : BishopC.BSet X where
  S1 := thm36D_upperSetC h t
  S2 := thm36D_lowerSetC h t
  disj := thm36D_levelSets_disjointC h t

@[simp] theorem thm36D_levelBSetC_S1 {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) :
    (thm36D_levelBSetC h t).S1 = thm36D_upperSetC h t := rfl

@[simp] theorem thm36D_levelBSetC_S2 {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) :
    (thm36D_levelBSetC h t).S2 = thm36D_lowerSetC h t := rfl

/-- `h` has an absolutely convergent point value at `x`, with sum strictly above `t`. -/
def thm36D_upperSetStrictC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) : Set X :=
  {x | ∃ (_habs : RepSeriesSum (fun n => CReal.abs ((h.fn n).toFun x)))
      (hx : RepSeriesSum (fun n => (h.fn n).toFun x)),
      regularSeqLtProp t hx.sum}

/-- `h` has an absolutely convergent point value at `x`, with sum at most `t`. -/
def thm36D_lowerSetWeakC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) : Set X :=
  {x | ∃ (_habs : RepSeriesSum (fun n => CReal.abs ((h.fn n).toFun x)))
      (hx : RepSeriesSum (fun n => (h.fn n).toFun x)),
      RegularSeqLe hx.sum t}

theorem thm36D_levelSetsB_disjointC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) :
    ∀ x ∈ thm36D_upperSetStrictC h t,
      ∀ y ∈ thm36D_lowerSetWeakC h t, x ≠ y := by
  intro x hx y hy hxy
  subst y
  rcases hx with ⟨_habsx, hxsum, hlt⟩
  rcases hy with ⟨_habsy, hysum, hle⟩
  have hsame : hxsum.sum ≈ hysum.sum := repSeriesSum_unique hxsum hysum
  have hlt_y : regularSeqLtProp t hysum.sum :=
    regularSeqLtProp_of_right_eventual hsame hlt
  exact regularSeqLtProp_irrefl t (regularSeqLtProp_of_lt_of_le hlt_y hle)

/-- B-pair level BSet: `({h > t}, {h ≤ t})`. -/
def thm36D_levelBSetStrictC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) : BishopC.BSet X where
  S1 := thm36D_upperSetStrictC h t
  S2 := thm36D_lowerSetWeakC h t
  disj := thm36D_levelSetsB_disjointC h t

@[simp] theorem thm36D_levelBSetStrictC_S1 {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) :
    (thm36D_levelBSetStrictC h t).S1 = thm36D_upperSetStrictC h t := rfl

@[simp] theorem thm36D_levelBSetStrictC_S2 {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (t : CReal) :
    (thm36D_levelBSetStrictC h t).S2 = thm36D_lowerSetWeakC h t := rfl


/-! ## Theorem 3.6-C: smooth-point ramp endpoint sequences (CReal-native) -/

section Thm36CLeft

variable {X : Type*} {S : IntSpaceC X}
variable (h : IntegrableRepC3 S) (a b : CReal)
variable (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
variable (spD : Thm36BSmoothPointDataC h a b hab ha)

/-- 3.6-C smooth point selected outside the 3.5 exception sequence. -/
noncomputable def thm36C_tC : CReal := spD.t

theorem thm36C_a_lt_tC : regularSeqLtProp a (thm36C_tC h a b hab ha spD) := by
  exact spD.a_lt_t

theorem thm36C_t_lt_bC : regularSeqLtProp (thm36C_tC h a b hab ha spD) b := by
  exact spD.t_lt_b

theorem thm36C_t_smoothC :
    (thm36A2_profileDefaultC h hab ha).IsSmoothAtC (thm36C_tC h a b hab ha spD) := by
  exact spD.smooth

/-- Left span `t-a`. -/
noncomputable def thm36C_spanLC : CReal :=
  CReal.sub (thm36C_tC h a b hab ha spD) a

theorem thm36C_spanL_posC :
    regularSeqLtProp CReal.zero (thm36C_spanLC h a b hab ha spD) := by
  unfold thm36C_spanLC
  exact regularSeqLtProp_zero_lt_sub (thm36C_a_lt_tC h a b hab ha spD)

/-- Left starting radius `(t-a)/2`. -/
noncomputable def thm36C_radiusLC : CReal :=
  CReal.mul CReal.half (thm36C_spanLC h a b hab ha spD)

theorem thm36C_radiusL_posC :
    regularSeqLtProp CReal.zero (thm36C_radiusLC h a b hab ha spD) := by
  unfold thm36C_radiusLC
  exact CReal.mul_pos_E CReal.half_pos_E (thm36C_spanL_posC h a b hab ha spD)

theorem thm36C_radiusL_nonnegC :
    RegularSeqLe CReal.zero (thm36C_radiusLC h a b hab ha spD) :=
  regularSeqLe_of_ltPropC (thm36C_radiusL_posC h a b hab ha spD)

theorem thm36C_radiusL_lt_spanC :
    regularSeqLtProp (thm36C_radiusLC h a b hab ha spD)
      (thm36C_spanLC h a b hab ha spD) := by
  unfold thm36C_radiusLC
  exact lemma35Half_mul_lt_selfC (thm36C_spanL_posC h a b hab ha spD)

/-- Geometric left gap `2^{-n} * (t-a)/2`. -/
noncomputable def thm36C_gapLC (n : Nat) : CReal :=
  CReal.mul (halfPow n) (thm36C_radiusLC h a b hab ha spD)

theorem thm36C_gapL_posC (n : Nat) :
    regularSeqLtProp CReal.zero (thm36C_gapLC h a b hab ha spD n) := by
  unfold thm36C_gapLC
  exact CReal.mul_pos_E (regularSeqLtProp_zero_halfPow n)
    (thm36C_radiusL_posC h a b hab ha spD)

theorem thm36C_gapL_nonnegC (n : Nat) :
    RegularSeqLe CReal.zero (thm36C_gapLC h a b hab ha spD n) :=
  regularSeqLe_of_ltPropC (thm36C_gapL_posC h a b hab ha spD n)

theorem thm36C_halfPow_le_oneC (n : Nat) :
    RegularSeqLe (halfPow n) CReal.one := by
  have hpow0 : RegularSeqLe (halfPow n) (halfPow 0) :=
    halfPow_antitone_leC (Nat.zero_le n)
  simpa [halfPow] using hpow0

theorem thm36C_gapL_le_radiusC (n : Nat) :
    RegularSeqLe (thm36C_gapLC h a b hab ha spD n)
      (thm36C_radiusLC h a b hab ha spD) := by
  unfold thm36C_gapLC
  have hmul : RegularSeqLe
      (CReal.mul (halfPow n) (thm36C_radiusLC h a b hab ha spD))
      (CReal.mul CReal.one (thm36C_radiusLC h a b hab ha spD)) :=
    regularSeqLe_mul_right_of_nonnegC (thm36C_halfPow_le_oneC n)
      (regularSeqNonneg_of_zero_le (thm36C_radiusL_nonnegC h a b hab ha spD))
  exact regularSeqLe_of_right_eventual
    (CReal.one_mul (thm36C_radiusLC h a b hab ha spD)) hmul

theorem thm36C_gapL_lt_spanC (n : Nat) :
    regularSeqLtProp (thm36C_gapLC h a b hab ha spD n)
      (thm36C_spanLC h a b hab ha spD) :=
  regularSeqLtProp_of_le_of_lt (thm36C_gapL_le_radiusC h a b hab ha spD n)
    (thm36C_radiusL_lt_spanC h a b hab ha spD)

/-- Ring bridge: `a + ((t-a)-g) ≈ t-g`. -/
theorem thm36C_add_span_sub_gap_equivC (a t gap : CReal) :
    CReal.add a (CReal.sub (CReal.sub t a) gap) ≈ CReal.sub t gap := by
  have hq : mkQuot (CReal.add a (CReal.sub (CReal.sub t a) gap)) =
      mkQuot (CReal.sub t gap) := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change mkQuot a + ((mkQuot t - mkQuot a) - mkQuot gap) = mkQuot t - mkQuot gap
    ring
  exact Quotient.exact hq

/-- Left endpoint level below `t`: `level_n = t - gap_n`. -/
noncomputable def thm36C_levelLC (n : Nat) : CReal :=
  CReal.sub (thm36C_tC h a b hab ha spD) (thm36C_gapLC h a b hab ha spD n)

theorem thm36C_levelL_lt_tC (n : Nat) :
    regularSeqLtProp (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) := by
  unfold thm36C_levelLC
  exact regularSeqLtProp_sub_sigma_selfC (thm36C_tC h a b hab ha spD)
    (thm36C_gapL_posC h a b hab ha spD n)

theorem thm36C_a_lt_levelLC (n : Nat) :
    regularSeqLtProp a (thm36C_levelLC h a b hab ha spD n) := by
  let t := thm36C_tC h a b hab ha spD
  let gap := thm36C_gapLC h a b hab ha spD n
  let span := thm36C_spanLC h a b hab ha spD
  have hgap_span : regularSeqLtProp gap span := by
    simpa [gap, span] using thm36C_gapL_lt_spanC h a b hab ha spD n
  have hdiff_pos : regularSeqLtProp CReal.zero (CReal.sub span gap) :=
    regularSeqLtProp_zero_lt_sub hgap_span
  have hraw : regularSeqLtProp (CReal.add a CReal.zero)
      (CReal.add a (CReal.sub span gap)) :=
    regularSeqLtProp_add_left a CReal.zero (CReal.sub span gap) hdiff_pos
  have hleft : regularSeqLtProp a (CReal.add a (CReal.sub span gap)) :=
    regularSeqLtProp_of_left_eventual (Setoid.symm (CReal.add_zero a)) hraw
  have hright : CReal.add a (CReal.sub span gap) ≈ thm36C_levelLC h a b hab ha spD n := by
    dsimp [span, gap, thm36C_spanLC, thm36C_levelLC]
    exact thm36C_add_span_sub_gap_equivC a t (thm36C_gapLC h a b hab ha spD n)
  exact regularSeqLtProp_of_right_eventual hright hleft

theorem thm36C_levelL_nonnegC (n : Nat) :
    ¬ CReal.ltE (thm36C_levelLC h a b hab ha spD n) CReal.zero := by
  have h0a : regularSeqLtProp CReal.zero a := regularSeqLtProp_zero_of_posData ha
  have h0level : regularSeqLtProp CReal.zero (thm36C_levelLC h a b hab ha spD n) :=
    regularSeqLtProp_trans CReal.zero a (thm36C_levelLC h a b hab ha spD n)
      h0a (thm36C_a_lt_levelLC h a b hab ha spD n)
  intro hlt
  exact regularSeqLtProp_irrefl CReal.zero
    (regularSeqLtProp_trans CReal.zero (thm36C_levelLC h a b hab ha spD n) CReal.zero
      h0level hlt)

noncomputable def thm36C_levelL_t_ltDataC (n : Nat) :
    regularSeqLtData (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) :=
  regularSeqLtData_of_ltPropC (thm36C_levelL_lt_tC h a b hab ha spD n)

noncomputable def thm36C_levelL_t_posDataC (n : Nat) :
    regularSeqLtData CReal.zero
      (CReal.sub (thm36C_tC h a b hab ha spD)
        (thm36C_levelLC h a b hab ha spD n)) :=
  sub_pos_dataC (thm36C_levelL_t_ltDataC h a b hab ha spD n)

noncomputable def thm36C_levelL_t_posEventuallyDataC (n : Nat) :
    PosEventuallyData
      (CReal.sub (thm36C_tC h a b hab ha spD)
        (thm36C_levelLC h a b hab ha spD n)) :=
  regularSeqLtData_zero_to_posEventuallyC
    (thm36C_levelL_t_posDataC h a b hab ha spD n)

/-- Left ramp approaching the smooth point from below. -/
noncomputable def thm36C_rampLC (n : Nat) : IntegrableRepC3 S :=
  thm_3_6_ramp_compC h
    (thm36C_levelLC h a b hab ha spD n)
    (thm36C_tC h a b hab ha spD)
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
    (thm36C_levelL_nonnegC h a b hab ha spD n)

/-- Code-level left ramp for the canonical 3.6 profile. -/
noncomputable def thm36C_rampCodeLC (n : Nat) : Thm36A2CodeC a b :=
  Thm36A2CodeC.ramp
    (thm36C_levelLC h a b hab ha spD n)
    (thm36C_tC h a b hab ha spD)
    (regularSeqLe_of_ltPropC (thm36C_a_lt_levelLC h a b hab ha spD n))
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
    (regularSeqLe_of_ltPropC (thm36C_t_lt_bC h a b hab ha spD))

end Thm36CLeft

section Thm36CRight

variable {X : Type*} {S : IntSpaceC X}
variable (h : IntegrableRepC3 S) (a b : CReal)
variable (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
variable (spD : Thm36BSmoothPointDataC h a b hab ha)

/-- Right span `b-t`. -/
noncomputable def thm36C_spanRC : CReal :=
  CReal.sub b (thm36C_tC h a b hab ha spD)

theorem thm36C_spanR_posC :
    regularSeqLtProp CReal.zero (thm36C_spanRC h a b hab ha spD) := by
  unfold thm36C_spanRC
  exact regularSeqLtProp_zero_lt_sub (thm36C_t_lt_bC h a b hab ha spD)

/-- Right starting radius `(b-t)/2`. -/
noncomputable def thm36C_radiusRC : CReal :=
  CReal.mul CReal.half (thm36C_spanRC h a b hab ha spD)

theorem thm36C_radiusR_posC :
    regularSeqLtProp CReal.zero (thm36C_radiusRC h a b hab ha spD) := by
  unfold thm36C_radiusRC
  exact CReal.mul_pos_E CReal.half_pos_E (thm36C_spanR_posC h a b hab ha spD)

theorem thm36C_radiusR_nonnegC :
    RegularSeqLe CReal.zero (thm36C_radiusRC h a b hab ha spD) :=
  regularSeqLe_of_ltPropC (thm36C_radiusR_posC h a b hab ha spD)

theorem thm36C_radiusR_lt_spanC :
    regularSeqLtProp (thm36C_radiusRC h a b hab ha spD)
      (thm36C_spanRC h a b hab ha spD) := by
  unfold thm36C_radiusRC
  exact lemma35Half_mul_lt_selfC (thm36C_spanR_posC h a b hab ha spD)

/-- Geometric right gap `2^{-n} * (b-t)/2`. -/
noncomputable def thm36C_gapRC (n : Nat) : CReal :=
  CReal.mul (halfPow n) (thm36C_radiusRC h a b hab ha spD)

theorem thm36C_gapR_posC (n : Nat) :
    regularSeqLtProp CReal.zero (thm36C_gapRC h a b hab ha spD n) := by
  unfold thm36C_gapRC
  exact CReal.mul_pos_E (regularSeqLtProp_zero_halfPow n)
    (thm36C_radiusR_posC h a b hab ha spD)

theorem thm36C_gapR_nonnegC (n : Nat) :
    RegularSeqLe CReal.zero (thm36C_gapRC h a b hab ha spD n) :=
  regularSeqLe_of_ltPropC (thm36C_gapR_posC h a b hab ha spD n)

theorem thm36C_gapR_le_radiusC (n : Nat) :
    RegularSeqLe (thm36C_gapRC h a b hab ha spD n)
      (thm36C_radiusRC h a b hab ha spD) := by
  unfold thm36C_gapRC
  have hmul : RegularSeqLe
      (CReal.mul (halfPow n) (thm36C_radiusRC h a b hab ha spD))
      (CReal.mul CReal.one (thm36C_radiusRC h a b hab ha spD)) :=
    regularSeqLe_mul_right_of_nonnegC (thm36C_halfPow_le_oneC n)
      (regularSeqNonneg_of_zero_le (thm36C_radiusR_nonnegC h a b hab ha spD))
  exact regularSeqLe_of_right_eventual
    (CReal.one_mul (thm36C_radiusRC h a b hab ha spD)) hmul

theorem thm36C_gapR_lt_spanC (n : Nat) :
    regularSeqLtProp (thm36C_gapRC h a b hab ha spD n)
      (thm36C_spanRC h a b hab ha spD) :=
  regularSeqLtProp_of_le_of_lt (thm36C_gapR_le_radiusC h a b hab ha spD n)
    (thm36C_radiusR_lt_spanC h a b hab ha spD)

/-- Ring bridge: `t + (b-t) ≈ b`. -/
theorem thm36C_add_spanR_equivC (t b : CReal) :
    CReal.add t (CReal.sub b t) ≈ b := by
  have hq : mkQuot (CReal.add t (CReal.sub b t)) = mkQuot b := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change mkQuot t + (mkQuot b - mkQuot t) = mkQuot b
    ring
  exact Quotient.exact hq

/-- Right endpoint level above `t`: `level_n = t + gap_n`. -/
noncomputable def thm36C_levelRC (n : Nat) : CReal :=
  CReal.add (thm36C_tC h a b hab ha spD) (thm36C_gapRC h a b hab ha spD n)

theorem thm36C_t_lt_levelRC (n : Nat) :
    regularSeqLtProp (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) := by
  unfold thm36C_levelRC
  exact regularSeqLtProp_self_add_sigmaC (thm36C_tC h a b hab ha spD)
    (thm36C_gapR_posC h a b hab ha spD n)

theorem thm36C_levelR_lt_bC (n : Nat) :
    regularSeqLtProp (thm36C_levelRC h a b hab ha spD n) b := by
  let t := thm36C_tC h a b hab ha spD
  let gap := thm36C_gapRC h a b hab ha spD n
  let span := thm36C_spanRC h a b hab ha spD
  have hgap_span : regularSeqLtProp gap span := by
    simpa [gap, span] using thm36C_gapR_lt_spanC h a b hab ha spD n
  have hraw : regularSeqLtProp (CReal.add t gap) (CReal.add t span) :=
    regularSeqLtProp_add_left t gap span hgap_span
  have hright : CReal.add t span ≈ b := by
    dsimp [span, thm36C_spanRC]
    exact thm36C_add_spanR_equivC t b
  exact regularSeqLtProp_of_right_eventual hright hraw

theorem thm36C_t_nonnegC :
    ¬ CReal.ltE (thm36C_tC h a b hab ha spD) CReal.zero := by
  have h0a : regularSeqLtProp CReal.zero a := regularSeqLtProp_zero_of_posData ha
  have h0t : regularSeqLtProp CReal.zero (thm36C_tC h a b hab ha spD) :=
    regularSeqLtProp_trans CReal.zero a (thm36C_tC h a b hab ha spD)
      h0a (thm36C_a_lt_tC h a b hab ha spD)
  intro hlt
  exact regularSeqLtProp_irrefl CReal.zero
    (regularSeqLtProp_trans CReal.zero (thm36C_tC h a b hab ha spD) CReal.zero
      h0t hlt)

theorem thm36C_levelR_nonnegC (n : Nat) :
    ¬ CReal.ltE (thm36C_levelRC h a b hab ha spD n) CReal.zero := by
  have h0t : regularSeqLtProp CReal.zero (thm36C_tC h a b hab ha spD) :=
    regularSeqLtProp_trans CReal.zero a (thm36C_tC h a b hab ha spD)
      (regularSeqLtProp_zero_of_posData ha)
      (thm36C_a_lt_tC h a b hab ha spD)
  have h0level : regularSeqLtProp CReal.zero (thm36C_levelRC h a b hab ha spD n) :=
    regularSeqLtProp_trans CReal.zero (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n)
      h0t (thm36C_t_lt_levelRC h a b hab ha spD n)
  intro hlt
  exact regularSeqLtProp_irrefl CReal.zero
    (regularSeqLtProp_trans CReal.zero (thm36C_levelRC h a b hab ha spD n) CReal.zero
      h0level hlt)

noncomputable def thm36C_t_levelR_ltDataC (n : Nat) :
    regularSeqLtData (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) :=
  regularSeqLtData_of_ltPropC (thm36C_t_lt_levelRC h a b hab ha spD n)

noncomputable def thm36C_t_levelR_posDataC (n : Nat) :
    regularSeqLtData CReal.zero
      (CReal.sub (thm36C_levelRC h a b hab ha spD n)
        (thm36C_tC h a b hab ha spD)) :=
  sub_pos_dataC (thm36C_t_levelR_ltDataC h a b hab ha spD n)

noncomputable def thm36C_t_levelR_posEventuallyDataC (n : Nat) :
    PosEventuallyData
      (CReal.sub (thm36C_levelRC h a b hab ha spD n)
        (thm36C_tC h a b hab ha spD)) :=
  regularSeqLtData_zero_to_posEventuallyC
    (thm36C_t_levelR_posDataC h a b hab ha spD n)

/-- Right ramp approaching the smooth point from above. -/
noncomputable def thm36C_rampRC (n : Nat) : IntegrableRepC3 S :=
  thm_3_6_ramp_compC h
    (thm36C_tC h a b hab ha spD)
    (thm36C_levelRC h a b hab ha spD n)
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
    (thm36C_t_nonnegC h a b hab ha spD)

/-- Code-level right ramp for the canonical 3.6 profile. -/
noncomputable def thm36C_rampCodeRC (n : Nat) : Thm36A2CodeC a b :=
  Thm36A2CodeC.ramp
    (thm36C_tC h a b hab ha spD)
    (thm36C_levelRC h a b hab ha spD n)
    (regularSeqLe_of_ltPropC (thm36C_a_lt_tC h a b hab ha spD))
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
    (regularSeqLe_of_ltPropC (thm36C_levelR_lt_bC h a b hab ha spD n))

end Thm36CRight


/-! ## Theorem 3.6-C: ramp code membership and lambda-integral ABI -/

/-- Function-level left ramp tag used by the default 3.6 profile. -/
noncomputable def thm36C_rampFnLC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) : CReal → CReal :=
  fun y =>
    rampFnC
      (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD)
      y
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)

/-- Function-level right ramp tag used by the default 3.6 profile. -/
noncomputable def thm36C_rampFnRC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) : CReal → CReal :=
  fun y =>
    rampFnC
      (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n)
      y
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)

/-- The left ramp code is in the canonical profile family. -/
theorem thm36C_rampCodeL_memC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) :
    thm36C_rampCodeLC h a b hab ha spD n ∈
      (thm36A2_profileDefaultC h hab ha).F := by
  change thm36C_rampCodeLC h a b hab ha spD n ∈ Set.univ
  trivial

/-- The right ramp code is in the canonical profile family. -/
theorem thm36C_rampCodeR_memC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) :
    thm36C_rampCodeRC h a b hab ha spD n ∈
      (thm36A2_profileDefaultC h hab ha).F := by
  change thm36C_rampCodeRC h a b hab ha spD n ∈ Set.univ
  trivial

@[simp] theorem thm36C_rampCodeL_embedC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) :
    (thm36A2_profileDefaultC h hab ha).embed
        (thm36C_rampCodeLC h a b hab ha spD n) =
      thm36C_rampFnLC h a b hab ha spD n := by
  rfl

@[simp] theorem thm36C_rampCodeR_embedC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) :
    (thm36A2_profileDefaultC h hab ha).embed
        (thm36C_rampCodeRC h a b hab ha spD n) =
      thm36C_rampFnRC h a b hab ha spD n := by
  rfl

/-- At level `n`, the left profile lambda is the integral of the left ramp. -/
theorem thm36C_levelLambda_eq_rampIntegralLC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) :
    (thm36A2_profileDefaultC h hab ha).lambda
        (thm36C_rampCodeLC h a b hab ha spD n) =
      (thm36C_rampLC h a b hab ha spD n).integral := by
  rfl

/-- At level `n`, the right profile lambda is the integral of the right ramp. -/
theorem thm36C_levelLambda_eq_rampIntegralRC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) (n : Nat) :
    (thm36A2_profileDefaultC h hab ha).lambda
        (thm36C_rampCodeRC h a b hab ha spD n) =
      (thm36C_rampRC h a b hab ha spD n).integral := by
  rfl



/-! ## Theorem 3.6-C: smooth lambda control for ramp sequences (Prop-level) -/

section Thm36CSmoothLambda

variable {X : Type*} {S : IntSpaceC X}
variable (h : IntegrableRepC3 S) (a b : CReal)
variable (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
variable (spD : Thm36BSmoothPointDataC h a b hab ha)

/-- Apartness of the selected 3.6-C point from the 3.5 exceptional sequence. -/
theorem thm36C_apartSeqC (n : Nat) :
    regularSeqLtProp CReal.zero
      (CReal.abs (CReal.sub (thm36C_tC h a b hab ha spD)
        (thm36ExceptionSeqC h hab ha n))) := by
  simpa [thm36C_tC] using spD.apart n

/-- The concrete smooth limiting value attached to the selected 3.6-C point. -/
noncomputable def thm36C_selectedLambdaBarC : CReal :=
  thm36C_lambdaBarC h hab ha (thm36C_tC h a b hab ha spD)
    (regularSeqLe_of_ltPropC (thm36C_a_lt_tC h a b hab ha spD))
    (regularSeqLe_of_ltPropC (thm36C_t_lt_bC h a b hab ha spD))
    (thm36C_apartSeqC h a b hab ha spD)

/-- Epsilon-delta smoothness spec for the concrete `thm36C_selectedLambdaBarC`. -/
theorem thm36C_lambdaBar_specC (eps : CReal)
    (heps : regularSeqLtProp CReal.zero eps) :
    ∃ delta : CReal,
      regularSeqLtProp CReal.zero delta ∧
        ∀ f ∈ (thm36A2_profileDefaultC h hab ha).F,
          (∀ x : CReal,
            RegularSeqLe (CReal.add (thm36C_tC h a b hab ha spD) delta) x →
              (thm36A2_profileDefaultC h hab ha).embed f x ≈ CReal.one) →
          (∀ x : CReal,
            RegularSeqLe x (CReal.sub (thm36C_tC h a b hab ha spD) delta) →
              (thm36A2_profileDefaultC h hab ha).embed f x ≈ CReal.zero) →
          regularSeqLtProp
            (CReal.abs (CReal.sub ((thm36A2_profileDefaultC h hab ha).lambda f)
              (thm36C_selectedLambdaBarC h a b hab ha spD))) eps := by
  simpa [thm36C_selectedLambdaBarC, thm36C_lambdaBarC] using
    thm_3_5_smooth_at_seq_specC (thm36A2_profileDefaultC h hab ha)
      (thm36C_tC h a b hab ha spD)
      (regularSeqLe_of_ltPropC (thm36C_a_lt_tC h a b hab ha spD))
      (regularSeqLe_of_ltPropC (thm36C_t_lt_bC h a b hab ha spD))
      (thm36C_apartSeqC h a b hab ha spD) eps heps

/-- Left dyadic gaps are antitone. -/
theorem thm36C_gapL_antitoneC {m n : Nat} (hmn : m ≤ n) :
    RegularSeqLe (thm36C_gapLC h a b hab ha spD n)
      (thm36C_gapLC h a b hab ha spD m) := by
  unfold thm36C_gapLC
  exact regularSeqLe_mul_right_of_nonnegC (halfPow_antitone_leC hmn)
    (regularSeqNonneg_of_zero_le (thm36C_radiusL_nonnegC h a b hab ha spD))

/-- Right dyadic gaps are antitone. -/
theorem thm36C_gapR_antitoneC {m n : Nat} (hmn : m ≤ n) :
    RegularSeqLe (thm36C_gapRC h a b hab ha spD n)
      (thm36C_gapRC h a b hab ha spD m) := by
  unfold thm36C_gapRC
  exact regularSeqLe_mul_right_of_nonnegC (halfPow_antitone_leC hmn)
    (regularSeqNonneg_of_zero_le (thm36C_radiusR_nonnegC h a b hab ha spD))

/-- Prop-level eventual smallness of the left dyadic gap. -/
theorem thm36C_gapL_eventually_ltPropC (delta : CReal)
    (hdelta : regularSeqLtProp CReal.zero delta) :
    ∃ N : Nat, regularSeqLtProp (thm36C_gapLC h a b hab ha spD N) delta := by
  let radius := thm36C_radiusLC h a b hab ha spD
  let hradData : PosEventuallyData radius :=
    regularSeqLtData_zero_to_posEventuallyC
      (regularSeqLtData_of_ltPropC (thm36C_radiusL_posC h a b hab ha spD))
  let inv := CReal.invPos radius hradData
  have hinv_pos : regularSeqLtProp CReal.zero inv :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData radius hradData)
  have hq : regularSeqLtProp CReal.zero (CReal.mul delta inv) :=
    CReal.mul_pos_E hdelta hinv_pos
  obtain ⟨N, hN⟩ := posC_imp_halfPow_lt hq
  refine ⟨N, ?_⟩
  have hmul : regularSeqLtProp (CReal.mul (halfPow N) radius)
      (CReal.mul (CReal.mul delta inv) radius) :=
    regularSeqLtProp_mul_right_of_posC hN (thm36C_radiusL_posC h a b hab ha spD)
  have hright : CReal.mul (CReal.mul delta inv) radius ≈ delta := by
    have hcomm : CReal.mul (CReal.mul delta inv) radius ≈
        CReal.mul radius (CReal.mul delta inv) :=
      CReal.mul_comm (CReal.mul delta inv) radius
    exact Setoid.trans hcomm (mul_invPos_scale_cancelC radius delta hradData)
  exact regularSeqLtProp_of_right_eventual hright hmul

/-- Prop-level eventual smallness of the right dyadic gap. -/
theorem thm36C_gapR_eventually_ltPropC (delta : CReal)
    (hdelta : regularSeqLtProp CReal.zero delta) :
    ∃ N : Nat, regularSeqLtProp (thm36C_gapRC h a b hab ha spD N) delta := by
  let radius := thm36C_radiusRC h a b hab ha spD
  let hradData : PosEventuallyData radius :=
    regularSeqLtData_zero_to_posEventuallyC
      (regularSeqLtData_of_ltPropC (thm36C_radiusR_posC h a b hab ha spD))
  let inv := CReal.invPos radius hradData
  have hinv_pos : regularSeqLtProp CReal.zero inv :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData radius hradData)
  have hq : regularSeqLtProp CReal.zero (CReal.mul delta inv) :=
    CReal.mul_pos_E hdelta hinv_pos
  obtain ⟨N, hN⟩ := posC_imp_halfPow_lt hq
  refine ⟨N, ?_⟩
  have hmul : regularSeqLtProp (CReal.mul (halfPow N) radius)
      (CReal.mul (CReal.mul delta inv) radius) :=
    regularSeqLtProp_mul_right_of_posC hN (thm36C_radiusR_posC h a b hab ha spD)
  have hright : CReal.mul (CReal.mul delta inv) radius ≈ delta := by
    have hcomm : CReal.mul (CReal.mul delta inv) radius ≈
        CReal.mul radius (CReal.mul delta inv) :=
      CReal.mul_comm (CReal.mul delta inv) radius
    exact Setoid.trans hcomm (mul_invPos_scale_cancelC radius delta hradData)
  exact regularSeqLtProp_of_right_eventual hright hmul

/-- DATA-modulus version of right-gap eventual smallness.
    The modulus is computed from DATA positivity of `delta`; no Prop-valued
    existence is eliminated. -/
noncomputable def thm36C_gapR_eventualSmallDataC (delta : CReal)
    (hdelta : PosEventuallyData delta) :
    { N : Nat // regularSeqLtProp (thm36C_gapRC h a b hab ha spD N) delta } := by
  let radius := thm36C_radiusRC h a b hab ha spD
  let chosen :=
    lemma34WidthScaleEventualSmallDataC_standard
      (a := CReal.zero) (b := radius) delta hdelta
  refine ⟨chosen.val, ?_⟩
  have hchosen :
      regularSeqLtProp
        (lemma34WidthScaleC CReal.zero radius chosen.val) delta :=
    chosen.property
  have heq :
      thm36C_gapRC h a b hab ha spD chosen.val ≈
        lemma34WidthScaleC CReal.zero radius chosen.val := by
    unfold thm36C_gapRC lemma34WidthScaleC radius
    calc
      CReal.mul (halfPow chosen.val) (thm36C_radiusRC h a b hab ha spD)
          ≈ CReal.mul (thm36C_radiusRC h a b hab ha spD) (halfPow chosen.val) :=
            CReal.mul_comm (halfPow chosen.val) (thm36C_radiusRC h a b hab ha spD)
      _ ≈ CReal.mul (CReal.sub (thm36C_radiusRC h a b hab ha spD) CReal.zero)
            (halfPow chosen.val) :=
            CReal.mul_respects_equiv _ _ _ _
              (Setoid.symm (CReal.sub_zeroC (thm36C_radiusRC h a b hab ha spD)))
              (Setoid.refl (halfPow chosen.val))
  exact regularSeqLtProp_of_left_eventual heq hchosen

/-- DATA-modulus version of left-gap eventual smallness.
    This is the left-ramp analogue of `thm36C_gapR_eventualSmallDataC`. -/
noncomputable def thm36C_gapL_eventualSmallDataC (delta : CReal)
    (hdelta : PosEventuallyData delta) :
    { N : Nat // regularSeqLtProp (thm36C_gapLC h a b hab ha spD N) delta } := by
  let radius := thm36C_radiusLC h a b hab ha spD
  let chosen :=
    lemma34WidthScaleEventualSmallDataC_standard
      (a := CReal.zero) (b := radius) delta hdelta
  refine ⟨chosen.val, ?_⟩
  have hchosen :
      regularSeqLtProp
        (lemma34WidthScaleC CReal.zero radius chosen.val) delta :=
    chosen.property
  have heq :
      thm36C_gapLC h a b hab ha spD chosen.val ≈
        lemma34WidthScaleC CReal.zero radius chosen.val := by
    unfold thm36C_gapLC lemma34WidthScaleC radius
    calc
      CReal.mul (halfPow chosen.val) (thm36C_radiusLC h a b hab ha spD)
          ≈ CReal.mul (thm36C_radiusLC h a b hab ha spD) (halfPow chosen.val) :=
            CReal.mul_comm (halfPow chosen.val) (thm36C_radiusLC h a b hab ha spD)
      _ ≈ CReal.mul (CReal.sub (thm36C_radiusLC h a b hab ha spD) CReal.zero)
            (halfPow chosen.val) :=
            CReal.mul_respects_equiv _ _ _ _
              (Setoid.symm (CReal.sub_zeroC (thm36C_radiusLC h a b hab ha spD)))
              (Setoid.refl (halfPow chosen.val))
  exact regularSeqLtProp_of_left_eventual heq hchosen

/-- Left ramp lambda values are eventually close to the selected `lambdaBar` (Prop-level). -/
theorem thm36C_rampLambdaL_eventually_closeC (k : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      regularSeqLtProp
        (CReal.abs (CReal.sub
          ((thm36A2_profileDefaultC h hab ha).lambda
            (thm36C_rampCodeLC h a b hab ha spD n))
          (thm36C_selectedLambdaBarC h a b hab ha spD)))
        (halfPow k) := by
  obtain ⟨delta, hdelta, hsmooth⟩ :=
    thm36C_lambdaBar_specC h a b hab ha spD (halfPow k)
      (regularSeqLtProp_zero_halfPow k)
  obtain ⟨N, hN⟩ := thm36C_gapL_eventually_ltPropC h a b hab ha spD delta hdelta
  refine ⟨N, ?_⟩
  intro n hNn
  have hgapLe : RegularSeqLe (thm36C_gapLC h a b hab ha spD n)
      (thm36C_gapLC h a b hab ha spD N) :=
    thm36C_gapL_antitoneC h a b hab ha spD hNn
  have hgap : regularSeqLtProp (thm36C_gapLC h a b hab ha spD n) delta :=
    regularSeqLtProp_of_le_of_lt hgapLe hN
  apply hsmooth (thm36C_rampCodeLC h a b hab ha spD n)
    (thm36C_rampCodeL_memC h a b hab ha spD n)
  · intro x htx
    change rampFnC (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) ≈ CReal.one
    have ht_tdelta : RegularSeqLe (thm36C_tC h a b hab ha spD)
        (CReal.add (thm36C_tC h a b hab ha spD) delta) :=
      regularSeqLe_self_add_of_nonneg (thm36C_tC h a b hab ha spD) delta
        (regularSeqLe_of_ltPropC hdelta)
    exact rampFnC_one (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans ht_tdelta htx)
  · intro x hxt
    change rampFnC (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) ≈ CReal.zero
    have hgapLeDelta : RegularSeqLe (thm36C_gapLC h a b hab ha spD n) delta :=
      regularSeqLe_of_ltPropC hgap
    have htdelta_le_level : RegularSeqLe
        (CReal.sub (thm36C_tC h a b hab ha spD) delta)
        (thm36C_levelLC h a b hab ha spD n) := by
      simpa [thm36C_levelLC] using
        regularSeqLe_subSeq_right (thm36C_tC h a b hab ha spD) hgapLeDelta
    exact rampFnC_zero (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans hxt htdelta_le_level)

/-- Right ramp lambda values are eventually close to the selected `lambdaBar` (Prop-level). -/
theorem thm36C_rampLambdaR_eventually_closeC (k : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      regularSeqLtProp
        (CReal.abs (CReal.sub
          ((thm36A2_profileDefaultC h hab ha).lambda
            (thm36C_rampCodeRC h a b hab ha spD n))
          (thm36C_selectedLambdaBarC h a b hab ha spD)))
        (halfPow k) := by
  obtain ⟨delta, hdelta, hsmooth⟩ :=
    thm36C_lambdaBar_specC h a b hab ha spD (halfPow k)
      (regularSeqLtProp_zero_halfPow k)
  obtain ⟨N, hN⟩ := thm36C_gapR_eventually_ltPropC h a b hab ha spD delta hdelta
  refine ⟨N, ?_⟩
  intro n hNn
  have hgapLe : RegularSeqLe (thm36C_gapRC h a b hab ha spD n)
      (thm36C_gapRC h a b hab ha spD N) :=
    thm36C_gapR_antitoneC h a b hab ha spD hNn
  have hgap : regularSeqLtProp (thm36C_gapRC h a b hab ha spD n) delta :=
    regularSeqLtProp_of_le_of_lt hgapLe hN
  apply hsmooth (thm36C_rampCodeRC h a b hab ha spD n)
    (thm36C_rampCodeR_memC h a b hab ha spD n)
  · intro x htx
    change rampFnC (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) ≈ CReal.one
    have hgapLeDelta : RegularSeqLe (thm36C_gapRC h a b hab ha spD n) delta :=
      regularSeqLe_of_ltPropC hgap
    have hlevel_le_tdelta : RegularSeqLe
        (thm36C_levelRC h a b hab ha spD n)
        (CReal.add (thm36C_tC h a b hab ha spD) delta) := by
      have htmp : RegularSeqLe
          (CReal.add (thm36C_tC h a b hab ha spD)
            (thm36C_gapRC h a b hab ha spD n))
          (CReal.add (thm36C_tC h a b hab ha spD) delta) :=
        regularSeqLe_add (regularSeqLe_refl (thm36C_tC h a b hab ha spD)) hgapLeDelta
      simpa [thm36C_levelRC] using htmp
    exact rampFnC_one (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans hlevel_le_tdelta htx)
  · intro x hxt
    change rampFnC (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) ≈ CReal.zero
    have htdelta_le_t : RegularSeqLe
        (CReal.sub (thm36C_tC h a b hab ha spD) delta)
        (thm36C_tC h a b hab ha spD) :=
      regularSeqLe_sub_right_self_of_nonneg (thm36C_tC h a b hab ha spD) delta
        (regularSeqLe_of_ltPropC hdelta)
    exact rampFnC_zero (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans hxt htdelta_le_t)

/-- DATA-modulus version of left ramp lambda convergence.
    This is the choice-free version consumed by the A-side signed telescope. -/
noncomputable def thm36C_rampLambdaL_modDataC (k : Nat) :
    { N : Nat // ∀ n : Nat, N ≤ n →
      regularSeqLtProp
        (CReal.abs (CReal.sub
          ((thm36A2_profileDefaultC h hab ha).lambda
            (thm36C_rampCodeLC h a b hab ha spD n))
          (thm36C_selectedLambdaBarC h a b hab ha spD)))
        (halfPow k) } := by
  let D :=
    thm_3_5_smooth_at_seq_dyadicSpecDataC
      (thm36A2_profileDefaultC h hab ha)
      (thm36C_tC h a b hab ha spD)
      (regularSeqLe_of_ltPropC (thm36C_a_lt_tC h a b hab ha spD))
      (regularSeqLe_of_ltPropC (thm36C_t_lt_bC h a b hab ha spD))
      (thm36C_apartSeqC h a b hab ha spD) k
  let delta : CReal := D.val
  have hdelta_pos : regularSeqLtProp CReal.zero delta := D.property.1
  let hdelta_data : PosEventuallyData delta :=
    regularSeqLtData_zero_to_posEventuallyC
      (regularSeqLtData_of_ltPropC hdelta_pos)
  let W := thm36C_gapL_eventualSmallDataC h a b hab ha spD delta hdelta_data
  refine ⟨W.val, ?_⟩
  intro n hWn
  have hgapLe : RegularSeqLe (thm36C_gapLC h a b hab ha spD n)
      (thm36C_gapLC h a b hab ha spD W.val) :=
    thm36C_gapL_antitoneC h a b hab ha spD hWn
  have hgap : regularSeqLtProp (thm36C_gapLC h a b hab ha spD n) delta :=
    regularSeqLtProp_of_le_of_lt hgapLe W.property
  apply D.property.2 (thm36C_rampCodeLC h a b hab ha spD n)
    (thm36C_rampCodeL_memC h a b hab ha spD n)
  · intro x htx
    change rampFnC (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) ≈ CReal.one
    have ht_tdelta : RegularSeqLe (thm36C_tC h a b hab ha spD)
        (CReal.add (thm36C_tC h a b hab ha spD) delta) :=
      regularSeqLe_self_add_of_nonneg (thm36C_tC h a b hab ha spD) delta
        (regularSeqLe_of_ltPropC hdelta_pos)
    exact rampFnC_one (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans ht_tdelta htx)
  · intro x hxt
    change rampFnC (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) ≈ CReal.zero
    have hgapLeDelta : RegularSeqLe (thm36C_gapLC h a b hab ha spD n) delta :=
      regularSeqLe_of_ltPropC hgap
    have htdelta_le_level : RegularSeqLe
        (CReal.sub (thm36C_tC h a b hab ha spD) delta)
        (thm36C_levelLC h a b hab ha spD n) := by
      simpa [thm36C_levelLC] using
        regularSeqLe_subSeq_right (thm36C_tC h a b hab ha spD) hgapLeDelta
    exact rampFnC_zero (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD) x
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans hxt htdelta_le_level)

/-- DATA-modulus version of right ramp lambda convergence.
    This is the choice-free version consumed by the B-side series modulus. -/
noncomputable def thm36C_rampLambdaR_modDataC (k : Nat) :
    { N : Nat // ∀ n : Nat, N ≤ n →
      regularSeqLtProp
        (CReal.abs (CReal.sub
          ((thm36A2_profileDefaultC h hab ha).lambda
            (thm36C_rampCodeRC h a b hab ha spD n))
          (thm36C_selectedLambdaBarC h a b hab ha spD)))
        (halfPow k) } := by
  let D :=
    thm_3_5_smooth_at_seq_dyadicSpecDataC
      (thm36A2_profileDefaultC h hab ha)
      (thm36C_tC h a b hab ha spD)
      (regularSeqLe_of_ltPropC (thm36C_a_lt_tC h a b hab ha spD))
      (regularSeqLe_of_ltPropC (thm36C_t_lt_bC h a b hab ha spD))
      (thm36C_apartSeqC h a b hab ha spD) k
  let delta : CReal := D.val
  have hdelta_pos : regularSeqLtProp CReal.zero delta := D.property.1
  let hdelta_data : PosEventuallyData delta :=
    regularSeqLtData_zero_to_posEventuallyC
      (regularSeqLtData_of_ltPropC hdelta_pos)
  let W := thm36C_gapR_eventualSmallDataC h a b hab ha spD delta hdelta_data
  refine ⟨W.val, ?_⟩
  intro n hWn
  have hgapLe : RegularSeqLe (thm36C_gapRC h a b hab ha spD n)
      (thm36C_gapRC h a b hab ha spD W.val) :=
    thm36C_gapR_antitoneC h a b hab ha spD hWn
  have hgap : regularSeqLtProp (thm36C_gapRC h a b hab ha spD n) delta :=
    regularSeqLtProp_of_le_of_lt hgapLe W.property
  apply D.property.2 (thm36C_rampCodeRC h a b hab ha spD n)
    (thm36C_rampCodeR_memC h a b hab ha spD n)
  · intro x htx
    change rampFnC (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) ≈ CReal.one
    have hgapLeDelta : RegularSeqLe (thm36C_gapRC h a b hab ha spD n) delta :=
      regularSeqLe_of_ltPropC hgap
    have hlevel_le_tdelta : RegularSeqLe
        (thm36C_levelRC h a b hab ha spD n)
        (CReal.add (thm36C_tC h a b hab ha spD) delta) := by
      have htmp : RegularSeqLe
          (CReal.add (thm36C_tC h a b hab ha spD)
            (thm36C_gapRC h a b hab ha spD n))
          (CReal.add (thm36C_tC h a b hab ha spD) delta) :=
        regularSeqLe_add (regularSeqLe_refl (thm36C_tC h a b hab ha spD)) hgapLeDelta
      simpa [thm36C_levelRC] using htmp
    exact rampFnC_one (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans hlevel_le_tdelta htx)
  · intro x hxt
    change rampFnC (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) ≈ CReal.zero
    have htdelta_le_t : RegularSeqLe
        (CReal.sub (thm36C_tC h a b hab ha spD) delta)
        (thm36C_tC h a b hab ha spD) :=
      regularSeqLe_sub_right_self_of_nonneg (thm36C_tC h a b hab ha spD) delta
        (regularSeqLe_of_ltPropC hdelta_pos)
    exact rampFnC_zero (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) x
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
      (regularSeqLe_trans hxt htdelta_le_t)

end Thm36CSmoothLambda


/-! ## Theorem 3.6-D: ramp endpoint classification helpers (Prop-level) -/

section Thm36DRampHelpers

variable {X : Type*} {S : IntSpaceC X}
variable (h : IntegrableRepC3 S) (a b : CReal)
variable (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
variable (spD : Thm36BSmoothPointDataC h a b hab ha)

/-- Ring bridge: `t - (t-y) ≈ y`. -/
theorem thm36D_sub_sub_equivC (t y : CReal) :
    CReal.sub t (CReal.sub t y) ≈ y := by
  have hq : mkQuot (CReal.sub t (CReal.sub t y)) = mkQuot y := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change mkQuot t - (mkQuot t - mkQuot y) = mkQuot y
    ring
  exact Quotient.exact hq

/-- If a CReal sequence tends to `z` and is eventually equivalent to the
constant `c`, then `z ≈ c`. -/
theorem thm36D_tendsto_eventually_constC
    {u : Nat → CReal} {z c : CReal} (H : RepSeriesTendsto u z)
    (N : Nat) (hu : ∀ n : Nat, N ≤ n → u n ≈ c) : z ≈ c := by
  intro k
  let n : Nat := Nat.max N (H.mod k)
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hnmod : H.mod k ≤ n := Nat.le_max_right _ _
  have huz : RepCloseAtGauge (k + 1) (u n) z := H.close k n hnmod
  have huc : RepCloseAtGauge (k + 1) (u n) c := (hu n hnN) (k + 1)
  exact repCloseAtGauge_triangle_succ k (repCloseAtGauge_symm huz) huc

/-- If `uₙ → z` and `y < z`, then some term satisfies `y < u_N`. -/
noncomputable def thm36D_lt_limit_eventuallyC
    {u : Nat → CReal} {y z : CReal} (H : RepSeriesTendsto u z)
    (hyz : regularSeqLtProp y z) : {N : Nat // regularSeqLtProp y (u N)} := by
  have hgap : regularSeqLtProp CReal.zero (CReal.sub z y) :=
    regularSeqLtProp_zero_lt_sub hyz
  let hgapData : PosEventuallyData (CReal.sub z y) :=
    regularSeqLtData_zero_to_posEventuallyC
      (regularSeqLtData_of_ltPropC hgap)
  let W := lemma34WidthScaleEventualSmallDataC_standard
    (a := CReal.zero) (b := CReal.one) (CReal.sub z y) hgapData
  let w : Nat := W.val
  have hw : regularSeqLtProp (halfPow w) (CReal.sub z y) := by
    have hW :
        regularSeqLtProp
          (lemma34WidthScaleC CReal.zero CReal.one w) (CReal.sub z y) := W.property
    have heq : halfPow w ≈ lemma34WidthScaleC CReal.zero CReal.one w := by
      unfold lemma34WidthScaleC
      calc
        halfPow w ≈ CReal.mul CReal.one (halfPow w) :=
          Setoid.symm (CReal.one_mul (halfPow w))
        _ ≈ CReal.mul (CReal.sub CReal.one CReal.zero) (halfPow w) :=
          CReal.mul_respects_equiv _ _ _ _
            (Setoid.symm (CReal.sub_zeroC CReal.one))
            (Setoid.refl (halfPow w))
    exact regularSeqLtProp_of_left_eventual heq hW
  let N : Nat := H.mod w
  have hclose : RepCloseAtGauge (w + 1) (u N) z :=
    H.close w N (Nat.le_refl N)
  have hzu : regularSeqLtProp (CReal.sub z (u N)) (halfPow w) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ w hclose
  have hzy : regularSeqLtProp (CReal.sub z (u N)) (CReal.sub z y) :=
    regularSeqLtProp_trans _ _ _ hzu hw
  exact ⟨N, regularSeqLtProp_sub_left_cancel_revC
    (x := y) (y := u N) (z := z) hzy⟩

/-- Dual limit lemma: if `uₙ → z` and `z < c`, then some term satisfies
`u_N < c`. -/
noncomputable def thm36D_limit_lt_eventuallyC
    {u : Nat → CReal} {z c : CReal} (H : RepSeriesTendsto u z)
    (hzc : regularSeqLtProp z c) : {N : Nat // regularSeqLtProp (u N) c} := by
  have hgap : regularSeqLtProp CReal.zero (CReal.sub c z) :=
    regularSeqLtProp_zero_lt_sub hzc
  let hgapData : PosEventuallyData (CReal.sub c z) :=
    regularSeqLtData_zero_to_posEventuallyC
      (regularSeqLtData_of_ltPropC hgap)
  let W := lemma34WidthScaleEventualSmallDataC_standard
    (a := CReal.zero) (b := CReal.one) (CReal.sub c z) hgapData
  let w : Nat := W.val
  have hw : regularSeqLtProp (halfPow w) (CReal.sub c z) := by
    have hW :
        regularSeqLtProp
          (lemma34WidthScaleC CReal.zero CReal.one w) (CReal.sub c z) := W.property
    have heq : halfPow w ≈ lemma34WidthScaleC CReal.zero CReal.one w := by
      unfold lemma34WidthScaleC
      calc
        halfPow w ≈ CReal.mul CReal.one (halfPow w) :=
          Setoid.symm (CReal.one_mul (halfPow w))
        _ ≈ CReal.mul (CReal.sub CReal.one CReal.zero) (halfPow w) :=
          CReal.mul_respects_equiv _ _ _ _
            (Setoid.symm (CReal.sub_zeroC CReal.one))
            (Setoid.refl (halfPow w))
    exact regularSeqLtProp_of_left_eventual heq hW
  let N : Nat := H.mod w
  have hclose : RepCloseAtGauge (w + 1) (u N) z :=
    H.close w N (Nat.le_refl N)
  have huz : regularSeqLtProp (CReal.sub (u N) z) (halfPow w) := by
    simpa [halfPow, CReal.epsSeq] using
      regularSeqLtProp_sub_of_repClose_succ w (repCloseAtGauge_symm hclose)
  have huc : regularSeqLtProp (CReal.sub (u N) z) (CReal.sub c z) :=
    regularSeqLtProp_trans _ _ _ huz hw
  exact ⟨N, regularSeqLtProp_add_sub_cancel_rightC
    (x := u N) (y := c) (z := z) huc⟩

/-- Left endpoints are monotone increasing. -/
theorem thm36C_levelL_monoC {m n : Nat} (hmn : m ≤ n) :
    RegularSeqLe (thm36C_levelLC h a b hab ha spD m)
      (thm36C_levelLC h a b hab ha spD n) := by
  have hgap : RegularSeqLe (thm36C_gapLC h a b hab ha spD n)
      (thm36C_gapLC h a b hab ha spD m) :=
    thm36C_gapL_antitoneC h a b hab ha spD hmn
  simpa [thm36C_levelLC] using
    regularSeqLe_subSeq_right (thm36C_tC h a b hab ha spD) hgap

/-- Right endpoints are monotone decreasing. -/
theorem thm36C_levelR_antiC {m n : Nat} (hmn : m ≤ n) :
    RegularSeqLe (thm36C_levelRC h a b hab ha spD n)
      (thm36C_levelRC h a b hab ha spD m) := by
  have hgap : RegularSeqLe (thm36C_gapRC h a b hab ha spD n)
      (thm36C_gapRC h a b hab ha spD m) :=
    thm36C_gapR_antitoneC h a b hab ha spD hmn
  simpa [thm36C_levelRC] using
    regularSeqLe_add (regularSeqLe_refl (thm36C_tC h a b hab ha spD)) hgap

/-- If `t ≤ y`, every left ramp is already one at `y`. -/
theorem thm36D_rampL_always_oneC (y : CReal)
    (hty : RegularSeqLe (thm36C_tC h a b hab ha spD) y) (n : Nat) :
    thm36C_rampFnLC h a b hab ha spD n y ≈ CReal.one := by
  change rampFnC (thm36C_levelLC h a b hab ha spD n)
    (thm36C_tC h a b hab ha spD) y
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) ≈ CReal.one
  exact rampFnC_one (thm36C_levelLC h a b hab ha spD n)
    (thm36C_tC h a b hab ha spD) y
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) hty

/-- If `y ≤ t`, every right ramp is still zero at `y`. -/
theorem thm36D_rampR_always_zeroC (y : CReal)
    (hyt : RegularSeqLe y (thm36C_tC h a b hab ha spD)) (n : Nat) :
    thm36C_rampFnRC h a b hab ha spD n y ≈ CReal.zero := by
  change rampFnC (thm36C_tC h a b hab ha spD)
    (thm36C_levelRC h a b hab ha spD n) y
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) ≈ CReal.zero
  exact rampFnC_zero (thm36C_tC h a b hab ha spD)
    (thm36C_levelRC h a b hab ha spD n) y
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) hyt

/-- If `y < t`, late left ramps are zero at `y`. -/
theorem thm36D_rampL_eventually_zeroC (y : CReal)
    (hyt : regularSeqLtProp y (thm36C_tC h a b hab ha spD)) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      thm36C_rampFnLC h a b hab ha spD n y ≈ CReal.zero := by
  let delta := CReal.sub (thm36C_tC h a b hab ha spD) y
  have hdelta : regularSeqLtProp CReal.zero delta := by
    dsimp [delta]
    exact regularSeqLtProp_zero_lt_sub hyt
  obtain ⟨N, hN⟩ := thm36C_gapL_eventually_ltPropC h a b hab ha spD delta hdelta
  refine ⟨N, ?_⟩
  intro n hNn
  have hgapLeN : RegularSeqLe (thm36C_gapLC h a b hab ha spD n)
      (thm36C_gapLC h a b hab ha spD N) :=
    thm36C_gapL_antitoneC h a b hab ha spD hNn
  have hgap : regularSeqLtProp (thm36C_gapLC h a b hab ha spD n) delta :=
    regularSeqLtProp_of_le_of_lt hgapLeN hN
  have hgapLeDelta : RegularSeqLe (thm36C_gapLC h a b hab ha spD n) delta :=
    regularSeqLe_of_ltPropC hgap
  have htdelta_le_level : RegularSeqLe
      (CReal.sub (thm36C_tC h a b hab ha spD) delta)
      (thm36C_levelLC h a b hab ha spD n) := by
    simpa [thm36C_levelLC] using
      regularSeqLe_subSeq_right (thm36C_tC h a b hab ha spD) hgapLeDelta
  have hy_le_level : RegularSeqLe y (thm36C_levelLC h a b hab ha spD n) :=
    regularSeqLe_of_left_eventual (Setoid.symm (thm36D_sub_sub_equivC
      (thm36C_tC h a b hab ha spD) y)) htdelta_le_level
  change rampFnC (thm36C_levelLC h a b hab ha spD n)
    (thm36C_tC h a b hab ha spD) y
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) ≈ CReal.zero
  exact rampFnC_zero (thm36C_levelLC h a b hab ha spD n)
    (thm36C_tC h a b hab ha spD) y
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) hy_le_level

/-- If `t < y`, late right ramps are one at `y`. -/
theorem thm36D_rampR_eventually_oneC (y : CReal)
    (hty : regularSeqLtProp (thm36C_tC h a b hab ha spD) y) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      thm36C_rampFnRC h a b hab ha spD n y ≈ CReal.one := by
  let delta := CReal.sub y (thm36C_tC h a b hab ha spD)
  have hdelta : regularSeqLtProp CReal.zero delta := by
    dsimp [delta]
    exact regularSeqLtProp_zero_lt_sub hty
  obtain ⟨N, hN⟩ := thm36C_gapR_eventually_ltPropC h a b hab ha spD delta hdelta
  refine ⟨N, ?_⟩
  intro n hNn
  have hgapLeN : RegularSeqLe (thm36C_gapRC h a b hab ha spD n)
      (thm36C_gapRC h a b hab ha spD N) :=
    thm36C_gapR_antitoneC h a b hab ha spD hNn
  have hgap : regularSeqLtProp (thm36C_gapRC h a b hab ha spD n) delta :=
    regularSeqLtProp_of_le_of_lt hgapLeN hN
  have hgapLeDelta : RegularSeqLe (thm36C_gapRC h a b hab ha spD n) delta :=
    regularSeqLe_of_ltPropC hgap
  have hlevel_le_tdelta : RegularSeqLe
      (thm36C_levelRC h a b hab ha spD n)
      (CReal.add (thm36C_tC h a b hab ha spD) delta) := by
    have htmp : RegularSeqLe
        (CReal.add (thm36C_tC h a b hab ha spD)
          (thm36C_gapRC h a b hab ha spD n))
        (CReal.add (thm36C_tC h a b hab ha spD) delta) :=
      regularSeqLe_add (regularSeqLe_refl (thm36C_tC h a b hab ha spD)) hgapLeDelta
    simpa [thm36C_levelRC] using htmp
  have hlevel_le_y : RegularSeqLe (thm36C_levelRC h a b hab ha spD n) y :=
    regularSeqLe_of_right_eventual
      (thm36C_add_spanR_equivC (thm36C_tC h a b hab ha spD) y) hlevel_le_tdelta
  change rampFnC (thm36C_tC h a b hab ha spD)
    (thm36C_levelRC h a b hab ha spD n) y
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) ≈ CReal.one
  exact rampFnC_one (thm36C_tC h a b hab ha spD)
    (thm36C_levelRC h a b hab ha spD n) y
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) hlevel_le_y

end Thm36DRampHelpers

/-- Extract the middle lane of a nonnegative 3-way merge series.  The proof
first compares the zero-injected middle lane with the full nonnegative merge,
then reads convergence back along the `3N+3` partial sums. -/
def repSeriesSum_merge3_middle_of_nonnegC {a b c : Nat → CReal}
    (ha : ∀ n, RegularSeqNonneg (a n))
    (hb : ∀ n, RegularSeqNonneg (b n))
    (hc : ∀ n, RegularSeqNonneg (c n))
    (hmerge : RepSeriesSum (bc1_seqMerge3 a b c)) :
    RepSeriesSum b := by
  let z : Nat → CReal := fun _ => CReal.zero
  let inj : Nat → CReal := bc1_seqMerge3 z b z
  have hinj_nonneg : ∀ n, RegularSeqNonneg (inj n) := by
    intro n
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
      subst n
      simpa [inj, z, bc1_seqMerge3_zero] using regularSeqNonneg_zero
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
      subst n
      simpa [inj, z, bc1_seqMerge3_one] using hb k
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
      subst n
      simpa [inj, z, bc1_seqMerge3_two] using regularSeqNonneg_zero
  have hinj_le : ∀ n, RegularSeqLe (inj n) (bc1_seqMerge3 a b c n) := by
    intro n
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
      subst n
      simpa [inj, z, bc1_seqMerge3_zero] using
        regularSeqLe_zero_of_nonneg (ha k)
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
      subst n
      simpa [inj, z, bc1_seqMerge3_one] using regularSeqLe_refl (b k)
    · obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
      subst n
      simpa [inj, z, bc1_seqMerge3_two] using
        regularSeqLe_zero_of_nonneg (hc k)
  let hinj : RepSeriesSum inj :=
    repSeriesSum_comparison hinj_nonneg hinj_le hmerge
  refine
    { sum := hinj.sum
      tends :=
        { mod := fun k => hinj.tends.mod (k + 1)
          close := ?_ } }
  intro k n hn
  have hidx : hinj.tends.mod (k + 1) ≤ 3 * n + 3 := by omega
  have hclose : RepCloseAtGauge (k + 2)
      (regularSeqFinSum inj (3 * n + 3)) hinj.sum :=
    hinj.tends.close (k + 1) (3 * n + 3) hidx
  have hfin_inj :
      regularSeqFinSum b n ≈ regularSeqFinSum inj (3 * n + 3) := by
    have hmerge_fin :
        regularSeqFinSum inj (3 * n + 3) ≈
          CReal.add
            (CReal.add (regularSeqFinSum z (n + 1)) (regularSeqFinSum b n))
            (regularSeqFinSum z n) := by
      simpa [inj] using bc1_finSum_merge3_b z b z n
    have hz1 : regularSeqFinSum z (n + 1) ≈ CReal.zero :=
      regularSeqFinSum_const_eventually_zero CReal.zero
        (relEventually_refl CReal.zero) (n + 1)
    have hz2 : regularSeqFinSum z n ≈ CReal.zero :=
      regularSeqFinSum_const_eventually_zero CReal.zero
        (relEventually_refl CReal.zero) n
    have hzeros :
        CReal.add
            (CReal.add (regularSeqFinSum z (n + 1)) (regularSeqFinSum b n))
            (regularSeqFinSum z n)
          ≈ regularSeqFinSum b n := by
      calc
        CReal.add
            (CReal.add (regularSeqFinSum z (n + 1)) (regularSeqFinSum b n))
            (regularSeqFinSum z n)
            ≈ CReal.add
                (CReal.add CReal.zero (regularSeqFinSum b n)) CReal.zero :=
              addSeq_respects_eventually _ _ _ _ (addSeq_respects_eventually _ _ _ _
                hz1 (relEventually_refl _)) hz2
        _ ≈ CReal.add (regularSeqFinSum b n) CReal.zero :=
              addSeq_respects_eventually _ _ _ _
                (CReal.zero_add (regularSeqFinSum b n)) (relEventually_refl _)
        _ ≈ regularSeqFinSum b n := CReal.add_zero (regularSeqFinSum b n)
    exact relEventually_symm _ _
      (relEventually_trans _ _ _ hmerge_fin hzeros)
  exact repCloseAtGauge_triangle_succ (k + 1)
    (bc1_repClose_of_relEventually hfin_inj (k + 2)) hclose

/-- Absolute convergence of `r.absVal` exposes absolute convergence of `r` at
that point: the middle lane of the three-way merge is the original `r.fn`. -/
noncomputable def IntegrableRepC3_absVal_absSeriesSum_midC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (x : X)
    (habs : RepSeriesSum
      (fun n => absSeq (((r.absVal).fn n).toFun x))) :
    RepSeriesSum (fun n => absSeq ((r.fn n).toFun x)) := by
  let negFn : Nat → BFunC X :=
    fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)
  let aseq : Nat → CReal := fun k => absSeq ((r.absDiffFn k).toFun x)
  let bseq : Nat → CReal := fun k => absSeq ((r.fn k).toFun x)
  let cseq : Nat → CReal := fun k => absSeq ((negFn k).toFun x)
  let hmerge : RepSeriesSum (bc1_seqMerge3 aseq bseq cseq) := by
    refine repSeriesSum_congr
      (by
        simpa [IntegrableRepC3.absVal, negFn] using habs) ?_
    intro n
    change relEventually (bc1_seqMerge3 aseq bseq cseq n)
      (absSeq ((bc1_seqMerge3 r.absDiffFn r.fn negFn n).toFun x))
    have hmap :
        absSeq ((bc1_seqMerge3 r.absDiffFn r.fn negFn n).toFun x) =
          bc1_seqMerge3 aseq bseq cseq n := by
      simpa [aseq, bseq, cseq] using
        bc1_seqMerge3_map (fun g : BFunC X => absSeq (g.toFun x))
          r.absDiffFn r.fn negFn n
    rw [← hmap]
    exact relEventually_refl _
  simpa [bseq] using
    repSeriesSum_merge3_middle_of_nonnegC
      (a := aseq) (b := bseq) (c := cseq)
      (fun k => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe ((r.absDiffFn k).toFun x)))
      (fun k => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe ((r.fn k).toFun x)))
      (fun k => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe ((negFn k).toFun x)))
      hmerge

/-- The canonical absolute-value representative is pointwise nonnegative. -/
theorem IntegrableRepC3_absVal_repNonnegC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) : RepNonnegC r.absVal := by
  intro x habs hx
  let hrabs : RepSeriesSum (fun n => absSeq ((r.fn n).toFun x)) :=
    IntegrableRepC3_absVal_absSeriesSum_midC r x habs
  let hr : RepSeriesSum (fun n => (r.fn n).toFun x) :=
    seriesSum_of_absC hrabs
  obtain ⟨hmodel, hmodel_eq⟩ := r.absVal_signed_value x hr
  have hx_eq : hx.sum ≈ hmodel.sum := repSeriesSum_unique hx hmodel
  have htarget : RegularSeqNonneg (CReal.abs hr.sum) :=
    regularSeqNonneg_of_zero_le (absSeq_nonnegative_regularSeqLe hr.sum)
  exact regularSeqNonneg_of_eventual
    (relEventually_trans _ _ _ hx_eq hmodel_eq) htarget

/-- Absolute convergence of the `cutConstVal` representation exposes the
middle lane, i.e. absolute convergence of the original represented function
at the same point. -/
noncomputable def cutConstVal_absSeriesSum_midC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (ha : ¬ CReal.ltE a CReal.zero)
    (x : X)
    (hcut : RepSeriesSum
      (fun n => absSeq (((r.cutConstVal a ha).fn n).toFun x))) :
    RepSeriesSum (fun n => absSeq ((r.fn n).toFun x)) := by
  let negFn : Nat → BFunC X :=
    fun k => BFunC.smul (CReal.neg CReal.one) (r.fn k)
  let aseq : Nat → CReal := fun k => absSeq ((r.cutConstDiffFn a k).toFun x)
  let bseq : Nat → CReal := fun k => absSeq ((r.fn k).toFun x)
  let cseq : Nat → CReal := fun k => absSeq ((negFn k).toFun x)
  let hmerge : RepSeriesSum (bc1_seqMerge3 aseq bseq cseq) := by
    refine repSeriesSum_congr
      (by
        simpa [IntegrableRepC3.cutConstVal, negFn] using hcut) ?_
    intro n
    change relEventually (bc1_seqMerge3 aseq bseq cseq n)
      (absSeq ((bc1_seqMerge3 (r.cutConstDiffFn a) r.fn negFn n).toFun x))
    have hmap :
        absSeq ((bc1_seqMerge3 (r.cutConstDiffFn a) r.fn negFn n).toFun x) =
          bc1_seqMerge3 aseq bseq cseq n := by
      simpa [aseq, bseq, cseq] using
        bc1_seqMerge3_map (fun g : BFunC X => absSeq (g.toFun x))
          (r.cutConstDiffFn a) r.fn negFn n
    rw [← hmap]
    exact relEventually_refl _
  simpa [bseq] using
    repSeriesSum_merge3_middle_of_nonnegC
      (a := aseq) (b := bseq) (c := cseq)
      (fun k => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe ((r.cutConstDiffFn a k).toFun x)))
      (fun k => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe ((r.fn k).toFun x)))
      (fun k => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe ((negFn k).toFun x)))
      hmerge

/-- Cancel a positive scalar from an absolutely convergent scaled CReal series. -/
noncomputable def thm36D_absSeries_of_pos_smulC
    (c : CReal) (hc : regularSeqLtProp CReal.zero c) (u : Nat → CReal)
    (hscaled : RepSeriesSum (fun n => CReal.abs (CReal.mul c (u n)))) :
    RepSeriesSum (fun n => CReal.abs (u n)) := by
  let hcData : PosEventuallyData c :=
    regularSeqLtData_zero_to_posEventuallyC (regularSeqLtData_of_ltPropC hc)
  have hcnn : ¬ CReal.ltE c CReal.zero := fun hbad =>
    regularSeqLtProp_irrefl CReal.zero
      (regularSeqLtProp_trans CReal.zero c CReal.zero hc hbad)
  let hmul : RepSeriesSum (fun n => CReal.mul c (CReal.abs (u n))) :=
    repSeriesSum_congr hscaled (fun n => by
      have habs : CReal.abs (CReal.mul c (u n)) ≈
          CReal.mul c (CReal.abs (u n)) :=
        Setoid.trans (CReal.abs_mul c (u n))
          (mulSeqConcrete_respects_eventually cRatScalarMulArch
            (CReal.abs c) c (CReal.abs (u n)) (CReal.abs (u n))
            (CReal.abs_of_nonneg_E hcnn) (relEventually_refl _))
      exact relEventually_symm _ _ habs)
  let hinv := repSeriesSum_smul (CReal.invPos c hcData) hmul
  refine repSeriesSum_congr hinv ?_
  intro n
  let inv := CReal.invPos c hcData
  let x := CReal.abs (u n)
  have hcancel : CReal.mul inv (CReal.mul c x) ≈ x := by
    have hq : mkQuot (CReal.mul inv (CReal.mul c x)) = mkQuot x := by
      letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
      have hcancel0 :
          mkQuot (CReal.mul c inv) = mkQuot CReal.one :=
        Quotient.sound (CReal.mul_invPos_eventually_one c hcData)
      have hcancel1 : mkQuot c * mkQuot inv = (1 : CRealQuot) := by
        simpa using hcancel0
      calc
        mkQuot inv * (mkQuot c * mkQuot x)
            = (mkQuot c * mkQuot inv) * mkQuot x := by ring
        _ = (1 : CRealQuot) * mkQuot x := by rw [hcancel1]
        _ = mkQuot x := by ring
    exact Quotient.exact hq
  exact relEventually_symm _ _ hcancel

section Thm36CbCore

variable {X : Type*} {S : IntSpaceC X}
variable (h : IntegrableRepC3 S) (a b : CReal)
variable (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
variable (spD : Thm36BSmoothPointDataC h a b hab ha)

private theorem regularSeqLe_congrC {a a' b b' : CReal}
    (ha : a ≈ a') (hb : b ≈ b') (h : RegularSeqLe a b) :
    RegularSeqLe a' b' := by
  change RegularSeqNonneg (subSeq b' a')
  have hrel : relEventually (subSeq b' a') (subSeq b a) :=
    subSeq_respects_eventually b' b a' a (Setoid.symm hb) (Setoid.symm ha)
  exact regularSeqNonneg_of_eventual hrel h

private theorem mul_assoc_left_invPos_cancelC
    (a x : CReal) (ha : PosEventuallyData a) :
    CReal.mul (CReal.mul a x) (CReal.invPos a ha) ≈ x := by
  have hq : mkQuot (CReal.mul (CReal.mul a x) (CReal.invPos a ha)) =
      mkQuot x := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    have hcancel0 :
        mkQuot (CReal.mul a (CReal.invPos a ha)) = mkQuot CReal.one :=
      Quotient.sound (CReal.mul_invPos_eventually_one a ha)
    have hcancel :
        mkQuot a * mkQuot (CReal.invPos a ha) = (1 : CRealQuot) := by
      simpa using hcancel0
    calc
      (mkQuot a * mkQuot x) * mkQuot (CReal.invPos a ha)
          = (mkQuot a * mkQuot (CReal.invPos a ha)) * mkQuot x := by ring
      _ = (1 : CRealQuot) * mkQuot x := by rw [hcancel]
      _ = mkQuot x := by ring
  exact Quotient.exact hq

private theorem mul_invPos_scale_cancel_leftC
    (a x : CReal) (ha : PosEventuallyData a) :
    CReal.mul a (CReal.mul (CReal.invPos a ha) x) ≈ x := by
  have hq : mkQuot (CReal.mul a (CReal.mul (CReal.invPos a ha) x)) =
      mkQuot x := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    have hcancel0 :
        mkQuot (CReal.mul a (CReal.invPos a ha)) = mkQuot CReal.one :=
      Quotient.sound (CReal.mul_invPos_eventually_one a ha)
    have hcancel :
        mkQuot a * mkQuot (CReal.invPos a ha) = (1 : CRealQuot) := by
      simpa using hcancel0
    calc
      mkQuot a * (mkQuot (CReal.invPos a ha) * mkQuot x)
          = (mkQuot a * mkQuot (CReal.invPos a ha)) * mkQuot x := by ring
      _ = (1 : CRealQuot) * mkQuot x := by rw [hcancel]
      _ = mkQuot x := by ring
  exact Quotient.exact hq

private theorem regularSeqLe_mul_cancel_left_posC {a x y : CReal}
    (ha : PosEventuallyData a)
    (h : RegularSeqLe (CReal.mul a x) (CReal.mul a y)) :
    RegularSeqLe x y := by
  have hinv_pos : regularSeqLtProp CReal.zero (CReal.invPos a ha) :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData a ha)
  have hinv_nn : RegularSeqNonneg (CReal.invPos a ha) :=
    regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC hinv_pos)
  have hmul : RegularSeqLe
      (CReal.mul (CReal.mul a x) (CReal.invPos a ha))
      (CReal.mul (CReal.mul a y) (CReal.invPos a ha)) :=
    regularSeqLe_mul_right_of_nonnegC h hinv_nn
  exact regularSeqLe_congrC
    (mul_assoc_left_invPos_cancelC a x ha)
    (mul_assoc_left_invPos_cancelC a y ha) hmul

/-- Right-endpoint antitonicity of the affine ratio:
if `v ≤ w`, then `(w-t)⁻¹(y-t) ≤ (v-t)⁻¹(y-t)` for `t ≤ y`. -/
theorem thm36Cb_ratio_antitone_rightC
    {t v w y : CReal}
    (hvw : RegularSeqLe v w)
    (htv : PosEventuallyData (CReal.sub v t))
    (htw : PosEventuallyData (CReal.sub w t))
    (hty : RegularSeqLe t y) :
    RegularSeqLe
      (CReal.mul (CReal.invPos (CReal.sub w t) htw) (CReal.sub y t))
      (CReal.mul (CReal.invPos (CReal.sub v t) htv) (CReal.sub y t)) := by
  let A := CReal.sub v t
  let B := CReal.sub w t
  let Y := CReal.sub y t
  let invA := CReal.invPos A htv
  let invB := CReal.invPos B htw
  have hAB : RegularSeqLe A B := by
    simpa [A, B] using
      regularSeqLe_sub_subC (a := v) (b := w) (c := t) (d := t)
        hvw (regularSeqLe_refl t)
  have hYnn : RegularSeqNonneg Y := by
    have hsub : RegularSeqLe (CReal.sub t t) (CReal.sub y t) := by
      exact regularSeqLe_sub_subC (a := t) (b := y) (c := t) (d := t)
        hty (regularSeqLe_refl t)
    exact regularSeqNonneg_of_zero_le
      (regularSeqLe_of_left_eventual
        (relEventually_symm _ _ (subSeq_self_eventually_law t))
        (by simpa [Y] using hsub))
  have hcross : RegularSeqLe (CReal.mul A Y) (CReal.mul B Y) :=
    regularSeqLe_mul_right_of_nonnegC hAB hYnn
  have hleft_eq :
      CReal.mul B (CReal.mul A (CReal.mul invB Y)) ≈ CReal.mul A Y := by
    have hcancel0 : mkQuot (CReal.mul B invB) = mkQuot CReal.one :=
      Quotient.sound (CReal.mul_invPos_eventually_one B htw)
    have hq : mkQuot (CReal.mul B (CReal.mul A (CReal.mul invB Y))) =
        mkQuot (CReal.mul A Y) := by
      letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
      have hcancel : mkQuot B * mkQuot invB = (1 : CRealQuot) := by
        simpa using hcancel0
      calc
        mkQuot B * (mkQuot A * (mkQuot invB * mkQuot Y))
            = (mkQuot B * mkQuot invB) * (mkQuot A * mkQuot Y) := by ring
        _ = (1 : CRealQuot) * (mkQuot A * mkQuot Y) := by rw [hcancel]
        _ = mkQuot A * mkQuot Y := by ring
    exact Quotient.exact hq
  have hB_goal : RegularSeqLe
      (CReal.mul B (CReal.mul A (CReal.mul invB Y)))
      (CReal.mul B Y) :=
    regularSeqLe_congrC (Setoid.symm hleft_eq) (relEventually_refl _) hcross
  have hA_left : RegularSeqLe (CReal.mul A (CReal.mul invB Y)) Y :=
    regularSeqLe_mul_cancel_left_posC htw hB_goal
  have hA_right_eq : CReal.mul A (CReal.mul invA Y) ≈ Y :=
    mul_invPos_scale_cancel_leftC A Y htv
  have hA_goal : RegularSeqLe
      (CReal.mul A (CReal.mul invB Y))
      (CReal.mul A (CReal.mul invA Y)) :=
    regularSeqLe_congrC (relEventually_refl _) (Setoid.symm hA_right_eq) hA_left
  exact regularSeqLe_mul_cancel_left_posC htv hA_goal

set_option maxHeartbeats 1200000 in
-- This unfolds both clamps in `rampFnC`; the quotient arithmetic is small but
-- the CReal min/max transport expands heavily.
theorem rampFnC_betweenC (u v y : CReal)
    (hpos : PosEventuallyData (CReal.sub v u))
    (huy : RegularSeqLe u y) (hyv : RegularSeqLe y v) :
    rampFnC u v y hpos ≈
      CReal.mul (CReal.invPos (CReal.sub v u) hpos) (CReal.sub y u) := by
  let inv := CReal.invPos (CReal.sub v u) hpos
  let prod := CReal.mul inv (CReal.sub y u)
  have hinv_pos : regularSeqLtProp CReal.zero inv :=
    regularSeqLtProp_zero_of_posData (CReal.invPos_posData (CReal.sub v u) hpos)
  have hinv_nn : RegularSeqNonneg inv :=
    regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC hinv_pos)
  have hyu_nn : RegularSeqNonneg (CReal.sub y u) := by
    have hsub : RegularSeqLe (CReal.sub u u) (CReal.sub y u) :=
      regularSeqLe_sub_subC (a := u) (b := y) (c := u) (d := u)
        huy (regularSeqLe_refl u)
    exact regularSeqNonneg_of_zero_le
      (regularSeqLe_of_left_eventual
        (relEventually_symm _ _ (subSeq_self_eventually_law u)) hsub)
  have hprod_nn : RegularSeqNonneg prod := by
    simpa [prod] using CReal.mul_nonneg_E hinv_nn hyu_nn
  have hvu_le : RegularSeqLe (CReal.sub y u) (CReal.sub v u) := by
    exact regularSeqLe_sub_subC (a := y) (b := v) (c := u) (d := u)
      hyv (regularSeqLe_refl u)
  have hprod_le_one : RegularSeqLe prod CReal.one := by
    have hmul : RegularSeqLe prod (CReal.mul inv (CReal.sub v u)) := by
      simpa [prod, inv] using regularSeqLe_mul_left_of_nonnegC hvu_le hinv_nn
    have hcancel : CReal.mul inv (CReal.sub v u) ≈ CReal.one := by
      have hcomm : CReal.mul inv (CReal.sub v u) ≈ CReal.mul (CReal.sub v u) inv := by
        have hq : mkQuot (CReal.mul inv (CReal.sub v u)) =
            mkQuot (CReal.mul (CReal.sub v u) inv) := by
          letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
          change mkQuot inv * mkQuot (CReal.sub v u) =
            mkQuot (CReal.sub v u) * mkQuot inv
          ring
        exact Quotient.exact hq
      exact Setoid.trans hcomm
        (CReal.mul_invPos_eventually_one (CReal.sub v u) hpos)
    exact regularSeqLe_congrC (relEventually_refl _) hcancel hmul
  have hmin : CReal.min prod CReal.one ≈ prod :=
    CReal.min_eq_left_of_leC hprod_le_one
  have hmax :
      CReal.max (CReal.min prod CReal.one) CReal.zero ≈
        CReal.min prod CReal.one := by
    have h0min : RegularSeqLe CReal.zero (CReal.min prod CReal.one) :=
      CReal.le_minC (regularSeqLe_zero_of_nonneg hprod_nn)
        (regularSeqLe_of_ltPropC CReal.one_pos_E)
    exact CReal.max_eq_left_of_leC h0min
  exact Setoid.trans hmax hmin

/-- Fixed-left ramp is antitone in its right endpoint. -/
theorem thm36Cb_rampFn_antitone_rightC
    {t v w : CReal}
    (hvw : RegularSeqLe v w)
    (htv : PosEventuallyData (CReal.sub v t))
    (htw : PosEventuallyData (CReal.sub w t)) :
    ∀ y : CReal,
      RegularSeqLe (rampFnC t w y htw) (rampFnC t v y htv) := by
  intro y
  apply regularSeqLe_of_not_ltQuot
  intro hbad
  have hbad' : regularSeqLtProp (rampFnC t v y htv) (rampFnC t w y htw) := hbad
  have hpos : regularSeqLtProp CReal.zero (rampFnC t w y htw) :=
    regularSeqLtProp_of_le_of_lt (rampFnC_zero_leC t v y htv) hbad'
  have hty_lt : regularSeqLtProp t y := rampFnC_pos_imp t w y htw hpos
  have hlt_one : regularSeqLtProp (rampFnC t v y htv) CReal.one :=
    regularSeqLtProp_of_lt_of_le hbad' (rampFnC_bound t w y htw).2
  have hyv_lt : regularSeqLtProp y v := rampFnC_lt_one_imp t v y htv hlt_one
  have hty : RegularSeqLe t y := regularSeqLe_of_ltPropC hty_lt
  have hyv : RegularSeqLe y v := regularSeqLe_of_ltPropC hyv_lt
  have hyw : RegularSeqLe y w := regularSeqLe_trans hyv hvw
  have hw_eq := rampFnC_betweenC t w y htw hty hyw
  have hv_eq := rampFnC_betweenC t v y htv hty hyv
  have hratio := thm36Cb_ratio_antitone_rightC hvw htv htw hty
  have hle_ramp : RegularSeqLe (rampFnC t w y htw) (rampFnC t v y htv) :=
    regularSeqLe_congrC (Setoid.symm hw_eq) (Setoid.symm hv_eq) hratio
  exact regularSeqLtProp_irrefl (rampFnC t v y htv)
    (regularSeqLtProp_of_lt_of_le hbad' hle_ramp)

/-- B-ramp pointwise monotonicity: `rampB n ≤ rampB (n+1)`. -/
theorem thm36Cb_rampBFn_succ_geC (n : Nat) (y : CReal) :
    RegularSeqLe
      (rampFnC (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD n) y
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n))
      (rampFnC (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD (n + 1)) y
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD (n + 1))) := by
  exact thm36Cb_rampFn_antitone_rightC
    (thm36C_levelR_antiC h a b hab ha spD (Nat.le_succ n))
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD (n + 1))
    (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) y

/-- Cross-ratio inequality used for fixed-right endpoint antitonicity. -/
theorem thm36Ca_cross_ratioC
    {u p y t : CReal} (hup : RegularSeqLe u p) (hyt : RegularSeqLe y t) :
    RegularSeqLe
      (CReal.mul (CReal.sub y p) (CReal.sub t u))
      (CReal.mul (CReal.sub y u) (CReal.sub t p)) := by
  have hpu : RegularSeqNonneg (CReal.sub p u) := by
    simpa [CReal.sub] using hup
  have hty : RegularSeqNonneg (CReal.sub t y) := by
    simpa [CReal.sub] using hyt
  have hprod : RegularSeqNonneg
      (CReal.mul (CReal.sub p u) (CReal.sub t y)) :=
    CReal.mul_nonneg_E hpu hty
  change RegularSeqNonneg
    (subSeq
      (CReal.mul (CReal.sub y u) (CReal.sub t p))
      (CReal.mul (CReal.sub y p) (CReal.sub t u)))
  have hrel :
      subSeq
        (CReal.mul (CReal.sub y u) (CReal.sub t p))
        (CReal.mul (CReal.sub y p) (CReal.sub t u))
        ≈ CReal.mul (CReal.sub p u) (CReal.sub t y) := by
    have hq :
        mkQuot
          (subSeq
            (CReal.mul (CReal.sub y u) (CReal.sub t p))
            (CReal.mul (CReal.sub y p) (CReal.sub t u))) =
        mkQuot (CReal.mul (CReal.sub p u) (CReal.sub t y)) := by
      letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
      change
        ((mkQuot y - mkQuot u) * (mkQuot t - mkQuot p)) -
          ((mkQuot y - mkQuot p) * (mkQuot t - mkQuot u)) =
        (mkQuot p - mkQuot u) * (mkQuot t - mkQuot y)
      ring
    exact Quotient.exact hq
  exact regularSeqNonneg_of_eventual hrel hprod

/-- Fixed-right affine ratio is antitone in the left endpoint. -/
theorem thm36Ca_ratio_antitone_leftC
    {u p y t : CReal}
    (hup : RegularSeqLe u p)
    (hut : PosEventuallyData (CReal.sub t u))
    (hpt : PosEventuallyData (CReal.sub t p))
    (hpy : RegularSeqLe p y) (hyt : RegularSeqLe y t) :
    RegularSeqLe
      (CReal.mul (CReal.invPos (CReal.sub t p) hpt) (CReal.sub y p))
      (CReal.mul (CReal.invPos (CReal.sub t u) hut) (CReal.sub y u)) := by
  let A := CReal.sub t p
  let B := CReal.sub t u
  let Yp := CReal.sub y p
  let Yu := CReal.sub y u
  let invA := CReal.invPos A hpt
  let invB := CReal.invPos B hut
  have hcross : RegularSeqLe (CReal.mul Yp B) (CReal.mul Yu A) := by
    simpa [Yp, Yu, A, B] using thm36Ca_cross_ratioC (u := u) (p := p) (y := y) (t := t) hup hyt
  have hright_eq :
      CReal.mul B (CReal.mul A (CReal.mul invB Yu)) ≈ CReal.mul Yu A := by
    have hcancel0 :
        mkQuot (CReal.mul B invB) = mkQuot CReal.one :=
      Quotient.sound (CReal.mul_invPos_eventually_one B hut)
    have hq :
        mkQuot (CReal.mul B (CReal.mul A (CReal.mul invB Yu))) =
          mkQuot (CReal.mul Yu A) := by
      letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
      have hcancel : mkQuot B * mkQuot invB = (1 : CRealQuot) := by
        simpa using hcancel0
      calc
        mkQuot B * (mkQuot A * (mkQuot invB * mkQuot Yu))
            = (mkQuot B * mkQuot invB) * (mkQuot Yu * mkQuot A) := by ring
        _ = (1 : CRealQuot) * (mkQuot Yu * mkQuot A) := by rw [hcancel]
        _ = mkQuot Yu * mkQuot A := by ring
    exact Quotient.exact hq
  have hcrossB : RegularSeqLe
      (CReal.mul B Yp) (CReal.mul B (CReal.mul A (CReal.mul invB Yu))) :=
    regularSeqLe_congrC
      (CReal.mul_comm Yp B) (Setoid.symm hright_eq) hcross
  have hYp : RegularSeqLe Yp (CReal.mul A (CReal.mul invB Yu)) :=
    regularSeqLe_mul_cancel_left_posC hut hcrossB
  have hleft_eq : CReal.mul A (CReal.mul invA Yp) ≈ Yp :=
    mul_invPos_scale_cancel_leftC A Yp hpt
  have hA : RegularSeqLe
      (CReal.mul A (CReal.mul invA Yp))
      (CReal.mul A (CReal.mul invB Yu)) :=
    regularSeqLe_congrC (Setoid.symm hleft_eq) (relEventually_refl _) hYp
  exact regularSeqLe_mul_cancel_left_posC hpt hA

/-- Fixed-right ramp is antitone in its left endpoint. -/
theorem thm36Ca_rampFn_antitone_leftC
    {u p t : CReal}
    (hup : RegularSeqLe u p)
    (hut : PosEventuallyData (CReal.sub t u))
    (hpt : PosEventuallyData (CReal.sub t p)) :
    ∀ y : CReal,
      RegularSeqLe (rampFnC p t y hpt) (rampFnC u t y hut) := by
  intro y
  apply regularSeqLe_of_not_ltQuot
  intro hbad
  have hbad' : regularSeqLtProp (rampFnC u t y hut) (rampFnC p t y hpt) := hbad
  have hpos : regularSeqLtProp CReal.zero (rampFnC p t y hpt) :=
    regularSeqLtProp_of_le_of_lt (rampFnC_zero_leC u t y hut) hbad'
  have hpy_lt : regularSeqLtProp p y := rampFnC_pos_imp p t y hpt hpos
  have hlt_one : regularSeqLtProp (rampFnC u t y hut) CReal.one :=
    regularSeqLtProp_of_lt_of_le hbad' (rampFnC_bound p t y hpt).2
  have hyt_lt : regularSeqLtProp y t := rampFnC_lt_one_imp u t y hut hlt_one
  have hpy : RegularSeqLe p y := regularSeqLe_of_ltPropC hpy_lt
  have hyt : RegularSeqLe y t := regularSeqLe_of_ltPropC hyt_lt
  have huy : RegularSeqLe u y := regularSeqLe_trans hup hpy
  have hp_eq := rampFnC_betweenC p t y hpt hpy hyt
  have hu_eq := rampFnC_betweenC u t y hut huy hyt
  have hratio := thm36Ca_ratio_antitone_leftC hup hut hpt hpy hyt
  have hle_ramp : RegularSeqLe (rampFnC p t y hpt) (rampFnC u t y hut) :=
    regularSeqLe_congrC (Setoid.symm hp_eq) (Setoid.symm hu_eq) hratio
  exact regularSeqLtProp_irrefl (rampFnC u t y hut)
    (regularSeqLtProp_of_lt_of_le hbad' hle_ramp)

/-- A-ramp pointwise monotonicity: `rampL (n+1) ≤ rampL n`. -/
theorem thm36Ca_rampLFn_succ_leC (n : Nat) (y : CReal) :
    RegularSeqLe
      (rampFnC (thm36C_levelLC h a b hab ha spD (n + 1))
        (thm36C_tC h a b hab ha spD) y
        (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD (n + 1)))
      (rampFnC (thm36C_levelLC h a b hab ha spD n)
        (thm36C_tC h a b hab ha spD) y
        (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)) := by
  exact thm36Ca_rampFn_antitone_leftC
    (thm36C_levelL_monoC h a b hab ha spD (Nat.le_succ n))
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
    (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD (n + 1)) y

private theorem thm36CReal_add_congr_leftC {x y z : CReal} (hxy : x ≈ y) :
    CReal.add x z ≈ CReal.add y z := by
  have hq : mkQuot (CReal.add x z) = mkQuot (CReal.add y z) := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change mkQuot x + mkQuot z = mkQuot y + mkQuot z
    rw [show mkQuot x = mkQuot y from Quotient.sound hxy]
  exact Quotient.exact hq

private theorem thm36CReal_add_congr_rightC {x y z : CReal} (hyz : y ≈ z) :
    CReal.add x y ≈ CReal.add x z := by
  have hq : mkQuot (CReal.add x y) = mkQuot (CReal.add x z) := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change mkQuot x + mkQuot y = mkQuot x + mkQuot z
    rw [show mkQuot y = mkQuot z from Quotient.sound hyz]
  exact Quotient.exact hq

private theorem thm36CReal_add_sub_cancelC (x y : CReal) :
    CReal.add x (CReal.sub y x) ≈ y := by
  have hq : mkQuot (CReal.add x (CReal.sub y x)) = mkQuot y := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change mkQuot x + (mkQuot y - mkQuot x) = mkQuot y
    ring
  exact Quotient.exact hq

private theorem thm36CReal_sub_add_sub_cancelC (base x y : CReal) :
    CReal.add (CReal.sub base x) (CReal.sub x y) ≈ CReal.sub base y := by
  have hq :
      mkQuot (CReal.add (CReal.sub base x) (CReal.sub x y)) =
        mkQuot (CReal.sub base y) := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (mkQuot base - mkQuot x) + (mkQuot x - mkQuot y) =
      mkQuot base - mkQuot y
    ring
  exact Quotient.exact hq

private theorem thm36CReal_two_sub_selfC (x : CReal) :
    CReal.sub (CReal.add x x) x ≈ x := by
  have hq : mkQuot (CReal.sub (CReal.add x x) x) = mkQuot x := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (mkQuot x + mkQuot x) - mkQuot x = mkQuot x
    ring
  exact Quotient.exact hq

private theorem thm36CReal_sub_sub_baseC (base x y : CReal) :
    CReal.sub (CReal.sub base x) (CReal.sub base y) ≈
      CReal.neg (CReal.sub x y) := by
  have hq :
      mkQuot (CReal.sub (CReal.sub base x) (CReal.sub base y)) =
        mkQuot (CReal.neg (CReal.sub x y)) := by
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    change (mkQuot base - mkQuot x) - (mkQuot base - mkQuot y) =
      - (mkQuot x - mkQuot y)
    ring
  exact Quotient.exact hq

/-- B-side signed telescoping term:
`H 0 = rampB 0`, `H (n+1) = rampB (n+1) - rampB n`. -/
noncomputable def thm36Cb_signedTermBC : Nat → IntegrableRepC3 S
  | 0 => thm36C_rampRC h a b hab ha spD 0
  | n + 1 =>
      (thm36C_rampRC h a b hab ha spD (n + 1)).sub
        (thm36C_rampRC h a b hab ha spD n)

/-- Collapse-free B-side term, matching the available `seriesIntegrableC` API. -/
noncomputable def thm36Cb_termBC (n : Nat) : IntegrableRepC3 S :=
  thm36Cb_signedTermBC h a b hab ha spD n

/-- Pointwise B-side signed telescoping term:
`H_0(y)=rampB_0(y)` and
`H_{n+1}(y)=rampB_{n+1}(y)-rampB_n(y)`. -/
noncomputable def thm36Cb_pointTermBC (z : CReal) : Nat → CReal
  | 0 => thm36C_rampFnRC h a b hab ha spD 0 z
  | n + 1 =>
      CReal.sub
        (thm36C_rampFnRC h a b hab ha spD (n + 1) z)
        (thm36C_rampFnRC h a b hab ha spD n z)

/-- Value witness for a B-side ramp representative. -/
noncomputable def thm36Cb_rampB_value_witnessC
    (n : Nat) (x : X)
    (hx : RepSeriesSum (fun m => (h.fn m).toFun x)) :
    {hr : RepSeriesSum
      (fun m => ((thm36C_rampRC h a b hab ha spD n).fn m).toFun x) //
      hr.sum ≈ thm36C_rampFnRC h a b hab ha spD n hx.sum} := by
  simpa [thm36C_rampRC, thm36C_rampFnRC] using
    thm36A1_ramp_comp_value_witnessC h
      (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n)
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
      (thm36C_t_nonnegC h a b hab ha spD) x hx

/-- Value witness for the B-side signed telescope term. -/
noncomputable def thm36Cb_signedTermB_value_witnessC
    (n : Nat) (x : X)
    (hx : RepSeriesSum (fun m => (h.fn m).toFun x)) :
    {hv : RepSeriesSum
      (fun m => ((thm36Cb_signedTermBC h a b hab ha spD n).fn m).toFun x) //
      hv.sum ≈ thm36Cb_pointTermBC h a b hab ha spD hx.sum n} := by
  cases n with
  | zero =>
      let W := thm36Cb_rampB_value_witnessC h a b hab ha spD 0 x hx
      let hv : RepSeriesSum
          (fun m => ((thm36Cb_signedTermBC h a b hab ha spD 0).fn m).toFun x) := by
        simpa [thm36Cb_signedTermBC] using W.val
      refine ⟨hv, ?_⟩
      change W.val.sum ≈ thm36Cb_pointTermBC h a b hab ha spD hx.sum 0
      simpa [thm36Cb_pointTermBC] using W.property
  | succ n =>
      let Wn := thm36Cb_rampB_value_witnessC h a b hab ha spD n x hx
      let Ws := thm36Cb_rampB_value_witnessC h a b hab ha spD (n + 1) x hx
      let hsub : RepSeriesSum
          (fun m => ((thm36Cb_signedTermBC h a b hab ha spD (n + 1)).fn m).toFun x) := by
        simpa [thm36Cb_signedTermBC] using
          sub_seriesSum_valueC3
            (r := thm36C_rampRC h a b hab ha spD (n + 1))
            (r' := thm36C_rampRC h a b hab ha spD n) (x := x) Ws.val Wn.val
      refine ⟨hsub, ?_⟩
      have hsub_sum : hsub.sum ≈ CReal.sub Ws.val.sum Wn.val.sum := by
        change relEventually (CReal.add Ws.val.sum (CReal.neg Wn.val.sum)) _
        exact relEventually_symm _ _
          (subSeq_eq_add_neg_eventually Ws.val.sum Wn.val.sum)
      have hmodel : CReal.sub Ws.val.sum Wn.val.sum ≈
          CReal.sub
            (thm36C_rampFnRC h a b hab ha spD (n + 1) hx.sum)
            (thm36C_rampFnRC h a b hab ha spD n hx.sum) :=
        subSeq_respects_eventually Ws.val.sum
          (thm36C_rampFnRC h a b hab ha spD (n + 1) hx.sum)
          Wn.val.sum
          (thm36C_rampFnRC h a b hab ha spD n hx.sum)
          Ws.property Wn.property
      exact Setoid.trans hsub_sum (by
        simpa [thm36Cb_pointTermBC] using hmodel)

/-- Collapse-free term value witness for the B-side telescope. -/
noncomputable def thm36Cb_termB_value_witnessC
    (n : Nat) (x : X)
    (hx : RepSeriesSum (fun m => (h.fn m).toFun x)) :
    {hv : RepSeriesSum
      (fun m => ((thm36Cb_termBC h a b hab ha spD n).fn m).toFun x) //
      hv.sum ≈ thm36Cb_pointTermBC h a b hab ha spD hx.sum n} := by
  let W := thm36Cb_signedTermB_value_witnessC h a b hab ha spD n x hx
  let hv : RepSeriesSum
      (fun m => ((thm36Cb_termBC h a b hab ha spD n).fn m).toFun x) := by
    simpa [thm36Cb_termBC] using W.val
  refine ⟨hv, ?_⟩
  change W.val.sum ≈ thm36Cb_pointTermBC h a b hab ha spD hx.sum n
  exact W.property

set_option maxHeartbeats 1200000 in
-- Recursive quotient arithmetic in the telescope partial sum needs a larger
-- heartbeat budget than the default.
/-- Pointwise partial sums of the B telescope recover the corresponding
right-ramp value. -/
theorem thm36Cb_partialSum_pointTermBC (z : CReal) :
    ∀ n : Nat,
      regularSeqFinSum (thm36Cb_pointTermBC h a b hab ha spD z) n ≈
        thm36C_rampFnRC h a b hab ha spD n z
  | 0 => by
      rfl
  | n + 1 => by
      have ih := thm36Cb_partialSum_pointTermBC z n
      let prev := thm36C_rampFnRC h a b hab ha spD n z
      let next := thm36C_rampFnRC h a b hab ha spD (n + 1) z
      let ps := regularSeqFinSum (thm36Cb_pointTermBC h a b hab ha spD z) n
      have hleft :
          regularSeqFinSum (thm36Cb_pointTermBC h a b hab ha spD z) (n + 1)
            ≈ CReal.add ps (CReal.sub next prev) := by
        change
          CReal.add ps (thm36Cb_pointTermBC h a b hab ha spD z (n + 1))
            ≈ CReal.add ps (CReal.sub next prev)
        rfl
      have hmid :
          CReal.add ps (CReal.sub next prev) ≈
            CReal.add prev (CReal.sub next prev) :=
        thm36CReal_add_congr_leftC ih
      have hcancel : CReal.add prev (CReal.sub next prev) ≈ next :=
        thm36CReal_add_sub_cancelC prev next
      exact Setoid.trans hleft (Setoid.trans hmid hcancel)

/-- Pointwise partial sums of the actual B terms recover the right-ramp
value at the point value of `h`. -/
theorem thm36Cb_partialSum_termB_valuesC
    (x : X) (hx : RepSeriesSum (fun m => (h.fn m).toFun x))
    (n : Nat) :
    regularSeqFinSum
        (fun j => (thm36Cb_termB_value_witnessC
          h a b hab ha spD j x hx).val.sum) n
      ≈ thm36C_rampFnRC h a b hab ha spD n hx.sum := by
  have hterms : ∀ j : Nat,
      (thm36Cb_termB_value_witnessC h a b hab ha spD j x hx).val.sum
        ≈ thm36Cb_pointTermBC h a b hab ha spD hx.sum j :=
    fun j => (thm36Cb_termB_value_witnessC h a b hab ha spD j x hx).property
  have hfin :
      regularSeqFinSum
          (fun j => (thm36Cb_termB_value_witnessC
            h a b hab ha spD j x hx).val.sum) n
        ≈ regularSeqFinSum (thm36Cb_pointTermBC h a b hab ha spD hx.sum) n :=
    bc1_regularSeqFinSum_congr_terms _ _ hterms n
  exact Setoid.trans hfin
    (thm36Cb_partialSum_pointTermBC h a b hab ha spD hx.sum n)

theorem thm36_normL1_eq_integral_on_fullC {A : Set X}
    (hA : IsFullC S A) (r : IntegrableRepC3 S)
    (hnn : ∀ x, x ∈ A →
      ∀ (hx : RepSeriesSum (fun n => (r.fn n).toFun x)), RegularSeqNonneg hx.sum) :
    r.normL1 ≈ r.integral := by
  change r.absVal.integral ≈ r.integral
  refine regularSeqLe_antisymm_eventuallyC ?_ ?_
  · refine prop_1_11C hA r.absVal r ?_
    intro x hxA hr_abs hr
    obtain ⟨hs_abs, hs_abs_eq⟩ := r.absVal_signed_value x hr
    have huniq : hr_abs.sum ≈ hs_abs.sum := repSeriesSum_unique hr_abs hs_abs
    have hnonneg : RegularSeqNonneg hr.sum := hnn x hxA hr
    have habs_eq : CReal.abs hr.sum ≈ hr.sum := CReal.abs_of_nonneg_E hnonneg
    have hpoint : hr_abs.sum ≈ hr.sum :=
      relEventually_trans _ _ _ huniq
        (relEventually_trans _ _ _ hs_abs_eq habs_eq)
    exact regularSeqLe_of_relEventually hpoint
  · refine prop_1_11C hA r r.absVal ?_
    intro x hxA hr hr_abs
    obtain ⟨hs_abs, hs_abs_eq⟩ := r.absVal_signed_value x hr
    have huniq : hr_abs.sum ≈ hs_abs.sum := repSeriesSum_unique hr_abs hs_abs
    have hnonneg : RegularSeqNonneg hr.sum := hnn x hxA hr
    have habs_eq : CReal.abs hr.sum ≈ hr.sum := CReal.abs_of_nonneg_E hnonneg
    have hpoint : hr_abs.sum ≈ hr.sum :=
      relEventually_trans _ _ _ huniq
        (relEventually_trans _ _ _ hs_abs_eq habs_eq)
    exact regularSeqLe_of_relEventually (relEventually_symm _ _ hpoint)

/-- A-side signed telescoping term:
`H 0 = rampL 0`, `H (n+1) = rampL (n+1) - rampL n`. -/
noncomputable def thm36Ca_signedTermAC : Nat → IntegrableRepC3 S
  | 0 => thm36C_rampLC h a b hab ha spD 0
  | n + 1 =>
      (thm36C_rampLC h a b hab ha spD (n + 1)).sub
        (thm36C_rampLC h a b hab ha spD n)

/-- A-side positive decrement `rampL n - rampL (n+1)`. -/
noncomputable def thm36Ca_decrementAC (n : Nat) : IntegrableRepC3 S :=
  (thm36C_rampLC h a b hab ha spD n).sub
    (thm36C_rampLC h a b hab ha spD (n + 1))

/-- Collapse-free A-side term, matching the available `seriesIntegrableC` API. -/
noncomputable def thm36Ca_termAC (n : Nat) : IntegrableRepC3 S :=
  thm36Ca_signedTermAC h a b hab ha spD n

/-- Pointwise A-side signed telescoping term:
`H_0(y)=rampL_0(y)` and
`H_{n+1}(y)=rampL_{n+1}(y)-rampL_n(y)`. -/
noncomputable def thm36Ca_pointTermAC (z : CReal) : Nat → CReal
  | 0 => thm36C_rampFnLC h a b hab ha spD 0 z
  | n + 1 =>
      CReal.sub
        (thm36C_rampFnLC h a b hab ha spD (n + 1) z)
        (thm36C_rampFnLC h a b hab ha spD n z)

/-- Value witness for an A-side left-ramp representative. -/
noncomputable def thm36Ca_rampA_value_witnessC
    (n : Nat) (x : X)
    (hx : RepSeriesSum (fun m => (h.fn m).toFun x)) :
    {hr : RepSeriesSum
      (fun m => ((thm36C_rampLC h a b hab ha spD n).fn m).toFun x) //
      hr.sum ≈ thm36C_rampFnLC h a b hab ha spD n hx.sum} := by
  simpa [thm36C_rampLC, thm36C_rampFnLC] using
    thm36A1_ramp_comp_value_witnessC h
      (thm36C_levelLC h a b hab ha spD n)
      (thm36C_tC h a b hab ha spD)
      (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
      (thm36C_levelL_nonnegC h a b hab ha spD n) x hx

/-- Value witness for the A-side signed telescope term. -/
noncomputable def thm36Ca_signedTermA_value_witnessC
    (n : Nat) (x : X)
    (hx : RepSeriesSum (fun m => (h.fn m).toFun x)) :
    {hv : RepSeriesSum
      (fun m => ((thm36Ca_signedTermAC h a b hab ha spD n).fn m).toFun x) //
      hv.sum ≈ thm36Ca_pointTermAC h a b hab ha spD hx.sum n} := by
  cases n with
  | zero =>
      let W := thm36Ca_rampA_value_witnessC h a b hab ha spD 0 x hx
      let hv : RepSeriesSum
          (fun m => ((thm36Ca_signedTermAC h a b hab ha spD 0).fn m).toFun x) := by
        simpa [thm36Ca_signedTermAC] using W.val
      refine ⟨hv, ?_⟩
      change W.val.sum ≈ thm36Ca_pointTermAC h a b hab ha spD hx.sum 0
      simpa [thm36Ca_pointTermAC] using W.property
  | succ n =>
      let Wn := thm36Ca_rampA_value_witnessC h a b hab ha spD n x hx
      let Ws := thm36Ca_rampA_value_witnessC h a b hab ha spD (n + 1) x hx
      let hsub : RepSeriesSum
          (fun m => ((thm36Ca_signedTermAC h a b hab ha spD (n + 1)).fn m).toFun x) := by
        simpa [thm36Ca_signedTermAC] using
          sub_seriesSum_valueC3
            (r := thm36C_rampLC h a b hab ha spD (n + 1))
            (r' := thm36C_rampLC h a b hab ha spD n) (x := x) Ws.val Wn.val
      refine ⟨hsub, ?_⟩
      have hsub_sum : hsub.sum ≈ CReal.sub Ws.val.sum Wn.val.sum := by
        change relEventually (CReal.add Ws.val.sum (CReal.neg Wn.val.sum)) _
        exact relEventually_symm _ _
          (subSeq_eq_add_neg_eventually Ws.val.sum Wn.val.sum)
      have hmodel : CReal.sub Ws.val.sum Wn.val.sum ≈
          CReal.sub
            (thm36C_rampFnLC h a b hab ha spD (n + 1) hx.sum)
            (thm36C_rampFnLC h a b hab ha spD n hx.sum) :=
        subSeq_respects_eventually Ws.val.sum
          (thm36C_rampFnLC h a b hab ha spD (n + 1) hx.sum)
          Wn.val.sum
          (thm36C_rampFnLC h a b hab ha spD n hx.sum)
          Ws.property Wn.property
      exact Setoid.trans hsub_sum (by
        simpa [thm36Ca_pointTermAC] using hmodel)

/-- Collapse-free term value witness for the A-side telescope. -/
noncomputable def thm36Ca_termA_value_witnessC
    (n : Nat) (x : X)
    (hx : RepSeriesSum (fun m => (h.fn m).toFun x)) :
    {hv : RepSeriesSum
      (fun m => ((thm36Ca_termAC h a b hab ha spD n).fn m).toFun x) //
      hv.sum ≈ thm36Ca_pointTermAC h a b hab ha spD hx.sum n} := by
  let W := thm36Ca_signedTermA_value_witnessC h a b hab ha spD n x hx
  let hv : RepSeriesSum
      (fun m => ((thm36Ca_termAC h a b hab ha spD n).fn m).toFun x) := by
    simpa [thm36Ca_termAC] using W.val
  refine ⟨hv, ?_⟩
  change W.val.sum ≈ thm36Ca_pointTermAC h a b hab ha spD hx.sum n
  exact W.property

set_option maxHeartbeats 1200000 in
-- Recursive quotient arithmetic in the A-side telescope partial sum needs a
-- larger heartbeat budget than the default.
/-- Pointwise partial sums of the A telescope recover the corresponding
left-ramp value. -/
theorem thm36Ca_partialSum_pointTermAC (z : CReal) :
    ∀ n : Nat,
      regularSeqFinSum (thm36Ca_pointTermAC h a b hab ha spD z) n ≈
        thm36C_rampFnLC h a b hab ha spD n z
  | 0 => by
      rfl
  | n + 1 => by
      have ih := thm36Ca_partialSum_pointTermAC z n
      let prev := thm36C_rampFnLC h a b hab ha spD n z
      let next := thm36C_rampFnLC h a b hab ha spD (n + 1) z
      let ps := regularSeqFinSum (thm36Ca_pointTermAC h a b hab ha spD z) n
      have hleft :
          regularSeqFinSum (thm36Ca_pointTermAC h a b hab ha spD z) (n + 1)
            ≈ CReal.add ps (CReal.sub next prev) := by
        change
          CReal.add ps (thm36Ca_pointTermAC h a b hab ha spD z (n + 1))
            ≈ CReal.add ps (CReal.sub next prev)
        rfl
      have hmid :
          CReal.add ps (CReal.sub next prev) ≈
            CReal.add prev (CReal.sub next prev) :=
        thm36CReal_add_congr_leftC ih
      have hcancel : CReal.add prev (CReal.sub next prev) ≈ next :=
        thm36CReal_add_sub_cancelC prev next
      exact Setoid.trans hleft (Setoid.trans hmid hcancel)

/-- Pointwise partial sums of the actual A terms recover the left-ramp
value at the point value of `h`. -/
theorem thm36Ca_partialSum_termA_valuesC
    (x : X) (hx : RepSeriesSum (fun m => (h.fn m).toFun x))
    (n : Nat) :
    regularSeqFinSum
        (fun j => (thm36Ca_termA_value_witnessC
          h a b hab ha spD j x hx).val.sum) n
      ≈ thm36C_rampFnLC h a b hab ha spD n hx.sum := by
  have hterms : ∀ j : Nat,
      (thm36Ca_termA_value_witnessC h a b hab ha spD j x hx).val.sum
        ≈ thm36Ca_pointTermAC h a b hab ha spD hx.sum j :=
    fun j => (thm36Ca_termA_value_witnessC h a b hab ha spD j x hx).property
  have hfin :
      regularSeqFinSum
          (fun j => (thm36Ca_termA_value_witnessC
            h a b hab ha spD j x hx).val.sum) n
        ≈ regularSeqFinSum (thm36Ca_pointTermAC h a b hab ha spD hx.sum) n :=
    bc1_regularSeqFinSum_congr_terms _ _ hterms n
  exact Setoid.trans hfin
    (thm36Ca_partialSum_pointTermAC h a b hab ha spD hx.sum n)

theorem thm36Ca_rampA_nonneg_on_domainC
    (n : Nat) (x : X) (hxdom : x ∈ h.domain)
    (hr : RepSeriesSum
      (fun m => ((thm36C_rampLC h a b hab ha spD n).fn m).toFun x)) :
    RegularSeqNonneg hr.sum := by
  rcases hxdom with ⟨_hdom, ⟨hxabs⟩⟩
  let hx : RepSeriesSum (fun m => (h.fn m).toFun x) := seriesSum_of_absC hxabs
  have hval : hr.sum ≈
      rampFnC (thm36C_levelLC h a b hab ha spD n)
        (thm36C_tC h a b hab ha spD) hx.sum
        (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n) := by
    simpa [thm36C_rampLC] using
      thm36A1_ramp_comp_valueC h
        (thm36C_levelLC h a b hab ha spD n)
        (thm36C_tC h a b hab ha spD)
        (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)
        (thm36C_levelL_nonnegC h a b hab ha spD n) x hx hr
  exact regularSeqNonneg_of_eventual hval
    (regularSeqNonneg_of_zero_le
      (rampFnC_zero_leC (thm36C_levelLC h a b hab ha spD n)
        (thm36C_tC h a b hab ha spD) hx.sum
        (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD n)))

theorem thm36Ca_decrementA_nonneg_on_domainC
    (n : Nat) (x : X) (hxdom : x ∈ h.domain)
    (hd : RepSeriesSum
      (fun m => ((thm36Ca_decrementAC h a b hab ha spD n).fn m).toFun x)) :
    RegularSeqNonneg hd.sum := by
  rcases hxdom with ⟨_hdom, ⟨hxabs⟩⟩
  let hx : RepSeriesSum (fun m => (h.fn m).toFun x) := seriesSum_of_absC hxabs
  let Wn := thm36Ca_rampA_value_witnessC h a b hab ha spD n x hx
  let Ws := thm36Ca_rampA_value_witnessC h a b hab ha spD (n + 1) x hx
  let hcan : RepSeriesSum
      (fun m => ((thm36Ca_decrementAC h a b hab ha spD n).fn m).toFun x) := by
    simpa [thm36Ca_decrementAC] using
      sub_seriesSum_valueC3
        (r := thm36C_rampLC h a b hab ha spD n)
        (r' := thm36C_rampLC h a b hab ha spD (n + 1)) (x := x) Wn.val Ws.val
  have hsum : hd.sum ≈ CReal.sub Wn.val.sum Ws.val.sum := by
    have huniq : hd.sum ≈ hcan.sum := repSeriesSum_unique hd hcan
    have hcan_sum : hcan.sum ≈ CReal.sub Wn.val.sum Ws.val.sum := by
      change relEventually (CReal.add Wn.val.sum (CReal.neg Ws.val.sum)) _
      exact relEventually_symm _ _
        (subSeq_eq_add_neg_eventually Wn.val.sum Ws.val.sum)
    exact Setoid.trans huniq hcan_sum
  have hmodel : CReal.sub Wn.val.sum Ws.val.sum ≈
      CReal.sub
        (thm36C_rampFnLC h a b hab ha spD n hx.sum)
        (thm36C_rampFnLC h a b hab ha spD (n + 1) hx.sum) :=
    subSeq_respects_eventually Wn.val.sum
      (thm36C_rampFnLC h a b hab ha spD n hx.sum)
      Ws.val.sum
      (thm36C_rampFnLC h a b hab ha spD (n + 1) hx.sum)
      Wn.property Ws.property
  have hmono : RegularSeqLe
      (thm36C_rampFnLC h a b hab ha spD (n + 1) hx.sum)
      (thm36C_rampFnLC h a b hab ha spD n hx.sum) :=
    thm36Ca_rampLFn_succ_leC h a b hab ha spD n hx.sum
  have hdiff_nn : RegularSeqNonneg
      (CReal.sub
        (thm36C_rampFnLC h a b hab ha spD n hx.sum)
        (thm36C_rampFnLC h a b hab ha spD (n + 1) hx.sum)) := hmono
  exact regularSeqNonneg_of_eventual
    (relEventually_trans _ _ _ hsum hmodel) hdiff_nn

set_option maxHeartbeats 1600000 in
-- This is the A-side signed analogue of the B-side nonnegative norm proof:
-- pointwise `|r_{n+1}-r_n|` is identified with the positive decrement
-- `r_n-r_{n+1}` on the full domain.
theorem thm36Ca_signedDiff_normL1C (n : Nat) :
    ((thm36C_rampLC h a b hab ha spD (n + 1)).sub
        (thm36C_rampLC h a b hab ha spD n)).normL1 ≈
      (thm36Ca_decrementAC h a b hab ha spD n).integral := by
  let s : IntegrableRepC3 S :=
    (thm36C_rampLC h a b hab ha spD (n + 1)).sub
      (thm36C_rampLC h a b hab ha spD n)
  let d : IntegrableRepC3 S := thm36Ca_decrementAC h a b hab ha spD n
  have hpoint : ∀ x, x ∈ h.domain →
      ∀ (hsabs : RepSeriesSum (fun m => ((s.absVal.fn m).toFun x)))
        (hd : RepSeriesSum (fun m => (d.fn m).toFun x)),
        hsabs.sum ≈ hd.sum := by
    intro x hxdom hsabs hd
    rcases hxdom with ⟨_hdom, ⟨hxabs⟩⟩
    let hx : RepSeriesSum (fun m => (h.fn m).toFun x) := seriesSum_of_absC hxabs
    let Wn := thm36Ca_rampA_value_witnessC h a b hab ha spD n x hx
    let Ws := thm36Ca_rampA_value_witnessC h a b hab ha spD (n + 1) x hx
    let hs : RepSeriesSum (fun m => (s.fn m).toFun x) := by
      dsimp [s, IntegrableRepC3.sub]
      exact sub_seriesSum_valueC3
        (r := thm36C_rampLC h a b hab ha spD (n + 1))
        (r' := thm36C_rampLC h a b hab ha spD n) (x := x) Ws.val Wn.val
    let hd0 : RepSeriesSum (fun m => (d.fn m).toFun x) := by
      dsimp [d, thm36Ca_decrementAC]
      exact sub_seriesSum_valueC3
        (r := thm36C_rampLC h a b hab ha spD n)
        (r' := thm36C_rampLC h a b hab ha spD (n + 1)) (x := x) Wn.val Ws.val
    obtain ⟨habsModel, habsModel_eq⟩ := s.absVal_signed_value x hs
    have hsabs_eq : hsabs.sum ≈ habsModel.sum := repSeriesSum_unique hsabs habsModel
    have hs_sum : hs.sum ≈ CReal.sub Ws.val.sum Wn.val.sum := by
      change relEventually (CReal.add Ws.val.sum (CReal.neg Wn.val.sum)) _
      exact relEventually_symm _ _
        (subSeq_eq_add_neg_eventually Ws.val.sum Wn.val.sum)
    have hd0_sum : hd0.sum ≈ CReal.sub Wn.val.sum Ws.val.sum := by
      change relEventually (CReal.add Wn.val.sum (CReal.neg Ws.val.sum)) _
      exact relEventually_symm _ _
        (subSeq_eq_add_neg_eventually Wn.val.sum Ws.val.sum)
    have hnn : RegularSeqNonneg hd0.sum :=
      thm36Ca_decrementA_nonneg_on_domainC h a b hab ha spD n x
        ⟨_hdom, ⟨hxabs⟩⟩ hd0
    calc
      hsabs.sum ≈ habsModel.sum := hsabs_eq
      _ ≈ CReal.abs hs.sum := habsModel_eq
      _ ≈ CReal.abs (CReal.sub Ws.val.sum Wn.val.sum) :=
            absSeq_respects_eventually _ _ hs_sum
      _ ≈ CReal.abs (CReal.neg (CReal.sub Wn.val.sum Ws.val.sum)) :=
            absSeq_respects_eventually _ _
              (subSeq_comm_neg_eventually Ws.val.sum Wn.val.sum)
      _ ≈ CReal.abs (CReal.sub Wn.val.sum Ws.val.sum) :=
            CReal.abs_neg (CReal.sub Wn.val.sum Ws.val.sum)
      _ ≈ CReal.abs hd0.sum :=
            absSeq_respects_eventually _ _ (Setoid.symm hd0_sum)
      _ ≈ hd0.sum := CReal.abs_of_nonneg_E hnn
      _ ≈ hd.sum := repSeriesSum_unique hd0 hd
  change s.absVal.integral ≈ d.integral
  refine regularSeqLe_antisymm_eventuallyC ?_ ?_
  · refine prop_1_11C h.domain_isFull s.absVal d ?_
    intro x hx hsabs hd
    exact regularSeqLe_of_relEventually (hpoint x hx hsabs hd)
  · refine prop_1_11C h.domain_isFull d s.absVal ?_
    intro x hx hd hsabs
    exact regularSeqLe_of_relEventually (Setoid.symm (hpoint x hx hsabs hd))

theorem thm36Ca_signedTermA_normL1C (m : Nat) :
    (thm36Ca_signedTermAC h a b hab ha spD m).normL1 ≈
      match m with
      | 0 => (thm36C_rampLC h a b hab ha spD 0).integral
      | n + 1 => (thm36Ca_decrementAC h a b hab ha spD n).integral := by
  cases m with
  | zero =>
      exact thm36_normL1_eq_integral_on_fullC h.domain_isFull _
        (fun x hxdom hx => thm36Ca_rampA_nonneg_on_domainC h a b hab ha spD 0 x hxdom hx)
  | succ n =>
      exact thm36Ca_signedDiff_normL1C h a b hab ha spD n

/-- A-side norm-value sequence: `N 0 = I(r₀)`,
`N(n+1)=I(r_n-r_{n+1})`. -/
noncomputable def thm36Ca_normValueAC : Nat → CReal
  | 0 => (thm36C_rampLC h a b hab ha spD 0).integral
  | n + 1 => (thm36Ca_decrementAC h a b hab ha spD n).integral

set_option maxHeartbeats 1200000 in
-- Recursive quotient arithmetic in the norm telescope needs a larger
-- heartbeat budget than the default.
theorem thm36Ca_partialSum_normValueAC :
    ∀ n : Nat,
      regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) n ≈
        CReal.sub
          (CReal.add (thm36C_rampLC h a b hab ha spD 0).integral
            (thm36C_rampLC h a b hab ha spD 0).integral)
          (thm36C_rampLC h a b hab ha spD n).integral
  | 0 => by
      exact Setoid.symm
        (thm36CReal_two_sub_selfC
          (thm36C_rampLC h a b hab ha spD 0).integral)
  | n + 1 => by
      have ih := thm36Ca_partialSum_normValueAC n
      let base := CReal.add (thm36C_rampLC h a b hab ha spD 0).integral
        (thm36C_rampLC h a b hab ha spD 0).integral
      let rn := (thm36C_rampLC h a b hab ha spD n).integral
      let rs := (thm36C_rampLC h a b hab ha spD (n + 1)).integral
      let ps := regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) n
      have hleft :
          regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) (n + 1)
            ≈ CReal.add ps (CReal.sub rn rs) := by
        change
          CReal.add ps (thm36Ca_normValueAC h a b hab ha spD (n + 1))
            ≈ CReal.add ps (CReal.sub rn rs)
        rfl
      have hmid :
          CReal.add ps (CReal.sub rn rs) ≈
            CReal.add (CReal.sub base rn) (CReal.sub rn rs) :=
        thm36CReal_add_congr_leftC ih
      have hcancel : CReal.add (CReal.sub base rn) (CReal.sub rn rs) ≈
          CReal.sub base rs :=
        thm36CReal_sub_add_sub_cancelC base rn rs
      exact Setoid.trans hleft (Setoid.trans hmid hcancel)

/-- A-side norm majorant series.  Its sum is `2 I(r₀) - lambdaBar`. -/
noncomputable def thm36Ca_normValueSeriesAC :
    RepSeriesSum (thm36Ca_normValueAC h a b hab ha spD) where
  sum :=
    CReal.sub
      (CReal.add (thm36C_rampLC h a b hab ha spD 0).integral
        (thm36C_rampLC h a b hab ha spD 0).integral)
      (thm36C_selectedLambdaBarC h a b hab ha spD)
  tends :=
    { mod := fun k =>
        (thm36C_rampLambdaL_modDataC h a b hab ha spD (k + 1)).val
      close := by
        intro k n hn
        let base := CReal.add (thm36C_rampLC h a b hab ha spD 0).integral
          (thm36C_rampLC h a b hab ha spD 0).integral
        have hclose_lambda :
            regularSeqLtProp
              (CReal.abs (CReal.sub
                ((thm36A2_profileDefaultC h hab ha).lambda
                  (thm36C_rampCodeLC h a b hab ha spD n))
                (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) :=
          (thm36C_rampLambdaL_modDataC h a b hab ha spD (k + 1)).property n hn
        have hclose_integral :
            regularSeqLtProp
              (CReal.abs (CReal.sub
                (thm36C_rampLC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) := by
          rw [← thm36C_levelLambda_eq_rampIntegralLC h a b hab ha spD n]
          exact hclose_lambda
        have hpartial :
            regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) n ≈
              CReal.sub base (thm36C_rampLC h a b hab ha spD n).integral :=
          thm36Ca_partialSum_normValueAC h a b hab ha spD n
        have hsub :
            CReal.sub
                (regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) n)
                (CReal.sub base (thm36C_selectedLambdaBarC h a b hab ha spD))
              ≈
            CReal.neg (CReal.sub
              (thm36C_rampLC h a b hab ha spD n).integral
              (thm36C_selectedLambdaBarC h a b hab ha spD)) := by
          have hstep :
              CReal.sub
                  (regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) n)
                  (CReal.sub base (thm36C_selectedLambdaBarC h a b hab ha spD))
                ≈
              CReal.sub
                (CReal.sub base (thm36C_rampLC h a b hab ha spD n).integral)
                (CReal.sub base (thm36C_selectedLambdaBarC h a b hab ha spD)) :=
            subSeq_respects_eventually _ _ _ _ hpartial (relEventually_refl _)
          exact Setoid.trans hstep
            (thm36CReal_sub_sub_baseC base
              (thm36C_rampLC h a b hab ha spD n).integral
              (thm36C_selectedLambdaBarC h a b hab ha spD))
        have habs :
            CReal.abs
              (CReal.sub
                (regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) n)
                (CReal.sub base (thm36C_selectedLambdaBarC h a b hab ha spD)))
              ≈
            CReal.abs
              (CReal.sub (thm36C_rampLC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD)) := by
          exact Setoid.trans (absSeq_respects_eventually _ _ hsub)
            (CReal.abs_neg
              (CReal.sub (thm36C_rampLC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD)))
        have hgap :
            regularSeqLtProp
              (CReal.abs
                (CReal.sub
                  (regularSeqFinSum (thm36Ca_normValueAC h a b hab ha spD) n)
                  (CReal.sub base (thm36C_selectedLambdaBarC h a b hab ha spD))))
              (halfPow (k + 1)) :=
          regularSeqLtProp_of_left_eventual habs hclose_integral
        exact repCloseAtGauge_of_absGap _ _ (k + 1) hgap }

/-- A-side L1 majorant series. -/
noncomputable def thm36Ca_normSeriesAC :
    RepSeriesSum (fun m => (thm36Ca_termAC h a b hab ha spD m).normL1) :=
  repSeriesSum_congr (thm36Ca_normValueSeriesAC h a b hab ha spD)
    (fun m => thm36Ca_signedTermA_normL1C h a b hab ha spD m)

/-- A-side L1 limit representative for the weak upper level set. -/
noncomputable def thm36Ca_fAC : IntegrableRepC3 S :=
  seriesSumRep_L1C (thm36Ca_termAC h a b hab ha spD)
    (thm36Ca_normSeriesAC h a b hab ha spD)

set_option maxHeartbeats 2000000 in
-- Signed A-side integral telescope: partial sums of `I(termA_m)` are exactly
-- the left ramp integrals, hence converge to the smooth value.
theorem thm36Ca_partialSum_termA_integralC :
    ∀ n : Nat,
      regularSeqFinSum
          (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) n ≈
        (thm36C_rampLC h a b hab ha spD n).integral
  | 0 => by
      rfl
  | n + 1 => by
      have ih := thm36Ca_partialSum_termA_integralC n
      let prev := (thm36C_rampLC h a b hab ha spD n).integral
      let next := (thm36C_rampLC h a b hab ha spD (n + 1)).integral
      let ps :=
        regularSeqFinSum
          (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) n
      have hps : ps ≈ prev := ih
      have hterm :
          (thm36Ca_termAC h a b hab ha spD (n + 1)).integral ≈
            CReal.sub next prev := by
        rfl
      have hleft :
          regularSeqFinSum
              (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) (n + 1)
            ≈ CReal.add ps (CReal.sub next prev) := by
        change
          CReal.add ps ((thm36Ca_termAC h a b hab ha spD (n + 1)).integral) ≈
            CReal.add ps (CReal.sub next prev)
        exact thm36CReal_add_congr_rightC hterm
      have hcancel : CReal.add prev (CReal.sub next prev) ≈ next :=
        thm36CReal_add_sub_cancelC prev next
      have hmid :
          CReal.add ps (CReal.sub next prev) ≈
            CReal.add prev (CReal.sub next prev) :=
        thm36CReal_add_congr_leftC hps
      exact Setoid.trans hleft (Setoid.trans hmid hcancel)

/-- A-side integral series: the signed telescoping integral partial sums
converge to the smooth value `lambdaBar`. -/
noncomputable def thm36Ca_termIntegralSeriesAC :
    RepSeriesSum (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) where
  sum := thm36C_selectedLambdaBarC h a b hab ha spD
  tends :=
    { mod := fun k =>
        (thm36C_rampLambdaL_modDataC h a b hab ha spD (k + 1)).val
      close := by
        intro k n hn
        have hclose_lambda :
            regularSeqLtProp
              (CReal.abs (CReal.sub
                ((thm36A2_profileDefaultC h hab ha).lambda
                  (thm36C_rampCodeLC h a b hab ha spD n))
                (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) :=
          (thm36C_rampLambdaL_modDataC h a b hab ha spD (k + 1)).property n hn
        have hclose_integral :
            regularSeqLtProp
              (CReal.abs (CReal.sub
                (thm36C_rampLC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) := by
          rw [← thm36C_levelLambda_eq_rampIntegralLC h a b hab ha spD n]
          exact hclose_lambda
        have hpartial :
            regularSeqFinSum
                (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) n ≈
              (thm36C_rampLC h a b hab ha spD n).integral :=
          thm36Ca_partialSum_termA_integralC h a b hab ha spD n
        have hsub :
            CReal.sub
                (regularSeqFinSum
                  (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) n)
                (thm36C_selectedLambdaBarC h a b hab ha spD)
              ≈
            CReal.sub (thm36C_rampLC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD) :=
          subSeq_respects_eventually _ _ _ _ hpartial (relEventually_refl _)
        have habs :
            CReal.abs
              (CReal.sub
                (regularSeqFinSum
                  (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) n)
                (thm36C_selectedLambdaBarC h a b hab ha spD))
              ≈
            CReal.abs
              (CReal.sub (thm36C_rampLC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD)) :=
          absSeq_respects_eventually _ _ hsub
        have hgap :
            regularSeqLtProp
              (CReal.abs
                (CReal.sub
                  (regularSeqFinSum
                    (fun m => (thm36Ca_termAC h a b hab ha spD m).integral) n)
                  (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) :=
          regularSeqLtProp_of_left_eventual habs hclose_integral
        exact repCloseAtGauge_of_absGap _ _ (k + 1) hgap }

/-- The A-side L1 representative has integral equal to the smooth value. -/
theorem thm36Ca_fA_integralC :
    (thm36Ca_fAC h a b hab ha spD).integral ≈
      thm36C_selectedLambdaBarC h a b hab ha spD := by
  let W := seriesSumRep_L1_integralC
    (thm36Ca_termAC h a b hab ha spD)
    (thm36Ca_normSeriesAC h a b hab ha spD)
  exact relEventually_trans _ _ _ W.property
    (repSeriesSum_unique W.val (thm36Ca_termIntegralSeriesAC h a b hab ha spD))

set_option maxHeartbeats 1600000 in
-- Same L1 value-continuity plumbing as the B-side representative, now for the
-- signed A-side telescope.
/-- Pointwise value series for the A-side L1 representative:
`f_A(x) = Σ_m termA_m(x)`. -/
noncomputable def thm36Ca_fA_value_seriesC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)))
    (hx : RepSeriesSum (fun n => (h.fn n).toFun x)) :
    { hser : RepSeriesSum
        (fun m => (thm36Ca_termA_value_witnessC
          h a b hab ha spD m x hx).val.sum) //
      (seriesSum_of_absC hfabs).sum ≈ hser.sum } := by
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_valueC
    (thm36Ca_termAC h a b hab ha spD)
    (thm36Ca_normSeriesAC h a b hab ha spD) hfabs
  refine ⟨repSeriesSum_congr hV (fun m => ?_), eV⟩
  let Wm := thm36Ca_termA_value_witnessC h a b hab ha spD m x hx
  refine relEventually_trans _ _ _
    (relEventually_symm _ _
      (seriesSumRep_L1_hsplit_valueC
        (thm36Ca_termAC h a b hab ha spD) m Wm.val)) ?_
  exact addSeq_respects_eventually _ _ _ _
    (relEventually_symm _ _
      (repSeriesSum_unique
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe
              (((G_mC (thm36Ca_termAC h a b hab ha spD) p).fn q).toFun x)))
          (add_absSeriesSum_leftC hfabs) m))
        (IntegrableRepC3.ofL_value
          (psi_m_memC (thm36Ca_termAC h a b hab ha spD) m) x).1))
    (relEventually_symm _ _
      (repSeriesSum_unique
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe
              (((tail_mC (thm36Ca_termAC h a b hab ha spD) p).fn q).toFun x)))
          (add_absSeriesSum_rightC hfabs) m))
        (IntegrableRepC3.tailFrom_valueC
          (thm36Ca_termAC h a b hab ha spD m)
          (NmC (thm36Ca_termAC h a b hab ha spD) m) x Wm.val).1))

/-- From absolute convergence of the A-side L1 limit representative at `x`,
recover absolute convergence of the zeroth A telescope term. -/
noncomputable def thm36D_termA0Abs_of_fAAbsC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x))) :
    RepSeriesSum
      (fun n => absSeq (((thm36Ca_termAC h a b hab ha spD 0).fn n).toFun x)) := by
  let F : Nat → IntegrableRepC3 S := thm36Ca_termAC h a b hab ha spD
  let N : Nat := NmC F 0
  let hTailRow : RepSeriesSum
      (fun q => absSeq (((tail_mC F 0).fn q).toFun x)) :=
    row_seriesSumC
      (fun p q => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe (((tail_mC F p).fn q).toFun x)))
      (add_absSeriesSum_rightC hfabs) 0
  let htail : RepSeriesSum
      (fun l => absSeq (((F 0).fn (N + 1 + l)).toFun x)) := by
    simpa [F, N, tail_mC, IntegrableRepC3.tailFrom, Nat.add_assoc] using hTailRow
  simpa [F] using repSeriesSum_of_tailC N htail

/-- From absolute convergence of the zeroth A ramp at `x`, recover absolute
convergence of the original representative `h` at `x`. -/
noncomputable def thm36D_hAbsA_of_rampA0AbsC (x : X)
    (hramp : RepSeriesSum
      (fun n => absSeq (((thm36C_rampLC h a b hab ha spD 0).fn n).toFun x))) :
    RepSeriesSum (fun n => absSeq ((h.fn n).toFun x)) := by
  let lo : CReal := thm36C_levelLC h a b hab ha spD 0
  let up : CReal := thm36C_tC h a b hab ha spD
  let hpos : PosEventuallyData (CReal.sub up lo) :=
    thm36C_levelL_t_posEventuallyDataC h a b hab ha spD 0
  let hu : ¬ CReal.ltE lo CReal.zero :=
    thm36C_levelL_nonnegC h a b hab ha spD 0
  let c : CReal := CReal.invPos (CReal.sub up lo) hpos
  let r : IntegrableRepC3 S := h.sub (h.cutConstVal lo hu)
  let q : IntegrableRepC3 S := IntegrableRepC3.smul c r
  let hOne : ¬ CReal.ltE CReal.one CReal.zero := by
    intro hlt
    exact regularSeqLtProp_irrefl CReal.zero
      (regularSeqLtProp_trans CReal.zero CReal.one CReal.zero
        CReal.one_pos_E hlt)
  let hcut : RepSeriesSum
      (fun n => absSeq (((q.cutConstVal CReal.one hOne).fn n).toFun x)) := by
    simpa [thm36C_rampLC, thm_3_6_ramp_compC, lo, up, c, r, q] using hramp
  let hq := cutConstVal_absSeriesSum_midC q CReal.one hOne x hcut
  let hscaled : RepSeriesSum
      (fun n => CReal.abs (CReal.mul c ((r.fn n).toFun x))) := by
    simpa [IntegrableRepC3.smul, BFunC.smul, q, c, r] using hq
  have hc : regularSeqLtProp CReal.zero c :=
    regularSeqLtProp_zero_of_posData
      (CReal.invPos_posData (CReal.sub up lo) hpos)
  let hr := thm36D_absSeries_of_pos_smulC c hc
    (fun n => (r.fn n).toFun x) hscaled
  simpa [r, IntegrableRepC3.sub] using
    (add_absSeriesSum_leftC
      (r := h) (r' := (h.cutConstVal lo hu).neg) (x := x) hr)

/-- From absolute convergence of the A-side L1 limit representative at `x`,
recover absolute convergence of the original `h` at `x`. -/
noncomputable def thm36D_hAbsA_of_fAAbsC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x))) :
    RepSeriesSum (fun n => absSeq ((h.fn n).toFun x)) := by
  let hterm0 := thm36D_termA0Abs_of_fAAbsC h a b hab ha spD x hfabs
  let hramp : RepSeriesSum
      (fun n => absSeq (((thm36C_rampLC h a b hab ha spD 0).fn n).toFun x)) := by
    simpa [thm36Ca_termAC, thm36Ca_signedTermAC] using hterm0
  exact thm36D_hAbsA_of_rampA0AbsC h a b hab ha spD x hramp

/-- Absolute-value point sequence of the A-side L1 representative. -/
noncomputable def thm36D_fAAbsSeqC (x : X) : Nat → CReal :=
  fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)

/-- Point-value sequence of the A-side L1 representative. -/
noncomputable def thm36D_fAValSeqC (x : X) : Nat → CReal :=
  fun n => ((thm36Ca_fAC h a b hab ha spD).fn n).toFun x

set_option maxHeartbeats 1200000 in
-- Transport the A-side L1 value-series limit through the pointwise telescope.
/-- Left-ramp point values at `h(x)` converge to the point value of `f_A`. -/
noncomputable def thm36D_rampTendsA_of_hSum_fAAbsC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)))
    (hSum : RepSeriesSum (fun n => (h.fn n).toFun x)) :
    RepSeriesTendsto
      (fun n => thm36C_rampFnLC h a b hab ha spD n hSum.sum)
      (seriesSum_of_absC hfabs).sum := by
  let fSum := seriesSum_of_absC hfabs
  let V := thm36Ca_fA_value_seriesC h a b hab ha spD x hfabs hSum
  let rowVals : Nat → CReal :=
    fun j => (thm36Ca_termA_value_witnessC
      h a b hab ha spD j x hSum).val.sum
  exact
    { mod := fun k => V.val.tends.mod (k + 2)
      close := by
        intro k n hn
        have hpartial :
            regularSeqFinSum rowVals n ≈
              thm36C_rampFnLC h a b hab ha spD n hSum.sum := by
          simpa [rowVals] using
            thm36Ca_partialSum_termA_valuesC h a b hab ha spD x hSum n
        have hpart_close : RepCloseAtGauge (k + 3)
            (thm36C_rampFnLC h a b hab ha spD n hSum.sum)
            (regularSeqFinSum rowVals n) :=
          bc1_repClose_of_relEventually
            (relEventually_symm _ _ hpartial) (k + 3)
        have hrow : RepCloseAtGauge (k + 3)
            (regularSeqFinSum rowVals n) V.val.sum :=
          V.val.tends.close (k + 2) n hn
        have hrV : RepCloseAtGauge (k + 2)
            (thm36C_rampFnLC h a b hab ha spD n hSum.sum) V.val.sum :=
          repCloseAtGauge_triangle_succ (k + 2) hpart_close hrow
        have hVf : RepCloseAtGauge (k + 2) V.val.sum fSum.sum :=
          bc1_repClose_of_relEventually
            (relEventually_symm _ _ V.property) (k + 2)
        exact repCloseAtGauge_triangle_succ (k + 1) hrV hVf }

theorem thm36D_pointA_mem_unionC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x))) :
    x ∈ thm36D_upperSetC h (thm36C_tC h a b hab ha spD) ∪
      thm36D_lowerSetC h (thm36C_tC h a b hab ha spD) := by
  let hAbs := thm36D_hAbsA_of_fAAbsC h a b hab ha spD x hfabs
  let hSum := seriesSum_of_absC hAbs
  let fSum := seriesSum_of_absC hfabs
  let rt := thm36D_rampTendsA_of_hSum_fAAbsC h a b hab ha spD x hfabs hSum
  rcases regularSeqLtProp_cotrans CReal.zero CReal.one fSum.sum CReal.one_pos_E
      with hpos | hltOne
  · have hty : RegularSeqLe (thm36C_tC h a b hab ha spD) hSum.sum := by
      apply regularSeqLe_of_not_ltQuot
      intro hyt
      have hyt' : regularSeqLtProp hSum.sum (thm36C_tC h a b hab ha spD) := hyt
      obtain ⟨N, hN⟩ :=
        thm36D_rampL_eventually_zeroC h a b hab ha spD hSum.sum hyt'
      have hz0 : fSum.sum ≈ CReal.zero :=
        thm36D_tendsto_eventually_constC rt N hN
      have h00 : regularSeqLtProp CReal.zero CReal.zero :=
        regularSeqLtProp_of_right_eventual hz0 hpos
      exact regularSeqLtProp_irrefl CReal.zero h00
    exact Or.inl ⟨hAbs, hSum, hty⟩
  · have hyt : regularSeqLtProp hSum.sum (thm36C_tC h a b hab ha spD) := by
      let WN := thm36D_limit_lt_eventuallyC rt hltOne
      exact rampFnC_lt_one_imp
        (thm36C_levelLC h a b hab ha spD WN.val)
        (thm36C_tC h a b hab ha spD)
        hSum.sum
        (thm36C_levelL_t_posEventuallyDataC h a b hab ha spD WN.val)
        WN.property
    exact Or.inr ⟨hAbs, hSum, hyt⟩

theorem thm36D_upperA_valueC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)))
    (hx : x ∈ thm36D_upperSetC h (thm36C_tC h a b hab ha spD))
    (hf : RepSeriesSum
      (fun n => ((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)) :
    hf.sum ≈ CReal.one := by
  rcases hx with ⟨_habs, hxsum, hle⟩
  let fSum := seriesSum_of_absC hfabs
  let rt := thm36D_rampTendsA_of_hSum_fAAbsC h a b hab ha spD x hfabs hxsum
  have hz1 : fSum.sum ≈ CReal.one :=
    thm36D_tendsto_eventually_constC rt 0
      (fun n _ => thm36D_rampL_always_oneC h a b hab ha spD hxsum.sum hle n)
  exact relEventually_trans _ _ _
    (repSeriesSum_unique hf fSum) hz1

theorem thm36D_lowerA_valueC (x : X)
    (hfabs : RepSeriesSum (thm36D_fAAbsSeqC h a b hab ha spD x))
    (hx : x ∈ thm36D_lowerSetC h (thm36C_tC h a b hab ha spD))
    (hf : RepSeriesSum (thm36D_fAValSeqC h a b hab ha spD x)) :
    hf.sum ≈ CReal.zero := by
  rcases hx with ⟨_habs, hxsum, hlt⟩
  let hfabsRaw : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)) := by
    simpa [thm36D_fAAbsSeqC] using hfabs
  let hfRaw : RepSeriesSum
      (fun n => ((thm36Ca_fAC h a b hab ha spD).fn n).toFun x) := by
    simpa [thm36D_fAValSeqC] using hf
  let fSum := seriesSum_of_absC hfabsRaw
  let rt := thm36D_rampTendsA_of_hSum_fAAbsC h a b hab ha spD x hfabsRaw hxsum
  obtain ⟨N, hN⟩ := thm36D_rampL_eventually_zeroC h a b hab ha spD hxsum.sum hlt
  have hz0 : fSum.sum ≈ CReal.zero :=
    thm36D_tendsto_eventually_constC rt N hN
  exact relEventually_trans _ _ _
    (repSeriesSum_unique hfRaw fSum) hz0

theorem thm36D_isFull_monoA_C {A B : Set X}
    (hA : IsFullC S A) (hsub : A ⊆ B) : IsFullC S B := by
  rcases hA with ⟨F, hF⟩
  exact ⟨F, fun x hx => hsub (hF hx)⟩

set_option maxHeartbeats 1200000 in
-- The valid field transports the `f_A` domain abs witness into the direct
-- point classifier and into the two value lemmas.
/-- The A-pair level set `({h≥t},{h<t})` is integrable at the selected smooth
point. -/
noncomputable def thm36D_integrableSetA_directC :
    IntegrableSet1C S
      (thm36D_levelBSetC h (thm36C_tC h a b hab ha spD)) := by
  let f : IntegrableRepC3 S := thm36Ca_fAC h a b hab ha spD
  have hsub : f.domain ⊆
      (thm36D_upperSetC h (thm36C_tC h a b hab ha spD) ∪
        thm36D_lowerSetC h (thm36C_tC h a b hab ha spD)) := by
    intro x hxdom
    rcases hxdom with ⟨_hdom, ⟨hfabs⟩⟩
    let hfabsRaw : RepSeriesSum
        (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)) := by
      simpa [f] using hfabs
    exact thm36D_pointA_mem_unionC h a b hab ha spD x hfabsRaw
  refine
    { full := thm36D_isFull_monoA_C (S := S) (IntegrableRepC3.domain_isFull f) hsub
      rep := f
      valid := ?_ }
  intro x hfabs
  let hfabsRaw : RepSeriesSum
      (fun n => absSeq (((thm36Ca_fAC h a b hab ha spD).fn n).toFun x)) := by
    simpa [f] using hfabs
  refine ⟨thm36D_pointA_mem_unionC h a b hab ha spD x hfabsRaw, ?_, ?_⟩
  · intro hx hf
    let hfRaw : RepSeriesSum
        (fun n => ((thm36Ca_fAC h a b hab ha spD).fn n).toFun x) := by
      simpa [f] using hf
    exact thm36D_upperA_valueC h a b hab ha spD x hfabsRaw hx hfRaw
  · intro hx hf
    let hfabsH : RepSeriesSum (thm36D_fAAbsSeqC h a b hab ha spD x) := by
      simpa [thm36D_fAAbsSeqC] using hfabsRaw
    let hfH : RepSeriesSum (thm36D_fAValSeqC h a b hab ha spD x) := by
      simpa [f, thm36D_fAValSeqC] using hf
    exact thm36D_lowerA_valueC h a b hab ha spD x hfabsH hx hfH

/-- The concrete A-pair package has measure/integral `lambdaBar`. -/
theorem thm36D_integrableSetA_measureC :
    (thm36D_integrableSetA_directC h a b hab ha spD).rep.integral ≈
      thm36C_selectedLambdaBarC h a b hab ha spD := by
  simpa [thm36D_integrableSetA_directC] using
    thm36Ca_fA_integralC h a b hab ha spD

/-- Existential A-pair level-set package at the selected smooth point. -/
noncomputable def thm36D_level_setsA_integrableC :
    { t : CReal // regularSeqLtProp a t ∧ regularSeqLtProp t b ∧
      ∃ A : BishopC.BSet X,
        (A.S1 = thm36D_upperSetC h t) ∧
        (A.S2 = thm36D_lowerSetC h t) ∧
        Nonempty (IntegrableSet1C S A) } := by
  refine ⟨thm36C_tC h a b hab ha spD,
    thm36C_a_lt_tC h a b hab ha spD,
    thm36C_t_lt_bC h a b hab ha spD, ?_⟩
  refine ⟨thm36D_levelBSetC h (thm36C_tC h a b hab ha spD), rfl, rfl, ?_⟩
  exact ⟨thm36D_integrableSetA_directC h a b hab ha spD⟩

theorem thm36Cb_rampB_nonneg_on_domainC
    (n : Nat) (x : X) (hxdom : x ∈ h.domain)
    (hr : RepSeriesSum
      (fun m => ((thm36C_rampRC h a b hab ha spD n).fn m).toFun x)) :
    RegularSeqNonneg hr.sum := by
  rcases hxdom with ⟨_hdom, ⟨hxabs⟩⟩
  let hx : RepSeriesSum (fun m => (h.fn m).toFun x) := seriesSum_of_absC hxabs
  have hval : hr.sum ≈
      rampFnC (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD n) hx.sum
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n) := by
    simpa [thm36C_rampRC] using
      thm36A1_ramp_comp_valueC h
        (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD n)
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
        (thm36C_t_nonnegC h a b hab ha spD) x hx hr
  exact regularSeqNonneg_of_eventual hval
    (rampFnC_bound (thm36C_tC h a b hab ha spD)
      (thm36C_levelRC h a b hab ha spD n) hx.sum
      (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)).1

theorem thm36Cb_decrementB_nonneg_on_domainC
    (n : Nat) (x : X) (hxdom : x ∈ h.domain)
    (hd : RepSeriesSum
      (fun m => (((thm36C_rampRC h a b hab ha spD (n + 1)).sub
          (thm36C_rampRC h a b hab ha spD n)).fn m).toFun x)) :
    RegularSeqNonneg hd.sum := by
  rcases hxdom with ⟨_hdom, ⟨hxabs⟩⟩
  let hx : RepSeriesSum (fun m => (h.fn m).toFun x) := seriesSum_of_absC hxabs
  let Wn := thm36A1_ramp_comp_value_witnessC h
        (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD n)
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)
        (thm36C_t_nonnegC h a b hab ha spD) x hx
  let Ws := thm36A1_ramp_comp_value_witnessC h
        (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD (n + 1))
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD (n + 1))
        (thm36C_t_nonnegC h a b hab ha spD) x hx
  let hsub : RepSeriesSum
      (fun m => (((thm36C_rampRC h a b hab ha spD (n + 1)).sub
          (thm36C_rampRC h a b hab ha spD n)).fn m).toFun x) := by
    exact sub_seriesSum_valueC3
      (r := thm36C_rampRC h a b hab ha spD (n + 1))
      (r' := thm36C_rampRC h a b hab ha spD n) (x := x) Ws.val Wn.val
  have hd_eq : hd.sum ≈ hsub.sum := repSeriesSum_unique hd hsub
  have hsub_sum : hsub.sum ≈ CReal.sub Ws.val.sum Wn.val.sum := by
    change relEventually (CReal.add Ws.val.sum (CReal.neg Wn.val.sum)) _
    exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually Ws.val.sum Wn.val.sum)
  have hmodel : CReal.sub Ws.val.sum Wn.val.sum ≈
      CReal.sub
        (rampFnC (thm36C_tC h a b hab ha spD)
          (thm36C_levelRC h a b hab ha spD (n + 1)) hx.sum
          (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD (n + 1)))
        (rampFnC (thm36C_tC h a b hab ha spD)
          (thm36C_levelRC h a b hab ha spD n) hx.sum
          (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n)) :=
    subSeq_respects_eventually Ws.val.sum
      (rampFnC (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD (n + 1)) hx.sum
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD (n + 1)))
      Wn.val.sum
      (rampFnC (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD n) hx.sum
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n))
      Ws.property Wn.property
  have hmono : RegularSeqLe
      (rampFnC (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD n) hx.sum
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n))
      (rampFnC (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD (n + 1)) hx.sum
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD (n + 1))) :=
    thm36Cb_rampBFn_succ_geC h a b hab ha spD n hx.sum
  have hdiff_nn : RegularSeqNonneg
      (CReal.sub
        (rampFnC (thm36C_tC h a b hab ha spD)
          (thm36C_levelRC h a b hab ha spD (n + 1)) hx.sum
          (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD (n + 1)))
        (rampFnC (thm36C_tC h a b hab ha spD)
          (thm36C_levelRC h a b hab ha spD n) hx.sum
          (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD n))) := hmono
  exact regularSeqNonneg_of_eventual
    (relEventually_trans _ _ _ hd_eq (relEventually_trans _ _ _ hsub_sum hmodel)) hdiff_nn

theorem thm36Cb_signedTermB_normL1C (m : Nat) :
    (thm36Cb_signedTermBC h a b hab ha spD m).normL1 ≈
      (thm36Cb_signedTermBC h a b hab ha spD m).integral := by
  cases m with
  | zero =>
      exact thm36_normL1_eq_integral_on_fullC h.domain_isFull _
        (fun x hxdom hx => thm36Cb_rampB_nonneg_on_domainC h a b hab ha spD 0 x hxdom hx)
  | succ n =>
      exact thm36_normL1_eq_integral_on_fullC h.domain_isFull _
        (fun x hxdom hx => by
          simpa [thm36Cb_signedTermBC] using
            thm36Cb_decrementB_nonneg_on_domainC h a b hab ha spD n x hxdom hx)

set_option maxHeartbeats 2000000 in
-- The recursive telescope unfolds the successor B term and several quotient
-- arithmetic transports; default heartbeats are too tight for this block.
theorem thm36Cb_partialSum_termB_integralC :
    ∀ n : Nat,
      regularSeqFinSum
          (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) n ≈
        (thm36C_rampRC h a b hab ha spD n).integral
  | 0 => by
      rfl
  | n + 1 => by
      have ih := thm36Cb_partialSum_termB_integralC n
      let prev := (thm36C_rampRC h a b hab ha spD n).integral
      let next := (thm36C_rampRC h a b hab ha spD (n + 1)).integral
      let ps :=
        regularSeqFinSum
          (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) n
      have hps : ps ≈ prev := ih
      have hterm :
          (thm36Cb_termBC h a b hab ha spD (n + 1)).integral ≈
            CReal.sub next prev := by
        rfl
      have hleft :
          regularSeqFinSum
              (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) (n + 1)
            ≈ CReal.add ps (CReal.sub next prev) := by
        change
          CReal.add ps ((thm36Cb_termBC h a b hab ha spD (n + 1)).integral) ≈
            CReal.add ps (CReal.sub next prev)
        exact thm36CReal_add_congr_rightC hterm
      have hcancel : CReal.add prev (CReal.sub next prev) ≈ next :=
        thm36CReal_add_sub_cancelC prev next
      have hmid :
          CReal.add ps (CReal.sub next prev) ≈
            CReal.add prev (CReal.sub next prev) :=
        thm36CReal_add_congr_leftC hps
      exact Setoid.trans hleft (Setoid.trans hmid hcancel)

/-- B-side integral series: the telescoping integral partial sums converge to
    the smooth value `lambdaBar`. -/
noncomputable def thm36Cb_termIntegralSeriesBC :
    RepSeriesSum (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) where
  sum := thm36C_selectedLambdaBarC h a b hab ha spD
  tends :=
    { mod := fun k =>
        (thm36C_rampLambdaR_modDataC h a b hab ha spD (k + 1)).val
      close := by
        intro k n hn
        have hclose_lambda :
            regularSeqLtProp
              (CReal.abs (CReal.sub
                ((thm36A2_profileDefaultC h hab ha).lambda
                  (thm36C_rampCodeRC h a b hab ha spD n))
                (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) :=
          (thm36C_rampLambdaR_modDataC h a b hab ha spD (k + 1)).property n hn
        have hclose_integral :
            regularSeqLtProp
              (CReal.abs (CReal.sub
                (thm36C_rampRC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) := by
          rw [← thm36C_levelLambda_eq_rampIntegralRC h a b hab ha spD n]
          exact hclose_lambda
        have hpartial :
            regularSeqFinSum
                (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) n ≈
              (thm36C_rampRC h a b hab ha spD n).integral :=
          thm36Cb_partialSum_termB_integralC h a b hab ha spD n
        have hsub :
            CReal.sub
                (regularSeqFinSum
                  (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) n)
                (thm36C_selectedLambdaBarC h a b hab ha spD)
              ≈
            CReal.sub (thm36C_rampRC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD) :=
          subSeq_respects_eventually _ _ _ _ hpartial (relEventually_refl _)
        have habs :
            CReal.abs
              (CReal.sub
                (regularSeqFinSum
                  (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) n)
                (thm36C_selectedLambdaBarC h a b hab ha spD))
              ≈
            CReal.abs
              (CReal.sub (thm36C_rampRC h a b hab ha spD n).integral
                (thm36C_selectedLambdaBarC h a b hab ha spD)) :=
          absSeq_respects_eventually _ _ hsub
        have hgap :
            regularSeqLtProp
              (CReal.abs
                (CReal.sub
                  (regularSeqFinSum
                    (fun m => (thm36Cb_termBC h a b hab ha spD m).integral) n)
                  (thm36C_selectedLambdaBarC h a b hab ha spD)))
              (halfPow (k + 1)) :=
          regularSeqLtProp_of_left_eventual habs hclose_integral
        exact repCloseAtGauge_of_absGap _ _ (k + 1) hgap }

/-- B-side L1 majorant series, obtained from nonnegativity of each signed
    telescoping term. -/
noncomputable def thm36Cb_normSeriesBC :
    RepSeriesSum (fun m => (thm36Cb_termBC h a b hab ha spD m).normL1) :=
  repSeriesSum_congr (thm36Cb_termIntegralSeriesBC h a b hab ha spD)
    (fun m => thm36Cb_signedTermB_normL1C h a b hab ha spD m)

/-- B-side L1 limit representative for the strict upper level set. -/
noncomputable def thm36Cb_fBC : IntegrableRepC3 S :=
  seriesSumRep_L1C (thm36Cb_termBC h a b hab ha spD)
    (thm36Cb_normSeriesBC h a b hab ha spD)

/-- The B-side L1 representative has integral equal to the smooth value. -/
theorem thm36Cb_fB_integralC :
    (thm36Cb_fBC h a b hab ha spD).integral ≈
      thm36C_selectedLambdaBarC h a b hab ha spD := by
  let W := seriesSumRep_L1_integralC
    (thm36Cb_termBC h a b hab ha spD)
    (thm36Cb_normSeriesBC h a b hab ha spD)
  exact relEventually_trans _ _ _ W.property
    (repSeriesSum_unique W.val (thm36Cb_termIntegralSeriesBC h a b hab ha spD))

set_option maxHeartbeats 1600000 in
-- This is the same `seriesSumRep_L1_valueC` / `hsplit` plumbing as
-- `IntegrableRepC3.prop_4_2_rep_value_seriesC`, specialized to the B-side
-- telescope terms.
/-- Pointwise value series for the B-side L1 representative:
`f_B(x) = Σ_m termB_m(x)`. -/
noncomputable def thm36Cb_fB_value_seriesC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)))
    (hx : RepSeriesSum (fun n => (h.fn n).toFun x)) :
    { hser : RepSeriesSum
        (fun m => (thm36Cb_termB_value_witnessC
          h a b hab ha spD m x hx).val.sum) //
      (seriesSum_of_absC hfabs).sum ≈ hser.sum } := by
  obtain ⟨hV, eV⟩ := seriesSumRep_L1_valueC
    (thm36Cb_termBC h a b hab ha spD)
    (thm36Cb_normSeriesBC h a b hab ha spD) hfabs
  refine ⟨repSeriesSum_congr hV (fun m => ?_), eV⟩
  let Wm := thm36Cb_termB_value_witnessC h a b hab ha spD m x hx
  refine relEventually_trans _ _ _
    (relEventually_symm _ _
      (seriesSumRep_L1_hsplit_valueC
        (thm36Cb_termBC h a b hab ha spD) m Wm.val)) ?_
  exact addSeq_respects_eventually _ _ _ _
    (relEventually_symm _ _
      (repSeriesSum_unique
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe
              (((G_mC (thm36Cb_termBC h a b hab ha spD) p).fn q).toFun x)))
          (add_absSeriesSum_leftC hfabs) m))
        (IntegrableRepC3.ofL_value
          (psi_m_memC (thm36Cb_termBC h a b hab ha spD) m) x).1))
    (relEventually_symm _ _
      (repSeriesSum_unique
        (seriesSum_of_absC (row_seriesSumC
          (fun p q => regularSeqNonneg_of_zero_le
            (absSeq_nonnegative_regularSeqLe
              (((tail_mC (thm36Cb_termBC h a b hab ha spD) p).fn q).toFun x)))
          (add_absSeriesSum_rightC hfabs) m))
        (IntegrableRepC3.tailFrom_valueC
          (thm36Cb_termBC h a b hab ha spD m)
          (NmC (thm36Cb_termBC h a b hab ha spD) m) x Wm.val).1))

/-- From absolute convergence of the L1-limit representative `f_B` at `x`,
recover absolute convergence of the zeroth B telescope term.  Only the tail
row is needed; the finite prefix is restored by `repSeriesSum_of_tailC`. -/
noncomputable def thm36D_termB0Abs_of_fBAbsC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x))) :
    RepSeriesSum
      (fun n => absSeq (((thm36Cb_termBC h a b hab ha spD 0).fn n).toFun x)) := by
  let F : Nat → IntegrableRepC3 S := thm36Cb_termBC h a b hab ha spD
  let N : Nat := NmC F 0
  let hTailRow : RepSeriesSum
      (fun q => absSeq (((tail_mC F 0).fn q).toFun x)) :=
    row_seriesSumC
      (fun p q => regularSeqNonneg_of_zero_le
        (absSeq_nonnegative_regularSeqLe (((tail_mC F p).fn q).toFun x)))
      (add_absSeriesSum_rightC hfabs) 0
  let htail : RepSeriesSum
      (fun l => absSeq (((F 0).fn (N + 1 + l)).toFun x)) := by
    simpa [F, N, tail_mC, IntegrableRepC3.tailFrom, Nat.add_assoc] using hTailRow
  simpa [F] using repSeriesSum_of_tailC N htail

/-- From absolute convergence of the zeroth B ramp at `x`, recover absolute
convergence of the original representative `h` at `x`.  This reverses the
right-ramp construction: cut at `t`, scale by `(level_0 - t)^{-1}`, then cut
at `1`; middle-lane extraction and positive-scalar cancellation remove those
operations. -/
noncomputable def thm36D_hAbsB_of_rampB0AbsC (x : X)
    (hramp : RepSeriesSum
      (fun n => absSeq (((thm36C_rampRC h a b hab ha spD 0).fn n).toFun x))) :
    RepSeriesSum (fun n => absSeq ((h.fn n).toFun x)) := by
  let lo : CReal := thm36C_tC h a b hab ha spD
  let up : CReal := thm36C_levelRC h a b hab ha spD 0
  let hpos : PosEventuallyData (CReal.sub up lo) :=
    thm36C_t_levelR_posEventuallyDataC h a b hab ha spD 0
  let hu : ¬ CReal.ltE lo CReal.zero :=
    thm36C_t_nonnegC h a b hab ha spD
  let c : CReal := CReal.invPos (CReal.sub up lo) hpos
  let r : IntegrableRepC3 S := h.sub (h.cutConstVal lo hu)
  let q : IntegrableRepC3 S := IntegrableRepC3.smul c r
  let hOne : ¬ CReal.ltE CReal.one CReal.zero := by
    intro hlt
    exact regularSeqLtProp_irrefl CReal.zero
      (regularSeqLtProp_trans CReal.zero CReal.one CReal.zero
        CReal.one_pos_E hlt)
  let hcut : RepSeriesSum
      (fun n => absSeq (((q.cutConstVal CReal.one hOne).fn n).toFun x)) := by
    simpa [thm36C_rampRC, thm_3_6_ramp_compC, lo, up, c, r, q] using hramp
  let hq := cutConstVal_absSeriesSum_midC q CReal.one hOne x hcut
  let hscaled : RepSeriesSum
      (fun n => CReal.abs (CReal.mul c ((r.fn n).toFun x))) := by
    simpa [IntegrableRepC3.smul, BFunC.smul, q, c, r] using hq
  have hc : regularSeqLtProp CReal.zero c :=
    regularSeqLtProp_zero_of_posData
      (CReal.invPos_posData (CReal.sub up lo) hpos)
  let hr := thm36D_absSeries_of_pos_smulC c hc
    (fun n => (r.fn n).toFun x) hscaled
  simpa [r, IntegrableRepC3.sub] using
    (add_absSeriesSum_leftC
      (r := h) (r' := (h.cutConstVal lo hu).neg) (x := x) hr)

/-- From absolute convergence of the B-side L1 limit representative at `x`,
recover absolute convergence of the original `h` at `x`. -/
noncomputable def thm36D_hAbsB_of_fBAbsC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x))) :
    RepSeriesSum (fun n => absSeq ((h.fn n).toFun x)) := by
  let hterm0 := thm36D_termB0Abs_of_fBAbsC h a b hab ha spD x hfabs
  let hramp : RepSeriesSum
      (fun n => absSeq (((thm36C_rampRC h a b hab ha spD 0).fn n).toFun x)) := by
    simpa [thm36Cb_termBC, thm36Cb_signedTermBC] using hterm0
  exact thm36D_hAbsB_of_rampB0AbsC h a b hab ha spD x hramp

/-- Absolute-value point sequence of the B-side L1 representative. -/
noncomputable def thm36D_fBAbsSeqC (x : X) : Nat → CReal :=
  fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)

/-- Point-value sequence of the B-side L1 representative. -/
noncomputable def thm36D_fBValSeqC (x : X) : Nat → CReal :=
  fun n => ((thm36Cb_fBC h a b hab ha spD).fn n).toFun x

/-- Right-ramp value sequence at a fixed point value `z`. -/
noncomputable def thm36D_rampValueSeqBC (z : CReal) : Nat → CReal :=
  fun n => thm36C_rampFnRC h a b hab ha spD n z

set_option maxHeartbeats 1200000 in
-- This transports the L1 value-series limit through two quotient-close
-- triangles and the pointwise telescope identity.
/-- Right-ramp point values at `h(x)` converge to the point value of `f_B`. -/
noncomputable def thm36D_rampTendsB_of_hSum_fBAbsC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)))
    (hSum : RepSeriesSum (fun n => (h.fn n).toFun x)) :
    RepSeriesTendsto
      (fun n => thm36C_rampFnRC h a b hab ha spD n hSum.sum)
      (seriesSum_of_absC hfabs).sum := by
  let fSum := seriesSum_of_absC hfabs
  let V := thm36Cb_fB_value_seriesC h a b hab ha spD x hfabs hSum
  let rowVals : Nat → CReal :=
    fun j => (thm36Cb_termB_value_witnessC
      h a b hab ha spD j x hSum).val.sum
  exact
    { mod := fun k => V.val.tends.mod (k + 2)
      close := by
        intro k n hn
        have hpartial :
            regularSeqFinSum rowVals n ≈
              thm36C_rampFnRC h a b hab ha spD n hSum.sum := by
          simpa [rowVals] using
            thm36Cb_partialSum_termB_valuesC h a b hab ha spD x hSum n
        have hpart_close : RepCloseAtGauge (k + 3)
            (thm36C_rampFnRC h a b hab ha spD n hSum.sum)
            (regularSeqFinSum rowVals n) :=
          bc1_repClose_of_relEventually
            (relEventually_symm _ _ hpartial) (k + 3)
        have hrow : RepCloseAtGauge (k + 3)
            (regularSeqFinSum rowVals n) V.val.sum :=
          V.val.tends.close (k + 2) n hn
        have hrV : RepCloseAtGauge (k + 2)
            (thm36C_rampFnRC h a b hab ha spD n hSum.sum) V.val.sum :=
          repCloseAtGauge_triangle_succ (k + 2) hpart_close hrow
        have hVf : RepCloseAtGauge (k + 2) V.val.sum fSum.sum :=
          bc1_repClose_of_relEventually
            (relEventually_symm _ _ V.property) (k + 2)
        exact repCloseAtGauge_triangle_succ (k + 1) hrV hVf }

/-- Pointwise B-side classifier: absolute convergence of `f_B` at `x` places
`x` in `{h>t} ∪ {h≤t}`. -/
theorem thm36D_pointB_mem_unionC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x))) :
    x ∈ thm36D_upperSetStrictC h (thm36C_tC h a b hab ha spD) ∪
      thm36D_lowerSetWeakC h (thm36C_tC h a b hab ha spD) := by
  let hAbs := thm36D_hAbsB_of_fBAbsC h a b hab ha spD x hfabs
  let hSum := seriesSum_of_absC hAbs
  let fSum := seriesSum_of_absC hfabs
  let rt := thm36D_rampTendsB_of_hSum_fBAbsC h a b hab ha spD x hfabs hSum
  rcases regularSeqLtProp_cotrans CReal.zero CReal.one fSum.sum CReal.one_pos_E
      with hpos | hltOne
  · have hty : regularSeqLtProp (thm36C_tC h a b hab ha spD) hSum.sum := by
      let WN := thm36D_lt_limit_eventuallyC rt hpos
      exact rampFnC_pos_imp
        (thm36C_tC h a b hab ha spD)
        (thm36C_levelRC h a b hab ha spD WN.val)
        hSum.sum
        (thm36C_t_levelR_posEventuallyDataC h a b hab ha spD WN.val)
        WN.property
    exact Or.inl ⟨hAbs, hSum, hty⟩
  · have hyt : RegularSeqLe hSum.sum (thm36C_tC h a b hab ha spD) := by
      apply regularSeqLe_of_not_ltQuot
      intro h_t_lt
      have h_t_lt' : regularSeqLtProp (thm36C_tC h a b hab ha spD) hSum.sum :=
        h_t_lt
      obtain ⟨N, hN⟩ :=
        thm36D_rampR_eventually_oneC h a b hab ha spD hSum.sum h_t_lt'
      have hz1 : fSum.sum ≈ CReal.one :=
        thm36D_tendsto_eventually_constC rt N hN
      have h11 : regularSeqLtProp CReal.one CReal.one :=
        regularSeqLtProp_of_left_eventual (Setoid.symm hz1) hltOne
      exact regularSeqLtProp_irrefl CReal.one h11
    exact Or.inr ⟨hAbs, hSum, hyt⟩

/-- On the strict upper side `{h>t}`, the B-side representative has value `1`. -/
theorem thm36D_upperB_valueC (x : X)
    (hfabs : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)))
    (hx : x ∈ thm36D_upperSetStrictC h (thm36C_tC h a b hab ha spD))
    (hf : RepSeriesSum
      (fun n => ((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)) :
    hf.sum ≈ CReal.one := by
  rcases hx with ⟨_habs, hxsum, hlt⟩
  let hAbs := thm36D_hAbsB_of_fBAbsC h a b hab ha spD x hfabs
  let hSum := seriesSum_of_absC hAbs
  let fSum := seriesSum_of_absC hfabs
  let rt := thm36D_rampTendsB_of_hSum_fBAbsC h a b hab ha spD x hfabs hSum
  have hsame : hxsum.sum ≈ hSum.sum := repSeriesSum_unique hxsum hSum
  have hltD : regularSeqLtProp (thm36C_tC h a b hab ha spD) hSum.sum :=
    regularSeqLtProp_of_right_eventual hsame hlt
  obtain ⟨N, hN⟩ := thm36D_rampR_eventually_oneC h a b hab ha spD hSum.sum hltD
  have hz1 : fSum.sum ≈ CReal.one :=
    thm36D_tendsto_eventually_constC rt N hN
  exact relEventually_trans _ _ _
    (repSeriesSum_unique hf fSum) hz1

set_option maxHeartbeats 1200000 in
-- The lower-side value proof reuses the ramp-tendsto transport and expands
-- several quotient-order congruences.
/-- On the weak lower side `{h≤t}`, the B-side representative has value `0`. -/
theorem thm36D_lowerB_valueC (x : X)
    (hfabs : RepSeriesSum (thm36D_fBAbsSeqC h a b hab ha spD x))
    (hx : x ∈ thm36D_lowerSetWeakC h (thm36C_tC h a b hab ha spD))
    (hf : RepSeriesSum (thm36D_fBValSeqC h a b hab ha spD x)) :
    hf.sum ≈ CReal.zero := by
  rcases hx with ⟨_habs, hxsum, hle⟩
  let hfabsRaw : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)) := by
    simpa [thm36D_fBAbsSeqC] using hfabs
  let hfRaw : RepSeriesSum
      (fun n => ((thm36Cb_fBC h a b hab ha spD).fn n).toFun x) := by
    simpa [thm36D_fBValSeqC] using hf
  let fSum := seriesSum_of_absC hfabsRaw
  let rt := thm36D_rampTendsB_of_hSum_fBAbsC h a b hab ha spD x hfabsRaw hxsum
  have hz0 : fSum.sum ≈ CReal.zero :=
    thm36D_tendsto_eventually_constC rt 0
      (fun n _ => thm36D_rampR_always_zeroC h a b hab ha spD hxsum.sum hle n)
  exact relEventually_trans _ _ _
    (repSeriesSum_unique hfRaw fSum) hz0

/-- Full sets are upward closed under subset inclusion. -/
theorem thm36D_isFull_monoC {A B : Set X}
    (hA : IsFullC S A) (hsub : A ⊆ B) : IsFullC S B := by
  rcases hA with ⟨F, hF⟩
  exact ⟨F, fun x hx => hsub (hF hx)⟩

set_option maxHeartbeats 1200000 in
-- The valid field transports the `f_B` domain abs witness into the direct
-- point classifier and into the two value lemmas.
/-- The B-pair level set `({h>t},{h≤t})` is integrable at the selected smooth
point. -/
noncomputable def thm36D_integrableSetB_directC :
    IntegrableSet1C S
      (thm36D_levelBSetStrictC h (thm36C_tC h a b hab ha spD)) := by
  let f : IntegrableRepC3 S := thm36Cb_fBC h a b hab ha spD
  have hsub : f.domain ⊆
      (thm36D_upperSetStrictC h (thm36C_tC h a b hab ha spD) ∪
        thm36D_lowerSetWeakC h (thm36C_tC h a b hab ha spD)) := by
    intro x hxdom
    rcases hxdom with ⟨_hdom, ⟨hfabs⟩⟩
    let hfabsRaw : RepSeriesSum
        (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)) := by
      simpa [f] using hfabs
    exact thm36D_pointB_mem_unionC h a b hab ha spD x hfabsRaw
  refine
    { full := thm36D_isFull_monoC (S := S) (IntegrableRepC3.domain_isFull f) hsub
      rep := f
      valid := ?_ }
  intro x hfabs
  let hfabsRaw : RepSeriesSum
      (fun n => absSeq (((thm36Cb_fBC h a b hab ha spD).fn n).toFun x)) := by
    simpa [f] using hfabs
  refine ⟨thm36D_pointB_mem_unionC h a b hab ha spD x hfabsRaw, ?_, ?_⟩
  · intro hx hf
    let hfRaw : RepSeriesSum
        (fun n => ((thm36Cb_fBC h a b hab ha spD).fn n).toFun x) := by
      simpa [f] using hf
    exact thm36D_upperB_valueC h a b hab ha spD x hfabsRaw hx hfRaw
  · intro hx hf
    let hfabsH : RepSeriesSum (thm36D_fBAbsSeqC h a b hab ha spD x) := by
      simpa [thm36D_fBAbsSeqC] using hfabsRaw
    let hfH : RepSeriesSum (thm36D_fBValSeqC h a b hab ha spD x) := by
      simpa [f, thm36D_fBValSeqC] using hf
    exact thm36D_lowerB_valueC h a b hab ha spD x hfabsH hx hfH

/-- The concrete B-pair package has measure/integral `lambdaBar`. -/
theorem thm36D_integrableSetB_measureC :
    (thm36D_integrableSetB_directC h a b hab ha spD).rep.integral ≈
      thm36C_selectedLambdaBarC h a b hab ha spD := by
  simpa [thm36D_integrableSetB_directC] using
    thm36Cb_fB_integralC h a b hab ha spD

/-- Existential B-pair level-set package at the selected smooth point. -/
noncomputable def thm36D_level_setsB_integrableC :
    { t : CReal // regularSeqLtProp a t ∧ regularSeqLtProp t b ∧
      ∃ A : BishopC.BSet X,
        (A.S1 = thm36D_upperSetStrictC h t) ∧
        (A.S2 = thm36D_lowerSetWeakC h t) ∧
        Nonempty (IntegrableSet1C S A) } := by
  refine ⟨thm36C_tC h a b hab ha spD,
    thm36C_a_lt_tC h a b hab ha spD,
    thm36C_t_lt_bC h a b hab ha spD, ?_⟩
  refine ⟨thm36D_levelBSetStrictC h (thm36C_tC h a b hab ha spD), rfl, rfl, ?_⟩
  exact ⟨thm36D_integrableSetB_directC h a b hab ha spD⟩

end Thm36CbCore

/-- CReal Theorem 3.6, selected smooth point form: at a carried smooth point
`spD`, both Bishop--Cheng level-set pairs
`({h >= t}, {h < t})` and `({h > t}, {h <= t})` are integrable sets. -/
noncomputable def thm_3_6_smoothPoint_level_sets_integrableC {X : Type*}
    {S : IntSpaceC X} (h : IntegrableRepC3 S) (a b : CReal)
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (spD : Thm36BSmoothPointDataC h a b hab ha) :
    { t : CReal // regularSeqLtProp a t ∧ regularSeqLtProp t b ∧
      (∃ A : BishopC.BSet X,
        (A.S1 = thm36D_upperSetC h t) ∧
        (A.S2 = thm36D_lowerSetC h t) ∧
        Nonempty (IntegrableSet1C S A)) ∧
      (∃ B : BishopC.BSet X,
        (B.S1 = thm36D_upperSetStrictC h t) ∧
        (B.S2 = thm36D_lowerSetWeakC h t) ∧
        Nonempty (IntegrableSet1C S B)) } := by
  let hA := thm36D_level_setsA_integrableC h a b hab ha spD
  let hB := thm36D_level_setsB_integrableC h a b hab ha spD
  refine ⟨thm36C_tC h a b hab ha spD, ?_, ?_, ?_, ?_⟩
  · exact hA.property.1
  · exact hA.property.2.1
  · exact hA.property.2.2
  · exact hB.property.2.2

/-- CReal Theorem 3.6, A-pair forall-apart interval form:
for every `t in (a,b)` apart from the explicit exception sequence supplied by
Theorem 3.5, `({h >= t}, {h < t})` is an integrable set. -/
noncomputable def thm_3_6_forall_apart_AC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    ∃ A : BishopC.BSet X,
      (A.S1 = thm36D_upperSetC h t) ∧
      (A.S2 = thm36D_lowerSetC h t) ∧
      Nonempty (IntegrableSet1C S A) := by
  let spD := thm36B_smoothPointData_of_apartC (a := a) (b := b)
    h hab ha t hat htb hT
  simpa [spD, thm36C_tC] using
    (thm36D_level_setsA_integrableC h a b hab ha spD).property.2.2

/-- CReal Theorem 3.6, B-pair forall-apart interval form:
for every `t in (a,b)` apart from the explicit exception sequence supplied by
Theorem 3.5, `({h > t}, {h <= t})` is an integrable set. -/
noncomputable def thm_3_6_forall_apart_BC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    ∃ B : BishopC.BSet X,
      (B.S1 = thm36D_upperSetStrictC h t) ∧
      (B.S2 = thm36D_lowerSetWeakC h t) ∧
      Nonempty (IntegrableSet1C S B) := by
  let spD := thm36B_smoothPointData_of_apartC (a := a) (b := b)
    h hab ha t hat htb hT
  simpa [spD, thm36C_tC] using
    (thm36D_level_setsB_integrableC h a b hab ha spD).property.2.2

/-- CReal Theorem 3.6, paired forall-apart interval form: for every admissible
`t`, both level-set pairs from Bishop--Cheng Theorem 3.6 are integrable. -/
noncomputable def thm_3_6_forall_apartC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    (∃ A : BishopC.BSet X,
      (A.S1 = thm36D_upperSetC h t) ∧
      (A.S2 = thm36D_lowerSetC h t) ∧
      Nonempty (IntegrableSet1C S A)) ∧
    (∃ B : BishopC.BSet X,
      (B.S1 = thm36D_upperSetStrictC h t) ∧
      (B.S2 = thm36D_lowerSetWeakC h t) ∧
      Nonempty (IntegrableSet1C S B)) := by
  exact ⟨
    thm_3_6_forall_apart_AC h hab ha t hat htb hT,
    thm_3_6_forall_apart_BC h hab ha t hat htb hT⟩

/-- CReal Theorem 3.6, A-pair with measure: for every admissible `t`, the
A-pair is integrable and its represented measure is the smooth value
`lambdaBar(t)`. -/
noncomputable def thm_3_6_forall_apart_measure_AC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    Σ' A : { A : BishopC.BSet X //
      (A.S1 = thm36D_upperSetC h t) ∧
      (A.S2 = thm36D_lowerSetC h t) },
      Σ' hA : IntegrableSet1C S A.val,
        hA.rep.integral ≈ thm36C_lambdaBarC h hab ha t (regularSeqLe_of_ltPropC hat) (regularSeqLe_of_ltPropC htb) hT := by
  let spD := thm36B_smoothPointData_of_apartC (a := a) (b := b)
    h hab ha t hat htb hT
  refine ⟨⟨thm36D_levelBSetC h t, ⟨rfl, rfl⟩⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [spD, thm36C_tC] using thm36D_integrableSetA_directC h a b hab ha spD
  · simpa [spD, thm36C_tC, thm36C_selectedLambdaBarC] using
      thm36D_integrableSetA_measureC h a b hab ha spD

/-- CReal Theorem 3.6, B-pair with measure: for every admissible `t`, the
B-pair is integrable and its represented measure is the smooth value
`lambdaBar(t)`. -/
noncomputable def thm_3_6_forall_apart_measure_BC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    Σ' B : { B : BishopC.BSet X //
      (B.S1 = thm36D_upperSetStrictC h t) ∧
      (B.S2 = thm36D_lowerSetWeakC h t) },
      Σ' hB : IntegrableSet1C S B.val,
        hB.rep.integral ≈ thm36C_lambdaBarC h hab ha t (regularSeqLe_of_ltPropC hat) (regularSeqLe_of_ltPropC htb) hT := by
  let spD := thm36B_smoothPointData_of_apartC (a := a) (b := b)
    h hab ha t hat htb hT
  refine ⟨⟨thm36D_levelBSetStrictC h t, ⟨rfl, rfl⟩⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [spD, thm36C_tC] using thm36D_integrableSetB_directC h a b hab ha spD
  · simpa [spD, thm36C_tC, thm36C_selectedLambdaBarC] using
      thm36D_integrableSetB_measureC h a b hab ha spD

/-- CReal Theorem 3.6, paired measure form: both Bishop--Cheng level-set pairs
are integrable and both measures are `lambdaBar(t)`. -/
noncomputable def thm_3_6_forall_apart_measureC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    (Σ' A : { A : BishopC.BSet X //
      (A.S1 = thm36D_upperSetC h t) ∧
      (A.S2 = thm36D_lowerSetC h t) },
      Σ' hA : IntegrableSet1C S A.val,
        hA.rep.integral ≈ thm36C_lambdaBarC h hab ha t (regularSeqLe_of_ltPropC hat) (regularSeqLe_of_ltPropC htb) hT) ×
    (Σ' B : { B : BishopC.BSet X //
      (B.S1 = thm36D_upperSetStrictC h t) ∧
      (B.S2 = thm36D_lowerSetWeakC h t) },
      Σ' hB : IntegrableSet1C S B.val,
        hB.rep.integral ≈ thm36C_lambdaBarC h hab ha t (regularSeqLe_of_ltPropC hat) (regularSeqLe_of_ltPropC htb) hT) :=
  ⟨thm_3_6_forall_apart_measure_AC h hab ha t hat htb hT,
    thm_3_6_forall_apart_measure_BC h hab ha t hat htb hT⟩

/-- CReal Theorem 3.6, equality of the represented measures of the A- and
B-pairs at every admissible `t`. -/
theorem thm_3_6_AB_measure_eqC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a)
    (t : CReal) (hat : regularSeqLtProp a t) (htb : regularSeqLtProp t b)
    (hT : ∀ n,
      regularSeqLtProp CReal.zero
        (CReal.abs (CReal.sub t (thm36ExceptionSeqC h hab ha n)))) :
    (thm_3_6_forall_apart_measure_AC h hab ha t hat htb hT).2.1.rep.integral ≈
      (thm_3_6_forall_apart_measure_BC h hab ha t hat htb hT).2.1.rep.integral := by
  let hA := thm_3_6_forall_apart_measure_AC h hab ha t hat htb hT
  let hB := thm_3_6_forall_apart_measure_BC h hab ha t hat htb hT
  exact relEventually_trans _ _ _
    hA.2.2
    (Setoid.symm hB.2.2)

/-! ### §4 Lemma 4.3 bridge: dyadic level-set data from Theorem 3.6 -/

/-- Smooth-point choices in every dyadic interval
`(2^{-(n+1)}, 2^{-n})`, in the explicit data form required for Lemma 4.3.
This keeps the countable-exception avoidance as input data rather than
extracting it from a Prop existential. -/
structure Lemma43DyadicSmoothDataC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) where
  smooth : ∀ n : Nat,
    Thm36BSmoothPointDataC h (halfPow (n + 1)) (halfPow n)
      (regularSeqLtProp_halfPow_succ n)
      (posEventuallyData_halfPowC (n + 1))

/-- Lemma 4.3 entrance data: thresholds `alpha n` with
`2^{-(n+1)} < alpha n < 2^{-n}`, and integrable level sets
`A n = ({h >= alpha n}, {h < alpha n})`, together with their represented
measures. -/
structure Lemma43LevelSetSeqDataC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) where
  alpha : Nat → CReal
  alpha_lower : ∀ n, regularSeqLtProp (halfPow (n + 1)) (alpha n)
  alpha_upper : ∀ n, regularSeqLtProp (alpha n) (halfPow n)
  A : Nat → BishopC.BSet X
  hA : ∀ n, IntegrableSet1C S (A n)
  A_s1 : ∀ n, (A n).S1 = thm36D_upperSetC h (alpha n)
  A_s2 : ∀ n, (A n).S2 = thm36D_lowerSetC h (alpha n)
  lambda : Nat → CReal
  measure_eq : ∀ n, (hA n).rep.integral ≈ lambda n

/-- Construct Lemma 4.3 level-set data from the selected smooth points supplied
in every dyadic interval.  This is the first source-level §4 bridge from
Theorem 3.6: it turns the smooth-level theorem into the explicit sequence
`A_n = ({h >= alpha_n}, {h < alpha_n})` used in Lemma 4.3. -/
noncomputable def lemma43LevelSetSeqDataC_of_dyadicSmoothDataC
    {X : Type*} {S : IntSpaceC X} (h : IntegrableRepC3 S)
    (D : Lemma43DyadicSmoothDataC h) :
    Lemma43LevelSetSeqDataC h where
  alpha := fun n =>
    thm36C_tC h (halfPow (n + 1)) (halfPow n)
      (regularSeqLtProp_halfPow_succ n)
      (posEventuallyData_halfPowC (n + 1))
      (D.smooth n)
  alpha_lower := by
    intro n
    simpa [thm36C_tC] using (D.smooth n).a_lt_t
  alpha_upper := by
    intro n
    simpa [thm36C_tC] using (D.smooth n).t_lt_b
  A := fun n =>
    thm36D_levelBSetC h
      (thm36C_tC h (halfPow (n + 1)) (halfPow n)
        (regularSeqLtProp_halfPow_succ n)
        (posEventuallyData_halfPowC (n + 1))
        (D.smooth n))
  hA := by
    intro n
    simpa [thm36C_tC] using
      thm36D_integrableSetA_directC h (halfPow (n + 1)) (halfPow n)
        (regularSeqLtProp_halfPow_succ n)
        (posEventuallyData_halfPowC (n + 1))
        (D.smooth n)
  A_s1 := by
    intro n
    rfl
  A_s2 := by
    intro n
    rfl
  lambda := fun n =>
    thm36C_selectedLambdaBarC h (halfPow (n + 1)) (halfPow n)
      (regularSeqLtProp_halfPow_succ n)
      (posEventuallyData_halfPowC (n + 1))
      (D.smooth n)
  measure_eq := by
    intro n
    simpa [thm36C_tC] using
      thm36D_integrableSetA_measureC h (halfPow (n + 1)) (halfPow n)
        (regularSeqLtProp_halfPow_succ n)
        (posEventuallyData_halfPowC (n + 1))
        (D.smooth n)

/-- The thresholds supplied by Lemma 4.3 entrance data converge to zero.
The modulus is explicit: `mod k = k+2`, using
`alpha n < 2^{-n} <= 2^{-(k+2)} < 2^{-(k+1)}`. -/
noncomputable def lemma43AlphaTendstoZeroC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h) :
    RepSeriesTendsto D.alpha CReal.zero where
  mod := fun k => k + 2
  close := by
    intro k n hn
    have h0alpha : regularSeqLtProp CReal.zero (D.alpha n) :=
      regularSeqLtProp_trans CReal.zero (halfPow (n + 1)) (D.alpha n)
        (regularSeqLtProp_zero_halfPow (n + 1)) (D.alpha_lower n)
    have hnn : RegularSeqNonneg (D.alpha n) := by
      intro hneg
      exact regularSeqLtProp_irrefl CReal.zero
        (regularSeqLtProp_trans CReal.zero (D.alpha n) CReal.zero h0alpha hneg)
    have hle : RegularSeqLe (D.alpha n) (halfPow n) :=
      regularSeqLe_of_ltPropC (D.alpha_upper n)
    have hy : regularSeqLtProp (halfPow n) (halfPow (k + 1)) :=
      regularSeqLtProp_of_le_of_lt
        (halfPow_antitone_leC hn)
        (regularSeqLtProp_halfPow_succ (k + 1))
    exact repCloseAtGauge_zero_of_nonneg_le_ltC hnn hle hy

/-- Lemma 4.3 local cutoff monotonicity:
    if `0 <= a <= b`, then `I(min(f,a)) <= I(min(f,b))`.
    Kept in the §3/§4 bridge layer to avoid forcing a heavy Sec1 rebuild for a
    lemma currently only used by Lemma 4.3. -/
theorem lemma43CutConstVal_integral_monoC {X : Type*} {S : IntSpaceC X}
    (f : IntegrableRepC3 S) {a b : CReal}
    (ha : ¬ a.ltE CReal.zero) (hb : ¬ b.ltE CReal.zero)
    (hab : RegularSeqLe a b) :
    RegularSeqLe (f.cutConstVal a ha).integral (f.cutConstVal b hb).integral := by
  refine prop_1_11C
    (isFull_interC (isFull_interC (f.cutConstVal a ha).domain_isFull
      (f.cutConstVal b hb).domain_isFull) f.domain_isFull)
    (f.cutConstVal a ha) (f.cutConstVal b hb) ?_
  intro x hx hr hr'
  obtain ⟨⟨_hxa, _hxb⟩, hxf⟩ := hx
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  let hf : RepSeriesSum (fun n => (f.fn n).toFun x) := seriesSum_of_absC hfabs
  obtain ⟨hca, hca_eq⟩ := f.cutConstVal_signed_valueC a ha x hf
  obtain ⟨hcb, hcb_eq⟩ := f.cutConstVal_signed_valueC b hb x hf
  have hmin : RegularSeqLe (CReal.min hf.sum a) (CReal.min hf.sum b) := by
    apply CReal.le_minC
    · exact regularSeqLe_trans (CReal.min_le_leftC hf.sum a)
        (regularSeqLe_refl hf.sum)
    · exact regularSeqLe_trans (CReal.min_le_rightC hf.sum a) hab
  have eL : hr.sum ≈ CReal.min hf.sum a :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr hca) hca_eq
  have eR : hr'.sum ≈ CReal.min hf.sum b :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr' hcb) hcb_eq
  exact regularSeqLe_of_left_eventual eL
    (regularSeqLe_of_right_eventual (Setoid.symm eR) hmin)

/-- Nonnegativity certificate for the Lemma 4.3 threshold `alpha n`. -/
noncomputable def lemma43AlphaNonnegC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h) (n : Nat) :
    ¬ (D.alpha n).ltE CReal.zero := by
  have h0alpha : regularSeqLtProp CReal.zero (D.alpha n) :=
    regularSeqLtProp_trans CReal.zero (halfPow (n + 1)) (D.alpha n)
      (regularSeqLtProp_zero_halfPow (n + 1)) (D.alpha_lower n)
  intro hneg
  exact regularSeqLtProp_irrefl CReal.zero
    (regularSeqLtProp_trans CReal.zero (D.alpha n) CReal.zero h0alpha hneg)

/-- Nonnegativity certificate for `halfPow n`. -/
noncomputable def lemma43HalfPowNonnegC (n : Nat) :
    ¬ (halfPow n).ltE CReal.zero := by
  intro hneg
  exact regularSeqLtProp_irrefl CReal.zero
    (regularSeqLtProp_trans CReal.zero (halfPow n) CReal.zero
      (regularSeqLtProp_zero_halfPow n) hneg)

/-- Since `alpha n < 2^{-n}`, the cutoff integral at `alpha n` is bounded by
the dyadic cutoff integral `I(min(f,2^{-n}))`.  This is the first analytic
estimate in Lemma 4.3 toward `I(min(f, alpha_n)) -> 0`. -/
theorem lemma43CutAlphaIntegral_le_cutHalfPowC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h) (n : Nat) :
    RegularSeqLe
      (h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral
      (h.cutConstVal (halfPow n) (lemma43HalfPowNonnegC n)).integral :=
  lemma43CutConstVal_integral_monoC h
    (lemma43AlphaNonnegC D n) (lemma43HalfPowNonnegC n)
    (regularSeqLe_of_ltPropC (D.alpha_upper n))

/-- For nonnegative `h`, the dyadic cutoff `min(h,2^{-n})` is bounded by the
standard small cutoff `min(|h|,2^{-n})`. -/
theorem lemma43CutHalfPowIntegral_le_cutSmallC {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) (hnn : RepNonnegC h) (n : Nat) :
    RegularSeqLe
      (h.cutConstVal (halfPow n) (lemma43HalfPowNonnegC n)).integral
      (h.cutSmallVal n).integral := by
  refine prop_1_11C
    (isFull_interC (isFull_interC
      (h.cutConstVal (halfPow n) (lemma43HalfPowNonnegC n)).domain_isFull
      (h.cutSmallVal n).domain_isFull) h.domain_isFull)
    (h.cutConstVal (halfPow n) (lemma43HalfPowNonnegC n))
    (h.cutSmallVal n) ?_
  intro x hx hr hr'
  obtain ⟨⟨_hxL, _hxR⟩, hxf⟩ := hx
  obtain ⟨_, ⟨hfabs⟩⟩ := hxf
  let hf : RepSeriesSum (fun k => (h.fn k).toFun x) := seriesSum_of_absC hfabs
  obtain ⟨hleft, hleft_eq⟩ :=
    h.cutConstVal_signed_valueC (halfPow n) (lemma43HalfPowNonnegC n) x hf
  obtain ⟨habsVal, habsVal_eq⟩ := h.absVal_signed_value x hf
  obtain ⟨hright, hright_eq0⟩ :=
    h.absVal.cutConstVal_signed_valueC
      (constSeq (eps n)) (epsConst_nonnegC n) x habsVal
  have hright_eq : hright.sum ≈ CReal.min habsVal.sum (halfPow n) := by
    simpa [halfPow, CReal.epsSeq] using hright_eq0
  have eL : hr.sum ≈ CReal.min hf.sum (halfPow n) :=
    relEventually_trans _ _ _ (repSeriesSum_unique hr hleft) hleft_eq
  have eR : hr'.sum ≈ CReal.min habsVal.sum (halfPow n) := by
    have huniq : hr'.sum ≈ hright.sum := by
      simpa [IntegrableRepC3.cutSmallVal] using repSeriesSum_unique hr' hright
    exact relEventually_trans _ _ _ huniq hright_eq
  have hnonneg : RegularSeqNonneg hf.sum := hnn x hfabs hf
  have habs_hf : CReal.abs hf.sum ≈ hf.sum := CReal.abs_of_nonneg_E hnonneg
  have habsVal_to_hf : habsVal.sum ≈ hf.sum :=
    relEventually_trans _ _ _ habsVal_eq habs_hf
  have hsame :
      CReal.min hf.sum (halfPow n) ≈ CReal.min habsVal.sum (halfPow n) :=
    minSeqWith_respects_eventually cRatScalarMulArch
      hf.sum habsVal.sum (halfPow n) (halfPow n)
      (Setoid.symm habsVal_to_hf) (Setoid.refl (halfPow n))
  have hmid : RegularSeqLe (CReal.min hf.sum (halfPow n))
      (CReal.min habsVal.sum (halfPow n)) :=
    regularSeqLe_of_relEventually hsame
  exact regularSeqLe_of_left_eventual eL
    (regularSeqLe_of_right_eventual (Setoid.symm eR) hmid)

/-- Combined Lemma 4.3 cutoff estimate:
`I(min(h,alpha_n)) <= I(min(|h|,2^{-n}))`. -/
theorem lemma43CutAlphaIntegral_le_cutSmallC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) (n : Nat) :
    RegularSeqLe
      (h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral
      (h.cutSmallVal n).integral :=
  regularSeqLe_trans
    (lemma43CutAlphaIntegral_le_cutHalfPowC D n)
    (lemma43CutHalfPowIntegral_le_cutSmallC h hnn n)

/-- Absolute-value version of the zero-gauge squeeze: if `|x| <= y` and
`y < 2^{-k}`, then `x` is close to zero at gauge `k`. -/
theorem lemma43RepCloseAtGauge_zero_of_abs_le_ltC {x y : CReal} {k : Nat}
    (hle : RegularSeqLe (CReal.abs x) y)
    (hy : regularSeqLtProp y (halfPow k)) :
    RepCloseAtGauge k x CReal.zero := by
  have habs_sub_le : RegularSeqLe (absSeq (subSeq x CReal.zero)) y := by
    exact regularSeqLe_trans
      (regularSeqLe_of_left_eventual
        (absSeq_respects_eventually (subSeq x CReal.zero) x
          (subSeq_zero_right_eventually x))
        (regularSeqLe_refl (absSeq x)))
      hle
  have hlt_abs : regularSeqLtProp (absSeq (subSeq x CReal.zero)) (halfPow k) :=
    regularSeqLtProp_of_le_of_lt habs_sub_le hy
  simpa [halfPow, CReal.epsSeq] using
    repCloseAtGauge_of_absGap x CReal.zero k hlt_abs

/-- Minimum of two nonnegative CReal representatives is nonnegative. -/
theorem lemma43Min_nonnegC {x a : CReal}
    (hx : RegularSeqNonneg x) (ha : RegularSeqNonneg a) :
    RegularSeqNonneg (CReal.min x a) := by
  let A := cRatScalarMulArch
  have left_mono :
      ∀ x y z : RegularSeq, RegularSeqLe x y →
        RegularSeqLe (minSeqWith A x z) (minSeqWith A y z) := by
    intro x y z hxy
    exact
      minSeqWith_monotone_left_regularSeqLe_of_strict_backward
        A
        (fun x y z hmin =>
          minSeqWith_strict_backward_of_same_sample_expansion
            A
            (fun x y z hmin =>
              minSeqWith_same_sample_expansion_of_two_sample_alignment
                A
                (fun x y z =>
                  twoSampleAlignment_of_commonMaxTransport
                    x y z (commonMaxMinHalfsumTransport_closed x y z))
                x y z hmin)
            x y z hmin)
        x y z hxy
  have right_mono :
      ∀ x y z : RegularSeq, RegularSeqLe y z →
        RegularSeqLe (minSeqWith A x y) (minSeqWith A x z) := by
    intro x y z hyz
    exact minSeqWith_monotone_right_regularSeqLe_from_left
      A left_mono x y z hyz
  have h0x : RegularSeqLe CReal.zero x := regularSeqLe_zero_of_nonneg hx
  have h0a : RegularSeqLe CReal.zero a := regularSeqLe_zero_of_nonneg ha
  have hleft :
      RegularSeqLe (minSeqWith A CReal.zero CReal.zero)
        (minSeqWith A x CReal.zero) :=
    left_mono CReal.zero x CReal.zero h0x
  have hright :
      RegularSeqLe (minSeqWith A x CReal.zero)
        (minSeqWith A x a) :=
    right_mono x CReal.zero a h0a
  have hmin00 : CReal.min CReal.zero CReal.zero ≈ CReal.zero :=
    CReal.min_zero_const (a := CReal.zero) (CReal.ltE_irrefl CReal.zero)
  have hle : RegularSeqLe CReal.zero (CReal.min x a) := by
    exact regularSeqLe_of_left_eventual
      (relEventually_symm (CReal.min CReal.zero CReal.zero) CReal.zero hmin00)
      (regularSeqLe_trans hleft hright)
  exact regularSeqNonneg_of_zero_le hle

/-- A nonnegative function remains nonnegative after `cutConstVal` by a
nonnegative cutoff. -/
theorem lemma43CutConstVal_nonnegC {X : Type*} {S : IntSpaceC X}
    (r : IntegrableRepC3 S) (a : CReal) (ha : RegularSeqNonneg a)
    (hr : RepNonnegC r) :
    RepNonnegC (r.cutConstVal a (fun h => ha h)) := by
  intro x hcutAbs hcutSigned
  let hbaseAbs : RepSeriesSum (fun n => absSeq ((r.fn n).toFun x)) :=
    cutConstVal_absSeriesSum_midC r a (fun h => ha h) x hcutAbs
  let hbaseSigned : RepSeriesSum (fun n => (r.fn n).toFun x) :=
    seriesSum_of_absC hbaseAbs
  let hval := r.cutConstVal_signed_valueC a (fun h => ha h) x hbaseSigned
  have huniq : relEventually hcutSigned.sum hval.val.sum :=
    repSeriesSum_unique hcutSigned hval.val
  have hto_min : relEventually hcutSigned.sum (CReal.min hbaseSigned.sum a) :=
    relEventually_trans hcutSigned.sum hval.val.sum (CReal.min hbaseSigned.sum a)
      huniq hval.property
  have hminnn : RegularSeqNonneg (CReal.min hbaseSigned.sum a) :=
    lemma43Min_nonnegC (hr x hbaseAbs hbaseSigned) ha
  exact regularSeqNonneg_of_eventual hto_min hminnn

/-- The alpha cutoff integral is absolutely bounded by the dyadic small cutoff
integral. -/
theorem lemma43CutAlphaIntegral_abs_le_cutSmallC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) (n : Nat) :
    RegularSeqLe
      (CReal.abs ((h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral))
      (h.cutSmallVal n).integral := by
  let ralpha : IntegrableRepC3 S :=
    h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)
  have hralpha_nn : RepNonnegC ralpha := by
    simpa [ralpha] using
      lemma43CutConstVal_nonnegC
        h (D.alpha n) (lemma43AlphaNonnegC D n) hnn
  have hnorm_eq : ralpha.normL1 ≈ ralpha.integral :=
    IntegrableRepC3.normL1_eq_integral_of_nonnegC ralpha hralpha_nn
  have habs_le_norm : RegularSeqLe (CReal.abs ralpha.integral) ralpha.normL1 :=
    IntegrableRepC3.abs_integral_le_normL1C ralpha
  have hnorm_le_integral : RegularSeqLe ralpha.normL1 ralpha.integral := by
    exact regularSeqLe_of_left_eventual hnorm_eq (regularSeqLe_refl ralpha.integral)
  have habs_le_integral : RegularSeqLe (CReal.abs ralpha.integral) ralpha.integral :=
    regularSeqLe_trans habs_le_norm hnorm_le_integral
  have hintegral_le : RegularSeqLe ralpha.integral (h.cutSmallVal n).integral := by
    simpa [ralpha] using lemma43CutAlphaIntegral_le_cutSmallC D hnn n
  exact regularSeqLe_trans habs_le_integral hintegral_le

/-- Since `alpha n < 2^{-n}`, the alpha cutoff integrals tend to zero. -/
def lemma43CutAlphaIntegral_tendsto_zeroC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) :
    RepSeriesTendsto
      (fun n => (h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral)
      CReal.zero where
  mod := fun k => (IntegrableRepC3.cutSmall_tendsto_rep h).mod (k + 1)
  close := by
    intro k n hn
    let smallT := IntegrableRepC3.cutSmall_tendsto_rep h
    have hsmall_close :
        RepCloseAtGauge ((k + 1) + 1) (h.cutSmallVal n).integral CReal.zero :=
      smallT.close (k + 1) n hn
    have hsmall_lt :
        regularSeqLtProp (h.cutSmallVal n).integral (halfPow (k + 1)) := by
      have hsub :
          regularSeqLtProp
            (subSeq (h.cutSmallVal n).integral CReal.zero)
            (halfPow (k + 1)) := by
        exact regularSeqLtProp_sub_of_repClose_succ (k + 1)
          (repCloseAtGauge_symm hsmall_close)
      exact regularSeqLtProp_of_left_eventual
        (relEventually_symm
          (subSeq (h.cutSmallVal n).integral CReal.zero)
          (h.cutSmallVal n).integral
          (subSeq_zero_right_eventually (h.cutSmallVal n).integral)) hsub
    exact lemma43RepCloseAtGauge_zero_of_abs_le_ltC
      (lemma43CutAlphaIntegral_abs_le_cutSmallC D hnn n) hsmall_lt

/-- Lemma 4.3 data package currently needed downstream:
level sets between adjacent dyadic thresholds, plus the analytic cutoff
convergence `I(min(h, alpha_n)) -> 0`. -/
noncomputable def lemma43AlphaCutIntegralSeqC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h) : Nat → CReal :=
  fun n => (h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral

/-- Algebra helper for the Lemma 4.3 sandwich: `x - x ≈ 0`. -/
theorem lemma43SubSelfZeroC (x : CReal) : relEventually (CReal.sub x x) CReal.zero := by
  have hq : mkQuot (CReal.sub x x) = mkQuot CReal.zero := by
    change subQuot (mkQuot x) (mkQuot x) = zeroQuot
    letI : CommRing CRealQuot := cRealQuotCommRingConcreteWith cRatScalarMulArch
    let Xq : CRealQuot := mkQuot x
    change Xq - Xq = 0
    ring
  exact Quotient.exact hq

/-- Algebra helper for the Lemma 4.3 sandwich: `x * 0 ≈ 0`. -/
theorem lemma43MulZeroRightC (x : CReal) : CReal.mul x CReal.zero ≈ CReal.zero := by
  change relEventually (mulSeqConcreteWith cRatScalarMulArch x CReal.zero) CReal.zero
  exact mulSeqConcrete_zero_right_eventually cRatScalarMulArch x

/-- Lemma 4.3 sandwich atom, outside the level set (`χ≈0`). -/
theorem lemma43SubMulZeroRight_le_minC {φ α χ : CReal}
    (hχ0 : χ ≈ CReal.zero)
    (hφα : RegularSeqLe φ α) :
    RegularSeqLe (CReal.sub φ (CReal.mul χ φ)) (CReal.min φ α) := by
  have hprod0 : CReal.mul χ φ ≈ CReal.zero :=
    Setoid.trans
      (mulSeqConcrete_respects_eventually cRatScalarMulArch
        χ CReal.zero φ φ hχ0 (relEventually_refl φ))
      (zero_mul_equivC φ)
  have hsub : CReal.sub φ (CReal.mul χ φ) ≈ φ :=
    Setoid.trans
      (subSeq_respects_eventually φ φ (CReal.mul χ φ) CReal.zero
        (relEventually_refl φ) hprod0)
      (CReal.sub_zeroC φ)
  have hφmin : RegularSeqLe φ (CReal.min φ α) :=
    CReal.le_minC (regularSeqLe_refl φ) hφα
  exact regularSeqLe_of_left_eventual hsub hφmin

/-- Lemma 4.3 sandwich atom, inside the level set (`χ≈1`). -/
theorem lemma43SubMulOneRight_le_minC {φ α χ : CReal}
    (hχ1 : χ ≈ CReal.one)
    (hφ : RegularSeqNonneg φ) (hα : RegularSeqNonneg α) :
    RegularSeqLe (CReal.sub φ (CReal.mul χ φ)) (CReal.min φ α) := by
  have hprod1 : CReal.mul χ φ ≈ φ :=
    Setoid.trans
      (mulSeqConcrete_respects_eventually cRatScalarMulArch
        χ CReal.one φ φ hχ1 (relEventually_refl φ))
      (CReal.one_mul φ)
  have hsub : CReal.sub φ (CReal.mul χ φ) ≈ CReal.zero :=
    Setoid.trans
      (subSeq_respects_eventually φ φ (CReal.mul χ φ) φ
        (relEventually_refl φ) hprod1)
      (lemma43SubSelfZeroC φ)
  have h0min : RegularSeqLe CReal.zero (CReal.min φ α) :=
    regularSeqLe_zero_of_nonneg (lemma43Min_nonnegC hφ hα)
  exact regularSeqLe_of_left_eventual hsub h0min

/-- Lemma 4.3 sandwich pointwise atom:
if `χ` is the characteristic value of `{φ ≥ α}`, then
`φ - χ φ ≤ min(φ, α)`. -/
theorem lemma43SubMulChi_le_minC {φ α χ : CReal}
    (hφ : RegularSeqNonneg φ) (hα : RegularSeqNonneg α)
    (hχ : χ ≈ CReal.zero ∨ χ ≈ CReal.one)
    (hsmall : χ ≈ CReal.zero → RegularSeqLe φ α) :
    RegularSeqLe (CReal.sub φ (CReal.mul χ φ)) (CReal.min φ α) := by
  rcases hχ with h0 | h1
  · exact lemma43SubMulZeroRight_le_minC h0 (hsmall h0)
  · exact lemma43SubMulOneRight_le_minC h1 hφ hα


-- This expands several `RepSeriesSum` wrappers through `prop_1_11C`.
set_option maxHeartbeats 1000000 in
/-- Lemma 4.3 sandwich atom: `phi - chi*phi` is nonnegative when `chi = 0`. -/
theorem lemma43SubMulZeroRight_nonnegC {φ χ : CReal}
    (hχ0 : χ ≈ CReal.zero) (hφ : RegularSeqNonneg φ) :
    RegularSeqNonneg (CReal.sub φ (CReal.mul χ φ)) := by
  have hmul0 : CReal.mul χ φ ≈ CReal.zero :=
    Setoid.trans
      (mulSeqConcrete_respects_eventually cRatScalarMulArch χ CReal.zero φ φ
        hχ0 (Setoid.refl φ))
      (zero_mul_equivC φ)
  have hsub : CReal.sub φ (CReal.mul χ φ) ≈ CReal.sub φ CReal.zero :=
    subSeq_respects_eventually φ φ (CReal.mul χ φ) CReal.zero
      (relEventually_refl φ) hmul0
  have hzero : CReal.sub φ CReal.zero ≈ φ := subSeq_zero_right_eventually φ
  exact regularSeqNonneg_of_eventual (Setoid.trans hsub hzero) hφ

/-- Lemma 4.3 sandwich atom: `phi - chi*phi` is nonnegative when `chi = 1`. -/
theorem lemma43SubMulOneRight_nonnegC {φ χ : CReal}
    (hχ1 : χ ≈ CReal.one) :
    RegularSeqNonneg (CReal.sub φ (CReal.mul χ φ)) := by
  have hmul1 : CReal.mul χ φ ≈ φ :=
    Setoid.trans
      (mulSeqConcrete_respects_eventually cRatScalarMulArch χ CReal.one φ φ
        hχ1 (Setoid.refl φ))
      (CReal.one_mul φ)
  have hsub : CReal.sub φ (CReal.mul χ φ) ≈ CReal.sub φ φ :=
    subSeq_respects_eventually φ φ (CReal.mul χ φ) φ
      (relEventually_refl φ) hmul1
  exact regularSeqNonneg_of_eventual
    (Setoid.trans hsub (lemma43SubSelfZeroC φ)) regularSeqNonneg_zero

/-- Lemma 4.3 sandwich atom: `phi - chi*phi` is nonnegative for characteristic `chi`. -/
theorem lemma43SubMulChi_nonnegC {φ χ : CReal}
    (hφ : RegularSeqNonneg φ)
    (hχ : χ ≈ CReal.zero ∨ χ ≈ CReal.one) :
    RegularSeqNonneg (CReal.sub φ (CReal.mul χ φ)) := by
  rcases hχ with h0 | h1
  · exact lemma43SubMulZeroRight_nonnegC h0 hφ
  · exact lemma43SubMulOneRight_nonnegC h1

-- Same pointwise expansion pattern as `lemma43ComplementIntegral_le_cutAlphaC`.
set_option maxHeartbeats 1000000 in
/-- Complement part of Lemma 4.3 is nonnegative after integration. -/
theorem lemma43ComplementIntegral_nonnegC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) (n : Nat) :
    RegularSeqNonneg
      (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)).integral := by
  let A := D.A n
  let hA := D.hA n
  let chi := IntegrableRepC3.prop_4_2_chi_f_repC A hA h
  let r0 := h.sub h
  let rL := h.sub chi
  have hzero_le : RegularSeqLe r0.integral rL.integral := by
    refine prop_1_11C
      (isFull_interC (isFull_interC (isFull_interC (isFull_interC
        r0.domain_isFull rL.domain_isFull) h.domain_isFull)
        chi.domain_isFull) hA.rep.domain_isFull)
      r0 rL ?_
    intro x hx hr hr'
    obtain ⟨⟨⟨⟨hx0, hxL⟩, hxh⟩, hxchi⟩, hxAchi⟩ := hx
    obtain ⟨_, ⟨_h0abs⟩⟩ := hx0
    obtain ⟨_, ⟨_hLabs⟩⟩ := hxL
    obtain ⟨_, ⟨hhabs⟩⟩ := hxh
    obtain ⟨_, ⟨hchiabs⟩⟩ := hxchi
    obtain ⟨_, ⟨hAchiabs⟩⟩ := hxAchi
    let hv := seriesSum_of_absC hhabs
    let chiVal := seriesSum_of_absC hAchiabs
    let chiFVal := seriesSum_of_absC hchiabs
    have hchi_value : chiFVal.sum ≈ CReal.mul chiVal.sum hv.sum := by
      exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hA h hnn
        hchiabs hAchiabs hhabs
    let hsub0Model := sub_seriesSum_valueC3 (r := h) (r' := h) (x := x) hv hv
    have hsub0_to_sub : hsub0Model.sum ≈ CReal.sub hv.sum hv.sum := by
      change relEventually (addSeq hv.sum (negSeq hv.sum)) (subSeq hv.sum hv.sum)
      exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually hv.sum hv.sum)
    have h0canon : hr.sum ≈ CReal.sub hv.sum hv.sum := by
      exact Setoid.trans (repSeriesSum_unique hr hsub0Model) hsub0_to_sub
    let hsubModel := sub_seriesSum_valueC3 (r := h) (r' := chi) (x := x) hv chiFVal
    have hmodel_to_subchi : hsubModel.sum ≈ CReal.sub hv.sum chiFVal.sum := by
      change relEventually (addSeq hv.sum (negSeq chiFVal.sum))
        (subSeq hv.sum chiFVal.sum)
      exact relEventually_symm _ _
        (subSeq_eq_add_neg_eventually hv.sum chiFVal.sum)
    have hsub_to_canon :
        hsubModel.sum ≈ CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum) := by
      have hsub_transport :
          CReal.sub hv.sum chiFVal.sum ≈
            CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum) := by
        exact subSeq_respects_eventually hv.sum hv.sum chiFVal.sum
          (CReal.mul chiVal.sum hv.sum) (relEventually_refl hv.sum) hchi_value
      exact Setoid.trans hmodel_to_subchi hsub_transport
    have hLcanon : hr'.sum ≈ CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum) := by
      exact Setoid.trans (repSeriesSum_unique hr' hsubModel) hsub_to_canon
    have hvalid := hA.valid x hAchiabs
    have hχ01 : chiVal.sum ≈ CReal.zero ∨ chiVal.sum ≈ CReal.one := by
      rcases hvalid.1 with hxS1 | hxS2
      · exact Or.inr (hvalid.2.1 hxS1 chiVal)
      · exact Or.inl (hvalid.2.2 hxS2 chiVal)
    have hright_nn : RegularSeqNonneg
        (CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum)) :=
      lemma43SubMulChi_nonnegC (hnn x hhabs hv) hχ01
    have hmid : RegularSeqLe
        (CReal.sub hv.sum hv.sum)
        (CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum)) :=
      regularSeqLe_of_left_eventual (lemma43SubSelfZeroC hv.sum)
        (regularSeqLe_zero_of_nonneg hright_nn)
    exact regularSeqLe_of_left_eventual h0canon
      (regularSeqLe_of_right_eventual (Setoid.symm hLcanon) hmid)
  have hr0_zero : r0.integral ≈ CReal.zero := by
    dsimp [r0]
    rw [IntegrableRepC3.integral_sub]
    have htoSub : addSeq h.integral (negSeq h.integral) ≈ CReal.sub h.integral h.integral := by
      exact relEventually_symm _ _
        (subSeq_eq_add_neg_eventually h.integral h.integral)
    exact Setoid.trans htoSub (lemma43SubSelfZeroC h.integral)
  exact regularSeqNonneg_of_zero_le
    (regularSeqLe_of_left_eventual (Setoid.symm hr0_zero) hzero_le)


/-- Complement part of Lemma 4.3 sandwich: the integral of `h - chi_A * h`
is bounded by the alpha cut.  Pointwise, `chi_A` is `0` outside `A` and
`1` inside `A`; outside `A` the lower level-set condition gives `h < alpha`. -/
theorem lemma43ComplementIntegral_le_cutAlphaC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) (n : Nat) :
    RegularSeqLe
      (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)).integral
      (h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral := by
  let A := D.A n
  let hA := D.hA n
  let chi := IntegrableRepC3.prop_4_2_chi_f_repC A hA h
  let rL := h.sub chi
  let rR := h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)
  change RegularSeqLe rL.integral rR.integral
  refine prop_1_11C
    (isFull_interC (isFull_interC (isFull_interC (isFull_interC
      rL.domain_isFull rR.domain_isFull) h.domain_isFull)
      chi.domain_isFull) hA.rep.domain_isFull)
    rL rR ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨hxL, hxR⟩, hxh⟩, hxchi⟩, hxAchi⟩ := hx
  obtain ⟨_, ⟨_hLabs⟩⟩ := hxL
  obtain ⟨_, ⟨_hRabs⟩⟩ := hxR
  obtain ⟨_, ⟨hhabs⟩⟩ := hxh
  obtain ⟨_, ⟨hchiabs⟩⟩ := hxchi
  obtain ⟨_, ⟨hAchiabs⟩⟩ := hxAchi
  let hv := seriesSum_of_absC hhabs
  let chiVal := seriesSum_of_absC hAchiabs
  let chiFVal := seriesSum_of_absC hchiabs
  have hchi_value : chiFVal.sum ≈ CReal.mul chiVal.sum hv.sum := by
    exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hA h hnn
      hchiabs hAchiabs hhabs
  let hsubModel := sub_seriesSum_valueC3 (r := h) (r' := chi) (x := x) hv chiFVal
  have hmodel_to_subchi : hsubModel.sum ≈ CReal.sub hv.sum chiFVal.sum := by
    change relEventually (addSeq hv.sum (negSeq chiFVal.sum))
      (subSeq hv.sum chiFVal.sum)
    exact relEventually_symm _ _
      (subSeq_eq_add_neg_eventually hv.sum chiFVal.sum)
  have hsub_to_canon :
      hsubModel.sum ≈ CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum) := by
    have hsub_transport :
        CReal.sub hv.sum chiFVal.sum ≈
          CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum) := by
      exact subSeq_respects_eventually hv.sum hv.sum chiFVal.sum
        (CReal.mul chiVal.sum hv.sum) (relEventually_refl hv.sum) hchi_value
    exact Setoid.trans hmodel_to_subchi hsub_transport
  have hLcanon : hr.sum ≈ CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum) := by
    exact Setoid.trans (repSeriesSum_unique hr hsubModel) hsub_to_canon
  obtain ⟨hcutModel, hcut_eq⟩ :=
    h.cutConstVal_signed_valueC (D.alpha n) (lemma43AlphaNonnegC D n) x hv
  have hRcanon : hr'.sum ≈ CReal.min hv.sum (D.alpha n) := by
    exact Setoid.trans (repSeriesSum_unique hr' hcutModel) hcut_eq
  have hvalid := hA.valid x hAchiabs
  have hmid : RegularSeqLe
      (CReal.sub hv.sum (CReal.mul chiVal.sum hv.sum))
      (CReal.min hv.sum (D.alpha n)) := by
    rcases hvalid.1 with hxS1 | hxS2
    · have hχ1 : chiVal.sum ≈ CReal.one := hvalid.2.1 hxS1 chiVal
      exact lemma43SubMulOneRight_le_minC hχ1
        (hnn x hhabs hv) (lemma43AlphaNonnegC D n)
    · have hχ0 : chiVal.sum ≈ CReal.zero := hvalid.2.2 hxS2 chiVal
      have hxLower : x ∈ thm36D_lowerSetC h (D.alpha n) := by
        rw [← D.A_s2 n]
        exact hxS2
      rcases hxLower with ⟨_hxdom, hxv0, hlt⟩
      have hltv : regularSeqLtProp hv.sum (D.alpha n) := by
        exact regularSeqLtProp_of_left_eventual (repSeriesSum_unique hv hxv0) hlt
      have hsmall : RegularSeqLe hv.sum (D.alpha n) :=
        regularSeqLe_of_ltPropC hltv
      exact lemma43SubMulZeroRight_le_minC hχ0 hsmall
  exact regularSeqLe_of_left_eventual hLcanon
    (regularSeqLe_of_right_eventual (Setoid.symm hRcanon) hmid)


/-- Lemma 4.3 complement integral absolute estimate. -/
theorem lemma43ComplementIntegral_abs_le_cutSmallC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) (n : Nat) :
    RegularSeqLe
      (CReal.abs
        ((h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)).integral))
      (h.cutSmallVal n).integral := by
  let rcomp := h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)
  have hcomp_nn : RegularSeqNonneg rcomp.integral := by
    simpa [rcomp] using lemma43ComplementIntegral_nonnegC D hnn n
  have habs_le_integral : RegularSeqLe (CReal.abs rcomp.integral) rcomp.integral :=
    regularSeqLe_abs_of_nonneg (regularSeqLe_zero_of_nonneg hcomp_nn)
  have hintegral_le_alpha :
      RegularSeqLe rcomp.integral
        (h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral := by
    simpa [rcomp] using lemma43ComplementIntegral_le_cutAlphaC D hnn n
  have halpha_le_small :
      RegularSeqLe
        (h.cutConstVal (D.alpha n) (lemma43AlphaNonnegC D n)).integral
        (h.cutSmallVal n).integral :=
    lemma43CutAlphaIntegral_le_cutSmallC D hnn n
  exact regularSeqLe_trans habs_le_integral
    (regularSeqLe_trans hintegral_le_alpha halpha_le_small)

/-- Lemma 4.3 complement integral tends to zero. -/
def lemma43ComplementIntegral_tendsto_zeroC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) :
    RepSeriesTendsto
      (fun n =>
        (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)).integral)
      CReal.zero where
  mod := fun k => (IntegrableRepC3.cutSmall_tendsto_rep h).mod (k + 1)
  close := by
    intro k n hn
    let smallT := IntegrableRepC3.cutSmall_tendsto_rep h
    have hsmall_close :
        RepCloseAtGauge ((k + 1) + 1) (h.cutSmallVal n).integral CReal.zero :=
      smallT.close (k + 1) n hn
    have hsmall_lt :
        regularSeqLtProp (h.cutSmallVal n).integral (halfPow (k + 1)) := by
      have hsub :
          regularSeqLtProp
            (subSeq (h.cutSmallVal n).integral CReal.zero)
            (halfPow (k + 1)) := by
        exact regularSeqLtProp_sub_of_repClose_succ (k + 1)
          (repCloseAtGauge_symm hsmall_close)
      exact regularSeqLtProp_of_left_eventual
        (relEventually_symm
          (subSeq (h.cutSmallVal n).integral CReal.zero)
          (h.cutSmallVal n).integral
          (subSeq_zero_right_eventually (h.cutSmallVal n).integral)) hsub
    exact lemma43RepCloseAtGauge_zero_of_abs_le_ltC
      (lemma43ComplementIntegral_abs_le_cutSmallC D hnn n) hsmall_lt

/-- Measure-bridge algebra for Lemma 4.3:
the complement over `C` is bounded by the complement over `A` plus the
relative integral over the set difference `A \ C`. -/
theorem lemma43ComplementIntegral_le_complement_plus_setdiffC {X : Type*} {S : IntSpaceC X}
    {A C : BishopC.BSet X} (hA : IntegrableSet1C S A) (hC : IntegrableSet1C S C)
    (h : IntegrableRepC3 S) (hnn : RepNonnegC h) :
    RegularSeqLe
      (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC h)).integral
      (addSeq
        (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC A hA h)).integral
        (relIntegralC (A.sub C) (IntegrableSet1_subC hA hC) h)) := by
  let IA : CReal := relIntegralC A hA h
  let IC : CReal := relIntegralC C hC h
  let IAC : CReal := relIntegralC (A.sub C) (IntegrableSet1_subC hA hC) h
  let compA : CReal :=
    (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC A hA h)).integral
  let compC : CReal :=
    (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC h)).integral
  have hset : RegularSeqLe IA (addSeq IC IAC) := by
    simpa [IA, IC, IAC] using relIntegral_le_setC_plus_setdiffC hA hC h hnn
  have hAadd : RegularSeqLe (addSeq IA compA) (addSeq (addSeq IC IAC) compA) := by
    exact regularSeqLe_add hset (regularSeqLe_refl compA)
  have hcompC_to_H : compC.add IC ≈ h.integral := by
    have hcomm : compC.add IC ≈ IC.add compC := addSeq_comm_eventually compC IC
    exact Setoid.trans hcomm
      (by simpa [IC, compC] using relIntegral_complement_additiveC hC h)
  have hH_to_compA : h.integral ≈ IA.add compA := by
    exact Setoid.symm
      (by simpa [IA, compA] using relIntegral_complement_additiveC hA h)
  have hleft_event : compC.add IC ≈ addSeq IA compA :=
    Setoid.trans hcompC_to_H hH_to_compA
  have hright_event : addSeq (addSeq IC IAC) compA ≈
      addSeq (addSeq compA IAC) IC := by
    calc
      addSeq (addSeq IC IAC) compA ≈ addSeq IC (addSeq IAC compA) :=
        addSeq_assoc_eventually IC IAC compA
      _ ≈ addSeq IC (addSeq compA IAC) :=
        addSeq_respects_eventually IC IC (addSeq IAC compA) (addSeq compA IAC)
          (relEventually_refl IC) (addSeq_comm_eventually IAC compA)
      _ ≈ addSeq (addSeq compA IAC) IC :=
        addSeq_comm_eventually IC (addSeq compA IAC)
  have hwithIC : RegularSeqLe (addSeq compC IC) (addSeq (addSeq compA IAC) IC) := by
    exact regularSeqLe_of_right_eventual hright_event
      (regularSeqLe_of_left_eventual hleft_event hAadd)
  have hcancel := regularSeqLe_cancel_add_right hwithIC
  simpa [compA, compC, IAC] using hcancel

/-- Scalar atom for the uniform-complement bridge:
for a characteristic value `chi`, pointwise domination `phi <= psi` implies
`phi - chi*phi <= psi - chi*psi`. -/
theorem lemma43SubMulChi_monoC {φ ψ χ : CReal}
    (hχ : χ ≈ CReal.zero ∨ χ ≈ CReal.one)
    (hle : RegularSeqLe φ ψ) :
    RegularSeqLe
      (CReal.sub φ (CReal.mul χ φ))
      (CReal.sub ψ (CReal.mul χ ψ)) := by
  rcases hχ with h0 | h1
  · have hmulL : CReal.mul χ φ ≈ CReal.zero :=
      Setoid.trans
        (mulSeqConcrete_respects_eventually cRatScalarMulArch χ CReal.zero φ φ
          h0 (relEventually_refl φ))
        (zero_mul_equivC φ)
    have hmulR : CReal.mul χ ψ ≈ CReal.zero :=
      Setoid.trans
        (mulSeqConcrete_respects_eventually cRatScalarMulArch χ CReal.zero ψ ψ
          h0 (relEventually_refl ψ))
        (zero_mul_equivC ψ)
    have hleft : CReal.sub φ (CReal.mul χ φ) ≈ φ :=
      Setoid.trans
        (subSeq_respects_eventually φ φ (CReal.mul χ φ) CReal.zero
          (relEventually_refl φ) hmulL)
        (CReal.sub_zeroC φ)
    have hright : CReal.sub ψ (CReal.mul χ ψ) ≈ ψ :=
      Setoid.trans
        (subSeq_respects_eventually ψ ψ (CReal.mul χ ψ) CReal.zero
          (relEventually_refl ψ) hmulR)
        (CReal.sub_zeroC ψ)
    exact regularSeqLe_of_left_eventual hleft
      (regularSeqLe_of_right_eventual (Setoid.symm hright) hle)
  · have hmulL : CReal.mul χ φ ≈ φ :=
      Setoid.trans
        (mulSeqConcrete_respects_eventually cRatScalarMulArch χ CReal.one φ φ
          h1 (relEventually_refl φ))
        (CReal.one_mul φ)
    have hmulR : CReal.mul χ ψ ≈ ψ :=
      Setoid.trans
        (mulSeqConcrete_respects_eventually cRatScalarMulArch χ CReal.one ψ ψ
          h1 (relEventually_refl ψ))
        (CReal.one_mul ψ)
    have hleft : CReal.sub φ (CReal.mul χ φ) ≈ CReal.zero :=
      Setoid.trans
        (subSeq_respects_eventually φ φ (CReal.mul χ φ) φ
          (relEventually_refl φ) hmulL)
        (lemma43SubSelfZeroC φ)
    have hright : CReal.sub ψ (CReal.mul χ ψ) ≈ CReal.zero :=
      Setoid.trans
        (subSeq_respects_eventually ψ ψ (CReal.mul χ ψ) ψ
          (relEventually_refl ψ) hmulR)
        (lemma43SubSelfZeroC ψ)
    exact regularSeqLe_of_left_eventual hleft
      (regularSeqLe_of_right_eventual (Setoid.symm hright)
        (regularSeqLe_refl CReal.zero))

set_option maxHeartbeats 1000000 in
-- reason: expands the same pointwise `prop_1_11C` domain/value plumbing used by Lemma 4.3.
/-- Complement integrals are monotone under pointwise domination. -/
theorem lemma43ComplementIntegral_le_of_le_funC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C)
    (g g' : IntegrableRepC3 S) (hnn : RepNonnegC g) (hnn' : RepNonnegC g')
    (hle : ∀ (x : X)
      (gv : RepSeriesSum fun k => (g.fn k).toFun x)
      (gv' : RepSeriesSum fun k => (g'.fn k).toFun x),
        RegularSeqLe gv.sum gv'.sum) :
    RegularSeqLe
      (g.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC g)).integral
      (g'.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC g')).integral := by
  let chiG := IntegrableRepC3.prop_4_2_chi_f_repC C hC g
  let chiG' := IntegrableRepC3.prop_4_2_chi_f_repC C hC g'
  let rL := g.sub chiG
  let rR := g'.sub chiG'
  change RegularSeqLe rL.integral rR.integral
  refine prop_1_11C
    (isFull_interC (isFull_interC (isFull_interC (isFull_interC (isFull_interC
      rL.domain_isFull rR.domain_isFull) g.domain_isFull)
      g'.domain_isFull) chiG.domain_isFull)
      (isFull_interC chiG'.domain_isFull hC.rep.domain_isFull))
    rL rR ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨⟨hxL, hxR⟩, hxg⟩, hxg'⟩, hxchiG⟩, hxchiG_hC⟩ := hx
  obtain ⟨hxchiG', hxCchi⟩ := hxchiG_hC
  obtain ⟨_, ⟨_hLabs⟩⟩ := hxL
  obtain ⟨_, ⟨_hRabs⟩⟩ := hxR
  obtain ⟨_, ⟨hgabs⟩⟩ := hxg
  obtain ⟨_, ⟨hg'abs⟩⟩ := hxg'
  obtain ⟨_, ⟨hchiGabs⟩⟩ := hxchiG
  obtain ⟨_, ⟨hchiG'abs⟩⟩ := hxchiG'
  obtain ⟨_, ⟨hCchiabs⟩⟩ := hxCchi
  let gv := seriesSum_of_absC hgabs
  let gv' := seriesSum_of_absC hg'abs
  let chiVal := seriesSum_of_absC hCchiabs
  let chiGVal := seriesSum_of_absC hchiGabs
  let chiG'Val := seriesSum_of_absC hchiG'abs
  have hchiG_value : chiGVal.sum ≈ CReal.mul chiVal.sum gv.sum := by
    exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC g hnn
      hchiGabs hCchiabs hgabs
  have hchiG'_value : chiG'Val.sum ≈ CReal.mul chiVal.sum gv'.sum := by
    exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC g' hnn'
      hchiG'abs hCchiabs hg'abs
  let hsubL := sub_seriesSum_valueC3 (r := g) (r' := chiG) (x := x) gv chiGVal
  let hsubR := sub_seriesSum_valueC3 (r := g') (r' := chiG') (x := x) gv' chiG'Val
  have hmodelL_to_sub : hsubL.sum ≈ CReal.sub gv.sum chiGVal.sum := by
    change relEventually (addSeq gv.sum (negSeq chiGVal.sum))
      (subSeq gv.sum chiGVal.sum)
    exact relEventually_symm _ _
      (subSeq_eq_add_neg_eventually gv.sum chiGVal.sum)
  have hmodelR_to_sub : hsubR.sum ≈ CReal.sub gv'.sum chiG'Val.sum := by
    change relEventually (addSeq gv'.sum (negSeq chiG'Val.sum))
      (subSeq gv'.sum chiG'Val.sum)
    exact relEventually_symm _ _
      (subSeq_eq_add_neg_eventually gv'.sum chiG'Val.sum)
  have hLcanon : hr.sum ≈ CReal.sub gv.sum (CReal.mul chiVal.sum gv.sum) := by
    have htransport : CReal.sub gv.sum chiGVal.sum ≈
        CReal.sub gv.sum (CReal.mul chiVal.sum gv.sum) :=
      subSeq_respects_eventually gv.sum gv.sum chiGVal.sum
        (CReal.mul chiVal.sum gv.sum) (relEventually_refl gv.sum) hchiG_value
    exact Setoid.trans (Setoid.trans (repSeriesSum_unique hr hsubL) hmodelL_to_sub)
      htransport
  have hRcanon : hr'.sum ≈ CReal.sub gv'.sum (CReal.mul chiVal.sum gv'.sum) := by
    have htransport : CReal.sub gv'.sum chiG'Val.sum ≈
        CReal.sub gv'.sum (CReal.mul chiVal.sum gv'.sum) :=
      subSeq_respects_eventually gv'.sum gv'.sum chiG'Val.sum
        (CReal.mul chiVal.sum gv'.sum) (relEventually_refl gv'.sum) hchiG'_value
    exact Setoid.trans (Setoid.trans (repSeriesSum_unique hr' hsubR) hmodelR_to_sub)
      htransport
  have hvalid := hC.valid x hCchiabs
  have hχ01 : chiVal.sum ≈ CReal.zero ∨ chiVal.sum ≈ CReal.one := by
    rcases hvalid.1 with hxS1 | hxS2
    · exact Or.inr (hvalid.2.1 hxS1 chiVal)
    · exact Or.inl (hvalid.2.2 hxS2 chiVal)
  have hmid : RegularSeqLe
      (CReal.sub gv.sum (CReal.mul chiVal.sum gv.sum))
      (CReal.sub gv'.sum (CReal.mul chiVal.sum gv'.sum)) :=
    lemma43SubMulChi_monoC hχ01 (hle x gv gv')
  exact regularSeqLe_of_left_eventual hLcanon
    (regularSeqLe_of_right_eventual (Setoid.symm hRcanon) hmid)


/-- Lemma 4.3 main convergence: the relative integrals over the level sets tend to `I(h)`. -/
def lemma43RelIntegral_tendsto_integralC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) :
    RepSeriesTendsto
      (fun n => relIntegralC (D.A n) (D.hA n) h)
      h.integral where
  mod := fun k => (lemma43ComplementIntegral_tendsto_zeroC D hnn).mod (k + 3)
  close := by
    intro k n hn
    let compT := lemma43ComplementIntegral_tendsto_zeroC D hnn
    let x := relIntegralC (D.A n) (D.hA n) h
    let c := (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)).integral
    have hc : RepCloseAtGauge ((k + 3) + 1) c CReal.zero := by
      simpa [c] using compT.close (k + 3) n hn
    have h1 : RepCloseAtGauge (k + 3) x (addSeq x CReal.zero) :=
      bc1_repClose_of_relEventually
        (relEventually_symm _ _ (addSeq_zero_right_eventually x)) (k + 3)
    have h2 : RepCloseAtGauge (k + 3) (addSeq x CReal.zero) (addSeq x c) := by
      exact bc1_repCloseAtGauge_add (k + 3)
        (bc1_repClose_of_relEventually (relEventually_refl x) ((k + 3) + 1))
        (repCloseAtGauge_symm hc)
    have h12 : RepCloseAtGauge (k + 2) x (addSeq x c) :=
      repCloseAtGauge_triangle_succ (k + 2) h1 h2
    have hadd : relEventually (addSeq x c) h.integral := by
      simpa [x, c, relIntegralC] using relIntegral_complement_additiveC (D.hA n) h
    have h3 : RepCloseAtGauge (k + 2) (addSeq x c) h.integral :=
      bc1_repClose_of_relEventually hadd (k + 2)
    exact repCloseAtGauge_triangle_succ (k + 1) h12 h3



/-- Data-valued dyadic absolute continuity: explicit delta for epsilon `2^-K`. -/
noncomputable def relIntegral_abs_continuous_delta_halfPowDataC {X : Type*} {S : IntSpaceC X}
    (g : IntegrableRepC3 S) (hnn : RepNonnegC g) (K : Nat) :
    Sigma (fun delta : CReal =>
      PProd (regularSeqLtProp CReal.zero delta)
        (∀ (C : BishopC.BSet X) (hC : IntegrableSet1C S C),
          regularSeqLtProp (hC.rep.integral) delta →
            regularSeqLtProp (relIntegralC C hC g) (halfPow K))) := by
  let k : Nat := K + 2
  let n : Nat := g.cutNat_tendsto_rep.mod k
  let denom : CReal := constSeq (Nat.cast (n + 1))
  let hpos : PosEventuallyData denom := natCast_succ_posDataC n
  let delta : CReal := CReal.mul (halfPow k) (CReal.invPos denom hpos)
  have hdenom_lt : regularSeqLtProp CReal.zero denom :=
    regularSeqLtProp_zero_of_posData hpos
  have hdelta_pos : regularSeqLtProp CReal.zero delta :=
    CReal.mul_pos_E (regularSeqLtProp_zero_halfPow k)
      (regularSeqLtProp_zero_of_posData (CReal.invPos_posData denom hpos))
  refine ⟨delta, ⟨hdelta_pos, ?_⟩⟩
  intro C hC hmu
  have hmain := relIntegral_le_cut_boundC hC g hnn k
  have hmu_nonneg : RegularSeqNonneg (hC.rep.integral) := by
    have hrepnn : RepNonnegC hC.rep := IntegrableSet1_repNonnegC hC
    have heq : hC.rep.normL1 ≈ hC.rep.integral :=
      hC.rep.normL1_eq_integral_of_nonnegC hrepnn
    exact regularSeqNonneg_of_eventual (Setoid.symm heq)
      (IntegrableRepC3.normL1_nonnegC hC.rep)
  have h1 : regularSeqLtProp (CReal.mul denom hC.rep.integral) (CReal.mul denom delta) :=
    mul_lt_mul_of_pos_leftC hmu hdenom_lt
  have h2 : CReal.mul denom delta ≈ halfPow k :=
    mul_invPos_scale_cancelC denom (halfPow k) hpos
  have h3 : regularSeqLtProp (CReal.mul denom hC.rep.integral) (halfPow k) :=
    regularSeqLtProp_of_right_eventual h2 h1
  have hn_le : RegularSeqLe (constSeq (Nat.cast n)) (constSeq (Nat.cast (n + 1))) :=
    natCast_le_of_leC (Nat.le_succ n)
  have h4 : RegularSeqLe (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral)
      (CReal.mul denom hC.rep.integral) :=
    regularSeqLe_mul_right_of_nonnegC hn_le hmu_nonneg
  have h5 : regularSeqLtProp (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k) :=
    regularSeqLtProp_of_le_of_lt h4 h3
  have h6 : regularSeqLtProp
      (addSeq (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k))
      (addSeq (halfPow k) (halfPow k)) := by
    have hL := regularSeqLtProp_add_left (halfPow k)
      (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k) h5
    exact regularSeqLtProp_of_left_eventual
      (addSeq_comm_eventually
        (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k)) hL
  have h7 : addSeq (halfPow k) (halfPow k) ≈ halfPow (K + 1) := by
    simpa [k, Nat.add_assoc] using halfPow_succ_add_self (K + 1)
  have h8 : regularSeqLtProp
      (addSeq (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k))
      (halfPow (K + 1)) :=
    regularSeqLtProp_of_right_eventual h7 h6
  have h9 : regularSeqLtProp
      (addSeq (CReal.mul (constSeq (Nat.cast n)) hC.rep.integral) (halfPow k))
      (halfPow K) :=
    regularSeqLtProp_trans _ _ _ h8 (regularSeqLtProp_halfPow_succ K)
  exact regularSeqLtProp_of_le_of_lt hmain h9

/-- Set-difference specialization of dyadic absolute continuity. -/
noncomputable def relIntegral_abs_continuous_setdiff_halfPowDataC {X : Type*} {S : IntSpaceC X}
    (g : IntegrableRepC3 S) (hnn : RepNonnegC g) (K : Nat) :
    Sigma (fun delta : CReal =>
      PProd (regularSeqLtProp CReal.zero delta)
        (∀ (A B : BishopC.BSet X) (hA : IntegrableSet1C S A) (hB : IntegrableSet1C S B),
          regularSeqLtProp ((IntegrableSet1_subC hA hB).rep.integral) delta →
            regularSeqLtProp (relIntegralC (BishopC.BSet.sub A B) (IntegrableSet1_subC hA hB) g)
              (halfPow K))) := by
  let d := relIntegral_abs_continuous_delta_halfPowDataC g hnn K
  refine ⟨d.1, ⟨d.2.1, ?_⟩⟩
  intro A B hA hB hmu
  exact d.2.2 (BishopC.BSet.sub A B) (IntegrableSet1_subC hA hB) hmu

/-- Data extraction from Lemma 4.3 complement convergence:
choose an explicit level-set index whose complement integral is below `2^-K`. -/
noncomputable def lemma43ComplementIntegral_lt_halfPowDataC {X : Type*} {S : IntSpaceC X}
    {h : IntegrableRepC3 S} (D : Lemma43LevelSetSeqDataC h)
    (hnn : RepNonnegC h) (K : Nat) :
    { n : Nat //
      regularSeqLtProp
        (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)).integral
        (halfPow K) } := by
  let T := lemma43ComplementIntegral_tendsto_zeroC D hnn
  let n : Nat := T.mod K
  refine ⟨n, ?_⟩
  let c : CReal :=
    (h.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A n) (D.hA n) h)).integral
  have hclose : RepCloseAtGauge (K + 1) c CReal.zero := by
    simpa [T, n, c] using T.close K n (Nat.le_refl n)
  have hsub : regularSeqLtProp (subSeq c CReal.zero) (halfPow K) := by
    have hraw :=
      regularSeqLtProp_sub_of_repClose_succ K (repCloseAtGauge_symm hclose)
    simpa [halfPow, CReal.epsSeq] using hraw
  exact regularSeqLtProp_of_left_eventual
    (relEventually_symm (subSeq c CReal.zero) c (subSeq_zero_right_eventually c)) hsub

/-- Dyadic uniform-complement data from a nonnegative majorant.
This is the Lemma 4.3 measure-bridge input needed by Lemma 4.14/4.15:
if every `fn n` is pointwise bounded by `g`, then for epsilon `2^-K` there is
an explicit level set `A` and explicit `delta` such that small `A \ C`
measure forces the complement of `fn n` outside `C` below `2^-K`. -/
noncomputable def lemma43UniformComplementData_of_majorant_halfPowC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (D : Lemma43LevelSetSeqDataC g)
    (hdom : ∀ n (x : X)
      (fv : RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe fv.sum gv.sum)
    (K : Nat) :
    Lemma414UniformComplementDataC fn hnn (halfPow K) := by
  let aData := lemma43ComplementIntegral_lt_halfPowDataC D hgnn (K + 1)
  let m : Nat := aData.1
  let d := relIntegral_abs_continuous_setdiff_halfPowDataC g hgnn (K + 1)
  refine {
    A := D.A m
    hA := D.hA m
    N := 0
    delta := d.1
    delta_pos := d.2.1
    small := ?_
  }
  intro n _hn C hC hmu
  let compFn : CReal :=
    ((fn n).sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC (fn n))).integral
  let compG_C : CReal :=
    (g.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC g)).integral
  let compG_A : CReal :=
    (g.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A m) (D.hA m) g)).integral
  let iAC : CReal :=
    relIntegralC ((D.A m).sub C) (IntegrableSet1_subC (D.hA m) hC) g
  have hle_dom : RegularSeqLe compFn compG_C := by
    simpa [compFn, compG_C] using
      lemma43ComplementIntegral_le_of_le_funC hC (fn n) g (hnn n) hgnn (hdom n)
  have hle_split : RegularSeqLe compG_C (addSeq compG_A iAC) := by
    simpa [compG_C, compG_A, iAC] using
      lemma43ComplementIntegral_le_complement_plus_setdiffC (D.hA m) hC g hgnn
  have hcomp : regularSeqLtProp compG_A (halfPow (K + 1)) := by
    simpa [aData, m, compG_A] using aData.2
  have hdiff : regularSeqLtProp iAC (halfPow (K + 1)) := by
    simpa [d, m, iAC] using d.2.2 (D.A m) C (D.hA m) hC hmu
  have hsum : regularSeqLtProp (addSeq compG_A iAC)
      (addSeq (halfPow (K + 1)) (halfPow (K + 1))) :=
    regularSeqLtProp_add hcomp hdiff
  have hsumK : regularSeqLtProp (addSeq compG_A iAC) (halfPow K) :=
    regularSeqLtProp_of_right_eventual (halfPow_succ_add_self K) hsum
  exact regularSeqLtProp_of_le_of_lt
    (regularSeqLe_trans hle_dom hle_split) hsumK

/-- Data-valued dyadic lower bound for a positive presented real:
from `PosEventuallyData a` choose an explicit `K` with `2^-K < a`. -/
noncomputable def halfPow_lt_of_posDataC {a : CReal}
    (ha : PosEventuallyData a) :
    { K : Nat // regularSeqLtProp (halfPow K) a } := by
  refine ⟨ha.k + 2, ha.k + 2, ha.N, ?_⟩
  intro n hn
  have hnadd : ha.N ≤ addIndex n := by
    unfold addIndex
    omega
  have hgap : BishopC.COF.lt (eps ha.k) (a.val (addIndex n)) :=
    ha.tail_pos (addIndex n) hnadd
  change BishopC.COF.lt (eps (ha.k + 2)) (a.val (addIndex n) - eps (ha.k + 2))
  have hsum : BishopC.COF.lt (eps (ha.k + 2) + eps (ha.k + 2))
      (a.val (addIndex n)) := by
    rw [eps_succ_add_self (ha.k + 1)]
    exact scalarCOFOSeed.lt_trans (eps_succ_lt_eps ha.k) hgap
  have ht := BishopC.COF.lt_add_left (-(eps (ha.k + 2))) hsum
  rwa [
    show -(eps (ha.k + 2)) + (eps (ha.k + 2) + eps (ha.k + 2)) =
        eps (ha.k + 2) from by ring,
    show -(eps (ha.k + 2)) + a.val (addIndex n) =
        a.val (addIndex n) - eps (ha.k + 2) from by ring] at ht

/-- Uniform-complement data from a nonnegative majorant for arbitrary positive
epsilon.  This is the `hui` producer needed by the presented DCT bridge. -/
noncomputable def lemma43UniformComplementData_of_majorantC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (D : Lemma43LevelSetSeqDataC g)
    (hdom : ∀ n (x : X)
      (fv : RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe fv.sum gv.sum)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps) :
    Lemma414UniformComplementDataC fn hnn eps := by
  let kData := halfPow_lt_of_posDataC (posEventuallyData_of_pos_zeroC heps)
  let U := lemma43UniformComplementData_of_majorant_halfPowC
    fn hnn g hgnn D hdom kData.1
  exact {
    A := U.A
    hA := U.hA
    N := U.N
    delta := U.delta
    delta_pos := U.delta_pos
    small := by
      intro n hn C hC hmu
      exact regularSeqLtProp_trans _ _ _
        (U.small n hn C hC hmu) kData.2
  }

/-- Theorem 4.15 bridge with an explicit nonnegative majorant and Lemma 4.3
level-set data for that majorant.  The level-set data produces the uniform
complement data required by the existing presented DCT kernel. -/
noncomputable def thm_4_15_integral_convergence_from_majorant_measure_convergeC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (herr_nn : ∀ n, RepNonnegC (thm_4_15_abs_errorC fn f n))
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (D : Lemma43LevelSetSeqDataC g)
    (hdom : ∀ n (x : X)
      (ev : RepSeriesSum fun k => (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe ev.sum gv.sum)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_uniform_and_measure_convergeC
    fn f herr_nn
    (fun eps heps =>
      lemma43UniformComplementData_of_majorantC
        (thm_4_15_abs_errorC fn f) herr_nn g hgnn D hdom eps heps)
    hconv

/-- Theorem 4.15 bridge with the §3/§4 smooth-point data as input.
`Lemma43DyadicSmoothDataC` is first converted to the level-set sequence data of
Lemma 4.3, then the majorant bridge above supplies the DCT conclusion. -/
noncomputable def thm_4_15_integral_convergence_from_majorant_smooth_measure_convergeC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (herr_nn : ∀ n, RepNonnegC (thm_4_15_abs_errorC fn f n))
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC g)
    (hdom : ∀ n (x : X)
      (ev : RepSeriesSum fun k => (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe ev.sum gv.sum)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_majorant_measure_convergeC
    fn f herr_nn g hgnn
    (lemma43LevelSetSeqDataC_of_dyadicSmoothDataC g Dsmooth)
    hdom hconv

/-- The absolute-error row used in Theorem 4.15 is automatically nonnegative. -/
theorem thm_4_15_abs_error_nonnegC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S) (n : Nat) :
    RepNonnegC (thm_4_15_abs_errorC fn f n) := by
  simpa [thm_4_15_abs_errorC] using
    IntegrableRepC3_absVal_repNonnegC ((fn n).sub f)

/-- Theorem 4.15 bridge with the absolute-error nonnegativity supplied
canonically from `absVal`.  This removes the mechanical `herr_nn` input from
the majorant/measure-convergence wrapper. -/
noncomputable def thm_4_15_integral_convergence_from_majorant_measure_converge_autoNonnegC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (D : Lemma43LevelSetSeqDataC g)
    (hdom : ∀ n (x : X)
      (ev : RepSeriesSum fun k => (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe ev.sum gv.sum)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_majorant_measure_convergeC
    fn f (thm_4_15_abs_error_nonnegC fn f) g hgnn D hdom hconv

/-- Smooth-data version of the previous auto-nonnegative wrapper. -/
noncomputable def thm_4_15_integral_convergence_from_majorant_smooth_measure_converge_autoNonnegC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC g)
    (hdom : ∀ n (x : X)
      (ev : RepSeriesSum fun k => (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe ev.sum gv.sum)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_majorant_smooth_measure_convergeC
    fn f (thm_4_15_abs_error_nonnegC fn f) g hgnn Dsmooth hdom hconv

/-- Goal B, presented/data-carrying form:
from a nonnegative integrable majorant with §3/§4 smooth level-set data,
pointwise domination of the absolute-error representatives by that majorant,
and measure-convergence data of the absolute error to zero, obtain convergence
of the integrals.  All constructive witnesses remain explicit data. -/
noncomputable def goalB_dominated_convergence_dataC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC g)
    (hdom : ∀ n (x : X)
      (ev : RepSeriesSum fun k => (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe ev.sum gv.sum)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_majorant_smooth_measure_converge_autoNonnegC
    fn f g hgnn Dsmooth hdom hconv


/-- Pointwise nonnegativity is closed under addition of representatives. -/
theorem RepNonnegC_addC {X : Type*} {S : IntSpaceC X}
    (r s : IntegrableRepC3 S) (hr : RepNonnegC r) (hs : RepNonnegC s) :
    RepNonnegC (r.add s) := by
  intro x habs hx
  let hrabs : RepSeriesSum (fun k => absSeq ((r.fn k).toFun x)) :=
    add_absSeriesSum_leftC (r := r) (r' := s) (x := x) habs
  let hsabs : RepSeriesSum (fun k => absSeq ((s.fn k).toFun x)) :=
    add_absSeriesSum_rightC (r := r) (r' := s) (x := x) habs
  let hrv : RepSeriesSum (fun k => (r.fn k).toFun x) := seriesSum_of_absC hrabs
  let hsv : RepSeriesSum (fun k => (s.fn k).toFun x) := seriesSum_of_absC hsabs
  let hmodel : RepSeriesSum (fun k => ((r.add s).fn k).toFun x) :=
    add_seriesSum_valueC3 (r := r) (r' := s) (x := x) hrv hsv
  have hxeq : hx.sum ≈ hmodel.sum := repSeriesSum_unique hx hmodel
  exact regularSeqNonneg_of_eventual hxeq
    (regularSeqNonneg_add (hr x hrabs hrv) (hs x hsabs hsv))

/-- Scalar triangle inequality in the form `|a-b| <= |a|+|b|`. -/
theorem regularSeqLe_abs_sub_le_add_absC (a b : CReal) :
    RegularSeqLe (CReal.abs (CReal.sub a b))
      (CReal.add (CReal.abs a) (CReal.abs b)) := by
  have hleft : CReal.abs (CReal.sub a b) ≈ CReal.abs (CReal.add a (CReal.neg b)) :=
    absSeq_respects_eventually (CReal.sub a b) (CReal.add a (CReal.neg b))
      (subSeq_eq_add_neg_eventually a b)
  have htri : RegularSeqLe (CReal.abs (CReal.add a (CReal.neg b)))
      (CReal.add (CReal.abs a) (CReal.abs (CReal.neg b))) :=
    regularSeqLe_abs_add a (CReal.neg b)
  have hright : CReal.add (CReal.abs a) (CReal.abs (CReal.neg b)) ≈
      CReal.add (CReal.abs a) (CReal.abs b) :=
    addSeq_respects_eventually _ _ _ _ (relEventually_refl (CReal.abs a))
      (absSeq_negSeq_eventually b)
  exact regularSeqLe_of_left_eventual hleft
    (regularSeqLe_of_right_eventual hright htri)

set_option maxHeartbeats 1000000 in
-- reason: same pointwise `prop_1_11C` plumbing as `lemma43ComplementIntegral_le_of_le_funC`, with two extra witnesses.
/-- Complement-integral monotonicity where the pointwise domination may inspect
absolute-convergence witnesses for both representatives. -/
theorem lemma43ComplementIntegral_le_of_le_funWithAbsC {X : Type*} {S : IntSpaceC X}
    {C : BishopC.BSet X} (hC : IntegrableSet1C S C)
    (u v : IntegrableRepC3 S) (hunn : RepNonnegC u) (hvnn : RepNonnegC v)
    (hle : ∀ (x : X)
      (huabs : RepSeriesSum fun k => CReal.abs ((u.fn k).toFun x))
      (hvabs : RepSeriesSum fun k => CReal.abs ((v.fn k).toFun x))
      (huv : RepSeriesSum fun k => (u.fn k).toFun x)
      (hvv : RepSeriesSum fun k => (v.fn k).toFun x),
        RegularSeqLe huv.sum hvv.sum) :
    RegularSeqLe
      (u.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC u)).integral
      (v.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC v)).integral := by
  let chiU := IntegrableRepC3.prop_4_2_chi_f_repC C hC u
  let chiV := IntegrableRepC3.prop_4_2_chi_f_repC C hC v
  let rL := u.sub chiU
  let rR := v.sub chiV
  change RegularSeqLe rL.integral rR.integral
  refine prop_1_11C
    (isFull_interC (isFull_interC (isFull_interC (isFull_interC (isFull_interC
      rL.domain_isFull rR.domain_isFull) u.domain_isFull)
      v.domain_isFull) chiU.domain_isFull)
      (isFull_interC chiV.domain_isFull hC.rep.domain_isFull))
    rL rR ?_
  intro x hx hr hr'
  obtain ⟨⟨⟨⟨⟨hxL, hxR⟩, hxu⟩, hxv⟩, hxchiU⟩, hxchiV_hC⟩ := hx
  obtain ⟨hxchiV, hxCchi⟩ := hxchiV_hC
  obtain ⟨_, ⟨_hLabs⟩⟩ := hxL
  obtain ⟨_, ⟨_hRabs⟩⟩ := hxR
  obtain ⟨_, ⟨huabs⟩⟩ := hxu
  obtain ⟨_, ⟨hvabs⟩⟩ := hxv
  obtain ⟨_, ⟨hchiUabs⟩⟩ := hxchiU
  obtain ⟨_, ⟨hchiVabs⟩⟩ := hxchiV
  obtain ⟨_, ⟨hCchiabs⟩⟩ := hxCchi
  let uv := seriesSum_of_absC huabs
  let vv := seriesSum_of_absC hvabs
  let chiVal := seriesSum_of_absC hCchiabs
  let chiUVal := seriesSum_of_absC hchiUabs
  let chiVVal := seriesSum_of_absC hchiVabs
  have hchiU_value : chiUVal.sum ≈ CReal.mul chiVal.sum uv.sum := by
    exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC u hunn
      hchiUabs hCchiabs huabs
  have hchiV_value : chiVVal.sum ≈ CReal.mul chiVal.sum vv.sum := by
    exact IntegrableRepC3.prop_4_2_chi_f_rep_valueC hC v hvnn
      hchiVabs hCchiabs hvabs
  let hsubL := sub_seriesSum_valueC3 (r := u) (r' := chiU) (x := x) uv chiUVal
  let hsubR := sub_seriesSum_valueC3 (r := v) (r' := chiV) (x := x) vv chiVVal
  have hmodelL_to_sub : hsubL.sum ≈ CReal.sub uv.sum chiUVal.sum := by
    change relEventually (addSeq uv.sum (negSeq chiUVal.sum))
      (subSeq uv.sum chiUVal.sum)
    exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually uv.sum chiUVal.sum)
  have hmodelR_to_sub : hsubR.sum ≈ CReal.sub vv.sum chiVVal.sum := by
    change relEventually (addSeq vv.sum (negSeq chiVVal.sum))
      (subSeq vv.sum chiVVal.sum)
    exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually vv.sum chiVVal.sum)
  have hLcanon : hr.sum ≈ CReal.sub uv.sum (CReal.mul chiVal.sum uv.sum) := by
    have htransport : CReal.sub uv.sum chiUVal.sum ≈
        CReal.sub uv.sum (CReal.mul chiVal.sum uv.sum) :=
      subSeq_respects_eventually uv.sum uv.sum chiUVal.sum
        (CReal.mul chiVal.sum uv.sum) (relEventually_refl uv.sum) hchiU_value
    exact Setoid.trans (Setoid.trans (repSeriesSum_unique hr hsubL) hmodelL_to_sub)
      htransport
  have hRcanon : hr'.sum ≈ CReal.sub vv.sum (CReal.mul chiVal.sum vv.sum) := by
    have htransport : CReal.sub vv.sum chiVVal.sum ≈
        CReal.sub vv.sum (CReal.mul chiVal.sum vv.sum) :=
      subSeq_respects_eventually vv.sum vv.sum chiVVal.sum
        (CReal.mul chiVal.sum vv.sum) (relEventually_refl vv.sum) hchiV_value
    exact Setoid.trans (Setoid.trans (repSeriesSum_unique hr' hsubR) hmodelR_to_sub)
      htransport
  have hvalid := hC.valid x hCchiabs
  have hχ01 : chiVal.sum ≈ CReal.zero ∨ chiVal.sum ≈ CReal.one := by
    rcases hvalid.1 with hxS1 | hxS2
    · exact Or.inr (hvalid.2.1 hxS1 chiVal)
    · exact Or.inl (hvalid.2.2 hxS2 chiVal)
  have hmid : RegularSeqLe
      (CReal.sub uv.sum (CReal.mul chiVal.sum uv.sum))
      (CReal.sub vv.sum (CReal.mul chiVal.sum vv.sum)) :=
    lemma43SubMulChi_monoC hχ01 (hle x huabs hvabs uv vv)
  exact regularSeqLe_of_left_eventual hLcanon
    (regularSeqLe_of_right_eventual (Setoid.symm hRcanon) hmid)

/-- Dyadic uniform complement bridge with an abs-aware domination hypothesis. -/
noncomputable def lemma43UniformComplementData_of_majorantWithAbs_halfPowC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (D : Lemma43LevelSetSeqDataC g)
    (hdom : ∀ n (x : X)
      (fvabs : RepSeriesSum fun k => CReal.abs (((fn n).fn k).toFun x))
      (gvabs : RepSeriesSum fun k => CReal.abs ((g.fn k).toFun x))
      (fv : RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe fv.sum gv.sum)
    (K : Nat) :
    Lemma414UniformComplementDataC fn hnn (halfPow K) := by
  let aData := lemma43ComplementIntegral_lt_halfPowDataC D hgnn (K + 1)
  let m : Nat := aData.1
  let d := relIntegral_abs_continuous_setdiff_halfPowDataC g hgnn (K + 1)
  refine {
    A := D.A m
    hA := D.hA m
    N := 0
    delta := d.1
    delta_pos := d.2.1
    small := ?_
  }
  intro n _hn C hC hmu
  let compFn : CReal :=
    ((fn n).sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC (fn n))).integral
  let compG_C : CReal :=
    (g.sub (IntegrableRepC3.prop_4_2_chi_f_repC C hC g)).integral
  let compG_A : CReal :=
    (g.sub (IntegrableRepC3.prop_4_2_chi_f_repC (D.A m) (D.hA m) g)).integral
  let iAC : CReal :=
    relIntegralC ((D.A m).sub C) (IntegrableSet1_subC (D.hA m) hC) g
  have hle_dom : RegularSeqLe compFn compG_C := by
    simpa [compFn, compG_C] using
      lemma43ComplementIntegral_le_of_le_funWithAbsC hC (fn n) g (hnn n) hgnn (hdom n)
  have hle_split : RegularSeqLe compG_C (addSeq compG_A iAC) := by
    simpa [compG_C, compG_A, iAC] using
      lemma43ComplementIntegral_le_complement_plus_setdiffC (D.hA m) hC g hgnn
  have hcomp : regularSeqLtProp compG_A (halfPow (K + 1)) := by
    simpa [aData, m, compG_A] using aData.2
  have hdiff : regularSeqLtProp iAC (halfPow (K + 1)) := by
    simpa [d, m, iAC] using d.2.2 (D.A m) C (D.hA m) hC hmu
  have hsum : regularSeqLtProp (addSeq compG_A iAC)
      (addSeq (halfPow (K + 1)) (halfPow (K + 1))) :=
    regularSeqLtProp_add hcomp hdiff
  have hsumK : regularSeqLtProp (addSeq compG_A iAC) (halfPow K) :=
    regularSeqLtProp_of_right_eventual (halfPow_succ_add_self K) hsum
  exact regularSeqLtProp_of_le_of_lt
    (regularSeqLe_trans hle_dom hle_split) hsumK

/-- Arbitrary-epsilon uniform complement bridge with an abs-aware domination hypothesis. -/
noncomputable def lemma43UniformComplementData_of_majorantWithAbsC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (hnn : ∀ n, RepNonnegC (fn n))
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (D : Lemma43LevelSetSeqDataC g)
    (hdom : ∀ n (x : X)
      (fvabs : RepSeriesSum fun k => CReal.abs (((fn n).fn k).toFun x))
      (gvabs : RepSeriesSum fun k => CReal.abs ((g.fn k).toFun x))
      (fv : RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe fv.sum gv.sum)
    (eps : CReal) (heps : regularSeqLtProp CReal.zero eps) :
    Lemma414UniformComplementDataC fn hnn eps := by
  let kData := halfPow_lt_of_posDataC (posEventuallyData_of_pos_zeroC heps)
  let U := lemma43UniformComplementData_of_majorantWithAbs_halfPowC
    fn hnn g hgnn D hdom kData.1
  exact {
    A := U.A
    hA := U.hA
    N := U.N
    delta := U.delta
    delta_pos := U.delta_pos
    small := by
      intro n hn C hC hmu
      exact regularSeqLtProp_trans _ _ _
        (U.small n hn C hC hmu) kData.2
  }

/-- Measure-convergence data for `fn -> f`, with explicit good-set witnesses. -/
structure Lemma415ConvergeInMeasureDataC {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S) : Type _ where
  close : ∀ (A : BishopC.BSet X) (hA : IntegrableSet1C S A)
      (eps : CReal), regularSeqLtProp CReal.zero eps →
    Sigma (fun N : Nat =>
      ∀ n, N ≤ n →
        Sigma (fun C : BishopC.BSet X =>
          Sigma (fun hC : IntegrableSet1C S C =>
            PProd (C.S1 ⊆ A.S1)
              (PProd
                (regularSeqLtProp ((IntegrableSet1_subC hA hC).rep.integral) eps)
                (∀ (x : X)
                  (hfabs : RepSeriesSum (fun m => absSeq ((f.fn m).toFun x)))
                  (hfnabs : RepSeriesSum (fun m => absSeq (((fn n).fn m).toFun x))),
                    regularSeqLtProp
                      (CReal.abs
                        (CReal.sub (seriesSum_of_absC hfabs).sum
                          (seriesSum_of_absC hfnabs).sum)) eps)))))

/-- `fn -> f` in measure data gives `|fn-f| -> 0` in the Lemma 4.14 input form. -/
noncomputable def lemma415_absError_convergeInMeasureToZeroDataC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (hconv : Lemma415ConvergeInMeasureDataC fn f) :
    Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f) where
  close := by
    intro A hA eps heps
    obtain ⟨N, hN⟩ := hconv.close A hA eps heps
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨C, hC, hsub, hmeasure, hsmall⟩ := hN n hn
    refine ⟨C, hC, hsub, hmeasure, ?_⟩
    intro x herrabs _hχabs _hχone
    let r : IntegrableRepC3 S := (fn n).sub f
    let hsubabs : RepSeriesSum (fun m => absSeq ((r.fn m).toFun x)) :=
      IntegrableRepC3_absVal_absSeriesSum_midC r x herrabs
    let hfnabs : RepSeriesSum (fun m => absSeq (((fn n).fn m).toFun x)) :=
      add_absSeriesSum_leftC (r := fn n) (r' := f.neg) (x := x) hsubabs
    let hfnegabs : RepSeriesSum (fun m => absSeq (((f.neg).fn m).toFun x)) :=
      add_absSeriesSum_rightC (r := fn n) (r' := f.neg) (x := x) hsubabs
    let hfabs : RepSeriesSum (fun m => absSeq ((f.fn m).toFun x)) :=
      neg_absSeriesSumC (r := f) (x := x) hfnegabs
    let hfnv : RepSeriesSum (fun m => ((fn n).fn m).toFun x) := seriesSum_of_absC hfnabs
    let hfv : RepSeriesSum (fun m => (f.fn m).toFun x) := seriesSum_of_absC hfabs
    let herrv : RepSeriesSum (fun m => (r.fn m).toFun x) :=
      sub_seriesSum_valueC3 (r := fn n) (r' := f) (x := x) hfnv hfv
    obtain ⟨habsModel, habsModel_eq⟩ := r.absVal_signed_value x herrv
    let herrSigned : RepSeriesSum
        (fun m => (((thm_4_15_abs_errorC fn f n).fn m).toFun x)) :=
      seriesSum_of_absC herrabs
    have herr_to_abs : herrSigned.sum ≈ CReal.abs (CReal.sub hfnv.sum hfv.sum) := by
      have huniq : herrSigned.sum ≈ habsModel.sum := by
        simpa [thm_4_15_abs_errorC, r] using repSeriesSum_unique herrSigned habsModel
      have herrv_sub : herrv.sum ≈ CReal.sub hfnv.sum hfv.sum := by
        change relEventually (addSeq hfnv.sum (negSeq hfv.sum))
          (subSeq hfnv.sum hfv.sum)
        exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually hfnv.sum hfv.sum)
      exact relEventually_trans _ _ _ huniq
        (relEventually_trans _ _ _ habsModel_eq
          (absSeq_respects_eventually herrv.sum (CReal.sub hfnv.sum hfv.sum) herrv_sub))
    have houter : CReal.abs herrSigned.sum ≈ CReal.abs (CReal.sub hfv.sum hfnv.sum) := by
      have hnonneg_abs : RegularSeqNonneg (CReal.abs (CReal.sub hfnv.sum hfv.sum)) :=
        regularSeqNonneg_of_zero_le
          (absSeq_nonnegative_regularSeqLe (CReal.sub hfnv.sum hfv.sum))
      have h1 : CReal.abs herrSigned.sum ≈
          CReal.abs (CReal.abs (CReal.sub hfnv.sum hfv.sum)) :=
        absSeq_respects_eventually herrSigned.sum
          (CReal.abs (CReal.sub hfnv.sum hfv.sum)) herr_to_abs
      have h2 : CReal.abs (CReal.abs (CReal.sub hfnv.sum hfv.sum)) ≈
          CReal.abs (CReal.sub hfnv.sum hfv.sum) :=
        CReal.abs_of_nonneg_E hnonneg_abs
      exact relEventually_trans _ _ _ h1
        (relEventually_trans _ _ _ h2
          (absSeq_subSeq_comm_eventually hfnv.sum hfv.sum))
    exact regularSeqLtProp_of_left_eventual houter (hsmall x hfabs hfnabs)

/-- Pointwise adapter: `|fn| <= g` implies `|fn-f| <= g+|f|`. -/
theorem lemma415_absError_le_majorant_add_absLimitC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f g : IntegrableRepC3 S)
    (hfn_bound : ∀ n (x : X)
      (hfnv : RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (hgv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe (CReal.abs hfnv.sum) hgv.sum) :
    ∀ n (x : X)
      (herrabs : RepSeriesSum fun k => CReal.abs (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (hHabs : RepSeriesSum fun k => CReal.abs ((((g.add f.absVal).fn k).toFun x)))
      (herrv : RepSeriesSum fun k => (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (hHv : RepSeriesSum fun k => (((g.add f.absVal).fn k).toFun x)),
        RegularSeqLe herrv.sum hHv.sum := by
  intro n x herrabs hHabs herrv hHv
  let H : IntegrableRepC3 S := g.add f.absVal
  let r : IntegrableRepC3 S := (fn n).sub f
  let hsubabs : RepSeriesSum (fun m => absSeq ((r.fn m).toFun x)) :=
    IntegrableRepC3_absVal_absSeriesSum_midC r x herrabs
  let hfnabs : RepSeriesSum (fun m => absSeq (((fn n).fn m).toFun x)) :=
    add_absSeriesSum_leftC (r := fn n) (r' := f.neg) (x := x) hsubabs
  let hfnegabs : RepSeriesSum (fun m => absSeq (((f.neg).fn m).toFun x)) :=
    add_absSeriesSum_rightC (r := fn n) (r' := f.neg) (x := x) hsubabs
  let hfabs_from_err : RepSeriesSum (fun m => absSeq ((f.fn m).toFun x)) :=
    neg_absSeriesSumC (r := f) (x := x) hfnegabs
  let hfnv : RepSeriesSum (fun m => ((fn n).fn m).toFun x) := seriesSum_of_absC hfnabs
  let hfv_from_err : RepSeriesSum (fun m => (f.fn m).toFun x) := seriesSum_of_absC hfabs_from_err
  let hgvabs : RepSeriesSum (fun m => absSeq ((g.fn m).toFun x)) :=
    add_absSeriesSum_leftC (r := g) (r' := f.absVal) (x := x) hHabs
  let hfAbsValAbs : RepSeriesSum (fun m => absSeq (((f.absVal).fn m).toFun x)) :=
    add_absSeriesSum_rightC (r := g) (r' := f.absVal) (x := x) hHabs
  let hgv : RepSeriesSum (fun m => (g.fn m).toFun x) := seriesSum_of_absC hgvabs
  let hfabs_from_H : RepSeriesSum (fun m => absSeq ((f.fn m).toFun x)) :=
    IntegrableRepC3_absVal_absSeriesSum_midC f x hfAbsValAbs
  let hfv_from_H : RepSeriesSum (fun m => (f.fn m).toFun x) := seriesSum_of_absC hfabs_from_H
  let hfAbsValV : RepSeriesSum (fun m => ((f.absVal).fn m).toFun x) :=
    seriesSum_of_absC hfAbsValAbs
  let hHmodel : RepSeriesSum (fun m => ((H.fn m).toFun x)) :=
    add_seriesSum_valueC3 (r := g) (r' := f.absVal) (x := x) hgv hfAbsValV
  let herrSubV : RepSeriesSum (fun m => (r.fn m).toFun x) :=
    sub_seriesSum_valueC3 (r := fn n) (r' := f) (x := x) hfnv hfv_from_err
  obtain ⟨herrAbsModel, herrAbs_eq⟩ := r.absVal_signed_value x herrSubV
  obtain ⟨hfAbsModel, hfAbs_eq⟩ := f.absVal_signed_value x hfv_from_H
  have herr_to_abs_sub : herrv.sum ≈ CReal.abs (CReal.sub hfnv.sum hfv_from_err.sum) := by
    have huniq : herrv.sum ≈ herrAbsModel.sum := by
      simpa [thm_4_15_abs_errorC, r] using repSeriesSum_unique herrv herrAbsModel
    have hsubeq : herrSubV.sum ≈ CReal.sub hfnv.sum hfv_from_err.sum := by
      change relEventually (addSeq hfnv.sum (negSeq hfv_from_err.sum))
        (subSeq hfnv.sum hfv_from_err.sum)
      exact relEventually_symm _ _ (subSeq_eq_add_neg_eventually hfnv.sum hfv_from_err.sum)
    exact relEventually_trans _ _ _ huniq
      (relEventually_trans _ _ _ herrAbs_eq
        (absSeq_respects_eventually herrSubV.sum (CReal.sub hfnv.sum hfv_from_err.sum) hsubeq))
  have hH_to_sum : hHv.sum ≈ CReal.add hgv.sum hfAbsValV.sum := by
    simpa [H] using repSeriesSum_unique hHv hHmodel
  have hfAbsVal_to_abs_f : hfAbsValV.sum ≈ CReal.abs hfv_from_H.sum :=
    relEventually_trans _ _ _ (repSeriesSum_unique hfAbsValV hfAbsModel) hfAbs_eq
  have hf_eq : hfv_from_err.sum ≈ hfv_from_H.sum :=
    repSeriesSum_unique hfv_from_err hfv_from_H
  have hf_abs_le : RegularSeqLe (CReal.abs hfv_from_err.sum) hfAbsValV.sum := by
    have hleft : CReal.abs hfv_from_err.sum ≈ CReal.abs hfv_from_H.sum :=
      absSeq_respects_eventually hfv_from_err.sum hfv_from_H.sum hf_eq
    exact regularSeqLe_of_left_eventual hleft
      (regularSeqLe_of_right_eventual (Setoid.symm hfAbsVal_to_abs_f)
        (regularSeqLe_refl (CReal.abs hfv_from_H.sum)))
  have htri : RegularSeqLe (CReal.abs (CReal.sub hfnv.sum hfv_from_err.sum))
      (CReal.add (CReal.abs hfnv.sum) (CReal.abs hfv_from_err.sum)) :=
    regularSeqLe_abs_sub_le_add_absC hfnv.sum hfv_from_err.sum
  have hsum_le : RegularSeqLe
      (CReal.add (CReal.abs hfnv.sum) (CReal.abs hfv_from_err.sum))
      (CReal.add hgv.sum hfAbsValV.sum) :=
    regularSeqLe_add (hfn_bound n x hfnv hgv) hf_abs_le
  exact regularSeqLe_of_left_eventual herr_to_abs_sub
    (regularSeqLe_of_right_eventual (Setoid.symm hH_to_sum)
      (regularSeqLe_trans htri hsum_le))

/-- Goal B with an abs-aware domination input. -/
noncomputable def goalB_dominated_convergence_dataWithAbsC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC g)
    (hdom : ∀ n (x : X)
      (evabs : RepSeriesSum fun k => CReal.abs (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (gvabs : RepSeriesSum fun k => CReal.abs ((g.fn k).toFun x))
      (ev : RepSeriesSum fun k => (((thm_4_15_abs_errorC fn f n).fn k).toFun x))
      (gv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe ev.sum gv.sum)
    (hconv : Lemma414ConvergeInMeasureToZeroDataC (thm_4_15_abs_errorC fn f)) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  thm_4_15_integral_convergence_from_uniform_and_measure_convergeC
    fn f (thm_4_15_abs_error_nonnegC fn f)
    (fun eps heps =>
      lemma43UniformComplementData_of_majorantWithAbsC
        (thm_4_15_abs_errorC fn f) (thm_4_15_abs_error_nonnegC fn f)
        g hgnn (lemma43LevelSetSeqDataC_of_dyadicSmoothDataC g Dsmooth)
        hdom eps heps)
    hconv

/-- Classical Goal B wrapper in fully data-carrying form: from pointwise
`|fn| <= g`, measure convergence data `fn -> f`, and smooth data for the
integrable majorant `g+|f|`, obtain convergence of integrals. -/
noncomputable def goalB_classical_dominated_convergence_dataC
    {X : Type*} {S : IntSpaceC X}
    (fn : Nat → IntegrableRepC3 S) (f : IntegrableRepC3 S)
    (g : IntegrableRepC3 S) (hgnn : RepNonnegC g)
    (Dsmooth : Lemma43DyadicSmoothDataC (g.add f.absVal))
    (hfn_bound : ∀ n (x : X)
      (hfnv : RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (hgv : RepSeriesSum fun k => (g.fn k).toFun x),
        RegularSeqLe (CReal.abs hfnv.sum) hgv.sum)
    (hconv : Lemma415ConvergeInMeasureDataC fn f) :
    RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  goalB_dominated_convergence_dataWithAbsC
    fn f (g.add f.absVal)
    (RepNonnegC_addC g f.absVal hgnn (IntegrableRepC3_absVal_repNonnegC f))
    Dsmooth
    (lemma415_absError_le_majorant_add_absLimitC fn f g hfn_bound)
    (lemma415_absError_convergeInMeasureToZeroDataC fn f hconv)


end BishopSec3P
