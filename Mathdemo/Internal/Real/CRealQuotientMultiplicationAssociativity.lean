import Mathdemo.Internal.Real.CRealCommonBoundMultiplicationTransport

/-!
# CReal quotient multiplication associativity

This file closes the remaining multiplication ring-law frontier recorded in
`CRealMultiplicationCompletionFrontier`: quotient-level associativity.  The proof transports the two
nested concrete products to one shared common-bound expression, applies the
common-bound associativity estimate from `CRealCommonBoundMultiplicationAssociativityEstimates`, and transports back.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A five-step scalar triangle inequality for the transport chain used in
nested multiplication associativity. -/
theorem scalar_abs_sub_le_five (a b c d e f : Scalar) :
    Le (COF.abs (a - f))
      (COF.abs (a - b) +
        (COF.abs (b - c) +
          (COF.abs (c - d) + (COF.abs (d - e) + COF.abs (e - f))))) := by
  have h1 : Le (COF.abs (a - f))
      (COF.abs (a - b) +
        COF.abs ((b - c) + ((c - d) + ((d - e) + (e - f))))) := by
    have h :=
      scalar_abs_add_le (a - b) ((b - c) + ((c - d) + ((d - e) + (e - f))))
    rwa [show (a - b) + ((b - c) + ((c - d) + ((d - e) + (e - f)))) =
        a - f from by ring] at h
  have h2 : Le (COF.abs ((b - c) + ((c - d) + ((d - e) + (e - f)))))
      (COF.abs (b - c) + COF.abs ((c - d) + ((d - e) + (e - f)))) :=
    scalar_abs_add_le (b - c) ((c - d) + ((d - e) + (e - f)))
  have h3 : Le (COF.abs ((c - d) + ((d - e) + (e - f))))
      (COF.abs (c - d) + COF.abs ((d - e) + (e - f))) :=
    scalar_abs_add_le (c - d) ((d - e) + (e - f))
  have h4 : Le (COF.abs ((d - e) + (e - f)))
      (COF.abs (d - e) + COF.abs (e - f)) :=
    scalar_abs_add_le (d - e) (e - f)
  have h34 := BishopC.le_add (BishopC.le_refl (COF.abs (c - d))) h4
  have h234 := BishopC.le_add (BishopC.le_refl (COF.abs (b - c)))
    (BishopC.le_trans h3 h34)
  have h1234 := BishopC.le_add (BishopC.le_refl (COF.abs (a - b)))
    (BishopC.le_trans h2 h234)
  exact BishopC.le_trans h1 h1234

/-- A common bound large enough for the three inputs and the two concrete inner
products in a nested associativity comparison. -/
def assocCommonBoundWith (A : ScalarMulArchimedeanData)
    (x y z : RegularSeq) : Nat :=
  Nat.max (standardBoundWith A x)
    (Nat.max (standardBoundWith A y)
      (Nat.max (standardBoundWith A z)
        (Nat.max (standardBoundWith A (mulSeqConcreteWith A x y))
          (standardBoundWith A (mulSeqConcreteWith A y z)))))

theorem assocCommonBound_x_le (A : ScalarMulArchimedeanData)
    (x y z : RegularSeq) :
    standardBoundWith A x <= assocCommonBoundWith A x y z := by
  simp [assocCommonBoundWith]

theorem assocCommonBound_y_le (A : ScalarMulArchimedeanData)
    (x y z : RegularSeq) :
    standardBoundWith A y <= assocCommonBoundWith A x y z := by
  unfold assocCommonBoundWith
  exact Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_max_right _ _)

theorem assocCommonBound_z_le (A : ScalarMulArchimedeanData)
    (x y z : RegularSeq) :
    standardBoundWith A z <= assocCommonBoundWith A x y z := by
  unfold assocCommonBoundWith
  exact Nat.le_trans
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)

theorem assocCommonBound_xy_le (A : ScalarMulArchimedeanData)
    (x y z : RegularSeq) :
    standardBoundWith A (mulSeqConcreteWith A x y) <=
      assocCommonBoundWith A x y z := by
  unfold assocCommonBoundWith
  exact Nat.le_trans
    (Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)

theorem assocCommonBound_yz_le (A : ScalarMulArchimedeanData)
    (x y z : RegularSeq) :
    standardBoundWith A (mulSeqConcreteWith A y z) <=
      assocCommonBoundWith A x y z := by
  unfold assocCommonBoundWith
  exact Nat.le_trans
    (Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _))
    (Nat.le_max_right _ _)

/-- The five dyadic error terms in the associativity transport chain fit in
the target precision. -/
theorem assoc_transport_budget (k : Nat) :
    Le (eps (k + 3) +
        (eps (k + 3) +
          (eps (k + 1) + (eps (k + 3) + eps (k + 3))))) (eps k) := by
  rw [show eps (k + 3) +
        (eps (k + 3) +
          (eps (k + 1) + (eps (k + 3) + eps (k + 3)))) =
        (eps (k + 3) + eps (k + 3)) +
          (eps (k + 1) + (eps (k + 3) + eps (k + 3))) from by ring]
  rw [show k + 3 = k + 2 + 1 from by omega]
  rw [eps_succ_add_self (k + 2)]
  rw [show eps (k + 2) + (eps (k + 1) + eps (k + 2)) =
        (eps (k + 2) + eps (k + 2)) + eps (k + 1) from by ring]
  rw [show k + 2 = k + 1 + 1 from by omega]
  rw [eps_succ_add_self (k + 1), eps_succ_add_self k]
  exact BishopC.le_refl (eps k)

/-- Concrete bounded multiplication is associative up to eventual equality. -/
theorem boundedMul_assoc_eventually_with
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    relEventually
      (mulSeqConcreteWith A (mulSeqConcreteWith A x y) z)
      (mulSeqConcreteWith A x (mulSeqConcreteWith A y z)) := by
  intro k
  set xy : RegularSeq := mulSeqConcreteWith A x y with hxydef
  set yz : RegularSeq := mulSeqConcreteWith A y z with hyzdef
  set C : Nat := assocCommonBoundWith A x y z with hCdef
  have hxC : standardBoundWith A x <= C := by
    rw [hCdef]
    exact assocCommonBound_x_le A x y z
  have hyC : standardBoundWith A y <= C := by
    rw [hCdef]
    exact assocCommonBound_y_le A x y z
  have hzC : standardBoundWith A z <= C := by
    rw [hCdef]
    exact assocCommonBound_z_le A x y z
  have hxyC : standardBoundWith A xy <= C := by
    rw [hxydef, hCdef]
    exact assocCommonBound_xy_le A x y z
  have hyzC : standardBoundWith A yz <= C := by
    rw [hyzdef, hCdef]
    exact assocCommonBound_yz_le A x y z
  set xyCommon : RegularSeq := mulSeqAtBoundWith A C x y hxC hyC with hxyCommondef
  set yzCommon : RegularSeq := mulSeqAtBoundWith A C y z hyC hzC with hyzCommondef
  rcases mulSeqConcrete_to_common_bound_eventually_with A xy z (C := C)
      hxyC hzC (k + 3) with
    ⟨NleftOuter, hNleftOuter⟩
  rcases mulSeqConcrete_to_common_bound_eventually_with A x y (C := C)
      hxC hyC (standardBoundWith A z + (k + 4)) with
    ⟨NinnerLeft, hNinnerLeft⟩
  rcases mulValWithBound_common_assoc_eventually_with A x y z (C := C)
      hxC hyC hzC (k + 1) with
    ⟨Nmid, hNmid⟩
  rcases mulSeqCommon_to_concrete_bound_eventually_with A y z (C := C)
      hyC hzC (standardBoundWith A x + (k + 4)) with
    ⟨NinnerRight, hNinnerRight⟩
  rcases mulSeqCommon_to_concrete_bound_eventually_with A x yz (C := C)
      hxC hyzC (k + 3) with
    ⟨NrightOuter, hNrightOuter⟩
  refine ⟨NleftOuter + NinnerLeft + Nmid + NinnerRight + NrightOuter, ?_⟩
  intro n hn
  have hnLeftOuter : NleftOuter <= n := by omega
  have hnInnerLeft : NinnerLeft <= n := by omega
  have hnMid : Nmid <= n := by omega
  have hnInnerRight : NinnerRight <= n := by omega
  have hnRightOuter : NrightOuter <= n := by omega
  set cidx : Nat := mulIndexFromBound C n with hcidxdef
  have hn_cidx : n <= cidx := by
    unfold cidx
    exact le_mulIndexFromBound C n
  have hInnerLeft_cidx : NinnerLeft <= cidx :=
    Nat.le_trans hnInnerLeft hn_cidx
  have hInnerRight_cidx : NinnerRight <= cidx :=
    Nat.le_trans hnInnerRight hn_cidx
  have hxy_close : Le (COF.abs (xy.val cidx - xyCommon.val cidx))
      (eps (standardBoundWith A z + (k + 4))) := by
    have h := hNinnerLeft cidx hInnerLeft_cidx
    simpa [hxydef, hxyCommondef, hcidxdef] using h
  have hz_zero : Le (COF.abs (z.val cidx - z.val cidx))
      (eps (standardBoundWith A xy + (k + 4))) := by
    rw [show z.val cidx - z.val cidx = (0 : Scalar) from by ring]
    change Le (BishopCRat.CRat.absF 0)
      (eps (standardBoundWith A xy + (k + 4)))
    rw [scalarCOFOSeed.abs_zero]
    exact eps_nonneg (standardBoundWith A xy + (k + 4))
  have hx_zero : Le (COF.abs (x.val cidx - x.val cidx))
      (eps (standardBoundWith A yz + (k + 4))) := by
    rw [show x.val cidx - x.val cidx = (0 : Scalar) from by ring]
    change Le (BishopCRat.CRat.absF 0)
      (eps (standardBoundWith A yz + (k + 4)))
    rw [scalarCOFOSeed.abs_zero]
    exact eps_nonneg (standardBoundWith A yz + (k + 4))
  have hyz_close : Le (COF.abs (yzCommon.val cidx - yz.val cidx))
      (eps (standardBoundWith A x + (k + 4))) := by
    have h := hNinnerRight cidx hInnerRight_cidx
    simpa [hyzdef, hyzCommondef, hcidxdef] using h
  have hleftOuter : Le (COF.abs
      ((mulSeqConcreteWith A xy z).val n -
        mulValWithBound C xy.val z.val n)) (eps (k + 3)) := by
    have h := hNleftOuter n hnLeftOuter
    simpa [mulSeqAtBoundWith] using h
  have hinnerLeft : Le (COF.abs
      (mulValWithBound C xy.val z.val n -
        mulValWithBound C xyCommon.val z.val n)) (eps (k + 3)) :=
    mulValWithBound_common_respects_point A xy xyCommon z z C (k + 2) n
      hxy_close
      (by
        simpa [show k + 2 + 2 = k + 4 from by omega] using hz_zero)
  have hmid0 : Le (COF.abs (mulValWithBound C
        (mulValWithBound C x.val y.val) z.val n -
      mulValWithBound C x.val (mulValWithBound C y.val z.val) n))
      (eps (k + 1)) :=
    hNmid n hnMid
  have hmid : Le (COF.abs
      (mulValWithBound C xyCommon.val z.val n -
        mulValWithBound C x.val yzCommon.val n)) (eps (k + 1)) := by
    simpa [hxyCommondef, hyzCommondef, mulSeqAtBoundWith] using hmid0
  have hinnerRight : Le (COF.abs
      (mulValWithBound C x.val yzCommon.val n -
        mulValWithBound C x.val yz.val n)) (eps (k + 3)) :=
    mulValWithBound_common_respects_point A x x yzCommon yz C (k + 2) n
      (by
        simpa [show k + 2 + 2 = k + 4 from by omega] using hx_zero)
      hyz_close
  have hrightOuter : Le (COF.abs
      (mulValWithBound C x.val yz.val n -
        (mulSeqConcreteWith A x yz).val n)) (eps (k + 3)) := by
    have h := hNrightOuter n hnRightOuter
    simpa [mulSeqAtBoundWith] using h
  set a : Scalar := (mulSeqConcreteWith A xy z).val n
  set b : Scalar := mulValWithBound C xy.val z.val n
  set c : Scalar := mulValWithBound C xyCommon.val z.val n
  set d : Scalar := mulValWithBound C x.val yzCommon.val n
  set e : Scalar := mulValWithBound C x.val yz.val n
  set f : Scalar := (mulSeqConcreteWith A x yz).val n
  have htri := scalar_abs_sub_le_five a b c d e f
  have hsum := BishopC.le_add hleftOuter
    (BishopC.le_add hinnerLeft
      (BishopC.le_add hmid (BishopC.le_add hinnerRight hrightOuter)))
  have hbudget := assoc_transport_budget k
  exact BishopC.le_trans htri (BishopC.le_trans hsum hbudget)

theorem mulQuotConcrete_assoc_mk
    (A : ScalarMulArchimedeanData) (x y z : RegularSeq) :
    mulQuotConcreteWith A (mulQuotConcreteWith A (mkQuot x) (mkQuot y)) (mkQuot z) =
      mulQuotConcreteWith A (mkQuot x)
        (mulQuotConcreteWith A (mkQuot y) (mkQuot z)) := by
  change mkQuot (mulSeqConcreteWith A (mulSeqConcreteWith A x y) z) =
    mkQuot (mulSeqConcreteWith A x (mulSeqConcreteWith A y z))
  apply Quotient.sound
  exact boundedMul_assoc_eventually_with A x y z

theorem mulQuotConcrete_assoc
    (A : ScalarMulArchimedeanData) (x y z : CRealQuot) :
    mulQuotConcreteWith A (mulQuotConcreteWith A x y) z =
      mulQuotConcreteWith A x (mulQuotConcreteWith A y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro x' y' z'
  exact mulQuotConcrete_assoc_mk A x' y' z'

/-- The multiplication ring-law data from `CRealMultiplicationCompletionFrontier`, now fully concrete. -/
def cRealQuotMulRingLawDataConcreteWith
    (A : ScalarMulArchimedeanData) :
    CRealQuotMulRingLawData (cRealMulCompletionObligationsWith A) where
  mul_assoc := by
    intro x y z
    change mulQuotConcreteWith A (mulQuotConcreteWith A x y) z =
      mulQuotConcreteWith A x (mulQuotConcreteWith A y z)
    exact mulQuotConcrete_assoc A x y z
  left_distrib := by
    intro x y z
    change mulQuotConcreteWith A x (addQuot y z) =
      addQuot (mulQuotConcreteWith A x y) (mulQuotConcreteWith A x z)
    exact mulQuotConcrete_left_distrib A x y z
  right_distrib := by
    intro x y z
    change mulQuotConcreteWith A (addQuot x y) z =
      addQuot (mulQuotConcreteWith A x z) (mulQuotConcreteWith A y z)
    exact mulQuotConcrete_right_distrib A x y z

/-- The Phase 9-11 multiplication frontier is closed for every explicit scalar
multiplicative Archimedean datum. -/
def cRealMulFinalFrontierConcreteWith
    (A : ScalarMulArchimedeanData) : CRealMulFinalFrontier where
  obligations := cRealMulCompletionObligationsWith A
  ringLaws := cRealQuotMulRingLawDataConcreteWith A

end BishopCReal

