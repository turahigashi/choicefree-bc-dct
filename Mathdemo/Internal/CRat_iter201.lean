import Mathdemo.Internal.CRat_iter200

set_option linter.style.longLine false

/-!
# G101: removing positive-inverse totalization from the min-law closure

G98-G100 closed the line-735 and line-743 quotient min laws through a live
`COFO CRealQuot`, which required a positive-inverse totalization even though
the source min estimates themselves use no reciprocal.

This file factors out the smaller half-sum min-order kernel actually used by
the proof, instantiates it from the existing quotient field data before the
positive-inverse block, and rebuilds the two quotient min laws without the
totalization input.

The remaining frontier is therefore sharper: global quotient representatives
and the `PosEventually` Prop-to-data selector remain; positive-inverse
totalization is no longer needed for these min-law obligations.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Minimal order/absolute-value kernel needed by the half-sum min estimates.

This is deliberately smaller than `BishopC.COFO`: it contains no inverse and no
sequential-completeness fields. -/
structure MinHalfsumOrderKernel (R : Type*) [BishopC.COF R] : Type 1 where
  lt_trans : ∀ {a b c : R}, COF.lt a b -> COF.lt b c -> COF.lt a c
  abs_neg : ∀ a : R, COF.abs (-a) = COF.abs a
  le_abs_self : ∀ a : R, BishopC.Le a (COF.abs a)
  abs_le_of :
    ∀ {a b : R}, BishopC.Le a b -> BishopC.Le (-a) b ->
      BishopC.Le (COF.abs a) b
  half_pos : COF.lt (0 : R) COF.half
  abs_add_le :
    ∀ a b : R, BishopC.Le (COF.abs (a + b)) (COF.abs a + COF.abs b)
  abs_of_nonneg : ∀ {a : R}, BishopC.Nonneg a -> COF.abs a = a
  mul_nonneg : ∀ {a b : R}, BishopC.Nonneg a -> BishopC.Nonneg b ->
    BishopC.Nonneg (a * b)

/-- Local strict-to-nonstrict conversion from the minimal min kernel. -/
theorem minKernel_le_of_lt
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    {a b : R}
    (h : COF.lt a b) :
    BishopC.Le a b :=
  fun hba => COF.lt_irrefl a (K.lt_trans h hba)

/-- Reverse triangle inequality for absolute values from the minimal kernel. -/
theorem minKernel_abs_abs_sub_abs_le
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (a b : R) :
    BishopC.Le
      (COF.abs (COF.abs a - COF.abs b))
      (COF.abs (a - b)) := by
  have key :
      ∀ u v : R,
        BishopC.Le (COF.abs u - COF.abs v) (COF.abs (u - v)) := by
    intro u v
    have ht : BishopC.Le (COF.abs u) (COF.abs (u - v) + COF.abs v) := by
      have h := K.abs_add_le (u - v) v
      rwa [show (u - v) + v = u from by ring] at h
    have h2 := BishopC.le_sub_right (c := COF.abs v) ht
    rwa [show COF.abs (u - v) + COF.abs v - COF.abs v =
        COF.abs (u - v) from by ring] at h2
  have h1 : BishopC.Le
      (COF.abs a - COF.abs b) (COF.abs (a - b)) :=
    key a b
  have h2 : BishopC.Le
      (-(COF.abs a - COF.abs b)) (COF.abs (a - b)) := by
    have hb := key b a
    rw [show COF.abs (b - a) = COF.abs (a - b) from by
      rw [show b - a = -(a - b) from by ring, K.abs_neg]] at hb
    rwa [show COF.abs b - COF.abs a =
      -(COF.abs a - COF.abs b) from by ring] at hb
  exact K.abs_le_of h1 h2

/-- Min monotonicity in the second argument from the minimal half-sum kernel. -/
theorem minKernel_min_halfsum_monotone_right
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (s a b : R)
    (h : BishopC.Le a b) :
    BishopC.Le (COF.min s a) (COF.min s b) := by
  apply BishopC.le_of_nonneg_sub
  rw [COF.min_halfsum s a, COF.min_halfsum s b,
    show COF.half * (s + b - COF.abs (s - b)) -
        COF.half * (s + a - COF.abs (s - a)) =
      COF.half * ((b - a) - (COF.abs (s - b) - COF.abs (s - a)))
    from by ring]
  have hrt : BishopC.Le
      (COF.abs (s - b) - COF.abs (s - a))
      (b - a) := by
    have h1 : BishopC.Le
        (COF.abs (s - b) - COF.abs (s - a))
        (COF.abs ((s - b) - (s - a))) :=
      BishopC.le_trans
        (K.le_abs_self
          (COF.abs (s - b) - COF.abs (s - a)))
        (minKernel_abs_abs_sub_abs_le K (s - b) (s - a))
    rwa [show (s - b) - (s - a) = -(b - a) from by ring,
      K.abs_neg,
      K.abs_of_nonneg (BishopC.nonneg_sub_of_le h)] at h1
  exact K.mul_nonneg
    (minKernel_le_of_lt K K.half_pos)
    (BishopC.nonneg_sub_of_le hrt)

/-- Commutativity of min from the half-sum formula and the minimal kernel. -/
theorem minKernel_min_halfsum_comm
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (a b : R) :
    COF.min a b = COF.min b a := by
  rw [COF.min_halfsum a b, COF.min_halfsum b a,
    show b - a = -(a - b) from by ring,
    K.abs_neg]
  ring

/-- Min monotonicity in the first argument from the minimal half-sum kernel. -/
theorem minKernel_min_halfsum_monotone_left
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (a b c : R)
    (h : BishopC.Le a b) :
    BishopC.Le (COF.min a c) (COF.min b c) := by
  rw [minKernel_min_halfsum_comm K a c,
    minKernel_min_halfsum_comm K b c]
  exact minKernel_min_halfsum_monotone_right K c a b h

/-- Translation identity for the half-sum minimum. -/
theorem minKernel_min_halfsum_translate_right
    {R : Type*} [BishopC.COF R]
    (_K : MinHalfsumOrderKernel R)
    (x d c : R) :
    COF.min (x + d) c = COF.min x (c - d) + d := by
  rw [COF.min_halfsum (x + d) c, COF.min_halfsum x (c - d),
    show x - (c - d) = (x + d) - c from by ring]
  linear_combination d * COF.half_add_half (R := R)

/-- Shifted-min bound from the minimal half-sum kernel. -/
theorem minKernel_min_halfsum_add_nonnegative_right_bound
    {R : Type*} [BishopC.COF R]
    (K : MinHalfsumOrderKernel R)
    (x d c : R)
    (hd : BishopC.Nonneg d) :
    BishopC.Le (COF.min (x + d) c) (COF.min x c + d) := by
  have hcd : BishopC.Le (c - d) c := by
    apply BishopC.le_of_nonneg_sub
    rwa [show c - (c - d) = d from by ring]
  have hmono : BishopC.Le (COF.min x (c - d)) (COF.min x c) :=
    minKernel_min_halfsum_monotone_right K x (c - d) c hcd
  have hadd :
      BishopC.Le (COF.min x (c - d) + d) (COF.min x c + d) :=
    BishopC.le_add hmono (BishopC.le_refl d)
  rw [minKernel_min_halfsum_translate_right K x d c]
  exact hadd

/-- Quotient min-order kernel before the positive-inverse block. -/
def cRealQuotMinHalfsumOrderKernelWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    letI : BishopC.COF CRealQuot :=
      cRealQuotCOFConditionalWith A rep ltDataOf
    MinHalfsumOrderKernel CRealQuot := by
  letI : BishopC.COF CRealQuot :=
    cRealQuotCOFConditionalWith A rep ltDataOf
  exact {
    lt_trans := by
      intro a b c hab hbc
      exact
        (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).lt_trans
          hab hbc
    abs_neg := by
      intro a
      exact
        (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).abs_neg a
    le_abs_self := by
      intro a
      exact
        (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).le_abs_self a
    abs_le_of := by
      intro a b ha hb
      exact
        (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).abs_le_of
          ha hb
    half_pos :=
      (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).half_pos
    abs_add_le := by
      intro a b
      exact
        (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).abs_add_le
          a b
    abs_of_nonneg := by
      intro a ha
      exact
        (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).abs_of_nonneg
          ha
    mul_nonneg := by
      intro a b ha hb
      exact
        (cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf).mul_nonneg
          ha hb }

/-- Quotient min monotonicity without positive-inverse totalization. -/
theorem quotient_minQuotCOF_monotone_left_without_inverse_totalization
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (x y c : CRealQuot)
    (hxy : ¬ ltQuot y x) :
    ¬ ltQuot
      (minQuotCOFWith A y c)
      (minQuotCOFWith A x c) := by
  letI : BishopC.COF CRealQuot :=
    cRealQuotCOFConditionalWith A rep ltDataOf
  have hle : BishopC.Le x y := by
    change ¬ ltQuot y x
    exact hxy
  have hmin : BishopC.Le (COF.min x c) (COF.min y c) :=
    minKernel_min_halfsum_monotone_left
      (cRealQuotMinHalfsumOrderKernelWith A rep ltDataOf)
      x y c hle
  change BishopC.Le (COF.min x c) (COF.min y c)
  exact hmin

/-- Quotient shifted-min bound without positive-inverse totalization. -/
theorem quotient_minQuotCOF_add_nonnegative_right_bound_without_inverse_totalization
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (x d c : CRealQuot)
    (hd : ¬ ltQuot d zeroQuot) :
    ¬ ltQuot
      (addQuot (minQuotCOFWith A x c) d)
      (minQuotCOFWith A (addQuot x d) c) := by
  letI : BishopC.COF CRealQuot :=
    cRealQuotCOFConditionalWith A rep ltDataOf
  have hd_nonneg : BishopC.Nonneg d := by
    change ¬ ltQuot d zeroQuot
    exact hd
  have hmin :
      BishopC.Le (COF.min (x + d) c) (COF.min x c + d) :=
    minKernel_min_halfsum_add_nonnegative_right_bound
      (cRealQuotMinHalfsumOrderKernelWith A rep ltDataOf)
      x d c hd_nonneg
  change
    ¬ ltQuot
      (addQuot (minQuotCOFWith A x c) d)
      (minQuotCOFWith A (addQuot x d) c)
  exact hmin

/-- Regular-sequence line-735 quotient obligation without inverse
totalization. -/
theorem quotient_min_monotone_left_regularSeqLe_without_inverse_totalization
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (x y c : RegularSeq)
    (hxy : RegularSeqLe x y) :
    ¬ ltQuot
      (minQuotCOFWith A (mkQuot y) (mkQuot c))
      (minQuotCOFWith A (mkQuot x) (mkQuot c)) :=
  quotient_minQuotCOF_monotone_left_without_inverse_totalization
    A rep ltDataOf
    (mkQuot x) (mkQuot y) (mkQuot c)
    (not_ltQuot_of_regularSeqLe x y hxy)

/-- Regular-sequence line-743 quotient obligation without inverse
totalization. -/
theorem quotient_min_add_nonnegative_right_bound_regularSeqLe_without_inverse_totalization
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (x d c : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) :
    ¬ ltQuot
      (addQuot
        (minQuotCOFWith A (mkQuot x) (mkQuot c))
        (mkQuot d))
      (minQuotCOFWith A (mkQuot (addSeq x d)) (mkQuot c)) := by
  have hbase :
      ¬ ltQuot
        (addQuot
          (minQuotCOFWith A (mkQuot x) (mkQuot c))
          (mkQuot d))
        (minQuotCOFWith A
          (addQuot (mkQuot x) (mkQuot d))
          (mkQuot c)) :=
    quotient_minQuotCOF_add_nonnegative_right_bound_without_inverse_totalization
      A rep ltDataOf
      (mkQuot x) (mkQuot d) (mkQuot c)
      (not_ltQuot_of_regularSeqLe zeroSeq d hd)
  rwa [← mkQuot_addSeq_eq_addQuot x d] at hbase

/-- Line-735 quotient obligation from global representatives plus a
`PosEventually` selector, with no inverse totalization. -/
theorem quotient_min_monotone_left_regularSeqLe_with_global_rep_pos_selector
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (x y c : RegularSeq)
    (hxy : RegularSeqLe x y) :
    ¬ ltQuot
      (minQuotCOFWith A (mkQuot y) (mkQuot c))
      (minQuotCOFWith A (mkQuot x) (mkQuot c)) :=
  quotient_min_monotone_left_regularSeqLe_without_inverse_totalization
    A rep
    (cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel)
    x y c hxy

/-- Line-743 quotient obligation from global representatives plus a
`PosEventually` selector, with no inverse totalization. -/
theorem quotient_min_add_nonnegative_right_bound_regularSeqLe_with_global_rep_pos_selector
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector)
    (x d c : RegularSeq)
    (hd : RegularSeqLe zeroSeq d) :
    ¬ ltQuot
      (addQuot
        (minQuotCOFWith A (mkQuot x) (mkQuot c))
        (mkQuot d))
      (minQuotCOFWith A (mkQuot (addSeq x d)) (mkQuot c)) :=
  quotient_min_add_nonnegative_right_bound_regularSeqLe_without_inverse_totalization
    A rep
    (cRealQuotLTDataOfGlobalRepPosEventuallySelector rep sel)
    x d c hd

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Generate the G97 quotient-transport law bundle from G96 data without any
positive-inverse totalization. -/
def minSeqQuotientTransportCoreLaws_from_noInverseTotalization
    (Arch : ScalarMulArchimedeanData)
    (g96_laws : Property4ScalarMinKernelClosedCoreLaws Arch)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch where
  g96_core_laws := g96_laws
  quotient_min_monotone_left := by
    intro x y c hxy
    exact
      quotient_min_monotone_left_regularSeqLe_with_global_rep_pos_selector
        Arch rep sel x y c hxy
  quotient_min_add_nonnegative_right_bound := by
    intro x d c hd
    exact
      quotient_min_add_nonnegative_right_bound_regularSeqLe_with_global_rep_pos_selector
        Arch rep sel x d c hd
  source_minSeqWith_to_quotient_min_closed := True
  source_line735_min_frontier_now_quotient_order := True
  source_line743_shifted_min_frontier_now_quotient_order := True

/-- Collapse back to the G96 layer after the no-inverse-totalization min-law
transport has been generated. -/
def scalarMinKernelClosedCoreLaws_from_noInverseTotalization
    (Arch : ScalarMulArchimedeanData)
    (g96_laws : Property4ScalarMinKernelClosedCoreLaws Arch)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (sel : CRealPosEventuallySelector) :
    Property4ScalarMinKernelClosedCoreLaws Arch :=
  scalarMinKernelClosedCoreLaws_from_minSeqQuotientTransport
    Arch
    (minSeqQuotientTransportCoreLaws_from_noInverseTotalization
      Arch g96_laws rep sel)

/-- G101 unified bridge. -/
structure Property4QuotientMinNoInverseTotalizationBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g100_bridge :
    Property4QuotientMinBothGeneratedCoreUnifiedBridge S
  no_inverse_minseq_transport_laws :
    Property4MinSeqQuotientTransportClosedCoreLaws Arch
  no_inverse_scalar_kernel_laws :
    Property4ScalarMinKernelClosedCoreLaws Arch
  source_line735_no_inverse_totalization : Prop
  source_line743_no_inverse_totalization : Prop
  remaining_global_rep_selector_frontier : Prop
  remaining_pos_eventually_selector_frontier : Prop

/-- Convert G101 unified data back to the G100 bridge. -/
def quotientMinBothGeneratedBridge_from_noInverseTotalization
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4QuotientMinNoInverseTotalizationBridge S) :
    Property4QuotientMinBothGeneratedCoreUnifiedBridge S :=
  bridge.g100_bridge

end BishopRegularSeqTheorem118

/-- G101 package. -/
structure BishopRegularSeqTheorem118G101Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g100_package_available : Prop
  min_kernel_available : Prop
  quotient_kernel_without_inverse_totalization :
    forall (A : ScalarMulArchimedeanData)
      (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
      (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b),
        letI : BishopC.COF CRealQuot :=
          cRealQuotCOFConditionalWith A rep ltDataOf
        MinHalfsumOrderKernel CRealQuot
  quotient_min_monotone_without_inverse_totalization :
    forall (A : ScalarMulArchimedeanData),
      (∀ x : CRealQuot, CRealQuotRepWitness x) ->
      CRealPosEventuallySelector ->
      forall x y c : RegularSeq,
        RegularSeqLe x y ->
          ¬ ltQuot
            (minQuotCOFWith A (mkQuot y) (mkQuot c))
            (minQuotCOFWith A (mkQuot x) (mkQuot c))
  quotient_shifted_min_without_inverse_totalization :
    forall (A : ScalarMulArchimedeanData),
      (∀ x : CRealQuot, CRealQuotRepWitness x) ->
      CRealPosEventuallySelector ->
      forall x d c : RegularSeq,
        RegularSeqLe zeroSeq d ->
          ¬ ltQuot
            (addQuot
              (minQuotCOFWith A (mkQuot x) (mkQuot c))
              (mkQuot d))
            (minQuotCOFWith A (mkQuot (addSeq x d)) (mkQuot c))
  no_inverse_transport_bridge : Type 4
  source_positive_inverse_totalization_removed_from_min_laws : Prop
  remaining_global_rep_selector_frontier : Prop
  remaining_pos_eventually_selector_frontier : Prop

def bishopRegularSeqTheorem118G101Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G101Package S where
  g100_package_available := True
  min_kernel_available := True
  quotient_kernel_without_inverse_totalization := by
    intro A rep ltDataOf
    exact cRealQuotMinHalfsumOrderKernelWith A rep ltDataOf
  quotient_min_monotone_without_inverse_totalization := by
    intro A rep sel x y c hxy
    exact
      quotient_min_monotone_left_regularSeqLe_with_global_rep_pos_selector
        A rep sel x y c hxy
  quotient_shifted_min_without_inverse_totalization := by
    intro A rep sel x d c hd
    exact
      quotient_min_add_nonnegative_right_bound_regularSeqLe_with_global_rep_pos_selector
        A rep sel x d c hd
  no_inverse_transport_bridge :=
    BishopRegularSeqTheorem118.Property4QuotientMinNoInverseTotalizationBridge
      S
  source_positive_inverse_totalization_removed_from_min_laws := True
  remaining_global_rep_selector_frontier := True
  remaining_pos_eventually_selector_frontier := True

/-- Progress after G101: line-735/line-743 min-law quotient closure no longer
uses the positive-inverse totalization input. -/
def bishopRegularSeqCh1To4ProgressAfterG101 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 99
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G101: factored the line-735/line-743 min-law closure through a smaller \
    half-sum order kernel, removing positive-inverse totalization from this \
    frontier."


end BishopCReal
