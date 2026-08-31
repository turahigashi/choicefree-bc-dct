import Mathdemo.Internal.CRat_iter323

set_option linter.style.longLine false

/-!
# G225: attaching the scalar Theorem 4.6 laws to carried mid sources

G224 closed the pure scalar increment bounds.  This file connects those scalar
facts to the actual Definition-1.6 representatives carried by
`Prop412DataCarryingMeasurable`.

The only extra support used below is the full domain of the auxiliary
characteristic-function representative required by the source proof of
`χ_A ≤ χ_(A∨B)`.  It is obtained directly from the corresponding
`IntegrableSet1` witness.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge

/-- Values of a partial function are independent of the proof of membership in
the same domain. -/
theorem pfun_value_proof_irrel
    {R : Type*} [COFOC R] {Y : Type}
    (f : BishopC.PFunR Y R) {x : Y}
    (hx hy : x ∈ f.dom) :
    f.toFun x hx = f.toFun x hy := by
  have h : hx = hy := Subsingleton.elim hx hy
  rw [h]

/-- Pointwise value data saying that `φ` is a nonnegative part bounded by the
nonnegative majorant `ψ`. -/
structure Theorem46PartAbsValueRelation
    {R : Type*} [COFOC R] {Y : Type}
    (φ ψ : BishopC.PFunR Y R) : Type _ where
  left_nonneg :
    ∀ x (hx : x ∈ φ.dom), BishopC.Nonneg (φ.toFun x hx)
  right_nonneg :
    ∀ x (hx : x ∈ ψ.dom), BishopC.Nonneg (ψ.toFun x hx)
  le_value :
    ∀ x (hxφ : x ∈ φ.dom) (hxψ : x ∈ ψ.dom),
      BishopC.Le (φ.toFun x hxφ) (ψ.toFun x hxψ)

/-- `f+` is a nonnegative part bounded by `|f|`. -/
def theorem46_pos_abs_value_relation
    {R : Type*} [COFOC R] {Y : Type}
    (f : BishopC.PFunR Y R) :
    Theorem46PartAbsValueRelation
      (theorem46_pfun_posPart f) (theorem46_pfun_absPart f) where
  left_nonneg := by
    intro x hx
    exact theorem46_scalar_posPart_nonneg (f.toFun x hx)
  right_nonneg := by
    intro x hx
    exact theorem46_scalar_absPart_nonneg (f.toFun x hx)
  le_value := by
    intro x hxφ hxψ
    dsimp [theorem46_pfun_posPart, theorem46_pfun_absPart]
    have hval : f.toFun x hxφ = f.toFun x hxψ :=
      pfun_value_proof_irrel f hxφ hxψ
    rw [hval]
    exact theorem46_scalar_posPart_le_abs (f.toFun x hxψ)

/-- `f-` is a nonnegative part bounded by `|f|`. -/
def theorem46_neg_abs_value_relation
    {R : Type*} [COFOC R] {Y : Type}
    (f : BishopC.PFunR Y R) :
    Theorem46PartAbsValueRelation
      (theorem46_pfun_negPart f) (theorem46_pfun_absPart f) where
  left_nonneg := by
    intro x hx
    exact theorem46_scalar_negPart_nonneg (f.toFun x hx)
  right_nonneg := by
    intro x hx
    exact theorem46_scalar_absPart_nonneg (f.toFun x hx)
  le_value := by
    intro x hxφ hxψ
    dsimp [theorem46_pfun_negPart, theorem46_pfun_absPart]
    have hval : f.toFun x hxφ = f.toFun x hxψ :=
      pfun_value_proof_irrel f hxφ hxψ
    rw [hval]
    exact theorem46_scalar_negPart_le_abs (f.toFun x hxψ)

/-- Left set-expansion support:
the four mid representatives plus the auxiliary `A₂` characteristic witness. -/
def theorem46_left_set_step_support
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (s1 s2 : Theorem46StateData S) : Set Y :=
  theorem46_pointwise_oneStep_fullSet Mφ Mψ
    (theorem46_stateData_or_leftN s1 s2) s1 ∩ s2.hA.rep.domain

theorem theorem46_left_set_step_support_isFull
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (s1 s2 : Theorem46StateData S) :
    BishopC.IsFull S
      (theorem46_left_set_step_support Mφ Mψ s1 s2) := by
  unfold theorem46_left_set_step_support
  exact BishopC.isFull_inter
    (theorem46_pointwise_oneStep_fullSet_isFull Mφ Mψ
      (theorem46_stateData_or_leftN s1 s2) s1)
    s2.hA.rep.domain_isFull

/-- Right set-expansion support:
the four mid representatives plus the auxiliary `A₁` characteristic witness. -/
def theorem46_right_set_step_support
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (s1 s2 : Theorem46StateData S) : Set Y :=
  theorem46_pointwise_oneStep_fullSet Mφ Mψ
    (theorem46_stateData_or_rightN s1 s2) s2 ∩ s1.hA.rep.domain

theorem theorem46_right_set_step_support_isFull
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (s1 s2 : Theorem46StateData S) :
    BishopC.IsFull S
      (theorem46_right_set_step_support Mφ Mψ s1 s2) := by
  unfold theorem46_right_set_step_support
  exact BishopC.isFull_inter
    (theorem46_pointwise_oneStep_fullSet_isFull Mφ Mψ
      (theorem46_stateData_or_rightN s1 s2) s2)
    s1.hA.rep.domain_isFull

/-- Truncation-expansion support: the four mid representatives already contain
the common characteristic witness. -/
def theorem46_trunc_step_support
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (u t : Theorem46StateData S) : Set Y :=
  theorem46_pointwise_oneStep_fullSet Mφ Mψ u t

theorem theorem46_trunc_step_support_isFull
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (u t : Theorem46StateData S) :
    BishopC.IsFull S (theorem46_trunc_step_support Mφ Mψ u t) := by
  unfold theorem46_trunc_step_support
  exact theorem46_pointwise_oneStep_fullSet_isFull Mφ Mψ u t

/-- Left set-expansion pointwise data. -/
def theorem46_left_set_step_pointwise_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (Rel : Theorem46PartAbsValueRelation φh ψh)
    (s1 s2 : Theorem46StateData S) :
    Theorem46MidPointwiseOneStepData Mφ Mψ
      (theorem46_stateData_or_leftN s1 s2) s1 where
  support := theorem46_left_set_step_support Mφ Mψ s1 s2
  support_isFull := theorem46_left_set_step_support_isFull Mφ Mψ s1 s2
  support_subset_mid_domains := by
    intro x hx
    exact hx.1
  monotone := by
    intro x hx hφtDom hφuDom _hψtDom _hψuDom hφt hφu _hψt _hψu
    obtain ⟨hauxDom, ⟨haux_abs⟩⟩ := hx.2
    have hφtdom :=
      (theorem46_mid_source Mφ s1).dom_of_mid_value x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).dom_of_mid_value
          x hφuDom hφu
    have hχADom :=
      (theorem46_mid_source Mφ s1).chiA_dom_of_mid_value x hφtDom hφt
    have hχOrDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχA :=
      (theorem46_mid_source Mφ s1).chiA_abs_of_mid_value x hφtDom hφt
    have hχOr :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hφtval :=
      (theorem46_mid_source Mφ s1).value_eq
        x hφtdom hχADom hφtDom hχA hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).value_eq
          x hφudom hχOrDom hφuDom hχOr hφu
    have hv_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    rw [hφtval, hφuval, hv_eq]
    exact theorem46_scalarMid_or_left_expansion_mono
      s1.hA s2.hA hχADom hauxDom hχOrDom hχA haux_abs hχOr s1.n
      (Rel.left_nonneg x hφtdom)
  increment_bound := by
    intro x hx hφtDom hφuDom hψtDom hψuDom hφt hφu hψt hψu
    obtain ⟨hauxDom, ⟨haux_abs⟩⟩ := hx.2
    have hφtdom :=
      (theorem46_mid_source Mφ s1).dom_of_mid_value x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).dom_of_mid_value
          x hφuDom hφu
    have hψtdom :=
      (theorem46_mid_source Mψ s1).dom_of_mid_value x hψtDom hψt
    have hψudom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).dom_of_mid_value
          x hψuDom hψu
    have hχAφDom :=
      (theorem46_mid_source Mφ s1).chiA_dom_of_mid_value x hφtDom hφt
    have hχOrφDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχAψDom :=
      (theorem46_mid_source Mψ s1).chiA_dom_of_mid_value x hψtDom hψt
    have hχOrψDom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).chiA_dom_of_mid_value
          x hψuDom hψu
    have hχAφ :=
      (theorem46_mid_source Mφ s1).chiA_abs_of_mid_value x hφtDom hφt
    have hχOrφ :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hχAψ :=
      (theorem46_mid_source Mψ s1).chiA_abs_of_mid_value x hψtDom hψt
    have hχOrψ :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).chiA_abs_of_mid_value
          x hψuDom hψu
    have hχA_eq :
        (BishopC.seriesSum_of_abs hχAφ).sum =
          (BishopC.seriesSum_of_abs hχAψ).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχAφ)
        (BishopC.seriesSum_of_abs hχAψ)
    have hχOr_eq :
        (BishopC.seriesSum_of_abs hχOrφ).sum =
          (BishopC.seriesSum_of_abs hχOrψ).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχOrφ)
        (BishopC.seriesSum_of_abs hχOrψ)
    have hφtval :=
      (theorem46_mid_source Mφ s1).value_eq
        x hφtdom hχAφDom hφtDom hχAφ hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).value_eq
          x hφudom hχOrφDom hφuDom hχOrφ hφu
    have hψtval :=
      (theorem46_mid_source Mψ s1).value_eq
        x hψtdom hχAψDom hψtDom hχAψ hψt
    have hψuval :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).value_eq
          x hψudom hχOrψDom hψuDom hχOrψ hψu
    have hφ_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    have hψ_eq : ψh.toFun x hψudom = ψh.toFun x hψtdom :=
      pfun_value_proof_irrel ψh hψudom hψtdom
    rw [hφtval, hφuval, hψtval, hψuval, hφ_eq, hψ_eq,
      hχA_eq, hχOr_eq]
    exact theorem46_scalarMid_chi_set_increment_bound s1.n
      (theorem46_chi_value_zero_or_one s1.hA hχAψDom hχAψ)
      (theorem46_chi_value_zero_or_one
        (BishopC.IntegrableSet1_or s1.hA s2.hA) hχOrψDom hχOrψ)
      (theorem46_chi_or_left_value_le s1.hA s2.hA
        hχAψDom hauxDom hχOrψDom hχAψ haux_abs hχOrψ)
      (Rel.left_nonneg x hφtdom)
      (Rel.right_nonneg x hψtdom)
      (Rel.le_value x hφtdom hψtdom)

/-- Right set-expansion pointwise data. -/
def theorem46_right_set_step_pointwise_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (Rel : Theorem46PartAbsValueRelation φh ψh)
    (s1 s2 : Theorem46StateData S) :
    Theorem46MidPointwiseOneStepData Mφ Mψ
      (theorem46_stateData_or_rightN s1 s2) s2 where
  support := theorem46_right_set_step_support Mφ Mψ s1 s2
  support_isFull := theorem46_right_set_step_support_isFull Mφ Mψ s1 s2
  support_subset_mid_domains := by
    intro x hx
    exact hx.1
  monotone := by
    intro x hx hφtDom hφuDom _hψtDom _hψuDom hφt hφu _hψt _hψu
    obtain ⟨hauxDom, ⟨haux_abs⟩⟩ := hx.2
    have hφtdom :=
      (theorem46_mid_source Mφ s2).dom_of_mid_value x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).dom_of_mid_value
          x hφuDom hφu
    have hχBDom :=
      (theorem46_mid_source Mφ s2).chiA_dom_of_mid_value x hφtDom hφt
    have hχOrDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχB :=
      (theorem46_mid_source Mφ s2).chiA_abs_of_mid_value x hφtDom hφt
    have hχOr :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hφtval :=
      (theorem46_mid_source Mφ s2).value_eq
        x hφtdom hχBDom hφtDom hχB hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).value_eq
          x hφudom hχOrDom hφuDom hχOr hφu
    have hv_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    rw [hφtval, hφuval, hv_eq]
    exact theorem46_scalarMid_or_right_expansion_mono
      s1.hA s2.hA hauxDom hχBDom hχOrDom haux_abs hχB hχOr s2.n
      (Rel.left_nonneg x hφtdom)
  increment_bound := by
    intro x hx hφtDom hφuDom hψtDom hψuDom hφt hφu hψt hψu
    obtain ⟨hauxDom, ⟨haux_abs⟩⟩ := hx.2
    have hφtdom :=
      (theorem46_mid_source Mφ s2).dom_of_mid_value x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).dom_of_mid_value
          x hφuDom hφu
    have hψtdom :=
      (theorem46_mid_source Mψ s2).dom_of_mid_value x hψtDom hψt
    have hψudom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).dom_of_mid_value
          x hψuDom hψu
    have hχBφDom :=
      (theorem46_mid_source Mφ s2).chiA_dom_of_mid_value x hφtDom hφt
    have hχOrφDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχBψDom :=
      (theorem46_mid_source Mψ s2).chiA_dom_of_mid_value x hψtDom hψt
    have hχOrψDom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).chiA_dom_of_mid_value
          x hψuDom hψu
    have hχBφ :=
      (theorem46_mid_source Mφ s2).chiA_abs_of_mid_value x hφtDom hφt
    have hχOrφ :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hχBψ :=
      (theorem46_mid_source Mψ s2).chiA_abs_of_mid_value x hψtDom hψt
    have hχOrψ :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).chiA_abs_of_mid_value
          x hψuDom hψu
    have hχB_eq :
        (BishopC.seriesSum_of_abs hχBφ).sum =
          (BishopC.seriesSum_of_abs hχBψ).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχBφ)
        (BishopC.seriesSum_of_abs hχBψ)
    have hχOr_eq :
        (BishopC.seriesSum_of_abs hχOrφ).sum =
          (BishopC.seriesSum_of_abs hχOrψ).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχOrφ)
        (BishopC.seriesSum_of_abs hχOrψ)
    have hφtval :=
      (theorem46_mid_source Mφ s2).value_eq
        x hφtdom hχBφDom hφtDom hχBφ hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).value_eq
          x hφudom hχOrφDom hφuDom hχOrφ hφu
    have hψtval :=
      (theorem46_mid_source Mψ s2).value_eq
        x hψtdom hχBψDom hψtDom hχBψ hψt
    have hψuval :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).value_eq
          x hψudom hχOrψDom hψuDom hχOrψ hψu
    have hφ_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    have hψ_eq : ψh.toFun x hψudom = ψh.toFun x hψtdom :=
      pfun_value_proof_irrel ψh hψudom hψtdom
    rw [hφtval, hφuval, hψtval, hψuval, hφ_eq, hψ_eq,
      hχB_eq, hχOr_eq]
    exact theorem46_scalarMid_chi_set_increment_bound s2.n
      (theorem46_chi_value_zero_or_one s2.hA hχBψDom hχBψ)
      (theorem46_chi_value_zero_or_one
        (BishopC.IntegrableSet1_or s1.hA s2.hA) hχOrψDom hχOrψ)
      (theorem46_chi_or_right_value_le s1.hA s2.hA
        hauxDom hχBψDom hχOrψDom haux_abs hχBψ hχOrψ)
      (Rel.left_nonneg x hφtdom)
      (Rel.right_nonneg x hψtdom)
      (Rel.le_value x hφtdom hψtdom)

/-- Left truncation-expansion pointwise data. -/
def theorem46_left_trunc_step_pointwise_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (Rel : Theorem46PartAbsValueRelation φh ψh)
    (s1 s2 : Theorem46StateData S) :
    Theorem46MidPointwiseOneStepData Mφ Mψ
      (theorem46_stateData_s3 s1 s2)
      (theorem46_stateData_or_leftN s1 s2) where
  support := theorem46_trunc_step_support Mφ Mψ
    (theorem46_stateData_s3 s1 s2)
    (theorem46_stateData_or_leftN s1 s2)
  support_isFull := theorem46_trunc_step_support_isFull Mφ Mψ
    (theorem46_stateData_s3 s1 s2)
    (theorem46_stateData_or_leftN s1 s2)
  support_subset_mid_domains := by
    intro x hx
    exact hx
  monotone := by
    intro x _hx hφtDom hφuDom _hψtDom _hψuDom hφt hφu _hψt _hψu
    have hφtdom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).dom_of_mid_value
          x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).dom_of_mid_value x hφuDom hφu
    have hχtDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_dom_of_mid_value
          x hφtDom hφt
    have hχuDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχt :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_abs_of_mid_value
          x hφtDom hφt
    have hχu :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hχ_eq :
        (BishopC.seriesSum_of_abs hχu).sum =
          (BishopC.seriesSum_of_abs hχt).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχu)
        (BishopC.seriesSum_of_abs hχt)
    have hφtval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).value_eq
          x hφtdom hχtDom hφtDom hχt hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).value_eq
          x hφudom hχuDom hφuDom hχu hφu
    have hφ_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    rw [hφtval, hφuval, hφ_eq, hχ_eq]
    exact theorem46_scalarMid_nonneg_trunc_mono
      (Nat.le_add_right s1.n s2.n)
      (COFO.mul_nonneg
        (theorem46_chi_value_nonneg
          (BishopC.IntegrableSet1_or s1.hA s2.hA) hχtDom hχt)
        (Rel.left_nonneg x hφtdom))
  increment_bound := by
    intro x _hx hφtDom hφuDom hψtDom hψuDom hφt hφu hψt hψu
    have hφtdom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).dom_of_mid_value
          x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).dom_of_mid_value x hφuDom hφu
    have hψtdom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).dom_of_mid_value
          x hψtDom hψt
    have hψudom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).dom_of_mid_value x hψuDom hψu
    have hχφtDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_dom_of_mid_value
          x hφtDom hφt
    have hχφuDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχψtDom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).chiA_dom_of_mid_value
          x hψtDom hψt
    have hχψuDom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).chiA_dom_of_mid_value
          x hψuDom hψu
    have hχφt :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).chiA_abs_of_mid_value
          x hφtDom hφt
    have hχφu :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hχψt :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).chiA_abs_of_mid_value
          x hψtDom hψt
    have hχψu :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).chiA_abs_of_mid_value
          x hψuDom hψu
    have hχφtψt :
        (BishopC.seriesSum_of_abs hχφt).sum =
          (BishopC.seriesSum_of_abs hχψt).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχφt)
        (BishopC.seriesSum_of_abs hχψt)
    have hχφuψu :
        (BishopC.seriesSum_of_abs hχφu).sum =
          (BishopC.seriesSum_of_abs hχψu).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχφu)
        (BishopC.seriesSum_of_abs hχψu)
    have hχu_t :
        (BishopC.seriesSum_of_abs hχψu).sum =
          (BishopC.seriesSum_of_abs hχψt).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχψu)
        (BishopC.seriesSum_of_abs hχψt)
    have hφtval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_leftN s1 s2)).value_eq
          x hφtdom hχφtDom hφtDom hχφt hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).value_eq
          x hφudom hχφuDom hφuDom hχφu hφu
    have hψtval :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_leftN s1 s2)).value_eq
          x hψtdom hχψtDom hψtDom hχψt hψt
    have hψuval :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).value_eq
          x hψudom hχψuDom hψuDom hχψu hψu
    have hφ_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    have hψ_eq : ψh.toFun x hψudom = ψh.toFun x hψtdom :=
      pfun_value_proof_irrel ψh hψudom hψtdom
    rw [hφtval, hφuval, hψtval, hψuval, hφ_eq, hψ_eq,
      hχφtψt, hχφuψu, hχu_t]
    exact theorem46_scalarMid_chi_trunc_increment_bound
      (Nat.le_add_right s1.n s2.n)
      (theorem46_chi_value_zero_or_one
        (BishopC.IntegrableSet1_or s1.hA s2.hA) hχψtDom hχψt)
      (Rel.left_nonneg x hφtdom)
      (Rel.right_nonneg x hψtdom)
      (Rel.le_value x hφtdom hψtdom)

/-- Right truncation-expansion pointwise data. -/
def theorem46_right_trunc_step_pointwise_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (Rel : Theorem46PartAbsValueRelation φh ψh)
    (s1 s2 : Theorem46StateData S) :
    Theorem46MidPointwiseOneStepData Mφ Mψ
      (theorem46_stateData_s3 s1 s2)
      (theorem46_stateData_or_rightN s1 s2) where
  support := theorem46_trunc_step_support Mφ Mψ
    (theorem46_stateData_s3 s1 s2)
    (theorem46_stateData_or_rightN s1 s2)
  support_isFull := theorem46_trunc_step_support_isFull Mφ Mψ
    (theorem46_stateData_s3 s1 s2)
    (theorem46_stateData_or_rightN s1 s2)
  support_subset_mid_domains := by
    intro x hx
    exact hx
  monotone := by
    intro x _hx hφtDom hφuDom _hψtDom _hψuDom hφt hφu _hψt _hψu
    have hφtdom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).dom_of_mid_value
          x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).dom_of_mid_value x hφuDom hφu
    have hχtDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_dom_of_mid_value
          x hφtDom hφt
    have hχuDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχt :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_abs_of_mid_value
          x hφtDom hφt
    have hχu :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hχ_eq :
        (BishopC.seriesSum_of_abs hχu).sum =
          (BishopC.seriesSum_of_abs hχt).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχu)
        (BishopC.seriesSum_of_abs hχt)
    have hφtval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).value_eq
          x hφtdom hχtDom hφtDom hχt hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).value_eq
          x hφudom hχuDom hφuDom hχu hφu
    have hφ_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    rw [hφtval, hφuval, hφ_eq, hχ_eq]
    exact theorem46_scalarMid_nonneg_trunc_mono
      (Nat.le_add_left s2.n s1.n)
      (COFO.mul_nonneg
        (theorem46_chi_value_nonneg
          (BishopC.IntegrableSet1_or s1.hA s2.hA) hχtDom hχt)
        (Rel.left_nonneg x hφtdom))
  increment_bound := by
    intro x _hx hφtDom hφuDom hψtDom hψuDom hφt hφu hψt hψu
    have hφtdom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).dom_of_mid_value
          x hφtDom hφt
    have hφudom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).dom_of_mid_value x hφuDom hφu
    have hψtdom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).dom_of_mid_value
          x hψtDom hψt
    have hψudom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).dom_of_mid_value x hψuDom hψu
    have hχφtDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_dom_of_mid_value
          x hφtDom hφt
    have hχφuDom :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_dom_of_mid_value
          x hφuDom hφu
    have hχψtDom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).chiA_dom_of_mid_value
          x hψtDom hψt
    have hχψuDom :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).chiA_dom_of_mid_value
          x hψuDom hψu
    have hχφt :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).chiA_abs_of_mid_value
          x hφtDom hφt
    have hχφu :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).chiA_abs_of_mid_value
          x hφuDom hφu
    have hχψt :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).chiA_abs_of_mid_value
          x hψtDom hψt
    have hχψu :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).chiA_abs_of_mid_value
          x hψuDom hψu
    have hχφtψt :
        (BishopC.seriesSum_of_abs hχφt).sum =
          (BishopC.seriesSum_of_abs hχψt).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχφt)
        (BishopC.seriesSum_of_abs hχψt)
    have hχφuψu :
        (BishopC.seriesSum_of_abs hχφu).sum =
          (BishopC.seriesSum_of_abs hχψu).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχφu)
        (BishopC.seriesSum_of_abs hχψu)
    have hχu_t :
        (BishopC.seriesSum_of_abs hχψu).sum =
          (BishopC.seriesSum_of_abs hχψt).sum :=
      BishopC.seriesSum_unique
        (BishopC.seriesSum_of_abs hχψu)
        (BishopC.seriesSum_of_abs hχψt)
    have hφtval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_or_rightN s1 s2)).value_eq
          x hφtdom hχφtDom hφtDom hχφt hφt
    have hφuval :=
      (theorem46_mid_source Mφ
        (theorem46_stateData_s3 s1 s2)).value_eq
          x hφudom hχφuDom hφuDom hχφu hφu
    have hψtval :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_or_rightN s1 s2)).value_eq
          x hψtdom hχψtDom hψtDom hχψt hψt
    have hψuval :=
      (theorem46_mid_source Mψ
        (theorem46_stateData_s3 s1 s2)).value_eq
          x hψudom hχψuDom hψuDom hχψu hψu
    have hφ_eq : φh.toFun x hφudom = φh.toFun x hφtdom :=
      pfun_value_proof_irrel φh hφudom hφtdom
    have hψ_eq : ψh.toFun x hψudom = ψh.toFun x hψtdom :=
      pfun_value_proof_irrel ψh hψudom hψtdom
    rw [hφtval, hφuval, hψtval, hψuval, hφ_eq, hψ_eq,
      hχφtψt, hχφuψu, hχu_t]
    exact theorem46_scalarMid_chi_trunc_increment_bound
      (Nat.le_add_left s2.n s1.n)
      (theorem46_chi_value_zero_or_one
        (BishopC.IntegrableSet1_or s1.hA s2.hA) hχψtDom hχψt)
      (Rel.left_nonneg x hφtdom)
      (Rel.right_nonneg x hψtdom)
      (Rel.le_value x hφtdom hψtdom)

/-- The source two-step pointwise domination follows from the value relation
`φ ≤ ψ`. -/
noncomputable def theorem46_part_abs_pointwise_two_step_domination
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {φh ψh : BishopC.PFunR Y R}
    (Mφ : Prop412DataCarryingMeasurable S φh)
    (Mψ : Prop412DataCarryingMeasurable S ψh)
    (Rel : Theorem46PartAbsValueRelation φh ψh) :
    Theorem46MidPointwiseTwoStepDominationData Mφ Mψ where
  left_set_step := by
    intro s1 s2
    exact theorem46_left_set_step_pointwise_data Mφ Mψ Rel s1 s2
  left_truncation_step := by
    intro s1 s2
    exact theorem46_left_trunc_step_pointwise_data Mφ Mψ Rel s1 s2
  right_set_step := by
    intro s1 s2
    exact theorem46_right_set_step_pointwise_data Mφ Mψ Rel s1 s2
  right_truncation_step := by
    intro s1 s2
    exact theorem46_right_trunc_step_pointwise_data Mφ Mψ Rel s1 s2

/-- Concrete pointwise data for Theorem 4.6 after G225. -/
noncomputable def theorem46_concrete_pointwise_parts_from_measurable_parts
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {f : BishopC.PFunR Y R}
    (Mpos : Prop412DataCarryingMeasurable S (theorem46_pfun_posPart f))
    (Mneg : Prop412DataCarryingMeasurable S (theorem46_pfun_negPart f))
    (Mabs : Prop412DataCarryingMeasurable S (theorem46_pfun_absPart f))
    (Habs :
      Sigma fun cAbs : R =>
        LocatedRangeSupremum
          (R := R) (T := Theorem46StateData S)
          (theorem46_midIntegralSurface Mabs) cAbs) :
    Theorem46ConcretePointwisePartSurfaceData S f where
  pos_measurable := Mpos
  neg_measurable := Mneg
  abs_measurable := Mabs
  positive_pointwise_two_step_domination :=
    theorem46_part_abs_pointwise_two_step_domination
      Mpos Mabs (theorem46_pos_abs_value_relation f)
  negative_pointwise_two_step_domination :=
    theorem46_part_abs_pointwise_two_step_domination
      Mneg Mabs (theorem46_neg_abs_value_relation f)
  abs_located_supremum := Habs

/-- Audit after G225. -/
structure Theorem46MidSourceConnectionAuditAfterG225 : Type where
  auxiliary_chi_supports_added_from_integrable_set_domains : Nat
  set_expansion_pointwise_data_closed : Nat
  truncation_expansion_pointwise_data_closed : Nat
  positive_negative_two_step_data_constructed_from_part_abs_relation : Nat
  external_choice_inputs_added : Nat
  prop_to_data_selector_inputs_added : Nat
  remaining_corollary47_connection_steps : Nat

def theorem46MidSourceConnectionAuditAfterG225 :
    Theorem46MidSourceConnectionAuditAfterG225 where
  auxiliary_chi_supports_added_from_integrable_set_domains := 1
  set_expansion_pointwise_data_closed := 1
  truncation_expansion_pointwise_data_closed := 1
  positive_negative_two_step_data_constructed_from_part_abs_relation := 1
  external_choice_inputs_added := 0
  prop_to_data_selector_inputs_added := 0
  remaining_corollary47_connection_steps := 1

/-- G225 package. -/
structure Chapter4G225Theorem46MidSourceConnectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g224 : Chapter4G224Theorem46ScalarIncrementPackage S
  audit : Theorem46MidSourceConnectionAuditAfterG225
  mid_source_connection_closed_this_step : Nat
  remaining_source_completion_steps_for_4_6_to_4_10 : Nat

def chapter4G225Theorem46MidSourceConnectionPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G225Theorem46MidSourceConnectionPackage S where
  g224 := chapter4G224Theorem46ScalarIncrementPackage S
  audit := theorem46MidSourceConnectionAuditAfterG225
  mid_source_connection_closed_this_step := 1
  remaining_source_completion_steps_for_4_6_to_4_10 := 1

end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46

/-- Progress after G225. -/
def bishopRegularSeqChapter4Theorem46MidSourceProgressAfterG225 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 97
  total_final_goal_percent := 98
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G225: connected the scalar set/truncation increment laws to the carried \
    Prop.4.12 mid-constructor sources for Theorem 4.6. Auxiliary characteristic \
    witnesses are read from IntegrableSet1 representative domains inside the \
    full support passed to Proposition 1.11; no external choice or Prop-to-data \
    selector is added. Remaining: connect the resulting Theorem 4.6 package into \
    the Corollary 4.7 / Theorem 4.10 route."


end BishopCReal
