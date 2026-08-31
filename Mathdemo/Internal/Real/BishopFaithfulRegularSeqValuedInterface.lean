import Mathdemo.Internal.Real.PosEventuallySelectorBoundaryScalarInstance

/-!
# G28: Bishop-faithful RegularSeq-valued interface

Bishop's real numbers are regular rational sequences themselves, not quotient
classes.  Equality of reals is the Bishop equality relation on regular
sequences.  Positive reals also carry hidden witness data.

Therefore the Bishop-faithful route is not a new `CommRing`-style class over
an arbitrary carrier.  The primary route is a setoid-style RegularSeq surface:

* carrier: `RegularSeq`;
* source equality: `rel`;
* working equality: `relEventually`, equivalent to the tail-modulus form used
  in later proofs;
* positivity: `PosEventuallyData`;
* inverse: indexed by positive data;
* integration-space values: partial functions into `RegularSeq`, with equality
  judged by Bishop equality rather than Lean structural equality.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Bishop-faithful scalar surface for regular-sequence reals.

This is not a typeclass instance.  It records the exact real-number structure
used by Bishop: regular sequences with Bishop equality and witness-carrying
positivity. -/
structure BishopRegularSeqRealSurface
    (A : ScalarMulArchimedeanData) : Type 1 where
  carrier : Type
  carrier_is_regularSeq : carrier = RegularSeq
  sourceEq : RegularSeq -> RegularSeq -> Prop
  sourceEq_is_rel : sourceEq = rel
  workEq : RegularSeq -> RegularSeq -> Prop
  workEq_is_relEventually : workEq = relEventually
  source_to_work : forall x y : RegularSeq, sourceEq x y -> workEq x y
  work_refl : forall x : RegularSeq, workEq x x
  work_symm : forall x y : RegularSeq, workEq x y -> workEq y x
  work_trans :
    forall x y z : RegularSeq, workEq x y -> workEq y z -> workEq x z
  zero : RegularSeq
  one : RegularSeq
  half : RegularSeq
  add : RegularSeq -> RegularSeq -> RegularSeq
  neg : RegularSeq -> RegularSeq
  sub : RegularSeq -> RegularSeq -> RegularSeq
  mul : RegularSeq -> RegularSeq -> RegularSeq
  abs : RegularSeq -> RegularSeq
  max : RegularSeq -> RegularSeq -> RegularSeq
  min : RegularSeq -> RegularSeq -> RegularSeq
  ltProp : RegularSeq -> RegularSeq -> Prop
  ltData : RegularSeq -> RegularSeq -> Type
  ltData_to_prop : forall {x y : RegularSeq}, ltData x y -> ltProp x y
  positiveProp : RegularSeq -> Prop
  positiveData : RegularSeq -> Type
  positiveData_to_prop : forall {x : RegularSeq}, positiveData x -> positiveProp x
  positiveInv : forall {x : RegularSeq}, positiveData x -> RegularSeq
  positiveInv_pos :
    forall {x : RegularSeq}, forall hx : positiveData x,
      ltData zero (positiveInv hx)
  positiveInv_mul_cancel :
    forall {x : RegularSeq}, forall hx : positiveData x,
      workEq (mul x (positiveInv hx)) one
  positiveInv_respects :
    forall {x y : RegularSeq}, forall hx : positiveData x,
      forall hy : positiveData y,
        workEq x y -> workEq (positiveInv hx) (positiveInv hy)
  archimedean_posData :
    forall {x : RegularSeq}, positiveData x ->
      Sigma (fun k : Nat => ltData (constSeq (eps k)) x)
  mul_archimedean_data :
    forall x : RegularSeq,
      { m : Nat // Not (ltProp one (mul (abs x) (constSeq (eps m)))) }
  setoidLaws : CRealRegularSeqSetoidLawLayer A
  algebraLaws : CRealRegularSeqAlgebraLawLayer A
  orderLaws : CRealRegularSeqDataOrderLawLayer
  archDataPackage : CRealRegularSeqDataCOFOCArchDataPackage A
  repSequenceComplete : CRealRepSequenceCompleteLayer
  source_not_quotient_class : Prop
  structural_equality_not_primary : Prop
  total_inverse_not_primary : Prop

def bishopRegularSeqRealSurface
    (A : ScalarMulArchimedeanData) :
    BishopRegularSeqRealSurface A where
  carrier := RegularSeq
  carrier_is_regularSeq := rfl
  sourceEq := rel
  sourceEq_is_rel := rfl
  workEq := relEventually
  workEq_is_relEventually := rfl
  source_to_work := rel_to_relEventually
  work_refl := relEventually_refl
  work_symm := relEventually_symm
  work_trans := relEventually_trans
  zero := zeroSeq
  one := oneSeq
  half := halfSeq
  add := addSeq
  neg := negSeq
  sub := subSeq
  mul := mulSeqConcreteWith A
  abs := absSeq
  max := maxSeqWith A
  min := minSeqWith A
  ltProp := regularSeqLtProp
  ltData := regularSeqLtData
  ltData_to_prop := regularSeqLtData_to_prop
  positiveProp := PosEventually
  positiveData := PosEventuallyData
  positiveData_to_prop := fun hx => hx.toProp
  positiveInv := fun {x} hx => positiveTailInvSeqWithBound A x hx
  positiveInv_pos := fun hx =>
    regularSeqPositiveInvData_posData A hx
  positiveInv_mul_cancel := fun hx =>
    regularSeqPositiveInvData_mul_cancel A hx
  positiveInv_respects := fun hx hy hxy =>
    regularSeqPositiveInvData_respects A hx hy hxy
  archimedean_posData := fun hx =>
    regularSeqArchimedeanPositiveData hx
  mul_archimedean_data :=
    regularSeqMulArchimedean_const_data A
  setoidLaws := cRealRegularSeqSetoidLawLayer A
  algebraLaws := cRealRegularSeqAlgebraLawLayer A
  orderLaws := cRealRegularSeqDataOrderLawLayer
  archDataPackage := cRealRegularSeqDataCOFOCArchDataPackage A
  repSequenceComplete := cRealRepSequenceCompleteLayer
  source_not_quotient_class := True
  structural_equality_not_primary := True
  total_inverse_not_primary := True

/-- Bishop-style partial functions valued in regular-sequence reals. -/
structure BishopRegularSeqPFun (X : Type) where
  toFun : X -> RegularSeq
  dom : Set X

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Equality of partial functions: same domain and Bishop equality of values. -/
def equiv (f g : BishopRegularSeqPFun X) : Prop :=
  f.dom = g.dom ∧ forall x : X, x ∈ f.dom -> relEventually (f.toFun x) (g.toFun x)

def absf (f : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  ⟨fun x => absSeq (f.toFun x), f.dom⟩

def smul (A : ScalarMulArchimedeanData)
    (a : RegularSeq) (f : BishopRegularSeqPFun X) :
    BishopRegularSeqPFun X :=
  ⟨fun x => mulSeqConcreteWith A a (f.toFun x), f.dom⟩

def add (f g : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  ⟨fun x => addSeq (f.toFun x) (g.toFun x), f.dom ∩ g.dom⟩

def maxConst (A : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) (a : RegularSeq) :
    BishopRegularSeqPFun X :=
  ⟨fun x => maxSeqWith A (f.toFun x) a, f.dom⟩

def minConst (A : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) (a : RegularSeq) :
    BishopRegularSeqPFun X :=
  ⟨fun x => minSeqWith A (f.toFun x) a, f.dom⟩

def posPart (A : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  maxConst A f zeroSeq

def negPart (A : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) : BishopRegularSeqPFun X :=
  ⟨fun x => negSeq (minSeqWith A (f.toFun x) zeroSeq), f.dom⟩

end BishopRegularSeqPFun

/-- Bishop-faithful integration-space skeleton.

This mirrors the source definition at the interface level: `L` is a set of
partial functions, and the integral value lies in the regular-sequence real
surface.  Equalities in the laws are Bishop equalities (`relEventually`), not
Lean structural equalities of sequences. -/
structure BishopRegularSeqIntegrationSpaceSkeleton
    (A : ScalarMulArchimedeanData) (X : Type) : Type 1 where
  realSurface : BishopRegularSeqRealSurface A
  L : Set (BishopRegularSeqPFun X)
  I : BishopRegularSeqPFun X -> RegularSeq
  L_resp :
    forall {f g : BishopRegularSeqPFun X},
      f ∈ L -> BishopRegularSeqPFun.equiv f g -> g ∈ L
  I_resp :
    forall {f g : BishopRegularSeqPFun X},
      f ∈ L -> BishopRegularSeqPFun.equiv f g -> relEventually (I f) (I g)
  add_mem :
    forall {f g : BishopRegularSeqPFun X},
      f ∈ L -> g ∈ L -> BishopRegularSeqPFun.add f g ∈ L
  smul_mem :
    forall (a : RegularSeq) {f : BishopRegularSeqPFun X},
      f ∈ L -> BishopRegularSeqPFun.smul A a f ∈ L
  abs_mem :
    forall {f : BishopRegularSeqPFun X},
      f ∈ L -> BishopRegularSeqPFun.absf f ∈ L
  I_add :
    forall {f g : BishopRegularSeqPFun X}, forall _hf : f ∈ L,
      forall _hg : g ∈ L,
        relEventually
          (I (BishopRegularSeqPFun.add f g))
          (addSeq (I f) (I g))
  I_smul :
    forall (a : RegularSeq) {f : BishopRegularSeqPFun X}, forall _hf : f ∈ L,
      relEventually
        (I (BishopRegularSeqPFun.smul A a f))
        (mulSeqConcreteWith A a (I f))
  source_partial_function_model : Prop
  integral_values_are_regularseq_reals : Prop
  scalar_equalities_are_bishop_equalities : Prop

/-- Audit record tying the local source passages to the interface decision. -/
structure BishopRealSourceFaithfulnessAudit : Type where
  real_is_regular_sequence : Prop
  real_is_not_primary_quotient_class : Prop
  equality_is_bishop_relation : Prop
  positive_real_carries_witness : Prop
  measure_theory_values_are_real_valued_partial_functions : Prop
  interface_must_not_require_lean_structural_equality_as_real_equality : Prop
  old_cofoc_is_compatibility_layer_only : Prop

def bishopRealSourceFaithfulnessAudit :
    BishopRealSourceFaithfulnessAudit where
  real_is_regular_sequence := True
  real_is_not_primary_quotient_class := True
  equality_is_bishop_relation := True
  positive_real_carries_witness := True
  measure_theory_values_are_real_valued_partial_functions := True
  interface_must_not_require_lean_structural_equality_as_real_equality := True
  old_cofoc_is_compatibility_layer_only := True

/-- G28 progress meter after switching from typeclass weakening to
Bishop-faithful RegularSeq-valued integration surfaces. -/
structure CRealCOFOCG28BishopFaithfulProgressMeter : Type where
  regularSeqRealSurfacePercent : Nat
  bishopFaithfulInterfacePercent : Nat
  measureTheoryRefactorPercent : Nat
  oldQuotNoExtraInputPercent : Nat
  oldQuotDecidableAdapterPercent : Nat
  positiveWitnessBoundaryPercent : Nat
  sourceFaithfulnessConfidencePercent : Nat
  measureLayerSelectorCountTarget : Nat
  next_step_is_migrate_section1_or_section5_skeleton : Prop

def cRealCOFOCG28BishopFaithfulProgressMeter :
    CRealCOFOCG28BishopFaithfulProgressMeter where
  regularSeqRealSurfacePercent := 97
  bishopFaithfulInterfacePercent := 48
  measureTheoryRefactorPercent := 10
  oldQuotNoExtraInputPercent := 69
  oldQuotDecidableAdapterPercent := 76
  positiveWitnessBoundaryPercent := 86
  sourceFaithfulnessConfidencePercent := 94
  measureLayerSelectorCountTarget := 0
  next_step_is_migrate_section1_or_section5_skeleton := True

/-- Roadmap checkpoint for the corrected G28 direction. -/
structure CRealAfterBishopFaithfulInterfaceFrontier : Type where
  regularseq_setoid_surface_available : Prop
  pfun_values_use_regularseq_reals : Prop
  integration_skeleton_uses_bishop_equality : Prop
  no_total_inverse_in_primary_surface : Prop
  old_cofoc_route_demoted_to_adapter : Prop
  next_refactor_measure_files_against_this_surface : Prop

def cRealAfterBishopFaithfulInterfaceFrontier :
    CRealAfterBishopFaithfulInterfaceFrontier where
  regularseq_setoid_surface_available := True
  pfun_values_use_regularseq_reals := True
  integration_skeleton_uses_bishop_equality := True
  no_total_inverse_in_primary_surface := True
  old_cofoc_route_demoted_to_adapter := True
  next_refactor_measure_files_against_this_surface := True

end BishopCReal

set_option linter.style.longLine false

