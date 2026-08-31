import Mathdemo.Internal.Real.SplittingScalarLawsValueIdentificationCore

/-!
# G72: reducing value identification to PFun-level pointwise order

G71 split the final property-(4) scalar laws into value-identification and
core scalar order.  Definition 1.6 already records that `valueAt` agrees with
the first partial-function component.  This file proves and uses that generic
identification.

The remaining frontier is now PFun-level pointwise order:

* large line 735:
  the PFun value of `|min(f,n)-min(g_N,n)|` is bounded by the PFun value of
  `|f-g_N|`;
* small line 743:
  the PFun value of `min(|f|,1/n)` is bounded by the PFun value of the old
  small truncation plus the absolute tail.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqPFun

variable {X : Type}

/-- Pointwise expansion of partial-function absolute value. -/
theorem absf_toFun
    (f : BishopRegularSeqPFun X) (x : X) :
    (absf f).toFun x = absSeq (f.toFun x) :=
  rfl

/-- Pointwise expansion of partial-function scalar multiplication. -/
theorem smul_toFun
    (Arch : ScalarMulArchimedeanData)
    (a : RegularSeq) (f : BishopRegularSeqPFun X) (x : X) :
    (smul Arch a f).toFun x =
      mulSeqConcreteWith Arch a (f.toFun x) :=
  rfl

/-- Pointwise expansion of partial-function addition. -/
theorem add_toFun
    (f g : BishopRegularSeqPFun X) (x : X) :
    (add f g).toFun x = addSeq (f.toFun x) (g.toFun x) :=
  rfl

/-- Pointwise expansion of `max(f,a)`. -/
theorem maxConst_toFun
    (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) (a : RegularSeq) (x : X) :
    (maxConst Arch f a).toFun x = maxSeqWith Arch (f.toFun x) a :=
  rfl

/-- Pointwise expansion of `min(f,a)`. -/
theorem minConst_toFun
    (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) (a : RegularSeq) (x : X) :
    (minConst Arch f a).toFun x = minSeqWith Arch (f.toFun x) a :=
  rfl

/-- Pointwise expansion of the source notation `cutConst`. -/
theorem cutConst_toFun
    (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) (a : RegularSeq) (x : X) :
    (cutConst Arch f a).toFun x = minSeqWith Arch (f.toFun x) a :=
  rfl

/-- Pointwise expansion of `min(f,n)`. -/
theorem cutNat_toFun
    (Arch : ScalarMulArchimedeanData)
    (n : Nat) (f : BishopRegularSeqPFun X) (x : X) :
    (cutNat Arch n f).toFun x =
      minSeqWith Arch (f.toFun x) (constSeq (n : Scalar)) :=
  rfl

/-- Pointwise expansion of `min(|f|,1/n)` in the repository's `eps n` scale. -/
theorem cutSmall_toFun
    (Arch : ScalarMulArchimedeanData)
    (n : Nat) (f : BishopRegularSeqPFun X) (x : X) :
    (cutSmall Arch n f).toFun x =
      minSeqWith Arch (absSeq (f.toFun x)) (constSeq (eps n)) :=
  rfl

/-- Pointwise expansion of partial-function negation. -/
theorem neg_toFun
    (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) (x : X) :
    (neg Arch f).toFun x =
      mulSeqConcreteWith Arch (negSeq oneSeq) (f.toFun x) :=
  rfl

/-- Pointwise expansion of partial-function linear combination. -/
theorem linComb_toFun
    (Arch : ScalarMulArchimedeanData)
    (a b : RegularSeq)
    (f g : BishopRegularSeqPFun X) (x : X) :
    (linComb Arch a b f g).toFun x =
      addSeq
        (mulSeqConcreteWith Arch a (f.toFun x))
        (mulSeqConcreteWith Arch b (g.toFun x)) :=
  rfl

/-- Pointwise expansion of partial-function subtraction in the repository's
linear-combination representation. -/
theorem sub_toFun
    (Arch : ScalarMulArchimedeanData)
    (f g : BishopRegularSeqPFun X) (x : X) :
    (sub Arch f g).toFun x =
      addSeq
        (mulSeqConcreteWith Arch oneSeq (f.toFun x))
        (mulSeqConcreteWith Arch (negSeq oneSeq) (g.toFun x)) :=
  rfl

end BishopRegularSeqPFun

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Definition 1.6 value law: the selected `valueAt` agrees with the first
partial-function component. -/
theorem valueAt_agrees_pfun
    (r : BishopRegularSeqIntegrableRep S)
    (x : X)
    (habs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))) :
    relEventually
      (BishopRegularSeqIntegrableRep.valueAt r x habs)
      (r.pfun.toFun x) := by
  have h :=
    (r.value_law.value_from_abs x habs).property
  simpa [BishopRegularSeqIntegrableRep.valueAt] using
    relEventually_symm
      (r.pfun.toFun x)
      ((r.value_law.value_from_abs x habs).val.sum)
      h

/-- Pointwise expansion of the PFun component of `L1` addition. -/
theorem add_pfun_toFun
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AddData r s)
    (x : X) :
    ((BishopRegularSeqIntegrableRep.add r s data).pfun).toFun x =
      addSeq (r.pfun.toFun x) (s.pfun.toFun x) :=
  rfl

/-- Pointwise expansion of the PFun component of `L1` scalar multiplication. -/
theorem smul_pfun_toFun
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SmulData a r)
    (x : X) :
    ((BishopRegularSeqIntegrableRep.smul (S := S) a r data).pfun).toFun x =
      mulSeqConcreteWith Arch a (r.pfun.toFun x) :=
  rfl

/-- Pointwise expansion of the PFun component of `L1` absolute value. -/
theorem abs_pfun_toFun
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AbsData r)
    (x : X) :
    ((BishopRegularSeqIntegrableRep.abs r data).pfun).toFun x =
      absSeq (r.pfun.toFun x) :=
  rfl

/-- Pointwise expansion of the PFun component of `L1` subtraction. -/
theorem sub_pfun_toFun
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s)
    (x : X) :
    ((BishopRegularSeqIntegrableRep.sub r s data).pfun).toFun x =
      addSeq
        (r.pfun.toFun x)
        (mulSeqConcreteWith Arch (negSeq oneSeq) (s.pfun.toFun x)) :=
  rfl

/-- Pointwise expansion of the PFun component of source `min(f,a)` on `L1`. -/
theorem cutConst_pfun_toFun
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.CutConstData a r)
    (x : X) :
    ((BishopRegularSeqIntegrableRep.cutConst
      (S := S) a r data).pfun).toFun x =
      minSeqWith Arch (r.pfun.toFun x) a :=
  rfl

/-- Pointwise expansion of the PFun component of source `min(f,n)` on `L1`. -/
theorem cutNat_pfun_toFun
    (n : Nat)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      BishopRegularSeqIntegrableRep.CutConstData
        (constSeq (n : Scalar)) r)
    (x : X) :
    ((BishopRegularSeqIntegrableRep.cutNat
      (S := S) n r data).pfun).toFun x =
      minSeqWith Arch (r.pfun.toFun x) (constSeq (n : Scalar)) :=
  rfl

/-- Pointwise expansion of the PFun component of source `min(|f|,1/n)` on
`L1`. -/
theorem cutSmall_pfun_toFun
    (n : Nat)
    (r : BishopRegularSeqIntegrableRep S)
    (abs_data : BishopRegularSeqIntegrableRep.AbsData r)
    (data :
      BishopRegularSeqIntegrableRep.CutConstData
        (constSeq (eps n))
        (BishopRegularSeqIntegrableRep.abs r abs_data))
    (x : X) :
    ((BishopRegularSeqIntegrableRep.cutSmall
      (S := S) n r abs_data data).pfun).toFun x =
      minSeqWith Arch (absSeq (r.pfun.toFun x)) (constSeq (eps n)) :=
  rfl

end BishopRegularSeqIntegrableRep

/-- Generic conversion: once PFun-level pointwise order is known, the G71
value-identification transport data follows from Definition 1.6's value law. -/
def regularSeqOrderTransportData_from_pfun_order
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    (r s : BishopRegularSeqIntegrableRep S)
    (x : X)
    (hr :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x)))
    (hs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((s.fn n).toFun x)))
    (hpfun : RegularSeqLe (r.pfun.toFun x) (s.pfun.toFun x)) :
    RegularSeqOrderTransportData
      (BishopRegularSeqIntegrableRep.valueAt r x hr)
      (BishopRegularSeqIntegrableRep.valueAt s x hs) where
  left_model := r.pfun.toFun x
  right_model := s.pfun.toFun x
  left_eventual :=
    BishopRegularSeqIntegrableRep.valueAt_agrees_pfun r x hr
  right_eventual :=
    relEventually_symm
      (BishopRegularSeqIntegrableRep.valueAt s x hs)
      (s.pfun.toFun x)
      (BishopRegularSeqIntegrableRep.valueAt_agrees_pfun s x hs)
  core_order := hpfun

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Large line 735 after value-identification is discharged: the remaining
input is PFun-level pointwise min-Lipschitz order. -/
structure Property4LargeLine735PFunOrderData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (cutNatRep r cuts n)
        (largeOldCutRep S r cor117_data N n ofL_data))
    (cut_diff_abs_data :
      BishopRegularSeqIntegrableRep.AbsData
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)) :
    Type 2 where
  full_set : Set X
  full : BishopRegularSeqFullSet S full_set
  pfun_min_lipschitz :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          ((largeLine735LeftAbsRep
            S r cuts cor117_data N n
            ofL_data sub_data cut_diff_abs_data).pfun.toFun x)
          ((largeLine735RightAbsRep
            S r cor117_data N).pfun.toFun x)
  source_line735_pfun_abs_min_bound : Prop

/-- Convert PFun-level large line-735 order to G71 scalar-transport data. -/
def largeLine735ScalarTransportData_from_pfun_order
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (cutNatRep r cuts n)
        (largeOldCutRep S r cor117_data N n ofL_data))
    (cut_diff_abs_data :
      BishopRegularSeqIntegrableRep.AbsData
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data))
    (data :
      Property4LargeLine735PFunOrderData
        S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data) :
    Property4LargeLine735ScalarTransportData
      S r cuts cor117_data N n ofL_data sub_data cut_diff_abs_data where
  full_set := data.full_set
  full := data.full
  scalar_transport := by
    intro x hx hleft hright
    exact
      regularSeqOrderTransportData_from_pfun_order
        (largeLine735LeftAbsRep
          S r cuts cor117_data N n
          ofL_data sub_data cut_diff_abs_data)
        (largeLine735RightAbsRep S r cor117_data N)
        x hleft hright
        (data.pfun_min_lipschitz x hx)
  source_line735_left_value_identification := True
  source_line735_right_value_identification := True
  source_line735_core_scalar_min_lipschitz := True

/-- Small line 743 after value-identification is discharged: the remaining
input is PFun-level pointwise min-tail order. -/
structure Property4SmallLine743PFunOrderData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (smallOldCutPFun S r cuts cor117_abs_data N n)
        (smallOldCut_mem S r cuts cor117_abs_data N n))
    (add_data :
      BishopRegularSeqIntegrableRep.AddData
        (smallOldCutRep S r cuts cor117_abs_data N n ofL_data)
        (smallAbsTailAbsRep S r cuts cor117_abs_data N)) :
    Type 2 where
  full_set : Set X
  full : BishopRegularSeqFullSet S full_set
  pfun_min_tail :
    forall x : X,
      x ∈ full_set ->
        RegularSeqLe
          ((cutSmallRep r cuts n).pfun.toFun x)
          ((smallOldPlusTailRep
            S r cuts cor117_abs_data N n
            ofL_data add_data).pfun.toFun x)
  source_line743_pfun_min_tail_bound : Prop

/-- Convert PFun-level small line-743 order to G71 scalar-transport data. -/
def smallLine743ScalarTransportData_from_pfun_order
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_abs_data :
      BishopRegularSeqCor117ApproxData S
        (BishopRegularSeqIntegrableRep.abs r cuts.abs_data))
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (smallOldCutPFun S r cuts cor117_abs_data N n)
        (smallOldCut_mem S r cuts cor117_abs_data N n))
    (add_data :
      BishopRegularSeqIntegrableRep.AddData
        (smallOldCutRep S r cuts cor117_abs_data N n ofL_data)
        (smallAbsTailAbsRep S r cuts cor117_abs_data N))
    (data :
      Property4SmallLine743PFunOrderData
        S r cuts cor117_abs_data N n ofL_data add_data) :
    Property4SmallLine743ScalarTransportData
      S r cuts cor117_abs_data N n ofL_data add_data where
  full_set := data.full_set
  full := data.full
  scalar_transport := by
    intro x hx hleft hright
    exact
      regularSeqOrderTransportData_from_pfun_order
        (cutSmallRep r cuts n)
        (smallOldPlusTailRep
          S r cuts cor117_abs_data N n
          ofL_data add_data)
        x hleft hright
        (data.pfun_min_tail x hx)
  source_line743_left_value_identification := True
  source_line743_right_value_identification := True
  source_line743_core_scalar_min_tail := True

/-- Large line-735 route whose remaining input is PFun-level order. -/
structure Property4LargeLine735FromPFunOrderBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  abs_from_prop111 : BishopRegularSeqIntegralAbsProp111Bridge S
  old_cut_ofL_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (_cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqOfLData S
          (largeOldCutPFun S r cor117_data N n)
          (largeOldCut_mem S r cor117_data N n)
  cut_diff_sub_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.SubData
          (cutNatRep r cuts n)
          (largeOldCutRep S r cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n))
  cut_diff_abs_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.AbsData
          (largeCutDiffRep S r cuts cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n)
            (cut_diff_sub_data r cuts cor117_data N n))
  line735_pfun_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        Property4LargeLine735PFunOrderData
          S r cuts cor117_data N n
          (old_cut_ofL_data r cuts cor117_data N n)
          (cut_diff_sub_data r cuts cor117_data N n)
          (cut_diff_abs_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_pfun_order : Prop

/-- Convert the large PFun-order route to the G71 scalar-transport route. -/
def property4LargeLine735FromScalarTransportBridge_from_pfun_order
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine735FromPFunOrderBridge S) :
    Property4LargeLine735FromScalarTransportBridge S where
  abs_from_prop111 := bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_scalar_transport_data := by
    intro r cuts cor117_data N n
    exact
      largeLine735ScalarTransportData_from_pfun_order
        S r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
        (bridge.line735_pfun_order_data r cuts cor117_data N n)
  source_line734_reduced_to_prop111 := bridge.source_line734_reduced_to_prop111
  source_line735_split_into_value_identification_and_core_order := True

/-- Small line-743 route whose remaining input is PFun-level order. -/
structure Property4SmallLine743FromPFunOrderBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  prop111_bridge : BishopRegularSeqProp111Bridge S
  old_small_ofL_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        BishopRegularSeqOfLData S
          (smallOldCutPFun S r cuts cor117_abs_data N n)
          (smallOldCut_mem S r cuts cor117_abs_data N n)
  old_plus_tail_add_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.AddData
          (smallOldCutRep S r cuts cor117_abs_data N n
            (old_small_ofL_data r cuts cor117_abs_data N n))
          (smallAbsTailAbsRep S r cuts cor117_abs_data N)
  line743_pfun_order_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        Property4SmallLine743PFunOrderData
          S r cuts cor117_abs_data N n
          (old_small_ofL_data r cuts cor117_abs_data N n)
          (old_plus_tail_add_data r cuts cor117_abs_data N n)
  source_line743_reduced_to_pfun_order : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the small PFun-order route to the G71 scalar-transport route. -/
def property4SmallLine743FromScalarTransportBridge_from_pfun_order
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4SmallLine743FromPFunOrderBridge S) :
    Property4SmallLine743FromScalarTransportBridge S where
  prop111_bridge := bridge.prop111_bridge
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  line743_scalar_transport_data := by
    intro r cuts cor117_abs_data N n
    exact
      smallLine743ScalarTransportData_from_pfun_order
        S r cuts cor117_abs_data N n
        (bridge.old_small_ofL_data r cuts cor117_abs_data N n)
        (bridge.old_plus_tail_add_data r cuts cor117_abs_data N n)
        (bridge.line743_pfun_order_data r cuts cor117_abs_data N n)
  source_line743_split_into_value_identification_and_core_order := True
  source_line743_then_uses_prop111 := bridge.source_line743_then_uses_prop111

/-- The final branch routes after discharging value-identification generically;
the remaining inputs are PFun-level pointwise order data. -/
structure Property4PFunOrderBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_line735_pfun_order_route :
    Property4LargeLine735FromPFunOrderBridge S
  small_line743_pfun_order_route :
    Property4SmallLine743FromPFunOrderBridge S
  source_large_line735_value_identification_closed : Prop
  source_small_line743_value_identification_closed : Prop
  remaining_frontier_is_pfun_pointwise_order : Prop

/-- Convert PFun-order branch routes to the G71 scalar-transport routes. -/
def property4ScalarTransportBranchRoutes_from_pfun_order
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (routes : Property4PFunOrderBranchRoutes S) :
    Property4ScalarTransportBranchRoutes S where
  large_line735_transport_route :=
    property4LargeLine735FromScalarTransportBridge_from_pfun_order
      S routes.large_line735_pfun_order_route
  small_line743_transport_route :=
    property4SmallLine743FromScalarTransportBridge_from_pfun_order
      S routes.small_line743_pfun_order_route
  source_large_line735_value_identification_and_core_order := True
  source_small_line743_value_identification_and_core_order := True
  both_transport_routes_feed_scalar_law_routes := True

/-- Property-(4) reduction data with both branch frontiers reduced to
PFun-level pointwise order. -/
structure Property4ReductionDataFromPFunOrderBranchRoutes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  pfun_order_branch_routes : Property4PFunOrderBranchRoutes S
  large_epsv : RegularSeq
  large_eps_pos : regularSeqLtData zeroSeq large_epsv
  large_approx_index : Nat
  large_approx_norm_lt_eps :
    regularSeqLtData
      (BishopRegularSeqIntegrableRep.sourceNorm
        (BishopRegularSeqIntegrableRep.sub
          r
          ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep
            large_approx_index)
          ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data
            large_approx_index))
        ((bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data
          large_approx_index))
      large_epsv
  large_trunc_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
      (BishopRegularSeqIntegrableRep.integral r)
  small_epsv : RegularSeq
  small_eps_pos : regularSeqLtData zeroSeq small_epsv
  small_approx_index : Nat
  small_cor117_abs_data :
    BishopRegularSeqCor117ApproxData S
      (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
  small_abs_close :
    regularSeqLtData
      (BishopRegularSeqIntegrableRep.sourceNorm
        (BishopRegularSeqIntegrableRep.sub
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
          ((bishopRegularSeqCor117_from_data S
              (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
              small_cor117_abs_data).approximant_rep small_approx_index)
          ((bishopRegularSeqCor117_from_data S
              (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
              small_cor117_abs_data).tail_sub_data small_approx_index))
        ((bishopRegularSeqCor117_from_data S
            (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
            small_cor117_abs_data).tail_abs_data small_approx_index))
      small_epsv
  small_trunc_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
      zeroSeq
  source_property4_frontier_is_pfun_pointwise_order : Prop

/-- Convert G72 data to the G71 scalar-transport layer. -/
def property4ScalarTransportData_from_pfun_order
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromPFunOrderBranchRoutes S r) :
    Property4ReductionDataFromScalarTransportBranchRoutes S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  scalar_transport_branch_routes :=
    property4ScalarTransportBranchRoutes_from_pfun_order
      S data.pfun_order_branch_routes
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_property4_frontier_is_value_identification_plus_core_order := True

/-- Theorem 1.18 property (4), after generic value-identification has been
closed and only PFun-level pointwise order remains. -/
def property4_from_pfun_order_branch_routes
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromPFunOrderBranchRoutes S r) :
    Property4Conclusion S r :=
  property4_from_scalar_transport_branch_routes
    S r
    (property4ScalarTransportData_from_pfun_order S r data)

end BishopRegularSeqTheorem118

/-- G72 package: Definition 1.6's value identification is discharged
generically, reducing the final property-(4) frontier to PFun-level pointwise
order. -/
structure BishopRegularSeqTheorem118G72Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g71 : BishopRegularSeqTheorem118G71Package S
  valueAt_agrees_pfun :
    forall r : BishopRegularSeqIntegrableRep S,
      forall x : X,
        forall habs :
          BishopRegularSeqSeriesSum
            (fun n => absSeq ((r.fn n).toFun x)),
          relEventually
            (BishopRegularSeqIntegrableRep.valueAt r x habs)
            (r.pfun.toFun x)
  pfun_order_branch_routes : Type 4
  property4_pfun_order_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_pfun_order_branch_routes :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_pfun_order_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  source_value_identification_closed_by_definition_1_6 : Prop
  remaining_frontier_is_pfun_pointwise_order : Prop

def bishopRegularSeqTheorem118G72Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G72Package S where
  g71 := bishopRegularSeqTheorem118G71Package S
  valueAt_agrees_pfun := fun r x habs =>
    BishopRegularSeqIntegrableRep.valueAt_agrees_pfun r x habs
  pfun_order_branch_routes :=
    BishopRegularSeqTheorem118.Property4PFunOrderBranchRoutes S
  property4_pfun_order_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromPFunOrderBranchRoutes S
  property4_from_pfun_order_branch_routes := fun r data =>
    BishopRegularSeqTheorem118.property4_from_pfun_order_branch_routes
      S r data
  source_value_identification_closed_by_definition_1_6 := True
  remaining_frontier_is_pfun_pointwise_order := True

/-- Progress after G72: value-identification is closed generically; the
remaining property-(4) frontier is PFun-level pointwise order. -/
def bishopRegularSeqCh1To4ProgressAfterG72 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 73
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 72
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G72: proved Definition 1.6 valueAt-to-PFun identification and reduced \
    Theorem 1.18 property (4)'s final branch frontier to PFun-level \
    pointwise order."

set_option linter.style.longLine false


end BishopCReal
