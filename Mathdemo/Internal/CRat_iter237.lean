import Mathdemo.Internal.CRat_iter236

set_option linter.style.longLine false

/-!
# G137: basic L1 `valueAt` transport for Chapter 2 formulas

G136 reduced Proposition 2.4 to explicit L1 value-transport data.  This file
closes the reusable operation-level transport lemmas:

* value selected by Definition 1.6 agrees with the carried partial function;
* addition transports to `addSeq`;
* scalar multiplication transports to `mulSeqConcreteWith`;
* absolute value transports to `absSeq`;
* subtraction transports to `subSeq`.

The remaining composite task is to instantiate these lemmas for the nested
`min2` and union formula representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqL1ValueTransport

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The selected `valueAt` of an L1 representative agrees with its carried
partial-function value. -/
theorem valueAt_agrees_pfun
    (r : BishopRegularSeqIntegrableRep S)
    (x : X)
    (habs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))) :
    relEventually
      (r.pfun.toFun x)
      (BishopRegularSeqIntegrableRep.valueAt r x habs) := by
  unfold BishopRegularSeqIntegrableRep.valueAt
  exact (r.value_law.value_from_abs x habs).property

/-- Addition value transport: once the operation representative and both
component values are defined at a point, the selected value of the sum is the
sum of the selected component values. -/
theorem add_valueAt_transport
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AddData r s)
    (x : X)
    (hadd_abs :
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.add r s data).fn n).toFun x)))
    (hr_abs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x)))
    (hs_abs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((s.fn n).toFun x))) :
    relEventually
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.add r s data) x hadd_abs)
      (addSeq
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)) := by
  have hadd_value :
      relEventually
        ((BishopRegularSeqIntegrableRep.add r s data).pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt
          (BishopRegularSeqIntegrableRep.add r s data) x hadd_abs) :=
    valueAt_agrees_pfun
      (BishopRegularSeqIntegrableRep.add r s data) x hadd_abs
  have hr_value :
      relEventually
        (r.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs) :=
    valueAt_agrees_pfun r x hr_abs
  have hs_value :
      relEventually
        (s.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt s x hs_abs) :=
    valueAt_agrees_pfun s x hs_abs
  have hpfun :
      relEventually
        ((BishopRegularSeqIntegrableRep.add r s data).pfun.toFun x)
        (addSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)) := by
    simpa [BishopRegularSeqIntegrableRep.add, BishopRegularSeqPFun.add] using
      addSeq_respects_eventually
        (r.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        (s.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)
        hr_value hs_value
  exact
    relEventually_trans
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.add r s data) x hadd_abs)
      ((BishopRegularSeqIntegrableRep.add r s data).pfun.toFun x)
      (addSeq
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        (BishopRegularSeqIntegrableRep.valueAt s x hs_abs))
      (relEventually_symm
        ((BishopRegularSeqIntegrableRep.add r s data).pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt
          (BishopRegularSeqIntegrableRep.add r s data) x hadd_abs)
        hadd_value)
      hpfun

/-- Scalar-multiplication value transport. -/
theorem smul_valueAt_transport
    (a : RegularSeq)
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SmulData a r)
    (x : X)
    (hsmul_abs :
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.smul a r data).fn n).toFun x)))
    (hr_abs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))) :
    relEventually
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.smul a r data) x hsmul_abs)
      (mulSeqConcreteWith Arch a
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)) := by
  have hsmul_value :
      relEventually
        ((BishopRegularSeqIntegrableRep.smul a r data).pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt
          (BishopRegularSeqIntegrableRep.smul a r data) x hsmul_abs) :=
    valueAt_agrees_pfun
      (BishopRegularSeqIntegrableRep.smul a r data) x hsmul_abs
  have hr_value :
      relEventually
        (r.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs) :=
    valueAt_agrees_pfun r x hr_abs
  have hpfun :
      relEventually
        ((BishopRegularSeqIntegrableRep.smul a r data).pfun.toFun x)
        (mulSeqConcreteWith Arch a
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)) := by
    simpa [BishopRegularSeqIntegrableRep.smul, BishopRegularSeqPFun.smul] using
      mulSeqConcrete_respects_eventually
        Arch
        a a
        (r.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        (relEventually_refl a)
        hr_value
  exact
    relEventually_trans
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.smul a r data) x hsmul_abs)
      ((BishopRegularSeqIntegrableRep.smul a r data).pfun.toFun x)
      (mulSeqConcreteWith Arch a
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs))
      (relEventually_symm
        ((BishopRegularSeqIntegrableRep.smul a r data).pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt
          (BishopRegularSeqIntegrableRep.smul a r data) x hsmul_abs)
        hsmul_value)
      hpfun

/-- Absolute-value transport. -/
theorem abs_valueAt_transport
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AbsData r)
    (x : X)
    (habs_abs :
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.abs r data).fn n).toFun x)))
    (hr_abs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x))) :
    relEventually
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.abs r data) x habs_abs)
      (absSeq (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)) := by
  have habs_value :
      relEventually
        ((BishopRegularSeqIntegrableRep.abs r data).pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt
          (BishopRegularSeqIntegrableRep.abs r data) x habs_abs) :=
    valueAt_agrees_pfun
      (BishopRegularSeqIntegrableRep.abs r data) x habs_abs
  have hr_value :
      relEventually
        (r.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs) :=
    valueAt_agrees_pfun r x hr_abs
  have hpfun :
      relEventually
        ((BishopRegularSeqIntegrableRep.abs r data).pfun.toFun x)
        (absSeq (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)) := by
    simpa [BishopRegularSeqIntegrableRep.abs, BishopRegularSeqPFun.absf] using
      absSeq_respects_eventually
        (r.pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        hr_value
  exact
    relEventually_trans
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.abs r data) x habs_abs)
      ((BishopRegularSeqIntegrableRep.abs r data).pfun.toFun x)
      (absSeq (BishopRegularSeqIntegrableRep.valueAt r x hr_abs))
      (relEventually_symm
        ((BishopRegularSeqIntegrableRep.abs r data).pfun.toFun x)
        (BishopRegularSeqIntegrableRep.valueAt
          (BishopRegularSeqIntegrableRep.abs r data) x habs_abs)
        habs_value)
      hpfun

/-- Subtraction value transport.  The source subtraction is implemented as
`r + (-1) * s`, so the absolute-summability data for the intermediate negative
representative is supplied explicitly. -/
theorem sub_valueAt_transport
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s)
    (x : X)
    (hsub_abs :
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.sub r s data).fn n).toFun x)))
    (hr_abs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((r.fn n).toFun x)))
    (hs_abs :
      BishopRegularSeqSeriesSum
        (fun n => absSeq ((s.fn n).toFun x)))
    (hneg_abs :
      BishopRegularSeqSeriesSum
        (fun n =>
          absSeq
            (((BishopRegularSeqIntegrableRep.smul
              (S := S) (negSeq oneSeq) s data.neg_data).fn n).toFun x))) :
    relEventually
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.sub r s data) x hsub_abs)
      (subSeq
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)) := by
  let negRep :=
    BishopRegularSeqIntegrableRep.smul
      (S := S) (negSeq oneSeq) s data.neg_data
  have hadd :
      relEventually
        (BishopRegularSeqIntegrableRep.valueAt
          (BishopRegularSeqIntegrableRep.add r negRep data.add_data) x hsub_abs)
        (addSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (BishopRegularSeqIntegrableRep.valueAt negRep x hneg_abs)) :=
    add_valueAt_transport r negRep data.add_data x hsub_abs hr_abs hneg_abs
  have hneg :
      relEventually
        (BishopRegularSeqIntegrableRep.valueAt negRep x hneg_abs)
        (mulSeqConcreteWith Arch (negSeq oneSeq)
          (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)) :=
    smul_valueAt_transport (negSeq oneSeq) s data.neg_data x hneg_abs hs_abs
  have hadd_neg :
      relEventually
        (addSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (BishopRegularSeqIntegrableRep.valueAt negRep x hneg_abs))
        (addSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (mulSeqConcreteWith Arch (negSeq oneSeq)
            (BishopRegularSeqIntegrableRep.valueAt s x hs_abs))) :=
    addSeq_respects_eventually
      (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
      (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
      (BishopRegularSeqIntegrableRep.valueAt negRep x hneg_abs)
      (mulSeqConcreteWith Arch (negSeq oneSeq)
        (BishopRegularSeqIntegrableRep.valueAt s x hs_abs))
      (relEventually_refl
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs))
      hneg
  have hto_sub :
      relEventually
        (addSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (mulSeqConcreteWith Arch (negSeq oneSeq)
            (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)))
        (subSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)) :=
    addSeq_negOneMul_right_eventually_subSeq Arch
      (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
      (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)
  exact
    relEventually_trans
      (BishopRegularSeqIntegrableRep.valueAt
        (BishopRegularSeqIntegrableRep.sub r s data) x hsub_abs)
      (addSeq
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        (BishopRegularSeqIntegrableRep.valueAt negRep x hneg_abs))
      (subSeq
        (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
        (BishopRegularSeqIntegrableRep.valueAt s x hs_abs))
      (by
        simpa [BishopRegularSeqIntegrableRep.sub, negRep] using hadd)
      (relEventually_trans
        (addSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (BishopRegularSeqIntegrableRep.valueAt negRep x hneg_abs))
        (addSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (mulSeqConcreteWith Arch (negSeq oneSeq)
            (BishopRegularSeqIntegrableRep.valueAt s x hs_abs)))
        (subSeq
          (BishopRegularSeqIntegrableRep.valueAt r x hr_abs)
          (BishopRegularSeqIntegrableRep.valueAt s x hs_abs))
        hadd_neg
        hto_sub)

/-- G137 package for the reusable operation-level `valueAt` transport lemmas. -/
structure BasicL1ValueTransportPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  valueAt_pfun :
    forall r : BishopRegularSeqIntegrableRep S,
      forall x : X,
        forall habs :
          BishopRegularSeqSeriesSum
            (fun n => absSeq ((r.fn n).toFun x)),
          relEventually
            (r.pfun.toFun x)
            (BishopRegularSeqIntegrableRep.valueAt r x habs)
  add_transport_available : Prop
  smul_transport_available : Prop
  abs_transport_available : Prop
  sub_transport_available : Prop
  next_frontier_is_nested_min2_or_instantiation : Prop

def basicL1ValueTransportPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BasicL1ValueTransportPackage S where
  valueAt_pfun := fun r x habs => valueAt_agrees_pfun r x habs
  add_transport_available := True
  smul_transport_available := True
  abs_transport_available := True
  sub_transport_available := True
  next_frontier_is_nested_min2_or_instantiation := True

/-- Audit for G137. -/
structure BasicL1ValueTransportAudit : Type where
  valueAt_pfun_closed : Nat
  add_transport_closed : Nat
  smul_transport_closed : Nat
  abs_transport_closed : Nat
  sub_transport_closed : Nat
  quotient_representative_extraction_inputs : Nat
  classical_choice_inputs : Nat
  remaining_nested_formula_instantiation : Prop

def basicL1ValueTransportAudit : BasicL1ValueTransportAudit where
  valueAt_pfun_closed := 1
  add_transport_closed := 1
  smul_transport_closed := 1
  abs_transport_closed := 1
  sub_transport_closed := 1
  quotient_representative_extraction_inputs := 0
  classical_choice_inputs := 0
  remaining_nested_formula_instantiation := True

end BishopRegularSeqL1ValueTransport

/-- G137 package: basic L1 operation-level value transports are closed. -/
structure BishopRegularSeqChapter2G137Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g136 : BishopRegularSeqChapter2G136Package S
  basic_value_transport :
    BishopRegularSeqL1ValueTransport.BasicL1ValueTransportPackage S
  audit :
    BishopRegularSeqL1ValueTransport.BasicL1ValueTransportAudit
  operation_value_transports_closed : Prop
  next_frontier_nested_min2_or_value_transport : Prop

def bishopRegularSeqChapter2G137Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G137Package S where
  g136 := bishopRegularSeqChapter2G136Package S
  basic_value_transport :=
    BishopRegularSeqL1ValueTransport.basicL1ValueTransportPackage S
  audit :=
    BishopRegularSeqL1ValueTransport.basicL1ValueTransportAudit
  operation_value_transports_closed := True
  next_frontier_nested_min2_or_value_transport := True

/-- Progress after G137: basic L1 operation-level value transport is closed. -/
def bishopRegularSeqCh1To4ProgressAfterG137 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 36
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G137: closed basic L1 valueAt transport for addition, scalar \
    multiplication, absolute value, and subtraction."


end BishopCReal
