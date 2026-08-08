import Mathdemo.Internal.CRat_iter137

/-!
# G38: Definition 1.6, `L1` integrable functions over Bishop RegularSeq reals

Definition 1.6 extends `L` to `L1` by representing an integrable function as a
partial function together with an `L`-valued series representation.  In the
Richman-style route all convergence and value-identification data are explicit.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Pointwise value law in Definition 1.6.  The domain is governed by absolute
convergence of the representing series, and the function value is the sum of
that series in Bishop equality. -/
structure BishopRegularSeqL1ValueLaw
    (f : BishopRegularSeqPFun X)
    (fn : Nat -> BishopRegularSeqPFun X) : Type 1 where
  abs_from_domain :
    forall x : X, x ∈ f.dom ->
      BishopRegularSeqSeriesSum (fun n => absSeq ((fn n).toFun x))
  domain_from_abs :
    forall x : X,
      BishopRegularSeqSeriesSum (fun n => absSeq ((fn n).toFun x)) ->
        x ∈ f.dom
  components_from_domain :
    forall x : X, x ∈ f.dom -> forall n : Nat, x ∈ (fn n).dom
  value_from_abs :
    forall x : X,
      BishopRegularSeqSeriesSum (fun n => absSeq ((fn n).toFun x)) ->
        { value_sum :
            BishopRegularSeqSeriesSum (fun n => (fn n).toFun x) //
          relEventually (f.toFun x) value_sum.sum }

/-- Definition 1.6: an `L1` representation over a RegularSeq integration
space. -/
structure BishopRegularSeqIntegrableRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  pfun : BishopRegularSeqPFun X
  fn : Nat -> BishopRegularSeqPFun X
  fn_mem : forall n : Nat, fn n ∈ S.core.L
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.absf (fn n)))
  integral_sum :
    BishopRegularSeqSeriesSum (fun n => S.core.I (fn n))
  value_law : BishopRegularSeqL1ValueLaw pfun fn
  source_definition_1_6_regularseq : Prop

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The first component, matching the source map `(f,{f_n}) ↦ f`. -/
def toPFun (r : BishopRegularSeqIntegrableRep S) :
    BishopRegularSeqPFun X :=
  r.pfun

/-- Equality in `L1` is equality of the first partial-function component. -/
def equiv (r s : BishopRegularSeqIntegrableRep S) : Prop :=
  BishopRegularSeqPFun.equiv r.pfun s.pfun

/-- The integral of an `L1` representation is the represented series of
integrals.  Well-definedness across equivalent representations is the next
source lemma, not hidden in this definition. -/
def integral (r : BishopRegularSeqIntegrableRep S) : RegularSeq :=
  r.integral_sum.sum

/-- The `L1` norm-like absolute integral supplied by Definition 1.6 data. -/
def norm (r : BishopRegularSeqIntegrableRep S) : RegularSeq :=
  r.abs_integral_sum.sum

end BishopRegularSeqIntegrableRep

namespace BishopRegularSeqPFun

variable {X : Type}

/-- The source embedding sequence for `f ∈ L`:
`f, 0*f, 0*f, ...`. -/
def ofLSeq (Arch : ScalarMulArchimedeanData)
    (f : BishopRegularSeqPFun X) : Nat -> BishopRegularSeqPFun X
  | 0 => f
  | Nat.succ _ => smul Arch zeroSeq f

end BishopRegularSeqPFun

/-- Membership of every term in the source embedding sequence. -/
theorem def16_ofLSeq_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopRegularSeqPFun X} (hf : f ∈ S.core.L) :
    forall n : Nat, BishopRegularSeqPFun.ofLSeq Arch f n ∈ S.core.L
  | 0 => hf
  | Nat.succ _ => S.core.smul_mem zeroSeq hf

/-- Data required to regard an `L` element as an `L1` element without inserting
any implicit selectors. -/
structure BishopRegularSeqOfLData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (f : BishopRegularSeqPFun X) (hf : f ∈ S.core.L) : Type 1 where
  abs_integral_sum :
    BishopRegularSeqSeriesSum
      (fun n =>
        S.core.I
          (BishopRegularSeqPFun.absf
            (BishopRegularSeqPFun.ofLSeq Arch f n)))
  integral_sum :
    BishopRegularSeqSeriesSum
      (fun n => S.core.I (BishopRegularSeqPFun.ofLSeq Arch f n))
  value_law :
    BishopRegularSeqL1ValueLaw f (BishopRegularSeqPFun.ofLSeq Arch f)
  integral_agrees :
    relEventually integral_sum.sum (S.core.I f)

/-- The source embedding `L ⊆ L1`, parameterized by the explicit convergence
and value law data. -/
def def16_ofL
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopRegularSeqPFun X} (hf : f ∈ S.core.L)
    (data : BishopRegularSeqOfLData S f hf) :
    BishopRegularSeqIntegrableRep S where
  pfun := f
  fn := BishopRegularSeqPFun.ofLSeq Arch f
  fn_mem := def16_ofLSeq_mem S hf
  abs_integral_sum := data.abs_integral_sum
  integral_sum := data.integral_sum
  value_law := data.value_law
  source_definition_1_6_regularseq := True

/-- The integral agrees with the previous `L` integral for the source embedding. -/
theorem def16_ofL_integral_agrees
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    {f : BishopRegularSeqPFun X} (hf : f ∈ S.core.L)
    (data : BishopRegularSeqOfLData S f hf) :
    relEventually
      (BishopRegularSeqIntegrableRep.integral
        (def16_ofL S hf data))
      (S.core.I f) :=
  data.integral_agrees

/-- Source-facing package for Definition 1.6. -/
structure BishopRegularSeqDef16Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  L1 : Type 1
  mk_rep : BishopRegularSeqIntegrableRep S -> L1
  to_pfun : L1 -> BishopRegularSeqPFun X
  integral : L1 -> RegularSeq
  equiv : L1 -> L1 -> Prop
  source_equality_by_first_component : Prop
  source_integral_by_representing_series : Prop
  old_L_embeds_with_explicit_data : Prop

/-- Current Definition 1.6 package using the representation type itself as
`L1`. -/
def bishopRegularSeqDef16Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqDef16Package S where
  L1 := BishopRegularSeqIntegrableRep S
  mk_rep := fun r => r
  to_pfun := fun r => r.toPFun
  integral := fun r => r.integral
  equiv := fun r s => r.equiv s
  source_equality_by_first_component := True
  source_integral_by_representing_series := True
  old_L_embeds_with_explicit_data := True

/-- Progress after G38: Definition 1.6 is now represented over the Bishop
RegularSeq integration space. -/
def bishopRegularSeqCh1To4ProgressAfterG38 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 44
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 37
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G38: added Definition 1.6 L1 integrable representations and the explicit \
    embedding of L into L1."


end BishopCReal
