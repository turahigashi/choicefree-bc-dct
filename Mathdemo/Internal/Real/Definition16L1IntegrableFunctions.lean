import Mathdemo.Internal.Real.SourceShapedLemma12Bridge

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



/-- The integral of an `L1` representation is the represented series of
integrals.  Well-definedness across equivalent representations is the next
source lemma, not hidden in this definition. -/
def integral (r : BishopRegularSeqIntegrableRep S) : RegularSeq :=
  r.integral_sum.sum


end BishopRegularSeqIntegrableRep

namespace BishopRegularSeqPFun

variable {X : Type}


end BishopRegularSeqPFun









end BishopCReal
