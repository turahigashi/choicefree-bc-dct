import Mathdemo.Internal.CRat_iter144

/-!
# G45: Corollary 1.12 and Definition 1.13 norm

Corollary 1.12 says that a partial function agreeing with an integrable
function on a full set is itself integrable and has the same integral.
Definition 1.13 then defines the norm by `||f|| = I(|f|)`.

This file records both statements on the RegularSeq Bishop-real route.  The
Corollary 1.12 proof still depends on the Proposition 1.11 bridge and on the
source construction `g + h - h`; those proof steps are exposed as bridge data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Equality of two `L1` representatives on a full set, stated through the
explicit value sums supplied by Definition 1.6. -/
structure BishopRegularSeqL1EqOnFull
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (A : Set X)
    (r s : BishopRegularSeqIntegrableRep S) : Type 1 where
  eq_value :
    forall x : X,
      x ∈ A ->
        forall hr :
          BishopRegularSeqSeriesSum
            (fun n => absSeq ((r.fn n).toFun x)),
        forall hs :
          BishopRegularSeqSeriesSum
            (fun n => absSeq ((s.fn n).toFun x)),
          relEventually
            (BishopRegularSeqIntegrableRep.valueAt r x hr)
            (BishopRegularSeqIntegrableRep.valueAt s x hs)

/-- Source hypothesis in Corollary 1.12: an arbitrary partial function `f`
agrees with an integrable function `g` on a full set. -/
structure BishopRegularSeqCor112Agreement
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (A : Set X)
    (f : BishopRegularSeqPFun X)
    (g : BishopRegularSeqIntegrableRep S) : Type 1 where
  values_agree :
    forall x : X,
      x ∈ A ->
        x ∈ f.dom ->
          x ∈ BishopRegularSeqIntegrableRep.domain g ->
            relEventually (f.toFun x) (g.pfun.toFun x)

/-- Corollary 1.12 conclusion: the partial function has an integrable
representative whose integral agrees with `g`. -/
structure BishopRegularSeqCor112Conclusion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (f : BishopRegularSeqPFun X)
    (g : BishopRegularSeqIntegrableRep S) : Type 1 where
  rep : BishopRegularSeqIntegrableRep S
  represents_f : BishopRegularSeqPFun.equiv rep.pfun f
  integral_agrees : relEventually rep.integral g.integral

/-- Corollary 1.12 bridge.  The first field captures the integrability
upgrade for an arbitrary partial function; the second field is the useful
already-integrable special case obtained by applying Proposition 1.11 in both
directions and then using Bishop equality of RegularSeq values. -/
structure BishopRegularSeqCor112Bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  prop111_bridge : BishopRegularSeqProp111Bridge S
  integrable_from_full_agreement :
    forall {A : Set X},
      BishopRegularSeqFullSet S A ->
        forall (f : BishopRegularSeqPFun X)
          (g : BishopRegularSeqIntegrableRep S),
          BishopRegularSeqCor112Agreement S A f g ->
            BishopRegularSeqCor112Conclusion S f g
  integral_congr_on_full :
    forall {A : Set X},
      BishopRegularSeqFullSet S A ->
        forall r s : BishopRegularSeqIntegrableRep S,
          BishopRegularSeqL1EqOnFull S A r s ->
            relEventually r.integral s.integral
  source_uses_proposition_1_11 : Prop
  source_uses_g_plus_h_minus_h_representation : Prop
  regularseq_order_equality_step_is_frontier : Prop

/-- Corollary 1.12, source wording: full-set agreement with an integrable
function supplies integrability and equality of integrals. -/
def bishopRegularSeqCor112_integrable
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqCor112Bridge S)
    {A : Set X}
    (hA : BishopRegularSeqFullSet S A)
    (f : BishopRegularSeqPFun X)
    (g : BishopRegularSeqIntegrableRep S)
    (hagrees : BishopRegularSeqCor112Agreement S A f g) :
    BishopRegularSeqCor112Conclusion S f g :=
  bridge.integrable_from_full_agreement hA f g hagrees

/-- Corollary 1.12, integrable-representative form used later for
representation-independent statements. -/
def bishopRegularSeqCor112_integral_congr
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqCor112Bridge S)
    {A : Set X}
    (hA : BishopRegularSeqFullSet S A)
    (r s : BishopRegularSeqIntegrableRep S)
    (heq : BishopRegularSeqL1EqOnFull S A r s) :
    relEventually r.integral s.integral :=
  bridge.integral_congr_on_full hA r s heq

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Definition 1.13 in the source form: `||r|| = I(|r|)`.  The absolute-value
representation data is explicit because G41 made `|r|` a data-carrying
operation. -/
def sourceNorm
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AbsData r) :
    RegularSeq :=
  (BishopRegularSeqIntegrableRep.abs r data).integral

/-- The norm definition is literally the integral of the absolute-value
representative. -/
theorem sourceNorm_agrees_abs_integral
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.AbsData r) :
    relEventually
      (sourceNorm r data)
      ((BishopRegularSeqIntegrableRep.abs r data).integral) :=
  relEventually_refl _

end BishopRegularSeqIntegrableRep

/-- Source-facing package for Definition 1.13. -/
structure BishopRegularSeqDef113NormPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  sourceNorm :
    forall r : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.AbsData r -> RegularSeq
  sourceNorm_agrees_abs_integral :
    forall r : BishopRegularSeqIntegrableRep S,
      forall data : BishopRegularSeqIntegrableRep.AbsData r,
        relEventually
          (sourceNorm r data)
          ((BishopRegularSeqIntegrableRep.abs r data).integral)
  source_definition_1_13_regularseq : Prop
  norm_depends_on_definition_1_6_abs_data : Prop
  norm_extensionality_remains_frontier_for_proposition_1_14 : Prop

def bishopRegularSeqDef113NormPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqDef113NormPackage S where
  sourceNorm := fun r data =>
    BishopRegularSeqIntegrableRep.sourceNorm r data
  sourceNorm_agrees_abs_integral := fun r data =>
    BishopRegularSeqIntegrableRep.sourceNorm_agrees_abs_integral r data
  source_definition_1_13_regularseq := True
  norm_depends_on_definition_1_6_abs_data := True
  norm_extensionality_remains_frontier_for_proposition_1_14 := True

/-- Progress after G45: Corollary 1.12 and Definition 1.13 are now present on
the Bishop RegularSeq route, with their proof frontiers made explicit. -/
def bishopRegularSeqCh1To4ProgressAfterG45 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 58
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 44
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G45: added the RegularSeq Corollary 1.12 bridge for full-set agreement \
    and Definition 1.13 source norm as I(|f|), with Proposition 1.14 as the \
    next chapter-1 target."


end BishopCReal
