import Mathdemo.Internal.Real.Theorem116TailSqueezeBridge

/-!
# G51: Corollary 1.17 density interface

Corollary 1.17 says that `L` is dense in `L1`.  In the RegularSeq route, an
`L1` element already carries a representing sequence of `L` terms.  The finite
sums of that representing sequence are therefore the source approximants.

This file closes the membership of those finite sums in `L`, and records the
remaining density conclusion as explicit norm-convergence data supplied by
Theorem 1.16.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqCor117

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The source approximant in Corollary 1.17: the finite sum of the given
`L1` representation. -/
def approxPFun (r : BishopRegularSeqIntegrableRep S) (N : Nat) :
    BishopRegularSeqPFun X :=
  BishopRegularSeqPFun.finSum r.fn N

/-- The approximants are actual members of the original integration class `L`.
This is the constructive content behind the phrase "`L` is dense". -/
theorem approxPFun_mem
    (r : BishopRegularSeqIntegrableRep S) :
    forall N : Nat, approxPFun r N ∈ S.core.L := by
  intro N
  exact def11_finSum_mem S r.fn r.fn_mem N

/-- Embed the finite approximant into the `L1` representation type. -/
def approxRep
    (r : BishopRegularSeqIntegrableRep S)
    (ofL_data :
      forall N : Nat,
        BishopRegularSeqOfLData S
          (approxPFun r N) (approxPFun_mem r N))
    (N : Nat) :
    BishopRegularSeqIntegrableRep S :=
  def16_ofL S (approxPFun_mem r N) (ofL_data N)

end BishopRegularSeqCor117

/-- Data witnessing Corollary 1.17 for a fixed `L1` element.  The finite
approximants are fixed by the source representation; the only analytic
remaining data is the norm convergence, supplied via Theorem 1.16. -/
structure BishopRegularSeqCor117ApproxData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  ofL_data :
    forall N : Nat,
      BishopRegularSeqOfLData S
        (BishopRegularSeqCor117.approxPFun r N)
        (BishopRegularSeqCor117.approxPFun_mem r N)
  tail_sub_data :
    forall N : Nat,
      BishopRegularSeqIntegrableRep.SubData
        r (BishopRegularSeqCor117.approxRep r ofL_data N)
  tail_abs_data :
    forall N : Nat,
      BishopRegularSeqIntegrableRep.AbsData
        (BishopRegularSeqIntegrableRep.sub
          r
          (BishopRegularSeqCor117.approxRep r ofL_data N)
          (tail_sub_data N))
  norm_tendsto_zero :
    BishopRegularSeqTendsto
      (fun N =>
        BishopRegularSeqIntegrableRep.sourceNorm
          (BishopRegularSeqIntegrableRep.sub
            r
            (BishopRegularSeqCor117.approxRep r ofL_data N)
            (tail_sub_data N))
          (tail_abs_data N))
      zeroSeq
  source_uses_theorem_1_16_tail_norm_convergence : Prop

/-- Source-facing conclusion of Corollary 1.17. -/
structure BishopRegularSeqCor117Conclusion
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 1 where
  approximant : Nat -> BishopRegularSeqPFun X
  approximant_mem : forall N : Nat, approximant N ∈ S.core.L
  approximant_rep : Nat -> BishopRegularSeqIntegrableRep S
  tail_sub_data :
    forall N : Nat,
      BishopRegularSeqIntegrableRep.SubData r (approximant_rep N)
  tail_abs_data :
    forall N : Nat,
      BishopRegularSeqIntegrableRep.AbsData
        (BishopRegularSeqIntegrableRep.sub
          r (approximant_rep N) (tail_sub_data N))
  norm_tendsto_zero :
    BishopRegularSeqTendsto
      (fun N =>
        BishopRegularSeqIntegrableRep.sourceNorm
          (BishopRegularSeqIntegrableRep.sub
            r (approximant_rep N) (tail_sub_data N))
          (tail_abs_data N))
      zeroSeq
  source_corollary_1_17_regularseq : Prop

/-- Corollary 1.17 assembled from the explicit finite-sum approximants and the
norm convergence data obtained from Theorem 1.16. -/
def bishopRegularSeqCor117_from_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqCor117ApproxData S r) :
    BishopRegularSeqCor117Conclusion S r where
  approximant := BishopRegularSeqCor117.approxPFun r
  approximant_mem := BishopRegularSeqCor117.approxPFun_mem r
  approximant_rep :=
    BishopRegularSeqCor117.approxRep r data.ofL_data
  tail_sub_data := data.tail_sub_data
  tail_abs_data := data.tail_abs_data
  norm_tendsto_zero := data.norm_tendsto_zero
  source_corollary_1_17_regularseq := True

/-- Source-facing package for Corollary 1.17. -/
structure BishopRegularSeqCor117Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  approx_pfun :
    BishopRegularSeqIntegrableRep S -> Nat -> BishopRegularSeqPFun X
  approx_mem :
    forall r : BishopRegularSeqIntegrableRep S,
      forall N : Nat, approx_pfun r N ∈ S.core.L
  approx_data : BishopRegularSeqIntegrableRep S -> Type 1
  conclusion :
    forall r : BishopRegularSeqIntegrableRep S,
      approx_data r -> BishopRegularSeqCor117Conclusion S r
  source_L_dense_in_L1 : Prop

def bishopRegularSeqCor117Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqCor117Package S where
  approx_pfun := fun r N => BishopRegularSeqCor117.approxPFun r N
  approx_mem := fun r N => BishopRegularSeqCor117.approxPFun_mem r N
  approx_data := BishopRegularSeqCor117ApproxData S
  conclusion := fun r data => bishopRegularSeqCor117_from_data S r data
  source_L_dense_in_L1 := True

/-- Progress after G51: Corollary 1.17 now has the finite-sum approximants in
`L` closed and the density conclusion packaged over RegularSeq `L1`. -/
def bishopRegularSeqCh1To4ProgressAfterG51 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 76
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 51
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G51: added Corollary 1.17 density data; finite-sum approximants are \
    proved to lie in L, with norm convergence supplied by Theorem 1.16."


end BishopCReal
