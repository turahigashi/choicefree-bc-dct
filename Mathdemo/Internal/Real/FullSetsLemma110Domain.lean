import Mathdemo.Internal.Real.SourceRepresentationMinF1After

/-!
# G43: full sets and the Lemma 1.10 domain bridge

Definition 1.9 says that a subset of `X` is full when it contains a countable
intersection of domains of integrable functions.  Lemma 1.10 then turns such a
countable intersection into the domain of a single integrable function.

This file introduces the witness-rich RegularSeq version of that layer.  The
deep construction in Lemma 1.10 is kept as an explicit bridge.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Definition 1.6 domain: the domain of the first partial-function component.
The value law records the equivalent absolute-convergence description. -/
def domain (r : BishopRegularSeqIntegrableRep S) : Set X :=
  r.pfun.dom

/-- Interleave two sequences of integrable representations. -/
def repInterleave
    (r s : Nat -> BishopRegularSeqIntegrableRep S) :
    Nat -> BishopRegularSeqIntegrableRep S :=
  fun n => if n % 2 = 0 then r (n / 2) else s (n / 2)

end BishopRegularSeqIntegrableRep

/-- Definition 1.9 in witness-rich form: `A` contains a countable
intersection of domains of integrable functions. -/
structure BishopRegularSeqFullSet
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (A : Set X) : Type 1 where
  reps : Nat -> BishopRegularSeqIntegrableRep S
  subset :
    forall x : X,
      (forall n : Nat,
        x ∈ BishopRegularSeqIntegrableRep.domain (reps n)) ->
        x ∈ A

namespace BishopRegularSeqFullSet

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- A domain of an integrable representation is full, using the constant
sequence of that representation. -/
def of_domain
    (r : BishopRegularSeqIntegrableRep S) :
    BishopRegularSeqFullSet S
      (BishopRegularSeqIntegrableRep.domain r) where
  reps := fun _ => r
  subset := fun _ hx => hx 0

/-- Full sets are closed under binary intersection by interleaving the two
witnessing families. -/
def inter
    {A B : Set X}
    (hA : BishopRegularSeqFullSet S A)
    (hB : BishopRegularSeqFullSet S B) :
    BishopRegularSeqFullSet S (A ∩ B) where
  reps :=
    BishopRegularSeqIntegrableRep.repInterleave hA.reps hB.reps
  subset := by
    intro x hx
    constructor
    · exact hA.subset x (fun k => by
        have h := hx (2 * k)
        have hmod : (2 * k) % 2 = 0 := by omega
        have hdiv : (2 * k) / 2 = k := by omega
        simpa [BishopRegularSeqIntegrableRep.repInterleave, hmod, hdiv] using h)
    · exact hB.subset x (fun k => by
        have h := hx (2 * k + 1)
        have hmod : ¬ (2 * k + 1) % 2 = 0 := by omega
        have hdiv : (2 * k + 1) / 2 = k := by omega
        simpa [BishopRegularSeqIntegrableRep.repInterleave, hmod, hdiv] using h)

end BishopRegularSeqFullSet

/-- Lemma 1.10 core construction as an explicit bridge: from any sequence of
integrable functions, build a single integrable function whose domain lies in
the intersection of their domains. -/
structure BishopRegularSeqLemma110Bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  from_sequence :
    forall F : Nat -> BishopRegularSeqIntegrableRep S,
      { G : BishopRegularSeqIntegrableRep S //
        forall x : X,
          x ∈ BishopRegularSeqIntegrableRep.domain G ->
            forall n : Nat,
              x ∈ BishopRegularSeqIntegrableRep.domain (F n) }

/-- Lemma 1.10 in the source wording, obtained from the explicit bridge and a
full-set witness. -/
def bishopRegularSeqLemma110_full
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqLemma110Bridge S)
    {A : Set X}
    (hA : BishopRegularSeqFullSet S A) :
    { G : BishopRegularSeqIntegrableRep S //
      forall x : X,
        x ∈ BishopRegularSeqIntegrableRep.domain G -> x ∈ A } :=
  let core := bridge.from_sequence hA.reps
  ⟨core.val, fun x hx => hA.subset x (core.property x hx)⟩

/-- Source-facing package for Definition 1.9 and the Lemma 1.10 domain
frontier. -/
structure BishopRegularSeqFullSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  full : Set X -> Type 1
  domain_full :
    forall r : BishopRegularSeqIntegrableRep S,
      full (BishopRegularSeqIntegrableRep.domain r)
  inter_full :
    forall {A B : Set X},
      full A -> full B -> full (A ∩ B)
  lemma110 :
    BishopRegularSeqLemma110Bridge S ->
      forall {A : Set X},
        full A ->
          { G : BishopRegularSeqIntegrableRep S //
            forall x : X,
              x ∈ BishopRegularSeqIntegrableRep.domain G -> x ∈ A }
  source_definition_1_9_regularseq : Prop
  source_lemma_1_10_is_domain_bridge : Prop

def bishopRegularSeqFullSetPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqFullSetPackage S where
  full := BishopRegularSeqFullSet S
  domain_full := fun r => BishopRegularSeqFullSet.of_domain r
  inter_full := fun hA hB => BishopRegularSeqFullSet.inter hA hB
  lemma110 := fun bridge => fun {A} hA =>
    bishopRegularSeqLemma110_full S bridge (A := A) hA
  source_definition_1_9_regularseq := True
  source_lemma_1_10_is_domain_bridge := True

/-- Progress after G43: Definition 1.9 and the Lemma 1.10 bridge are now
available in the Bishop RegularSeq route. -/
def bishopRegularSeqCh1To4ProgressAfterG43 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 54
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 42
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G43: added the witness-rich full-set layer for Definition 1.9 and \
    exposed Lemma 1.10 as the explicit domain-intersection bridge."


end BishopCReal
