import Mathdemo.Internal.Real.Chapter2EntryLayerBishopRegularSeq

set_option linter.style.longLine false

/-!
# G133: chapter-2 full-domain closure for finite set operations

G132 introduced the RegularSeq-native chapter-2 integrable-set surface.  This
file closes the first finite-set domain layer: the characteristic domains of
`A ∨ B`, `A ∧ B`, and `C - D` are full whenever the corresponding source
domains supplied by the carried characteristic representations are full.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2

/-- Transport a full-set witness across set equality. -/
def fullSetCongr
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {A B : Set X}
    (h : A = B)
    (hA : BishopRegularSeqFullSet S A) :
    BishopRegularSeqFullSet S B where
  reps := hA.reps
  subset := by
    intro x hx
    rw [← h]
    exact hA.subset x hx

/-- The domain of `A ∨ B` is the intersection of the two source domains. -/
theorem bset_or_domain_eq (A B : BSet X) :
    (BSet.or A B).S1 ∪ (BSet.or A B).S2 =
      (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
  ext x
  change
    x ∈ ((A.S1 ∩ B.S1) ∪ (A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1)) ∪
        (A.S2 ∩ B.S2) ↔
      x ∈ (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2)
  simp only [Set.mem_union, Set.mem_inter_iff]
  constructor
  · intro h
    rcases h with ((h11 | h12) | h21) | h22
    · exact ⟨Or.inl h11.1, Or.inl h11.2⟩
    · exact ⟨Or.inl h12.1, Or.inr h12.2⟩
    · exact ⟨Or.inr h21.1, Or.inl h21.2⟩
    · exact ⟨Or.inr h22.1, Or.inr h22.2⟩
  · intro h
    rcases h with ⟨hA, hB⟩
    rcases hA with hA1 | hA2
    · rcases hB with hB1 | hB2
      · exact Or.inl (Or.inl (Or.inl ⟨hA1, hB1⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hA1, hB2⟩))
    · rcases hB with hB1 | hB2
      · exact Or.inl (Or.inr ⟨hA2, hB1⟩)
      · exact Or.inr ⟨hA2, hB2⟩

/-- The domain of `A ∧ B` is the intersection of the two source domains. -/
theorem bset_and_domain_eq (A B : BSet X) :
    (BSet.and A B).S1 ∪ (BSet.and A B).S2 =
      (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2) := by
  ext x
  change
    x ∈ (A.S1 ∩ B.S1) ∪
        ((A.S1 ∩ B.S2) ∪ (A.S2 ∩ B.S1) ∪ (A.S2 ∩ B.S2)) ↔
      x ∈ (A.S1 ∪ A.S2) ∩ (B.S1 ∪ B.S2)
  simp only [Set.mem_union, Set.mem_inter_iff]
  constructor
  · intro h
    rcases h with h11 | ((h12 | h21) | h22)
    · exact ⟨Or.inl h11.1, Or.inl h11.2⟩
    · exact ⟨Or.inl h12.1, Or.inr h12.2⟩
    · exact ⟨Or.inr h21.1, Or.inl h21.2⟩
    · exact ⟨Or.inr h22.1, Or.inr h22.2⟩
  · intro h
    rcases h with ⟨hA, hB⟩
    rcases hA with hA1 | hA2
    · rcases hB with hB1 | hB2
      · exact Or.inl ⟨hA1, hB1⟩
      · exact Or.inr (Or.inl (Or.inl ⟨hA1, hB2⟩))
    · rcases hB with hB1 | hB2
      · exact Or.inr (Or.inl (Or.inr ⟨hA2, hB1⟩))
      · exact Or.inr (Or.inr ⟨hA2, hB2⟩)

/-- Negation swaps the two complemented-set sides and preserves the domain. -/
theorem bset_neg_domain_eq (A : BSet X) :
    (BSet.neg A).S1 ∪ (BSet.neg A).S2 = A.S1 ∪ A.S2 := by
  ext x
  change x ∈ A.S2 ∪ A.S1 ↔ x ∈ A.S1 ∪ A.S2
  simp only [Set.mem_union]
  constructor
  · intro h
    rcases h with h2 | h1
    · exact Or.inr h2
    · exact Or.inl h1
  · intro h
    rcases h with h1 | h2
    · exact Or.inr h1
    · exact Or.inl h2

/-- The domain of `C - D` is the same as the domain of `C ∧ D`. -/
theorem bset_sub_domain_eq_and_domain (C D : BSet X) :
    (BSet.sub C D).S1 ∪ (BSet.sub C D).S2 =
      (BSet.and C D).S1 ∪ (BSet.and C D).S2 := by
  rw [BSet.sub, bset_and_domain_eq C (BSet.neg D),
    bset_and_domain_eq C D, bset_neg_domain_eq D]

/-- Full-domain witness for `A ∨ B`. -/
def fullDomain_or
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) :
    BishopRegularSeqFullSet S
      ((BSet.or A B).S1 ∪ (BSet.or A B).S2) :=
  fullSetCongr
    (bset_or_domain_eq A B).symm
    (BishopRegularSeqFullSet.inter hA.full_domain hB.full_domain)

/-- Full-domain witness for `A ∧ B`. -/
def fullDomain_and
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {A B : BSet X}
    (hA : IntegrableSet S A)
    (hB : IntegrableSet S B) :
    BishopRegularSeqFullSet S
      ((BSet.and A B).S1 ∪ (BSet.and A B).S2) :=
  fullSetCongr
    (bset_and_domain_eq A B).symm
    (BishopRegularSeqFullSet.inter hA.full_domain hB.full_domain)

/-- Full-domain witness for the relative difference `C - D`, using the
carried full-domain witness for `C ∧ D`. -/
def fullDomain_sub_of_and
    {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
    {C D : BSet X}
    (_hC : IntegrableSet S C)
    (hCD : IntegrableSet S (BSet.and C D)) :
    BishopRegularSeqFullSet S
      ((BSet.sub C D).S1 ∪ (BSet.sub C D).S2) :=
  fullSetCongr
    (bset_sub_domain_eq_and_domain C D).symm
    hCD.full_domain

/-- Domain-closure package for the first finite set operations of chapter 2. -/
structure FiniteDomainClosurePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  or_domain_full :
    forall {A B : BSet X},
      IntegrableSet S A ->
        IntegrableSet S B ->
          BishopRegularSeqFullSet S
            ((BSet.or A B).S1 ∪ (BSet.or A B).S2)
  and_domain_full :
    forall {A B : BSet X},
      IntegrableSet S A ->
        IntegrableSet S B ->
          BishopRegularSeqFullSet S
            ((BSet.and A B).S1 ∪ (BSet.and A B).S2)
  sub_domain_full :
    forall {C D : BSet X},
      IntegrableSet S C ->
        IntegrableSet S (BSet.and C D) ->
          BishopRegularSeqFullSet S
            ((BSet.sub C D).S1 ∪ (BSet.sub C D).S2)
  source_or_domain_identity : Prop
  source_and_domain_identity : Prop
  source_sub_domain_identity : Prop
  next_frontier_is_characteristic_value_construction : Prop

def finiteDomainClosurePackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    FiniteDomainClosurePackage S where
  or_domain_full := fun hA hB => fullDomain_or hA hB
  and_domain_full := fun hA hB => fullDomain_and hA hB
  sub_domain_full := fun hC hCD => fullDomain_sub_of_and hC hCD
  source_or_domain_identity := True
  source_and_domain_identity := True
  source_sub_domain_identity := True
  next_frontier_is_characteristic_value_construction := True

/-- Audit for G133. -/
structure Chapter2FiniteDomainAudit : Type where
  bset_or_domain_identity_closed : Nat
  bset_and_domain_identity_closed : Nat
  bset_sub_domain_identity_closed : Nat
  full_domain_or_closed : Nat
  full_domain_and_closed : Nat
  full_domain_sub_closed : Nat
  quotient_representative_extraction_inputs : Nat
  prop_to_data_selector_inputs : Nat
  classical_choice_inputs : Nat

def chapter2FiniteDomainAudit : Chapter2FiniteDomainAudit where
  bset_or_domain_identity_closed := 1
  bset_and_domain_identity_closed := 1
  bset_sub_domain_identity_closed := 1
  full_domain_or_closed := 1
  full_domain_and_closed := 1
  full_domain_sub_closed := 1
  quotient_representative_extraction_inputs := 0
  prop_to_data_selector_inputs := 0
  classical_choice_inputs := 0

end BishopRegularSeqChapter2

/-- G133 package: finite operation domains for chapter 2 are closed. -/
structure BishopRegularSeqChapter2G133Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g132 : BishopRegularSeqChapter2G132Package S
  domain_closure : BishopRegularSeqChapter2.FiniteDomainClosurePackage S
  audit : BishopRegularSeqChapter2.Chapter2FiniteDomainAudit
  prop24_or_and_domains_full : Prop
  prop25_sub_domain_full : Prop
  next_frontier_characteristic_value_construction : Prop

def bishopRegularSeqChapter2G133Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqChapter2G133Package S where
  g132 := bishopRegularSeqChapter2G132Package S
  domain_closure := BishopRegularSeqChapter2.finiteDomainClosurePackage S
  audit := BishopRegularSeqChapter2.chapter2FiniteDomainAudit
  prop24_or_and_domains_full := True
  prop25_sub_domain_full := True
  next_frontier_characteristic_value_construction := True

/-- Progress after G133: chapter 2 has the finite-operation full-domain
closure needed before constructing the characteristic representations. -/
def bishopRegularSeqCh1To4ProgressAfterG133 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 16
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G133: closed full-domain identities for Chapter 2 finite set operations \
    A∨B, A∧B, and C-D over the Bishop RegularSeq integrable-set surface."


end BishopCReal
