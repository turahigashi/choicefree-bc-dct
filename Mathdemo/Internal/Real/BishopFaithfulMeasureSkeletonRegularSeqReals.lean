import Mathdemo.Internal.Real.BishopFaithfulRegularSeqValuedInterface

/-!
# G29: Bishop-faithful measure skeleton over RegularSeq reals

The existing chapter-5 measure file is written over `[COFOC R]` and evaluates
simple functions by deciding membership in a complemented set.  For Bishop
reals this is the wrong primary interface: the scalar values should be
`RegularSeq`, equality should be Bishop equality, and pointwise simple-function
branches should be supplied as data.

This file fixes the target shape for the chapter-5 refactor without changing
the previous compatibility layer.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Finite sums in the RegularSeq surface, using the source addition. -/
def regularSeqFinSum (u : Nat -> RegularSeq) : Nat -> RegularSeq
  | 0 => u 0
  | Nat.succ n => addSeq (regularSeqFinSum u n) (u (Nat.succ n))

/-- Chapter-5 measure-space skeleton whose values are Bishop reals represented
by regular sequences.  Measure equalities are Bishop equalities. -/
structure BishopRegularSeqMeasureSpaceSkeleton
    (Arch : ScalarMulArchimedeanData) (X : Type) : Type 1 where
  realSurface : BishopRegularSeqRealSurface Arch
  m : Set (BSet X)
  mu : (E : BSet X) -> E ∈ m -> RegularSeq
  mu_nonneg :
    forall E hE, Not (regularSeqLtProp (mu E hE) zeroSeq)
  mu_empty :
    forall E hE, (forall x : X, Not (x ∈ E.S1)) ->
      relEventually (mu E hE) zeroSeq
  m_or : forall E F : BSet X, E ∈ m -> F ∈ m -> BSet.or E F ∈ m
  m_and : forall E F : BSet X, E ∈ m -> F ∈ m -> BSet.and E F ∈ m
  mu_add :
    forall E F : BSet X, forall hE : E ∈ m, forall hF : F ∈ m,
      relEventually
        (addSeq (mu E hE) (mu F hF))
        (addSeq
          (mu (BSet.or E F) (m_or E F hE hF))
          (mu (BSet.and E F) (m_and E F hE hF)))
  m_sub :
    forall E F : BSet X, E ∈ m -> BSet.and E F ∈ m -> BSet.sub E F ∈ m
  mu_sub :
    forall E F : BSet X, forall hE : E ∈ m, forall hAnd : BSet.and E F ∈ m,
      relEventually
        (mu E hE)
        (addSeq
          (mu (BSet.and E F) hAnd)
          (mu (BSet.sub E F) (m_sub E F hE hAnd)))
  m_pos_E : BSet X
  m_pos_mem : m_pos_E ∈ m
  m_pos_data : regularSeqLtData zeroSeq (mu m_pos_E m_pos_mem)
  m_limit :
    forall (E : Nat -> BSet X), forall hE : forall n, E n ∈ m,
      (forall n, regularSeqLtData zeroSeq (mu (E n) (hE n))) ->
        { x : X // forall n, x ∈ (E n).S1 }


namespace BishopRegularSeqSimpleFunction

variable {Arch : ScalarMulArchimedeanData} {X : Type}
variable {M : BishopRegularSeqMeasureSpaceSkeleton Arch X}






end BishopRegularSeqSimpleFunction







end BishopCReal

set_option linter.style.longLine false

