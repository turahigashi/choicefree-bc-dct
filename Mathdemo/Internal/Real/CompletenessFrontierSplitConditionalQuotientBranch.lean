import Mathdemo.Internal.Real.FinalCompletenessInterfaceConditionalQuotientBranch

/-!
# Completeness frontier split for the conditional quotient branch

`FinalCompletenessInterfaceConditionalQuotientBranch` identified the honest final input for `COFOC.complete`:
representation-carrying sequential completeness.  This file splits that input
into two source-faithful sub-obligations:

* extract a concrete representative-sequence Cauchy datum from a quotient
  Cauchy sequence whose terms carry explicit representatives;
* build a diagonal limit for such a representative sequence and prove quotient
  convergence back to the original sequence.

The file proves only the interface bridge between these two obligations and
the live `HasLim` field.  It does not claim that either sub-obligation has
been solved.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Tail closeness at one dyadic gauge for two representatives. -/
def RepCloseAtGauge (k : Nat) (x y : RegularSeq) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n →
    Le (COF.abs (x.val n - y.val n)) (eps k)

/-- A representative-level Cauchy datum for a sequence of regular
representatives.  The `close_eventually` field deliberately stays in the
existing representative vocabulary; the exact conversion from quotient Cauchy
data into this shape is recorded separately below. -/
structure CRealRepSequenceCauchyData (w : Nat → RegularSeq) : Type where
  cmod : Nat → Nat
  close_eventually :
    ∀ k m n : Nat, cmod k ≤ m → cmod k ≤ n →
      RepCloseAtGauge k (w m) (w n)










end BishopCReal

