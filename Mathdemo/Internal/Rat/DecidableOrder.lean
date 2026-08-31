import Mathdemo.Internal.Rat.Quotient
import Mathdemo.Internal.BishopB

/-! Technical auxiliary material for the public import closure. -/

namespace BishopCRat
open Q
open BishopC  -- Technical note.

namespace CRat

/-- Technical lemma used in the public import closure. -/
def lt : CRat → CRat → Prop :=
  Quotient.lift₂ Q.lt (fun _ _ _ _ ha hb => propext (Q.lt_congr ha hb))

/-- Decidability of the lifted rational order.  This is needed only for the
data-valued cotransitivity field in the current `BishopB.COF` interface.
The quotient lift is independent of representatives by proof irrelevance for
`Decidable` values. -/
def ltDecidable (a b : CRat) : Decidable (lt a b) :=
  Quotient.rec
    (motive := fun a => (b : CRat) → Decidable (lt a b))
    (fun qa =>
      Quotient.rec
        (motive := fun b => Decidable (lt (mk qa) b))
        (fun qb => by
          change Decidable (qa.num * qb.den < qb.num * qa.den)
          infer_instance)
        (fun _ _ _ => Subsingleton.elim _ _))
    (fun _ _ _ => by
      funext b
      exact Subsingleton.elim _ _)
    a b

instance instDecidableLt (a b : CRat) : Decidable (lt a b) :=
  ltDecidable a b

theorem lt_irrefl (a : CRat) : ¬ lt a a := by
  induction a using Quotient.inductionOn with | _ qa => exact Q.lt_irrefl qa

theorem lt_cotrans {a b : CRat} (h : lt a b) (c : CRat) : lt a c ∨ lt c b := by
  induction a using Quotient.inductionOn with | _ qa =>
  induction b using Quotient.inductionOn with | _ qb =>
  induction c using Quotient.inductionOn with | _ qc =>
  exact Q.lt_cotrans h qc

/-- Data-valued cotransitivity for the current `BishopB.COF` interface. -/
def lt_cotrans_data {a b : CRat} (h : lt a b) (c : CRat) : PSum (lt a c) (lt c b) := by
  by_cases hleft : lt a c
  · exact PSum.inl hleft
  · refine PSum.inr ?_
    cases lt_cotrans h c with
    | inl hl => exact False.elim (hleft hl)
    | inr hr => exact hr

theorem lt_add_left (c : CRat) {a b : CRat} (h : lt a b) : lt (c + a) (c + b) := by
  induction c using Quotient.inductionOn with | _ qc =>
  induction a using Quotient.inductionOn with | _ qa =>
  induction b using Quotient.inductionOn with | _ qb =>
  exact Q.lt_add_left qc h

/-- Technical lemma used in the public import closure. -/
def absF : CRat → CRat :=
  Quotient.lift (fun a => mk (Q.abs a)) (fun _ _ h => Quotient.sound (Q.abs_congr h))

/-- Technical lemma used in the public import closure. -/
def half : CRat := mk Q.half

/-- Technical lemma used in the public import closure. -/
def maxF (a b : CRat) : CRat := half * (a + b + absF (a - b))
def minF (a b : CRat) : CRat := half * (a + b - absF (a - b))

theorem half_add_half : half + half = (1 : CRat) := Quotient.sound Q.half_add_half

theorem max_halfsum (a b : CRat) : maxF a b = half * (a + b + absF (a - b)) := rfl
theorem min_halfsum (a b : CRat) : minF a b = half * (a + b - absF (a - b)) := rfl

/-- Technical lemma used in the public import closure. -/
instance instCOF : COF CRat := {
  instCommRing with
  lt := lt
  lt_irrefl := lt_irrefl
  lt_cotrans := lt_cotrans
  lt_cotrans_data := lt_cotrans_data
  lt_add_left := lt_add_left
  abs := absF
  max := maxF
  min := minF
  half := half
  half_add_half := half_add_half
  max_halfsum := max_halfsum
  min_halfsum := min_halfsum
}

end CRat
end BishopCRat

-- Technical note.
