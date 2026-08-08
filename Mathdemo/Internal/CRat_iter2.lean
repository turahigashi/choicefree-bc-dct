import Mathdemo.Internal.CRat_iter1

/-! Technical auxiliary material for the public import closure. -/

namespace BishopCRat
open Q

/-- Technical lemma used in the public import closure. -/
instance setoid : Setoid Q := ⟨rel, rel_refl, fun {_ _} => rel_symm, fun {_ _ _} => rel_trans⟩

/-- Technical lemma used in the public import closure. -/
def CRat := Quotient setoid

namespace CRat

/-- Technical lemma used in the public import closure. -/
def mk (a : Q) : CRat := Quotient.mk setoid a

def add : CRat → CRat → CRat :=
  Quotient.lift₂ (fun a b => mk (Q.add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (Q.add_congr ha hb))

def mul : CRat → CRat → CRat :=
  Quotient.lift₂ (fun a b => mk (Q.mul a b))
    (fun _ _ _ _ ha hb => Quotient.sound (Q.mul_congr ha hb))

def neg : CRat → CRat :=
  Quotient.lift (fun a => mk (Q.neg a)) (fun _ _ h => Quotient.sound (Q.neg_congr h))

def zero : CRat := mk Q.zero
def one : CRat := mk Q.one

/-! Technical auxiliary material for the public import closure. -/

theorem add_comm (x y : CRat) : add x y = add y x :=
  Quotient.inductionOn₂ x y (fun a b => Quotient.sound (Q.add_comm a b))

theorem add_assoc (x y z : CRat) : add (add x y) z = add x (add y z) :=
  Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound (Q.add_assoc a b c))

theorem zero_add (x : CRat) : add zero x = x :=
  Quotient.inductionOn x (fun a => Quotient.sound (Q.zero_add a))

theorem add_zero (x : CRat) : add x zero = x :=
  Quotient.inductionOn x (fun a => Quotient.sound (Q.add_zero a))

theorem neg_add_cancel (x : CRat) : add (neg x) x = zero :=
  Quotient.inductionOn x (fun a => Quotient.sound (Q.neg_add_cancel a))

theorem mul_comm (x y : CRat) : mul x y = mul y x :=
  Quotient.inductionOn₂ x y (fun a b => Quotient.sound (Q.mul_comm a b))

theorem mul_assoc (x y z : CRat) : mul (mul x y) z = mul x (mul y z) :=
  Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound (Q.mul_assoc a b c))

theorem one_mul (x : CRat) : mul one x = x :=
  Quotient.inductionOn x (fun a => Quotient.sound (Q.one_mul a))

theorem mul_one (x : CRat) : mul x one = x :=
  Quotient.inductionOn x (fun a => Quotient.sound (Q.mul_one a))

theorem left_distrib (x y z : CRat) : mul x (add y z) = add (mul x y) (mul x z) :=
  Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound (Q.left_distrib a b c))

theorem right_distrib (x y z : CRat) : mul (add x y) z = add (mul x z) (mul y z) :=
  Quotient.inductionOn₃ x y z (fun a b c => Quotient.sound (Q.right_distrib a b c))

theorem zero_mul (x : CRat) : mul zero x = zero :=
  Quotient.inductionOn x (fun a => Quotient.sound (Q.zero_mul a))

theorem mul_zero (x : CRat) : mul x zero = zero :=
  Quotient.inductionOn x (fun a => Quotient.sound (Q.mul_zero a))

/-- Technical lemma used in the public import closure. -/
def nsmulCRat : ℕ → CRat → CRat := fun n x => Nat.rec zero (fun _ ih => add ih x) n
/-- Technical lemma used in the public import closure. -/
def zsmulCRat : ℤ → CRat → CRat := fun n x =>
  match n with
  | Int.ofNat m => nsmulCRat m x
  | Int.negSucc m => neg (nsmulCRat (m + 1) x)

/-! Technical auxiliary material for the public import closure. -/
instance instCommRing : CommRing CRat where
  add := add
  mul := mul
  neg := neg
  zero := zero
  one := one
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  nsmul := nsmulCRat
  zsmul := zsmulCRat

end CRat
end BishopCRat

-- Technical note.
