import Mathdemo.Internal.Nodes
/-! Technical auxiliary material for the public import closure. -/
namespace BishopC

/-- Reduced constructive ordered-ring core: algebra plus Prop-valued order
transport.  It deliberately omits the Type-valued cotransitivity split. -/
class COF_core (R : Type*) extends CommRing R where
  lt : R → R → Prop
  lt_irrefl : ∀ a : R, ¬ lt a a
  lt_cotrans : ∀ {a b : R}, lt a b → ∀ c : R, lt a c ∨ lt c b
  lt_add_left : ∀ (c : R) {a b : R}, lt a b → lt (c + a) (c + b)
  abs : R → R
  max : R → R → R
  min : R → R → R
  half : R
  half_add_half : half + half = 1
  max_halfsum : ∀ a b : R, max a b = half * (a + b + abs (a - b))
  min_halfsum : ∀ a b : R, min a b = half * (a + b - abs (a - b))

namespace COF_core
variable {R : Type*} [COF_core R]
def halfPow : Nat → R
  | 0 => 1
  | Nat.succ n => COF_core.half * halfPow n
@[simp] theorem halfPow_zero : halfPow (R := R) 0 = (1 : R) := rfl
@[simp] theorem halfPow_succ (n : Nat) :
    halfPow (R := R) (Nat.succ n) = COF_core.half * halfPow n := rfl
def Close (k : Nat) (a b : R) : Prop :=
  COF_core.lt (COF_core.abs (a - b)) (halfPow (R := R) k)
end COF_core

/-- Technical lemma used in the public import closure. -/
class COF (R : Type*) extends COF_core R where
  /-- Technical lemma used in the public import closure. -/
  lt_cotrans_data : ∀ {a b : R}, lt a b → ∀ c : R, PSum (lt a c) (lt c b)

namespace COF
export COF_core
  (lt lt_irrefl lt_cotrans lt_add_left abs max min half
   half_add_half max_halfsum min_halfsum)
end COF

structure BFunR (X R : Type*) where
  dom : Set X
  toFun : ∀ x, x ∈ dom → R

namespace BFunR
variable {X R : Type*} [COF R]
def BEquiv (f g : BFunR X R) : Prop :=
  ∃ hdom : f.dom = g.dom,
    ∀ x (hx : x ∈ f.dom), f.toFun x hx = g.toFun x (hdom ▸ hx)
theorem BEquiv.refl (f : BFunR X R) : BEquiv f f :=
  ⟨rfl, fun _ _ => rfl⟩
def absf (f : BFunR X R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => COF.abs (f.toFun x hx)
def smul (a : R) (f : BFunR X R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => a * f.toFun x hx
def add (f g : BFunR X R) : BFunR X R where
  dom := f.dom ∩ g.dom
  toFun := fun x hx => f.toFun x hx.1 + g.toFun x hx.2
def maxConst (f : BFunR X R) (a : R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => COF.max (f.toFun x hx) a
def posPart (f : BFunR X R) : BFunR X R := maxConst f 0
def negPart (f : BFunR X R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => - COF.min (f.toFun x hx) 0
def cutConst (f : BFunR X R) (a : R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => COF.min (f.toFun x hx) a
def cutNat (n : Nat) (f : BFunR X R) : BFunR X R := cutConst f (n : R)
/-- Technical lemma used in the public import closure. -/
def seqSum (u : Nat → BFunR X R) : Nat → BFunR X R
  | 0 => u 0
  | Nat.succ n => add (seqSum u n) (u (Nat.succ n))
def seqSum_mem (u : Nat → BFunR X R) (x : X)
    (hx : ∀ n, x ∈ (u n).dom) : ∀ n, x ∈ (seqSum u n).dom
  | 0 => hx 0
  | n + 1 => ⟨seqSum_mem u x hx n, hx (n + 1)⟩
def PointwiseNonneg (f : BFunR X R) : Prop :=
  ∀ x : X, ∀ hx : x ∈ f.dom, ¬ COF.lt (f.toFun x hx) 0
structure PointwiseLE (f g : BFunR X R) : Prop where
  dom_eq : f.dom = g.dom
  le_val : ∀ x : X, ∀ hx : x ∈ f.dom,
    ¬ COF.lt (g.toFun x (dom_eq ▸ hx)) (f.toFun x hx)
end BFunR

namespace COF
variable {R : Type*} [COF R]
abbrev halfPow : Nat → R := COF_core.halfPow
abbrev Close (k : Nat) (a b : R) : Prop := COF_core.Close k a b
/-- Technical lemma used in the public import closure. -/
theorem max_add_negmin_eq_abs (a : R) : COF.max a 0 + (- COF.min a 0) = COF.abs a := by
  rw [COF.max_halfsum, COF.min_halfsum, sub_zero,
      show COF.half * (a + 0 + COF.abs a) + -(COF.half * (a + 0 - COF.abs a))
        = (COF.half + COF.half) * COF.abs a from by ring,
      COF.half_add_half, one_mul]
/-- Technical lemma used in the public import closure. -/
theorem max_add_min_eq_self (a : R) : COF.max a 0 + COF.min a 0 = a := by
  rw [COF.max_halfsum, COF.min_halfsum,
      show COF.half * (a + 0 + COF.abs (a - 0)) + COF.half * (a + 0 - COF.abs (a - 0))
        = (COF.half + COF.half) * (a + 0) from by ring,
      COF.half_add_half, one_mul, add_zero]
end COF

namespace RSeq
variable {R : Type*} [COF R]
def partialSum (u : Nat → R) : Nat → R
  | 0 => u 0
  | Nat.succ n => partialSum u n + u (Nat.succ n)
structure TendstoHalf (u : Nat → R) (l : R) where
  mod : Nat → Nat
  close : ∀ k n : Nat, mod k ≤ n → COF.Close k (u n) l
structure SeriesSum (u : Nat → R) where
  sum : R
  tends : TendstoHalf (partialSum u) sum
end RSeq

/-- Technical lemma used in the public import closure. -/
theorem BFunR.seqSum_toFun {X R : Type*} [COF R] (u : Nat → BFunR X R)
    (x : X) (hx : ∀ n, x ∈ (u n).dom) :
    ∀ n, (BFunR.seqSum u n).toFun x (BFunR.seqSum_mem u x hx n) =
      RSeq.partialSum (fun n => (u n).toFun x (hx n)) n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
      show (BFunR.seqSum u n).toFun x (BFunR.seqSum_mem u x hx n) +
          (u (n+1)).toFun x (hx (n + 1)) =
        RSeq.partialSum (fun n => (u n).toFun x (hx n)) n +
          (u (n+1)).toFun x (hx (n + 1))
      rw [ih]

structure PointwiseSeriesBelow {X R : Type*} [COF R]
    (fs : Nat → BFunR X R) (f : BFunR X R) where
  x : X
  hx_f : x ∈ f.dom
  hx_fs : ∀ n : Nat, x ∈ (fs n).dom
  point_sum : RSeq.SeriesSum (fun n => (fs n).toFun x (hx_fs n))
  below : COF.lt point_sum.sum (f.toFun x hx_f)

structure IntSpaceR (X R : Type*) [COF R] where
  L : Set (BFunR X R)
  I : BFunR X R → R
  L_resp : ∀ {f g : BFunR X R}, f ∈ L → BFunR.BEquiv f g → g ∈ L
  I_resp : ∀ {f g : BFunR X R}, f ∈ L → BFunR.BEquiv f g → I f = I g
  add_mem : ∀ {f g : BFunR X R}, f ∈ L → g ∈ L → BFunR.add f g ∈ L
  smul_mem : ∀ (a : R) {f : BFunR X R}, f ∈ L → BFunR.smul a f ∈ L
  abs_mem : ∀ {f : BFunR X R}, f ∈ L → BFunR.absf f ∈ L
  I_add : ∀ {f g : BFunR X R}, f ∈ L → g ∈ L → I (BFunR.add f g) = I f + I g
  I_smul : ∀ (a : R) {f : BFunR X R}, f ∈ L → I (BFunR.smul a f) = a * I f

namespace IntSpaceR
variable {X R : Type*} [COF R] (S : IntSpaceR X R)
theorem I_neg {f : BFunR X R} (hf : f ∈ S.L) : S.I (BFunR.smul (-1) f) = - S.I f := by
  rw [S.I_smul (-1) hf]; ring
theorem I_sub {f g : BFunR X R} (hf : f ∈ S.L) (hg : g ∈ S.L) :
    S.I (BFunR.add f (BFunR.smul (-1) g)) = S.I f - S.I g := by
  rw [S.I_add hf (S.smul_mem (-1) hg), S.I_smul (-1) hg]; ring
/-- Technical lemma used in the public import closure. -/
theorem seqSum_mem {u : Nat → BFunR X R} (hu : ∀ n, u n ∈ S.L) :
    ∀ n, BFunR.seqSum u n ∈ S.L := by
  intro n; induction n with
  | zero => exact hu 0
  | succ n ih => exact S.add_mem ih (hu (n + 1))
/-- Technical lemma used in the public import closure. -/
theorem I_seqSum {u : Nat → BFunR X R} (hu : ∀ n, u n ∈ S.L) :
    ∀ n, S.I (BFunR.seqSum u n) = RSeq.partialSum (fun k => S.I (u k)) n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
      show S.I (BFunR.add (BFunR.seqSum u n) (u (n + 1)))
         = RSeq.partialSum (fun k => S.I (u k)) n + S.I (u (n + 1))
      rw [S.I_add (seqSum_mem S hu n) (hu (n + 1)), ih]
/-- Technical lemma used in the public import closure. -/
theorem posPart_mem {f : BFunR X R} (hf : f ∈ S.L) : BFunR.posPart f ∈ S.L := by
  have hmem : BFunR.smul (COF.half : R) (BFunR.add f (BFunR.absf f)) ∈ S.L :=
    S.smul_mem _ (S.add_mem hf (S.abs_mem hf))
  refine S.L_resp hmem ⟨?_, ?_⟩
  · show f.dom ∩ f.dom = f.dom
    exact Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  · intro x hx
    show (COF.half : R) * (f.toFun x hx.1 + COF.abs (f.toFun x hx.2)) =
      COF.max (f.toFun x hx.1) 0
    rw [COF.max_halfsum, add_zero, sub_zero]
/-- Technical lemma used in the public import closure. -/
theorem negPart_mem {f : BFunR X R} (hf : f ∈ S.L) : BFunR.negPart f ∈ S.L := by
  have hmem : BFunR.smul (COF.half : R) (BFunR.add (BFunR.smul (-1) f) (BFunR.absf f)) ∈ S.L :=
    S.smul_mem _ (S.add_mem (S.smul_mem (-1) hf) (S.abs_mem hf))
  refine S.L_resp hmem ⟨?_, ?_⟩
  · show f.dom ∩ f.dom = f.dom
    exact Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  · intro x hx
    show (COF.half : R) * ((-1) * f.toFun x hx.1 + COF.abs (f.toFun x hx.2)) =
      - COF.min (f.toFun x hx.1) 0
    rw [COF.min_halfsum, add_zero, sub_zero]; ring
/-- I(|f|) = I(f⁺) + I(f⁻)(|f| ≃ᵇ f⁺+f⁻ + I_add)。 -/
theorem I_absf_eq {f : BFunR X R} (hf : f ∈ S.L) :
    S.I (BFunR.absf f) = S.I (BFunR.posPart f) + S.I (BFunR.negPart f) := by
  rw [← S.I_add (posPart_mem S hf) (negPart_mem S hf)]
  refine S.I_resp (S.abs_mem hf) ⟨?_, ?_⟩
  · show f.dom = f.dom ∩ f.dom
    exact Set.ext fun x => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  · intro x hx
    show COF.abs (f.toFun x hx) =
      COF.max (f.toFun x hx) 0 + (- COF.min (f.toFun x hx) 0)
    exact (COF.max_add_negmin_eq_abs (f.toFun x hx)).symm
/-- I(f) = I(f⁺) - I(f⁻)(f ≃ᵇ f⁺-f⁻ + I_add/I_neg)。 -/
theorem I_self_eq {f : BFunR X R} (hf : f ∈ S.L) :
    S.I f = S.I (BFunR.posPart f) - S.I (BFunR.negPart f) := by
  rw [sub_eq_add_neg, ← S.I_neg (negPart_mem S hf),
      ← S.I_add (posPart_mem S hf) (S.smul_mem (-1) (negPart_mem S hf))]
  refine S.I_resp hf ⟨?_, ?_⟩
  · show f.dom = f.dom ∩ f.dom
    exact Set.ext fun x => ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  · intro x hx
    show f.toFun x hx =
      COF.max (f.toFun x hx) 0 + (-1) * (- COF.min (f.toFun x hx) 0)
    rw [show COF.max (f.toFun x hx) 0 + (-1) * (- COF.min (f.toFun x hx) 0)
          = COF.max (f.toFun x hx) 0 + COF.min (f.toFun x hx) 0 from by ring]
    exact (COF.max_add_min_eq_self (f.toFun x hx)).symm
end IntSpaceR

structure IntSpaceRC (X R : Type*) [COF R] extends IntSpaceR X R where
  cutConst_mem : ∀ (a : R) {f : BFunR X R}, f ∈ L → BFunR.cutConst f a ∈ L
  continuity :
    ∀ {f : BFunR X R} {fs : Nat → BFunR X R},
      f ∈ L → (∀ n : Nat, fs n ∈ L) → (∀ n : Nat, BFunR.PointwiseNonneg (fs n)) →
      (hI : RSeq.SeriesSum (fun n => I (fs n))) → COF.lt hI.sum (I f) →
      PointwiseSeriesBelow fs f
  normalized : {p : BFunR X R // p ∈ L ∧ I p = 1}
  cutNat_tendsto :
    ∀ {f : BFunR X R}, f ∈ L → RSeq.TendstoHalf (fun n => I (BFunR.cutNat n f)) (I f)
  /-- Technical lemma used in the public import closure. -/
  cutSmall_tendsto :
    ∀ {f : BFunR X R}, f ∈ L →
      RSeq.TendstoHalf (fun k => I (BFunR.cutConst (BFunR.absf f) (COF.halfPow k))) 0

/-- Reduced order/absolute-value core used by the constructive CReal route.
It keeps the standard order, absolute-value, Archimedean, and completeness-facing
frontier fields, but omits the total reciprocal operation. -/
class COFO_core (R : Type*) extends COF_core R where
  lt_trans : ∀ {a b c : R}, lt a b → lt b c → lt a c
  abs_zero : abs (0 : R) = 0
  abs_neg : ∀ a : R, abs (-a) = abs a
  neg_le_abs : ∀ a : R, ¬ lt (abs a) (-a)            -- -a ≤ |a|
  le_abs_self : ∀ a : R, ¬ lt (abs a) a              --  a ≤ |a|
  abs_le_of : ∀ {a b : R}, ¬ lt b a → ¬ lt b (-a) → ¬ lt b (abs a)   -- a≤b,-a≤b ⟹ |a|≤b
  one_pos : lt (0 : R) 1
  half_pos : lt (0 : R) half
  mul_pos : ∀ {a b : R}, lt 0 a → lt 0 b → lt 0 (a * b)
  archimedean : ∀ t : R, lt 0 t → ∃ k : Nat, lt (COF_core.halfPow k) t
  -- Technical note.
  -- Technical note.
  archimedean_pos : ∀ t : R, lt 0 t → { k : Nat // lt (COF_core.halfPow k) t }
  abs_add_le : ∀ a b : R, ¬ lt (abs a + abs b) (abs (a + b))             -- |a+b| ≤ |a|+|b|
  eq_of_small : ∀ {a b : R}, (∀ k : Nat, ¬ lt (COF_core.halfPow k) (abs (a - b))) → a = b
  abs_of_nonneg : ∀ {a : R}, ¬ lt a 0 → abs a = a                        -- 0≤a ⟹ |a|=a
  max_zero_nonneg : ∀ a : R, ¬ lt (max a 0) 0                            -- max(a,0) ≥ 0
  max_le_abs : ∀ a : R, ¬ lt (abs a) (max a 0)                           -- max(a,0) ≤ |a|
  neg_min_zero_nonneg : ∀ a : R, ¬ lt (- min a 0) 0                      -- -min(a,0) ≥ 0
  neg_min_le_abs : ∀ a : R, ¬ lt (abs a) (- min a 0)                     -- -min(a,0) ≤ |a|
  lt_or_lt_of_abs_pos : ∀ {c : R}, lt 0 (abs c) → lt 0 c ∨ lt c 0        -- |c|>0 ⟹ c#0(apartness)
  abs_mul : ∀ a b : R, abs (a * b) = abs a * abs b                       -- |a·b| = |a|·|b|
  mul_nonneg : ∀ {a b : R}, ¬ lt a 0 → ¬ lt b 0 → ¬ lt (a * b) 0         -- 0≤a,0≤b ⟹ 0≤a·b
  mul_archimedean : ∀ x : R, { m : Nat // ¬ lt 1 (abs x * COF_core.halfPow m) }  -- Technical note.

/-- Technical lemma used in the public import closure. -/
class COFO (R : Type*) extends COF R, COFO_core R where
  /-- Technical lemma used in the public import closure. -/
  inv : R → R
  mul_inv_cancel : ∀ {x : R}, lt 0 x → x * inv x = 1          -- Technical note.
  inv_pos : ∀ {x : R}, lt 0 x → lt 0 (inv x)                  -- Technical note.

/-! Technical auxiliary material for the public import closure. -/
section Order
variable {R : Type*} [COF R]
/-- Technical lemma used in the public import closure. -/
def Le (a b : R) : Prop := ¬ COF.lt b a
/-- Technical lemma used in the public import closure. -/
def Nonneg (a : R) : Prop := Le (0 : R) a

theorem nonneg_zero : Nonneg (0 : R) := COF.lt_irrefl 0

/-- Technical lemma used in the public import closure. -/
theorem lt_of_nonneg_of_lt {a b : R} (ha : Nonneg a) (hab : COF.lt a b) : COF.lt 0 b := by
  rcases COF.lt_cotrans hab 0 with h | h
  · exact absurd h ha
  · exact h
/-- Technical lemma used in the public import closure. -/
theorem lt_of_lt_of_le {a b c : R} (hab : COF.lt a b) (hbc : Le b c) : COF.lt a c := by
  rcases COF.lt_cotrans hab c with h | h
  · exact h
  · exact absurd h hbc

/-- a < 0 ⟹ 0 < -a。 -/
theorem neg_pos_of_neg {a : R} (h : COF.lt a 0) : COF.lt 0 (-a) := by
  have key := COF.lt_add_left (-a) h
  rwa [show (-a + a) = (0:R) from by ring, show (-a + (0:R)) = -a from by ring] at key
/-- 0 < -a ⟹ a < 0。 -/
theorem neg_of_neg_pos {a : R} (h : COF.lt 0 (-a)) : COF.lt a 0 := by
  have key := COF.lt_add_left a h
  rwa [show (a + (0:R)) = a from by ring, show (a + -a) = (0:R) from by ring] at key
/-- a - b < 0 ⟹ a < b。 -/
theorem lt_of_sub_neg {a b : R} (h : COF.lt (a - b) 0) : COF.lt a b := by
  have key := COF.lt_add_left b h
  rwa [show (b + (a - b)) = a from by ring, show (b + (0:R)) = b from by ring] at key
/-- a < b ⟹ a - b < 0。 -/
theorem sub_neg_of_lt {a b : R} (h : COF.lt a b) : COF.lt (a - b) 0 := by
  have key := COF.lt_add_left (-b) h
  rwa [show (-b + a) = (a - b) from by ring, show (-b + b) = (0:R) from by ring] at key
/-- a ≤ a。 -/
theorem le_refl (a : R) : Le a a := COF.lt_irrefl a
/-- a ≤ b ≤ c ⟹ a ≤ c(cotransitivity)。 -/
theorem le_trans {a b c : R} (h1 : Le a b) (h2 : Le b c) : Le a c := by
  intro h
  rcases COF.lt_cotrans h b with hcb | hba
  · exact h2 hcb
  · exact h1 hba
/-- a≤b, c≤d ⟹ a+c ≤ b+d。 -/
theorem le_add {a b c d : R} (h1 : Le a b) (h2 : Le c d) : Le (a + c) (b + d) := by
  have e1 : Le (a + c) (b + c) := by
    intro h
    apply h1
    have t := COF.lt_add_left (-c) h
    rwa [show (-c + (b + c)) = b from by ring, show (-c + (a + c)) = a from by ring] at t
  have e2 : Le (b + c) (b + d) := by
    intro h
    apply h2
    have t := COF.lt_add_left (-b) h
    rwa [show (-b + (b + d)) = d from by ring, show (-b + (b + c)) = c from by ring] at t
  exact le_trans e1 e2
/-- 0 ≤ b - a ⟹ a ≤ b。 -/
theorem le_of_nonneg_sub {a b : R} (h : Nonneg (b - a)) : Le a b := fun hlt => h (sub_neg_of_lt hlt)
/-- a ≤ b ⟹ 0 ≤ b - a。 -/
theorem nonneg_sub_of_le {a b : R} (h : Le a b) : Nonneg (b - a) := fun hlt => h (lt_of_sub_neg hlt)
/-- a ≤ b ⟹ a - c ≤ b - c。 -/
theorem le_sub_right {a b c : R} (h : Le a b) : Le (a - c) (b - c) := by
  have t := le_add h (le_refl (-c))
  rwa [show a + -c = a - c from by ring, show b + -c = b - c from by ring] at t
/-- Technical lemma used in the public import closure. -/
theorem le_of_add_le_add_right {a b c : R} (h : Le (a + c) (b + c)) : Le a b := by
  intro hlt
  apply h
  have t := COF.lt_add_left c hlt
  rwa [show c + b = b + c from by ring, show c + a = a + c from by ring] at t
end Order

/-! Technical auxiliary material for the public import closure. -/
section OrderO
variable {R : Type*} [COFO R]
theorem halfPow_pos (k : Nat) : COF.lt 0 (COF.halfPow (R := R) k) := by
  induction k with
  | zero => exact COFO.one_pos
  | succ n ih => exact COFO.mul_pos COFO.half_pos ih

/-- Technical lemma used in the public import closure. -/
theorem nonneg_of_tendstoHalf_zeroseq {v : Nat → R} (s : R)
    (hv : ∀ n, v n = 0) (ht : RSeq.TendstoHalf v s) : Nonneg s := by
  intro hs                                  -- Technical note.
  have hnegpos : COF.lt 0 (-s) := neg_pos_of_neg hs
  have habspos : COF.lt 0 (COF.abs s) :=
    lt_of_lt_of_le hnegpos (COFO.neg_le_abs s)
  obtain ⟨k, hk⟩ := COFO.archimedean (COF.abs s) habspos     -- hk : halfPow k < |s|
  have hclose := ht.close k (ht.mod k) (Nat.le_refl _)
  -- Close k (v (mod k)) s = lt (abs (v(mod k) - s)) (halfPow k)
  rw [show COF.Close k (v (ht.mod k)) s
        = COF.lt (COF.abs (v (ht.mod k) - s)) (COF.halfPow k) from rfl, hv (ht.mod k)] at hclose
  rw [show ((0:R) - s) = -s from by ring, COFO.abs_neg] at hclose   -- hclose : |s| < halfPow k
  exact COF.lt_irrefl _ (COFO.lt_trans hk hclose)

/-- a ≤ b < c ⟹ a < c。 -/
theorem lt_of_le_of_lt {a b c : R} (hab : Le a b) (hbc : COF.lt b c) : COF.lt a c := by
  rcases COF.lt_cotrans hbc a with h | h
  · exact absurd h hab
  · exact h
/-- a<b, c<d ⟹ a+c < b+d。 -/
theorem lt_add {a b c d : R} (h1 : COF.lt a b) (h2 : COF.lt c d) :
    COF.lt (a + c) (b + d) := by
  have e1 : COF.lt (a + c) (b + c) := by
    have t := COF.lt_add_left c h1
    rwa [show c + a = a + c from by ring, show c + b = b + c from by ring] at t
  exact COFO.lt_trans e1 (COF.lt_add_left b h2)
/-- (½)^{k+1} + (½)^{k+1} = (½)^k。 -/
theorem halfPow_succ_add (k : Nat) :
    COF.halfPow (R := R) (k+1) + COF.halfPow (R := R) (k+1) = COF.halfPow (R := R) k := by
  show COF.half * COF.halfPow (R := R) k + COF.half * COF.halfPow (R := R) k
        = COF.halfPow (R := R) k
  rw [show COF.half * COF.halfPow (R := R) k + COF.half * COF.halfPow (R := R) k
        = (COF.half + COF.half) * COF.halfPow (R := R) k from by ring,
      COF.half_add_half, one_mul]
/-- Technical lemma used in the public import closure. -/
theorem tendstoHalf_unique {u : Nat → R} {s s' : R}
    (h : RSeq.TendstoHalf u s) (h' : RSeq.TendstoHalf u s') : s = s' := by
  apply COFO.eq_of_small
  intro k hcon
  obtain ⟨n, hn1, hn2⟩ : ∃ n, h.mod (k+1) ≤ n ∧ h'.mod (k+1) ≤ n :=
    ⟨h.mod (k+1) + h'.mod (k+1), Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  have hb1 : COF.lt (COF.abs (u n - s)) (COF.halfPow (k+1)) := h.close (k+1) n hn1
  have hb2 : COF.lt (COF.abs (u n - s')) (COF.halfPow (k+1)) := h'.close (k+1) n hn2
  have htri : Le (COF.abs (s - s')) (COF.abs (u n - s) + COF.abs (u n - s')) := by
    have hadd := COFO.abs_add_le (s - u n) (u n - s')
    rw [show (s - u n) + (u n - s') = s - s' from by ring,
        show COF.abs (s - u n) = COF.abs (u n - s) from by
          rw [show s - u n = -(u n - s) from by ring, COFO.abs_neg]] at hadd
    exact hadd
  have hsum : COF.lt (COF.abs (u n - s) + COF.abs (u n - s')) (COF.halfPow k) := by
    have t := lt_add hb1 hb2
    rwa [halfPow_succ_add] at t
  exact COF.lt_irrefl _ (COFO.lt_trans hcon (lt_of_le_of_lt htri hsum))
/-- Technical lemma used in the public import closure. -/
theorem seriesSum_unique {u : Nat → R} (a b : RSeq.SeriesSum u) : a.sum = b.sum :=
  tendstoHalf_unique a.tends b.tends

/-! Technical auxiliary material for the public import closure. -/
/-- 0≤a, 0≤b ⟹ 0≤a+b。 -/
theorem nonneg_add {a b : R} (ha : Nonneg a) (hb : Nonneg b) : Nonneg (a + b) := by
  intro hlt
  have h1 : COF.lt b (-a) := by
    have t := COF.lt_add_left (-a) hlt
    rwa [show (-a + (a + b)) = b from by ring, show (-a + (0:R)) = -a from by ring] at t
  have h2 : Le (-a) 0 := fun hpos => ha (neg_of_neg_pos hpos)
  exact hb (lt_of_lt_of_le h1 h2)
/-- Technical lemma used in the public import closure. -/
theorem nonneg_of_tendstoHalf_nonnegseq {u : Nat → R} (s : R)
    (hu : ∀ n, Nonneg (u n)) (ht : RSeq.TendstoHalf u s) : Nonneg s := by
  intro hs
  have hnegpos : COF.lt 0 (-s) := neg_pos_of_neg hs
  obtain ⟨k, hk⟩ := COFO.archimedean (-s) hnegpos
  have hclose : COF.lt (COF.abs (u (ht.mod k) - s)) (COF.halfPow k) :=
    ht.close k (ht.mod k) (Nat.le_refl _)
  have h1 : COF.lt (u (ht.mod k) - s) (-s) :=
    lt_of_le_of_lt (COFO.le_abs_self (u (ht.mod k) - s)) (COFO.lt_trans hclose hk)
  have h2 : COF.lt (u (ht.mod k)) 0 := by
    have t := COF.lt_add_left s h1
    rwa [show (s + (u (ht.mod k) - s)) = u (ht.mod k) from by ring,
        show (s + (-s)) = (0:R) from by ring] at t
  exact hu (ht.mod k) h2
/-- Technical lemma used in the public import closure. -/
theorem seriesSum_nonneg {u : Nat → R} (hu : ∀ n, Nonneg (u n)) (h : RSeq.SeriesSum u) :
    Nonneg h.sum := by
  have hps : ∀ n, Nonneg (RSeq.partialSum u n) := by
    intro n; induction n with
    | zero => exact hu 0
    | succ n ih =>
        show Nonneg (RSeq.partialSum u n + u (n + 1))
        exact nonneg_add ih (hu (n + 1))
  exact nonneg_of_tendstoHalf_nonnegseq h.sum hps h.tends
/-- Technical lemma used in the public import closure. -/
theorem abs_nonneg (a : R) : Nonneg (COF.abs a) := by
  intro hlt
  have h2 : Nonneg (COF.abs a + COF.abs a) := by
    have t := le_add (COFO.le_abs_self a) (COFO.neg_le_abs a)
    rwa [show a + -a = 0 from by ring] at t
  exact h2 (by have t := lt_add hlt hlt; rwa [show (0:R) + 0 = 0 from by ring] at t)
/-- Technical lemma used in the public import closure. -/
theorem le_antisymm {a b : R} (h1 : Le a b) (h2 : Le b a) : a = b := by
  apply COFO.eq_of_small
  intro k hk
  -- hk : lt (halfPow k) (abs (a-b)) → 0 < |a-b| → a-b#0 → b<a ∨ a<b
  have hpos : COF.lt 0 (COF.abs (a - b)) := COFO.lt_trans (halfPow_pos k) hk
  rcases COFO.lt_or_lt_of_abs_pos hpos with h | h
  · -- Technical note.
    apply h1
    have t := COF.lt_add_left b h
    rwa [show b + 0 = b from by ring, show b + (a - b) = a from by ring] at t
  · -- Technical note.
    exact h2 (lt_of_sub_neg h)
end OrderO

/-! Technical auxiliary material for the public import closure. -/
section Cauchy
variable {R : Type*} [COF R]
/-- Technical lemma used in the public import closure. -/
structure IsCauchy (v : Nat → R) where
  cmod : Nat → Nat
  ccond : ∀ k m n : Nat, cmod k ≤ m → cmod k ≤ n → COF.lt (COF.abs (v m - v n)) (COF.halfPow k)
/-- Technical lemma used in the public import closure. -/
structure HasLim (v : Nat → R) where
  val : R
  tends : RSeq.TendstoHalf v val
end Cauchy

namespace RSeq_core
variable {R : Type*} [COF_core R]
def partialSum (u : Nat → R) : Nat → R
  | 0 => u 0
  | Nat.succ n => partialSum u n + u (Nat.succ n)
structure TendstoHalf (u : Nat → R) (l : R) where
  mod : Nat → Nat
  close : ∀ k n : Nat, mod k ≤ n → COF_core.Close k (u n) l
structure SeriesSum (u : Nat → R) where
  sum : R
  tends : TendstoHalf (partialSum u) sum
end RSeq_core

section CauchyCore
variable {R : Type*} [COF_core R]
/-- Core modulus-carrying Cauchy sequence. -/
structure IsCauchy_core (v : Nat → R) where
  cmod : Nat → Nat
  ccond : ∀ k m n : Nat, cmod k ≤ m → cmod k ≤ n →
    COF_core.lt (COF_core.abs (v m - v n)) (COF_core.halfPow k)
/-- Core limit data. -/
structure HasLim_core (v : Nat → R) where
  val : R
  tends : RSeq_core.TendstoHalf v val
end CauchyCore

/-- Reduced completeness interface over the reduced order/absolute-value core. -/
class COFOC_core (R : Type*) extends COFO_core R where
  complete : ∀ {v : Nat → R}, IsCauchy_core v → HasLim_core v

/-- Technical lemma used in the public import closure. -/
class COFOC (R : Type*) extends COFO R where
  complete : ∀ {v : Nat → R}, IsCauchy v → HasLim v

section Complete
variable {R : Type*} [COFOC R]
/-- Technical lemma used in the public import closure. -/
def isCauchy_of_tendsto {v : Nat → R} {l : R} (h : RSeq.TendstoHalf v l) : IsCauchy v where
  cmod := fun k => h.mod (k + 1)
  ccond := by
    intro k m n hm hn
    have hbm : COF.lt (COF.abs (v m - l)) (COF.halfPow (k+1)) := h.close (k+1) m hm
    have hbn : COF.lt (COF.abs (v n - l)) (COF.halfPow (k+1)) := h.close (k+1) n hn
    have htri : Le (COF.abs (v m - v n)) (COF.abs (v m - l) + COF.abs (v n - l)) := by
      have hadd := COFO.abs_add_le (v m - l) (l - v n)
      rw [show (v m - l) + (l - v n) = v m - v n from by ring,
          show COF.abs (l - v n) = COF.abs (v n - l) from by
            rw [show l - v n = -(v n - l) from by ring, COFO.abs_neg]] at hadd
      exact hadd
    have hsum : COF.lt (COF.abs (v m - l) + COF.abs (v n - l)) (COF.halfPow k) := by
      have t := lt_add hbm hbn
      rwa [halfPow_succ_add] at t
    exact lt_of_le_of_lt htri hsum
/-- Technical lemma used in the public import closure. -/
def seriesSum_of_partialCauchy {u : Nat → R} (hc : IsCauchy (RSeq.partialSum u)) :
    RSeq.SeriesSum u :=
  let lim := COFOC.complete hc
  { sum := lim.val, tends := lim.tends }
end Complete

/-! Technical auxiliary material for the public import closure. -/
section Comparison
variable {R : Type*} [COFOC R]
/-- Technical lemma used in the public import closure. -/
theorem partialSum_gap {a b : Nat → R} (ha : ∀ n, Nonneg (a n)) (hab : ∀ n, Le (a n) (b n)) :
    ∀ m d : Nat, Nonneg (RSeq.partialSum a (m + d) - RSeq.partialSum a m) ∧
      Le (RSeq.partialSum a (m + d) - RSeq.partialSum a m)
         (RSeq.partialSum b (m + d) - RSeq.partialSum b m) := by
  intro m d
  induction d with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [show RSeq.partialSum a (m + 0) - RSeq.partialSum a m = 0 from by ring]; exact nonneg_zero
      · rw [show RSeq.partialSum a (m + 0) - RSeq.partialSum a m = 0 from by ring,
            show RSeq.partialSum b (m + 0) - RSeq.partialSum b m = 0 from by ring]
        exact le_refl 0
  | succ d ih =>
      have ka : RSeq.partialSum a (m + (d + 1)) - RSeq.partialSum a m
              = (RSeq.partialSum a (m + d) - RSeq.partialSum a m) + a (m + d + 1) := by
        show RSeq.partialSum a (m + d) + a (m + d + 1) - RSeq.partialSum a m
           = (RSeq.partialSum a (m + d) - RSeq.partialSum a m) + a (m + d + 1)
        ring
      have kb : RSeq.partialSum b (m + (d + 1)) - RSeq.partialSum b m
              = (RSeq.partialSum b (m + d) - RSeq.partialSum b m) + b (m + d + 1) := by
        show RSeq.partialSum b (m + d) + b (m + d + 1) - RSeq.partialSum b m
           = (RSeq.partialSum b (m + d) - RSeq.partialSum b m) + b (m + d + 1)
        ring
      refine ⟨?_, ?_⟩
      · rw [ka]; exact nonneg_add ih.1 (ha (m + d + 1))
      · rw [ka, kb]; exact le_add ih.2 (hab (m + d + 1))
/-- Technical lemma used in the public import closure. -/
theorem partialSum_absdiff_aux {a b : Nat → R} (ha : ∀ n, Nonneg (a n)) (hab : ∀ n, Le (a n) (b n))
    (m d : Nat) :
    Le (COF.abs (RSeq.partialSum a m - RSeq.partialSum a (m + d)))
       (COF.abs (RSeq.partialSum b m - RSeq.partialSum b (m + d))) := by
  obtain ⟨hnna, hleab⟩ := partialSum_gap ha hab m d
  have hbnn : ∀ n, Nonneg (b n) := fun n => le_trans (ha n) (hab n)
  obtain ⟨hnnb, _⟩ := partialSum_gap hbnn (fun n => le_refl (b n)) m d
  rw [show RSeq.partialSum a m - RSeq.partialSum a (m + d)
        = -(RSeq.partialSum a (m + d) - RSeq.partialSum a m) from by ring,
      COFO.abs_neg, COFO.abs_of_nonneg hnna,
      show RSeq.partialSum b m - RSeq.partialSum b (m + d)
        = -(RSeq.partialSum b (m + d) - RSeq.partialSum b m) from by ring,
      COFO.abs_neg, COFO.abs_of_nonneg hnnb]
  exact hleab
/-- Technical lemma used in the public import closure. -/
theorem partialSum_absdiff_le {a b : Nat → R} (ha : ∀ n, Nonneg (a n)) (hab : ∀ n, Le (a n) (b n))
    (m n : Nat) :
    Le (COF.abs (RSeq.partialSum a m - RSeq.partialSum a n))
       (COF.abs (RSeq.partialSum b m - RSeq.partialSum b n)) := by
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨d, rfl⟩ := Nat.le.dest hmn
    exact partialSum_absdiff_aux ha hab m d
  · obtain ⟨d, rfl⟩ := Nat.le.dest hnm
    rw [show RSeq.partialSum a (n + d) - RSeq.partialSum a n
          = -(RSeq.partialSum a n - RSeq.partialSum a (n + d)) from by ring, COFO.abs_neg,
        show RSeq.partialSum b (n + d) - RSeq.partialSum b n
          = -(RSeq.partialSum b n - RSeq.partialSum b (n + d)) from by ring, COFO.abs_neg]
    exact partialSum_absdiff_aux ha hab n d
/-- Technical lemma used in the public import closure. -/
def seriesSum_comparison {a b : Nat → R} (ha : ∀ n, Nonneg (a n)) (hab : ∀ n, Le (a n) (b n))
    (hb : RSeq.SeriesSum b) : RSeq.SeriesSum a :=
  let hbcau := isCauchy_of_tendsto hb.tends
  seriesSum_of_partialCauchy
    { cmod := hbcau.cmod
      ccond := fun k m n hm hn =>
        lt_of_le_of_lt (partialSum_absdiff_le ha hab m n) (hbcau.ccond k m n hm hn) }
/-- Technical lemma used in the public import closure. -/
theorem partialSum_le_sum {u : Nat → R} (hu : ∀ n, Nonneg (u n)) (h : RSeq.SeriesSum u) (N : Nat) :
    Le (RSeq.partialSum u N) h.sum := by
  intro hlt                          -- Technical note.
  have hpos : COF.lt 0 (RSeq.partialSum u N - h.sum) := by
    have h2 := neg_pos_of_neg (sub_neg_of_lt hlt)
    rwa [show -(h.sum - RSeq.partialSum u N) = RSeq.partialSum u N - h.sum from by ring] at h2
  obtain ⟨k, hk⟩ := COFO.archimedean _ hpos   -- hk : halfPow k < partialSum u N - h.sum
  obtain ⟨m, hmN, hmmod⟩ : ∃ m, N ≤ m ∧ h.tends.mod k ≤ m :=
    ⟨N + h.tends.mod k, Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  obtain ⟨d, rfl⟩ := Nat.le.dest hmN          -- m = N + d
  -- Technical note.
  have hmono : Le (RSeq.partialSum u N - h.sum) (RSeq.partialSum u (N+d) - h.sum) :=
    le_sub_right (le_of_nonneg_sub (partialSum_gap hu (fun n => le_refl (u n)) N d).1)
  -- partialSum u (N+d) - h.sum < halfPow k
  have hcl : COF.lt (COF.abs (RSeq.partialSum u (N+d) - h.sum)) (COF.halfPow k) :=
    h.tends.close k (N+d) hmmod
  have hlt2 : COF.lt (RSeq.partialSum u (N+d) - h.sum) (COF.halfPow k) :=
    lt_of_le_of_lt (COFO.le_abs_self _) hcl
  -- Technical note.
  exact COF.lt_irrefl _ (COFO.lt_trans hk (lt_of_le_of_lt hmono hlt2))
end Comparison

/-! Technical auxiliary material for the public import closure. -/
section SeriesAlg
variable {R : Type*} [COFO R]
theorem partialSum_add (u v : Nat → R) :
    ∀ n, RSeq.partialSum (fun n => u n + v n) n = RSeq.partialSum u n + RSeq.partialSum v n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
      show RSeq.partialSum (fun n => u n + v n) n + (u (n+1) + v (n+1))
         = RSeq.partialSum u n + u (n+1) + (RSeq.partialSum v n + v (n+1))
      rw [ih]; ring
/-- Technical lemma used in the public import closure. -/
def seriesSum_add {u v : Nat → R} (hu : RSeq.SeriesSum u) (hv : RSeq.SeriesSum v) :
    RSeq.SeriesSum (fun n => u n + v n) :=
  { sum := hu.sum + hv.sum
    tends :=
      { mod := fun k => hu.tends.mod (k+1) + hv.tends.mod (k+1)
        close := by
          intro k n hn
          show COF.lt (COF.abs (RSeq.partialSum (fun n => u n + v n) n - (hu.sum + hv.sum)))
                 (COF.halfPow k)
          rw [partialSum_add u v n]
          have hnu : hu.tends.mod (k+1) ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
          have hnv : hv.tends.mod (k+1) ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
          have bu : COF.lt (COF.abs (RSeq.partialSum u n - hu.sum)) (COF.halfPow (k+1)) :=
            hu.tends.close (k+1) n hnu
          have bv : COF.lt (COF.abs (RSeq.partialSum v n - hv.sum)) (COF.halfPow (k+1)) :=
            hv.tends.close (k+1) n hnv
          have htri : Le (COF.abs (RSeq.partialSum u n + RSeq.partialSum v n - (hu.sum + hv.sum)))
                       (COF.abs (RSeq.partialSum u n - hu.sum)
                          + COF.abs (RSeq.partialSum v n - hv.sum)) := by
            have hadd := COFO.abs_add_le (RSeq.partialSum u n - hu.sum) (RSeq.partialSum v n - hv.sum)
            rwa [show (RSeq.partialSum u n - hu.sum) + (RSeq.partialSum v n - hv.sum)
                  = RSeq.partialSum u n + RSeq.partialSum v n - (hu.sum + hv.sum) from by ring] at hadd
          have hsum : COF.lt (COF.abs (RSeq.partialSum u n - hu.sum)
                              + COF.abs (RSeq.partialSum v n - hv.sum)) (COF.halfPow k) := by
            have t := lt_add bu bv; rwa [halfPow_succ_add] at t
          exact lt_of_le_of_lt htri hsum } }
/-- a≤b ⟹ c-b ≤ c-a。 -/
theorem le_sub_left {a b c : R} (h : Le a b) : Le (c - b) (c - a) := by
  intro hlt
  apply h
  have t1 := COF.lt_add_left (-c) hlt
  rw [show -c + (c - a) = -a from by ring, show -c + (c - b) = -b from by ring] at t1
  have t2 := COF.lt_add_left (a + b) t1
  rwa [show (a + b) + -a = b from by ring, show (a + b) + -b = a from by ring] at t2
/-- Technical lemma used in the public import closure. -/
theorem le_of_tendsto_le {u : Nat → R} (h : RSeq.SeriesSum u) (c : R)
    (hub : ∀ n, Le (RSeq.partialSum u n) c) : Le h.sum c := by
  intro hlt
  have hpos : COF.lt 0 (h.sum - c) := by
    have t := neg_pos_of_neg (sub_neg_of_lt hlt)
    rwa [show -(c - h.sum) = h.sum - c from by ring] at t
  obtain ⟨k, hk⟩ := COFO.archimedean _ hpos
  have hcl : COF.lt (COF.abs (RSeq.partialSum u (h.tends.mod k) - h.sum)) (COF.halfPow k) :=
    h.tends.close k (h.tends.mod k) (Nat.le_refl _)
  have h1 : COF.lt (h.sum - RSeq.partialSum u (h.tends.mod k)) (COF.halfPow k) := by
    refine lt_of_le_of_lt (COFO.le_abs_self (h.sum - RSeq.partialSum u (h.tends.mod k))) ?_
    rwa [show COF.abs (h.sum - RSeq.partialSum u (h.tends.mod k))
          = COF.abs (RSeq.partialSum u (h.tends.mod k) - h.sum) from by
            rw [show h.sum - RSeq.partialSum u (h.tends.mod k)
                  = -(RSeq.partialSum u (h.tends.mod k) - h.sum) from by ring, COFO.abs_neg]]
  have h2 : Le (h.sum - c) (h.sum - RSeq.partialSum u (h.tends.mod k)) :=
    le_sub_left (hub (h.tends.mod k))
  exact COF.lt_irrefl _ (COFO.lt_trans hk (lt_of_le_of_lt h2 h1))
theorem partialSum_sub (u v : Nat → R) :
    ∀ n, RSeq.partialSum (fun n => u n - v n) n = RSeq.partialSum u n - RSeq.partialSum v n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
      show RSeq.partialSum (fun n => u n - v n) n + (u (n+1) - v (n+1))
         = RSeq.partialSum u n + u (n+1) - (RSeq.partialSum v n + v (n+1))
      rw [ih]; ring
/-- Technical lemma used in the public import closure. -/
def seriesSum_sub {u v : Nat → R} (hu : RSeq.SeriesSum u) (hv : RSeq.SeriesSum v) :
    RSeq.SeriesSum (fun n => u n - v n) :=
  { sum := hu.sum - hv.sum
    tends :=
      { mod := fun k => hu.tends.mod (k+1) + hv.tends.mod (k+1)
        close := by
          intro k n hn
          show COF.lt (COF.abs (RSeq.partialSum (fun n => u n - v n) n - (hu.sum - hv.sum)))
                 (COF.halfPow k)
          rw [partialSum_sub u v n]
          have hnu : hu.tends.mod (k+1) ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
          have hnv : hv.tends.mod (k+1) ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
          have bu : COF.lt (COF.abs (RSeq.partialSum u n - hu.sum)) (COF.halfPow (k+1)) :=
            hu.tends.close (k+1) n hnu
          have bv : COF.lt (COF.abs (RSeq.partialSum v n - hv.sum)) (COF.halfPow (k+1)) :=
            hv.tends.close (k+1) n hnv
          have htri : Le (COF.abs (RSeq.partialSum u n - RSeq.partialSum v n - (hu.sum - hv.sum)))
                       (COF.abs (RSeq.partialSum u n - hu.sum)
                          + COF.abs (RSeq.partialSum v n - hv.sum)) := by
            have hadd := COFO.abs_add_le (RSeq.partialSum u n - hu.sum)
                            (-(RSeq.partialSum v n - hv.sum))
            rw [COFO.abs_neg] at hadd
            rwa [show (RSeq.partialSum u n - hu.sum) + -(RSeq.partialSum v n - hv.sum)
                  = RSeq.partialSum u n - RSeq.partialSum v n - (hu.sum - hv.sum) from by ring] at hadd
          have hsum : COF.lt (COF.abs (RSeq.partialSum u n - hu.sum)
                              + COF.abs (RSeq.partialSum v n - hv.sum)) (COF.halfPow k) := by
            have t := lt_add bu bv; rwa [halfPow_succ_add] at t
          exact lt_of_le_of_lt htri hsum } }
/-- Technical lemma used in the public import closure. -/
theorem seriesSum_sum_congr {u v : Nat → R} (h : ∀ n, u n = v n)
    (hu : RSeq.SeriesSum u) (hv : RSeq.SeriesSum v) : hu.sum = hv.sum := by
  have hf : u = v := funext h
  subst hf
  exact seriesSum_unique hu hv
theorem partialSum_neg (u : Nat → R) :
    ∀ n, RSeq.partialSum (fun n => - u n) n = - RSeq.partialSum u n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
      show RSeq.partialSum (fun n => - u n) n + (- u (n+1)) = -(RSeq.partialSum u n + u (n+1))
      rw [ih]; ring
/-- Technical lemma used in the public import closure. -/
def seriesSum_neg {u : Nat → R} (hu : RSeq.SeriesSum u) :
    RSeq.SeriesSum (fun n => - u n) :=
  { sum := - hu.sum
    tends :=
      { mod := hu.tends.mod
        close := by
          intro k n hn
          show COF.lt (COF.abs (RSeq.partialSum (fun n => - u n) n - (- hu.sum))) (COF.halfPow k)
          rw [partialSum_neg u n,
              show - RSeq.partialSum u n - (- hu.sum) = -(RSeq.partialSum u n - hu.sum) from by ring,
              COFO.abs_neg]
          exact hu.tends.close k n hn } }
end SeriesAlg

/-! Technical auxiliary material for the public import closure. -/
section SeriesSmul
variable {R : Type*} [COFO R]

/-- a<b ⟹ a≤b。 -/
theorem le_of_lt {a b : R} (h : COF.lt a b) : Le a b :=
  fun hba => COF.lt_irrefl a (COFO.lt_trans h hba)

/-- Technical lemma used in the public import closure. -/
theorem abs_abs_sub_abs_le (a b : R) :
    Le (COF.abs (COF.abs a - COF.abs b)) (COF.abs (a - b)) := by
  have key : ∀ u v : R, Le (COF.abs u - COF.abs v) (COF.abs (u - v)) := by
    intro u v
    have ht : Le (COF.abs u) (COF.abs (u - v) + COF.abs v) := by
      have h := COFO.abs_add_le (u - v) v
      rw [show (u - v) + v = u from by ring] at h
      exact h
    have h2 := le_sub_right (c := COF.abs v) ht
    rwa [show COF.abs (u - v) + COF.abs v - COF.abs v = COF.abs (u - v) from by ring] at h2
  have h1 : Le (COF.abs a - COF.abs b) (COF.abs (a - b)) := key a b
  have h2 : Le (-(COF.abs a - COF.abs b)) (COF.abs (a - b)) := by
    have hb := key b a
    rw [show COF.abs (b - a) = COF.abs (a - b) from by
          rw [show b - a = -(a - b) from by ring, COFO.abs_neg]] at hb
    rwa [show COF.abs b - COF.abs a = -(COF.abs a - COF.abs b) from by ring] at hb
  exact COFO.abs_le_of h1 h2

/-- Technical lemma used in the public import closure. -/
theorem partialSum_smul (c : R) (u : Nat → R) :
    ∀ n, RSeq.partialSum (fun k => c * u k) n = c * RSeq.partialSum u n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
      show RSeq.partialSum (fun k => c * u k) n + c * u (n + 1)
         = c * (RSeq.partialSum u n + u (n + 1))
      rw [ih]; ring

/-- (½)^{j+m} = (½)^j · (½)^m。 -/
theorem halfPow_add (j m : Nat) :
    COF.halfPow (R := R) (j + m) = COF.halfPow j * COF.halfPow m := by
  induction m with
  | zero =>
      show COF.halfPow (R := R) j = COF.halfPow j * COF.halfPow 0
      rw [show COF.halfPow (R := R) 0 = (1 : R) from rfl, mul_one]
  | succ m ih =>
      show COF.halfPow (R := R) (j + (m + 1)) = COF.halfPow j * COF.halfPow (m + 1)
      rw [show COF.halfPow (R := R) (j + (m + 1)) = COF.half * COF.halfPow (j + m) from rfl,
          show COF.halfPow (R := R) (m + 1) = COF.half * COF.halfPow m from rfl, ih]
      ring

/-- (½)^{k+1} < (½)^k。 -/
theorem halfPow_lt_succ (k : Nat) : COF.lt (COF.halfPow (R := R) (k + 1)) (COF.halfPow k) := by
  have h := COF.lt_add_left (COF.halfPow (R := R) (k + 1)) (halfPow_pos (R := R) (k + 1))
  rw [add_zero, halfPow_succ_add] at h
  exact h

/-- Technical lemma used in the public import closure. -/
theorem mul_le_mul_left {a b c : R} (hab : Le a b) (hc : Nonneg c) : Le (c * a) (c * b) := by
  have hsub : Nonneg (c * (b - a)) := COFO.mul_nonneg hc (nonneg_sub_of_le hab)
  rw [show c * (b - a) = c * b - c * a from by ring] at hsub
  exact le_of_nonneg_sub hsub

/-- Technical lemma used in the public import closure. -/
def seriesSum_smul (c : R) {u : Nat → R} (h : RSeq.SeriesSum u) :
    RSeq.SeriesSum (fun n => c * u n) where
  sum := c * h.sum
  tends :=
    { mod := fun k => h.tends.mod (k + 1 + (COFO.mul_archimedean c).val)
      close := by
        intro k n hn
        set m := (COFO.mul_archimedean c).val with hm
        have hcm : Le (COF.abs c * COF.halfPow m) 1 := (COFO.mul_archimedean c).property
        show COF.lt (COF.abs (RSeq.partialSum (fun n => c * u n) n - c * h.sum)) (COF.halfPow k)
        rw [partialSum_smul c u n,
            show c * RSeq.partialSum u n - c * h.sum = c * (RSeq.partialSum u n - h.sum) from by ring,
            COFO.abs_mul]
        have hb : COF.lt (COF.abs (RSeq.partialSum u n - h.sum)) (COF.halfPow (k + 1 + m)) :=
          h.tends.close (k + 1 + m) n hn
        have e1 : Le (COF.abs c * COF.abs (RSeq.partialSum u n - h.sum))
                     (COF.abs c * COF.halfPow (k + 1 + m)) :=
          mul_le_mul_left (le_of_lt hb) (abs_nonneg c)
        have e2 : COF.abs c * COF.halfPow (k + 1 + m)
                = COF.halfPow (k + 1) * (COF.abs c * COF.halfPow m) := by
          rw [halfPow_add (k + 1) m]; ring
        have e3 : Le (COF.halfPow (R := R) (k + 1) * (COF.abs c * COF.halfPow m))
                     (COF.halfPow (k + 1)) := by
          have hh := mul_le_mul_left hcm (le_of_lt (halfPow_pos (R := R) (k + 1)))
          rwa [mul_one] at hh
        have e4 : Le (COF.abs c * COF.abs (RSeq.partialSum u n - h.sum)) (COF.halfPow (k + 1)) := by
          refine le_trans e1 ?_
          rw [e2]; exact e3
        exact lt_of_le_of_lt e4 (halfPow_lt_succ k) }

end SeriesSmul

/-! Technical auxiliary material for the public import closure. -/
namespace IntSpaceRC
variable {X R : Type*} [COFO R] (S : IntSpaceRC X R)

/-- Technical lemma used in the public import closure. -/
theorem pos_witness {g : BFunR X R} (hg : g ∈ S.L) (hpos : COF.lt 0 (S.I g)) :
    ∃ x, ∃ hx : x ∈ g.dom, COF.lt 0 (g.toFun x hx) := by
  -- Technical note.
  have hzmem : ∀ _ : Nat, BFunR.smul (0:R) g ∈ S.L := fun _ => S.smul_mem 0 hg
  have hzval : ∀ x (hx : x ∈ g.dom),
      (BFunR.smul (0:R) g).toFun x hx = 0 := by
    intro x hx
    show (0:R) * g.toFun x hx = 0
    ring
  have hznn : ∀ _ : Nat, BFunR.PointwiseNonneg (BFunR.smul (0:R) g) := by
    intro _ x hx
    rw [hzval x hx]
    exact COF.lt_irrefl 0
  have hIz : S.I (BFunR.smul (0:R) g) = 0 := by rw [S.I_smul 0 hg]; ring
  -- hI : SeriesSum (fun n => I (smul 0 g))
  have hps : ∀ n, RSeq.partialSum (fun _ => S.I (BFunR.smul (0:R) g)) n = 0 := by
    intro n; induction n with
    | zero => exact hIz
    | succ n ih =>
        show RSeq.partialSum (fun _ => S.I (BFunR.smul (0:R) g)) n
              + S.I (BFunR.smul (0:R) g) = 0
        rw [ih, hIz]; ring
  let hI : RSeq.SeriesSum (fun n => S.I (BFunR.smul (0:R) g)) :=
    { sum := 0
      tends :=
        { mod := fun _ => 0
          close := by
            intro k n _
            show COF.lt (COF.abs
              (RSeq.partialSum (fun _ => S.I (BFunR.smul (0:R) g)) n - 0)) (COF.halfPow k)
            rw [hps n, show ((0:R) - 0) = 0 from by ring, COFO.abs_zero]
            exact halfPow_pos k } }
  -- Technical note.
  have hlt : COF.lt hI.sum (S.I g) := hpos
  have hpsb := S.continuity hg hzmem hznn hI hlt
  refine ⟨hpsb.x, hpsb.hx_f, ?_⟩
  -- Technical note.
  have hzeroval : ∀ n,
      (BFunR.smul (0:R) g).toFun hpsb.x (hpsb.hx_fs n) = 0 :=
    fun n => hzval hpsb.x (hpsb.hx_fs n)
  have hpv : ∀ n, RSeq.partialSum
      (fun n : Nat => (BFunR.smul (0:R) g).toFun hpsb.x (hpsb.hx_fs n)) n = 0 := by
    intro n; induction n with
    | zero => exact hzeroval 0
    | succ n ih =>
        show RSeq.partialSum
              (fun n : Nat => (BFunR.smul (0:R) g).toFun hpsb.x (hpsb.hx_fs n)) n
              + (BFunR.smul (0:R) g).toFun hpsb.x (hpsb.hx_fs (n + 1)) = 0
        rw [ih, hzeroval (n + 1)]
        ring
  have hnn : Nonneg hpsb.point_sum.sum :=
    nonneg_of_tendstoHalf_zeroseq hpsb.point_sum.sum hpv hpsb.point_sum.tends
  exact lt_of_nonneg_of_lt hnn hpsb.below

/-- Technical lemma used in the public import closure. -/
theorem I_nonneg {g : BFunR X R} (hg : g ∈ S.L) (hgnn : BFunR.PointwiseNonneg g) :
    Nonneg (S.I g) := by
  intro hneg                              -- Technical note.
  -- Technical note.
  have hIneg : COF.lt 0 (S.I (BFunR.smul (-1) g)) := by
    rw [S.toIntSpaceR.I_neg hg]; exact neg_pos_of_neg hneg
  obtain ⟨x, hxdom, hxpos⟩ := pos_witness S (S.smul_mem (-1) hg) hIneg
  -- (smul -1 g).dom = g.dom, (smul -1 g) x = -1 * g x
  have hxdom' : x ∈ g.dom := hxdom
  have : COF.lt 0 (-(g.toFun x hxdom')) := by
    have e : (BFunR.smul (-1:R) g).toFun x hxdom =
        -(g.toFun x hxdom') := by
      show (-1:R) * g.toFun x hxdom' = -(g.toFun x hxdom')
      ring
    rwa [e] at hxpos
  exact hgnn x hxdom' (neg_of_neg_pos this)

/-- Technical lemma used in the public import closure. -/
theorem I_mono {f g : BFunR X R} (hf : f ∈ S.L) (hg : g ∈ S.L)
    (hfg : BFunR.PointwiseLE f g) : Le (S.I f) (S.I g) := by
  -- Technical note.
  have hsub : BFunR.add g (BFunR.smul (-1) f) ∈ S.L := S.add_mem hg (S.smul_mem (-1) hf)
  have hsubnn : BFunR.PointwiseNonneg (BFunR.add g (BFunR.smul (-1) f)) := by
    intro x hx
    -- Technical note.
    have hxg : x ∈ g.dom := hx.1
    have hxf : x ∈ f.dom := hx.2
    have e : (BFunR.add g (BFunR.smul (-1) f)).toFun x hx =
        g.toFun x hxg - f.toFun x hxf := by
      show g.toFun x hxg + (-1:R) * f.toFun x hxf =
        g.toFun x hxg - f.toFun x hxf
      ring
    rw [e]
    -- Technical note.
    intro hlt
    exact hfg.le_val x hxf (lt_of_sub_neg hlt)
  have hIsub : Nonneg (S.I (BFunR.add g (BFunR.smul (-1) f))) := I_nonneg S hsub hsubnn
  -- I(g - f) = I g - I f
  rw [S.toIntSpaceR.I_sub hg hf] at hIsub
  -- Technical note.
  intro hlt
  exact hIsub (sub_neg_of_lt hlt)

/-- Technical lemma used in the public import closure. -/
theorem I_abs_ge {f : BFunR X R} (hf : f ∈ S.L) :
    Le (COF.abs (S.I f)) (S.I (BFunR.absf f)) := by
  -- Technical note.
  have habs : BFunR.absf f ∈ S.L := S.abs_mem hf
  -- f ≤ |f|
  have hle1 : BFunR.PointwiseLE f (BFunR.absf f) :=
    { dom_eq := rfl
      le_val := by intro x hx; exact COFO.le_abs_self (f.toFun x hx) }
  -- -f ≤ |f|
  have hle2 : BFunR.PointwiseLE (BFunR.smul (-1) f) (BFunR.absf f) :=
    { dom_eq := rfl
      le_val := by
        intro x hx
        show ¬ COF.lt (COF.abs (f.toFun x hx))
          ((BFunR.smul (-1:R) f).toFun x hx)
        rw [show (BFunR.smul (-1:R) f).toFun x hx = -(f.toFun x hx) from by
              show (-1:R) * f.toFun x hx = -(f.toFun x hx); ring]
        exact COFO.neg_le_abs (f.toFun x hx) }
  have hI1 : Le (S.I f) (S.I (BFunR.absf f)) := I_mono S hf habs hle1
  have hI2 : Le (S.I (BFunR.smul (-1) f)) (S.I (BFunR.absf f)) :=
    I_mono S (S.smul_mem (-1) hf) habs hle2
  rw [S.toIntSpaceR.I_neg hf] at hI2     -- hI2 : Le (-(I f)) (I|f|)
  -- |I f| ≤ I|f|
  exact COFO.abs_le_of hI1 hI2

end IntSpaceRC

/-! Technical auxiliary material for the public import closure. -/
section PosNeg
variable {X R : Type*} [COFO R]
theorem posPart_pwnn (f : BFunR X R) : BFunR.PointwiseNonneg (BFunR.posPart f) :=
  fun x hx => COFO.max_zero_nonneg (f.toFun x hx)
theorem posPart_le_abs (f : BFunR X R) : BFunR.PointwiseLE (BFunR.posPart f) (BFunR.absf f) where
  dom_eq := rfl
  le_val := fun x hx => COFO.max_le_abs (f.toFun x hx)
theorem negPart_pwnn (f : BFunR X R) : BFunR.PointwiseNonneg (BFunR.negPart f) :=
  fun x hx => COFO.neg_min_zero_nonneg (f.toFun x hx)
theorem negPart_le_abs (f : BFunR X R) : BFunR.PointwiseLE (BFunR.negPart f) (BFunR.absf f) where
  dom_eq := rfl
  le_val := fun x hx => COFO.neg_min_le_abs (f.toFun x hx)
end PosNeg

section CapstonePrep
variable {X R : Type*} [COFOC R] (S : IntSpaceRC X R)
/-- Technical lemma used in the public import closure. -/
def I_posPart_seriesConv {f : Nat → BFunR X R} (hmem : ∀ n, f n ∈ S.L)
    (habs : RSeq.SeriesSum (fun n => S.I (BFunR.absf (f n)))) :
    RSeq.SeriesSum (fun n => S.I (BFunR.posPart (f n))) :=
  seriesSum_comparison
    (fun n => S.I_nonneg (S.toIntSpaceR.posPart_mem (hmem n)) (posPart_pwnn (f n)))
    (fun n => S.I_mono (S.toIntSpaceR.posPart_mem (hmem n)) (S.abs_mem (hmem n))
                (posPart_le_abs (f n)))
    habs
/-- Technical lemma used in the public import closure. -/
def I_negPart_seriesConv {f : Nat → BFunR X R} (hmem : ∀ n, f n ∈ S.L)
    (habs : RSeq.SeriesSum (fun n => S.I (BFunR.absf (f n)))) :
    RSeq.SeriesSum (fun n => S.I (BFunR.negPart (f n))) :=
  seriesSum_comparison
    (fun n => S.I_nonneg (S.toIntSpaceR.negPart_mem (hmem n)) (negPart_pwnn (f n)))
    (fun n => S.I_mono (S.toIntSpaceR.negPart_mem (hmem n)) (S.abs_mem (hmem n))
                (negPart_le_abs (f n)))
    habs
end CapstonePrep

/-! Technical auxiliary material for the public import closure. -/
section Capstone
variable {X R : Type*} [COFOC R] (S : IntSpaceRC X R)
theorem lemma_1_7 {f : Nat → BFunR X R} (hmem : ∀ n, f n ∈ S.L)
    (habs : RSeq.SeriesSum (fun n => S.I (BFunR.absf (f n))))
    (hpos : ∀ x : X, ∀ (hx : ∀ n, x ∈ (f n).dom),
              RSeq.SeriesSum (fun n => COF.abs ((f n).toFun x (hx n))) →
              ∀ (hfx : RSeq.SeriesSum (fun n => (f n).toFun x (hx n))),
                Nonneg hfx.sum)
    (hsum : RSeq.SeriesSum (fun n => S.I (f n))) :
    Nonneg hsum.sum := by
  let cP := I_posPart_seriesConv S hmem habs
  let cM := I_negPart_seriesConv S hmem habs
  have habs_split : habs.sum = cP.sum + cM.sum :=
    seriesSum_sum_congr (fun n => S.toIntSpaceR.I_absf_eq (hmem n)) habs (seriesSum_add cP cM)
  -- Technical note.
  have per_N : ∀ N : Nat,
      Le (RSeq.partialSum (fun n => S.I (BFunR.negPart (f n))) N
          + RSeq.partialSum (fun n => S.I (BFunR.negPart (f n))) N) habs.sum := by
    intro N
    have hgmem : ∀ n, BFunR.negPart (f n) ∈ S.L := fun n => S.toIntSpaceR.negPart_mem (hmem n)
    have hseq_mem : BFunR.seqSum (fun n => BFunR.negPart (f n)) N ∈ S.L :=
      S.toIntSpaceR.seqSum_mem hgmem N
    have hIG : S.I (BFunR.add (BFunR.seqSum (fun n => BFunR.negPart (f n)) N)
                              (BFunR.seqSum (fun n => BFunR.negPart (f n)) N))
             = RSeq.partialSum (fun n => S.I (BFunR.negPart (f n))) N
               + RSeq.partialSum (fun n => S.I (BFunR.negPart (f n))) N := by
      rw [S.I_add hseq_mem hseq_mem, S.toIntSpaceR.I_seqSum hgmem N]
    rw [← hIG]
    intro hlt
    have hpsb := S.continuity (S.add_mem hseq_mem hseq_mem)
      (fun n => S.abs_mem (hmem n))
      (fun n x hx => abs_nonneg ((f n).toFun x hx))
      habs hlt
    obtain ⟨x, hxG, hxfs0, point_sum0, below⟩ := hpsb
    let hxfs : ∀ n, x ∈ (f n).dom := fun n => hxfs0 n
    let point_sum : RSeq.SeriesSum
        (fun n => COF.abs ((f n).toFun x (hxfs n))) := by
      simpa [BFunR.absf] using point_sum0
    have cPx : RSeq.SeriesSum (fun n => COF.max ((f n).toFun x (hxfs n)) 0) :=
      seriesSum_comparison (fun n => COFO.max_zero_nonneg _) (fun n => COFO.max_le_abs _) point_sum
    have cMx : RSeq.SeriesSum (fun n => - COF.min ((f n).toFun x (hxfs n)) 0) :=
      seriesSum_comparison (fun n => COFO.neg_min_zero_nonneg _) (fun n => COFO.neg_min_le_abs _)
        point_sum
    have hfx : RSeq.SeriesSum (fun n => (f n).toFun x (hxfs n)) := by
      have hsub := seriesSum_sub cPx cMx
      have heq : (fun n => COF.max ((f n).toFun x (hxfs n)) 0 -
          (- COF.min ((f n).toFun x (hxfs n)) 0)) =
          (fun n => (f n).toFun x (hxfs n)) := by
        funext n; rw [sub_neg_eq_add, COF.max_add_min_eq_self]
      exact heq ▸ hsub
    have hnn : Nonneg hfx.sum := hpos x hxfs point_sum hfx
    have hfx_split : hfx.sum = cPx.sum - cMx.sum :=
      seriesSum_sum_congr (fun n => by rw [sub_neg_eq_add, COF.max_add_min_eq_self]) hfx
        (seriesSum_sub cPx cMx)
    have hMP : Le cMx.sum cPx.sum := le_of_nonneg_sub (hfx_split ▸ hnn)
    have hps_split : point_sum.sum = cPx.sum + cMx.sum :=
      seriesSum_sum_congr
        (fun n => (COF.max_add_negmin_eq_abs ((f n).toFun x (hxfs n))).symm)
        point_sum
        (seriesSum_add cPx cMx)
    have hpartial_le : Le (RSeq.partialSum
        (fun n => (BFunR.negPart (f n)).toFun x (hxfs n)) N) cMx.sum :=
      partialSum_le_sum (fun n => COFO.neg_min_zero_nonneg _) cMx N
    have hGx : (BFunR.add (BFunR.seqSum (fun n => BFunR.negPart (f n)) N)
                          (BFunR.seqSum (fun n => BFunR.negPart (f n)) N)).toFun x hxG
             = RSeq.partialSum
                 (fun n => (BFunR.negPart (f n)).toFun x (hxfs n)) N
               + RSeq.partialSum
                 (fun n => (BFunR.negPart (f n)).toFun x (hxfs n)) N := by
      show (BFunR.seqSum (fun n => BFunR.negPart (f n)) N).toFun x
          (BFunR.seqSum_mem (fun n => BFunR.negPart (f n)) x hxfs N) +
        (BFunR.seqSum (fun n => BFunR.negPart (f n)) N).toFun x
          (BFunR.seqSum_mem (fun n => BFunR.negPart (f n)) x hxfs N) = _
      rw [BFunR.seqSum_toFun (fun n => BFunR.negPart (f n)) x hxfs N]
    have hle : Le ((BFunR.add (BFunR.seqSum (fun n => BFunR.negPart (f n)) N)
                              (BFunR.seqSum (fun n => BFunR.negPart (f n)) N)).toFun x hxG)
                 point_sum.sum := by
      rw [hGx, hps_split]
      exact le_add (le_trans hpartial_le hMP) hpartial_le
    exact hle below
  -- 2cM.sum ≤ habs.sum
  have h2cm : Le (cM.sum + cM.sum) habs.sum := by
    refine le_of_tendsto_le (seriesSum_add cM cM) habs.sum (fun N => ?_)
    rw [partialSum_add]
    exact per_N N
  -- cM.sum ≤ cP.sum
  have hkey : Le cM.sum cP.sum := by
    rw [habs_split] at h2cm
    exact le_of_add_le_add_right h2cm
  -- ΣI(fₙ) = cP.sum - cM.sum ≥ 0
  have hsum_split : hsum.sum = cP.sum - cM.sum :=
    seriesSum_sum_congr (fun n => S.toIntSpaceR.I_self_eq (hmem n)) hsum (seriesSum_sub cP cM)
  rw [hsum_split]
  exact nonneg_sub_of_le hkey

/-- Technical lemma used in the public import closure. -/
theorem lemma_1_7_zero {f : Nat → BFunR X R} (hmem : ∀ n, f n ∈ S.L)
    (habs : RSeq.SeriesSum (fun n => S.I (BFunR.absf (f n))))
    (hzero : ∀ x : X, ∀ (hx : ∀ n, x ∈ (f n).dom),
              RSeq.SeriesSum (fun n => COF.abs ((f n).toFun x (hx n))) →
              ∀ (hfx : RSeq.SeriesSum (fun n => (f n).toFun x (hx n))),
                hfx.sum = 0)
    (hsum : RSeq.SeriesSum (fun n => S.I (f n))) :
    hsum.sum = 0 := by
  -- Technical note.
  have hge : Nonneg hsum.sum :=
    lemma_1_7 S hmem habs
      (fun x hx hax hfx => by rw [hzero x hx hax hfx]; exact nonneg_zero) hsum
  -- Technical note.
  -- habs'(|-fₙ|=|fₙ|)
  have hI_eq : ∀ n, S.I (BFunR.absf (BFunR.smul (-1) (f n))) = S.I (BFunR.absf (f n)) := by
    intro n
    refine S.toIntSpaceR.I_resp (S.abs_mem (S.smul_mem (-1) (hmem n))) ⟨rfl, ?_⟩
    intro x hx
    show COF.abs ((-1) * (f n).toFun x hx) = COF.abs ((f n).toFun x hx)
    rw [show (-1) * (f n).toFun x hx = - (f n).toFun x hx from by ring,
      COFO.abs_neg]
  have habs' : RSeq.SeriesSum (fun n => S.I (BFunR.absf (BFunR.smul (-1) (f n)))) := by
    rw [show (fun n => S.I (BFunR.absf (BFunR.smul (-1) (f n))))
          = (fun n => S.I (BFunR.absf (f n))) from funext hI_eq]
    exact habs
  -- hsum'(Σ I(-fₙ) = -Σ I(fₙ))
  have hsum' : RSeq.SeriesSum (fun n => S.I (BFunR.smul (-1) (f n))) := by
    rw [show (fun n => S.I (BFunR.smul (-1) (f n))) = (fun n => - S.I (f n)) from
          funext (fun n => S.toIntSpaceR.I_neg (hmem n))]
    exact seriesSum_neg hsum
  -- hpos'(Σ(-fₙ)(x) = -Σfₙ(x) = 0 ≥ 0)
  have hge' : Nonneg hsum'.sum := by
    refine lemma_1_7 S (fun n => S.smul_mem (-1) (hmem n)) habs'
      (fun x hx hax' hfx' => ?_) hsum'
    have hax : RSeq.SeriesSum
        (fun n => COF.abs ((f n).toFun x (hx n))) := by
      rw [show (fun n => COF.abs
            ((BFunR.smul (-1) (f n)).toFun x (hx n))) =
            (fun n => COF.abs ((f n).toFun x (hx n))) from by
            funext n
            show COF.abs ((-1) * (f n).toFun x (hx n)) =
              COF.abs ((f n).toFun x (hx n))
            rw [show (-1) * (f n).toFun x (hx n) =
              - (f n).toFun x (hx n) from by ring, COFO.abs_neg]] at hax'
      exact hax'
    have hfₓ : RSeq.SeriesSum (fun n => (f n).toFun x (hx n)) := by
      rw [show (fun n => (f n).toFun x (hx n)) =
          (fun n => - (BFunR.smul (-1) (f n)).toFun x (hx n)) from by
            funext n
            show (f n).toFun x (hx n) = - ((-1) * (f n).toFun x (hx n))
            ring]
      exact seriesSum_neg hfx'
    have hfx'_eq : hfx'.sum = (seriesSum_neg hfₓ).sum :=
      seriesSum_sum_congr (fun n => by
        show (-1) * (f n).toFun x (hx n) = - (f n).toFun x (hx n)
        ring)
        hfx' (seriesSum_neg hfₓ)
    rw [hfx'_eq]
    show Nonneg (- hfₓ.sum)
    rw [hzero x hx hax hfₓ, neg_zero]
    exact nonneg_zero
  -- hsum'.sum = - hsum.sum ⟹ hsum.sum ≤ 0
  have hsum'_eq : hsum'.sum = - hsum.sum :=
    seriesSum_sum_congr (fun n => S.toIntSpaceR.I_neg (hmem n)) hsum' (seriesSum_neg hsum)
  have hle : Le hsum.sum 0 := by
    intro hlt
    apply (hsum'_eq ▸ hge' : Nonneg (- hsum.sum))
    have t := COF.lt_add_left (- hsum.sum) hlt
    rwa [show - hsum.sum + 0 = - hsum.sum from by ring,
         show - hsum.sum + hsum.sum = 0 from by ring] at t
  -- Technical note.
  exact le_antisymm hle hge
end Capstone


/-- Technical lemma used in the public import closure. -/
def seqInterleave {α : Type*} (u v : Nat → α) : Nat → α :=
  fun n => if n % 2 = 0 then u (n / 2) else v (n / 2)

theorem seqInterleave_even {α : Type*} (u v : Nat → α) (k : Nat) :
    seqInterleave u v (2 * k) = u k := by
  show (if (2 * k) % 2 = 0 then u ((2 * k) / 2) else v ((2 * k) / 2)) = u k
  rw [if_pos (show (2 * k) % 2 = 0 by omega), show (2 * k) / 2 = k by omega]

theorem seqInterleave_odd {α : Type*} (u v : Nat → α) (k : Nat) :
    seqInterleave u v (2 * k + 1) = v k := by
  show (if (2 * k + 1) % 2 = 0 then u ((2 * k + 1) / 2) else v ((2 * k + 1) / 2)) = v k
  rw [if_neg (show ¬ (2 * k + 1) % 2 = 0 by omega), show (2 * k + 1) / 2 = k by omega]

/-- Technical lemma used in the public import closure. -/
theorem seqInterleave_map {α β : Type*} (φ : α → β) (a b : Nat → α) (n : Nat) :
    φ (seqInterleave a b n) = seqInterleave (fun k => φ (a k)) (fun k => φ (b k)) n := by
  show φ (if n % 2 = 0 then a (n / 2) else b (n / 2))
     = if n % 2 = 0 then φ (a (n / 2)) else φ (b (n / 2))
  rw [apply_ite φ]

/-- Technical lemma used in the public import closure. -/
theorem natEvenOrOdd' (n : Nat) : (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · exact Or.inl ⟨n / 2, by omega⟩
  · exact Or.inr ⟨n / 2, by omega⟩

section
variable {R : Type*} [COF R]

/-- Technical lemma used in the public import closure. -/
theorem partialSum_interleave_odd (u v : Nat → R) (N : Nat) :
    RSeq.partialSum (seqInterleave u v) (2 * N + 1)
      = RSeq.partialSum u N + RSeq.partialSum v N := by
  induction N with
  | zero =>
      have h0 : seqInterleave u v 0 = u 0 := seqInterleave_even u v 0
      have h1 : seqInterleave u v 1 = v 0 := seqInterleave_odd u v 0
      show RSeq.partialSum (seqInterleave u v) 0 + seqInterleave u v 1 = u 0 + v 0
      rw [show RSeq.partialSum (seqInterleave u v) 0 = seqInterleave u v 0 from rfl, h0, h1]
  | succ N ih =>
      have e2 : seqInterleave u v (2 * N + 2) = u (N + 1) := seqInterleave_even u v (N + 1)
      have e3 : seqInterleave u v (2 * N + 3) = v (N + 1) := seqInterleave_odd u v (N + 1)
      show (RSeq.partialSum (seqInterleave u v) (2 * N + 1) + seqInterleave u v (2 * N + 2))
            + seqInterleave u v (2 * N + 3)
         = RSeq.partialSum u (N + 1) + RSeq.partialSum v (N + 1)
      rw [ih, e2, e3]
      show (RSeq.partialSum u N + RSeq.partialSum v N + u (N + 1)) + v (N + 1)
         = (RSeq.partialSum u N + u (N + 1)) + (RSeq.partialSum v N + v (N + 1))
      ring

/-- Technical lemma used in the public import closure. -/
theorem partialSum_interleave_even (u v : Nat → R) (N : Nat) :
    RSeq.partialSum (seqInterleave u v) (2 * N + 2)
      = RSeq.partialSum u (N + 1) + RSeq.partialSum v N := by
  have e2 : seqInterleave u v (2 * N + 2) = u (N + 1) := seqInterleave_even u v (N + 1)
  show RSeq.partialSum (seqInterleave u v) (2 * N + 1) + seqInterleave u v (2 * N + 2)
     = RSeq.partialSum u (N + 1) + RSeq.partialSum v N
  rw [partialSum_interleave_odd u v N, e2]
  show (RSeq.partialSum u N + RSeq.partialSum v N) + u (N + 1)
     = (RSeq.partialSum u N + u (N + 1)) + RSeq.partialSum v N
  ring

end

section
variable {R : Type*} [COFO R]

/-- Technical lemma used in the public import closure. -/
theorem close_of_two_close {pa pb su sv : R} (k : Nat)
    (ha : COF.lt (COF.abs (pa - su)) (COF.halfPow (k + 1)))
    (hb : COF.lt (COF.abs (pb - sv)) (COF.halfPow (k + 1))) :
    COF.lt (COF.abs ((pa + pb) - (su + sv))) (COF.halfPow k) := by
  have htri : Le (COF.abs ((pa + pb) - (su + sv))) (COF.abs (pa - su) + COF.abs (pb - sv)) := by
    have hadd := COFO.abs_add_le (pa - su) (pb - sv)
    rwa [show (pa - su) + (pb - sv) = (pa + pb) - (su + sv) from by ring] at hadd
  have hsum : COF.lt (COF.abs (pa - su) + COF.abs (pb - sv)) (COF.halfPow k) := by
    have t := lt_add ha hb; rwa [halfPow_succ_add] at t
  exact lt_of_le_of_lt htri hsum

/-- Technical lemma used in the public import closure. -/
def seriesSum_interleave {u v : Nat → R} (hu : RSeq.SeriesSum u) (hv : RSeq.SeriesSum v) :
    RSeq.SeriesSum (seqInterleave u v) where
  sum := hu.sum + hv.sum
  tends :=
    { mod := fun k => 2 * (hu.tends.mod (k + 1) + hv.tends.mod (k + 1)) + 2
      close := by
        intro k m hm
        have hm2 : 2 * (hu.tends.mod (k + 1) + hv.tends.mod (k + 1)) + 2 ≤ m := hm
        show COF.lt (COF.abs (RSeq.partialSum (seqInterleave u v) m - (hu.sum + hv.sum)))
              (COF.halfPow k)
        obtain ⟨N, hodd, hbu, hbv⟩ | ⟨N, heven, hbu, hbv⟩ :
            (∃ N, m = 2 * N + 1 ∧ hu.tends.mod (k + 1) ≤ N ∧ hv.tends.mod (k + 1) ≤ N) ∨
            (∃ N, m = 2 * N + 2 ∧ hu.tends.mod (k + 1) ≤ N + 1 ∧ hv.tends.mod (k + 1) ≤ N) := by
          rcases natEvenOrOdd' m with ⟨t, ht⟩ | ⟨t, ht⟩
          · exact Or.inr ⟨t - 1, by omega, by omega, by omega⟩
          · exact Or.inl ⟨t, by omega, by omega, by omega⟩
        · subst hodd
          rw [partialSum_interleave_odd u v N]
          exact close_of_two_close k (hu.tends.close (k + 1) N hbu) (hv.tends.close (k + 1) N hbv)
        · subst heven
          rw [partialSum_interleave_even u v N]
          exact close_of_two_close k (hu.tends.close (k + 1) (N + 1) hbu)
                  (hv.tends.close (k + 1) N hbv) }

/-- Technical lemma used in the public import closure. -/
theorem partialSum_interleave_odd_eq_add (u v : Nat → R) (N : Nat) :
    RSeq.partialSum (seqInterleave u v) (2 * N + 1)
      = RSeq.partialSum (fun k => u k + v k) N := by
  rw [partialSum_interleave_odd u v N, partialSum_add u v N]

/-- Technical lemma used in the public import closure. -/
def seriesSum_add_of_interleave {u v : Nat → R} (h : RSeq.SeriesSum (seqInterleave u v)) :
    RSeq.SeriesSum (fun k => u k + v k) where
  sum := h.sum
  tends :=
    { mod := fun k => h.tends.mod k
      close := by
        intro k N hN
        show COF.lt (COF.abs (RSeq.partialSum (fun k => u k + v k) N - h.sum)) (COF.halfPow k)
        rw [← partialSum_interleave_odd_eq_add u v N]
        exact h.tends.close k (2 * N + 1) (by omega) }

end

section
variable {R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
def seriesSum_interleave_left {u v : Nat → R}
    (hu : ∀ n, Nonneg (u n)) (hv : ∀ n, Nonneg (v n))
    (h : RSeq.SeriesSum (seqInterleave u v)) : RSeq.SeriesSum u :=
  seriesSum_comparison hu
    (fun n => le_of_nonneg_sub (show Nonneg ((u n + v n) - u n) from by
      rw [show (u n + v n) - u n = v n from by ring]; exact hv n))
    (seriesSum_add_of_interleave h)

/-- Technical lemma used in the public import closure. -/
def seriesSum_interleave_right {u v : Nat → R}
    (hu : ∀ n, Nonneg (u n)) (hv : ∀ n, Nonneg (v n))
    (h : RSeq.SeriesSum (seqInterleave u v)) : RSeq.SeriesSum v :=
  seriesSum_comparison hv
    (fun n => le_of_nonneg_sub (show Nonneg ((u n + v n) - v n) from by
      rw [show (u n + v n) - v n = u n from by ring]; exact hu n))
    (seriesSum_add_of_interleave h)

/-- Technical lemma used in the public import closure. -/
theorem abs_partialSum_gap_le (u : Nat → R) (n d : Nat) :
    Le (COF.abs (RSeq.partialSum u (n + d) - RSeq.partialSum u n))
       (RSeq.partialSum (fun k => COF.abs (u k)) (n + d)
        - RSeq.partialSum (fun k => COF.abs (u k)) n) := by
  induction d with
  | zero =>
      rw [show RSeq.partialSum u (n + 0) - RSeq.partialSum u n = 0 from by ring,
          show RSeq.partialSum (fun k => COF.abs (u k)) (n + 0)
                - RSeq.partialSum (fun k => COF.abs (u k)) n = 0 from by ring,
          COFO.abs_zero]
      exact le_refl 0
  | succ d ih =>
      have ku : RSeq.partialSum u (n + (d + 1)) - RSeq.partialSum u n
              = (RSeq.partialSum u (n + d) - RSeq.partialSum u n) + u (n + d + 1) := by
        show RSeq.partialSum u (n + d) + u (n + d + 1) - RSeq.partialSum u n
           = (RSeq.partialSum u (n + d) - RSeq.partialSum u n) + u (n + d + 1)
        ring
      have ka : RSeq.partialSum (fun k => COF.abs (u k)) (n + (d + 1))
                - RSeq.partialSum (fun k => COF.abs (u k)) n
              = (RSeq.partialSum (fun k => COF.abs (u k)) (n + d)
                 - RSeq.partialSum (fun k => COF.abs (u k)) n) + COF.abs (u (n + d + 1)) := by
        show RSeq.partialSum (fun k => COF.abs (u k)) (n + d) + COF.abs (u (n + d + 1))
              - RSeq.partialSum (fun k => COF.abs (u k)) n
           = (RSeq.partialSum (fun k => COF.abs (u k)) (n + d)
              - RSeq.partialSum (fun k => COF.abs (u k)) n) + COF.abs (u (n + d + 1))
        ring
      rw [ku, ka]
      exact le_trans (COFO.abs_add_le _ _) (le_add ih (le_refl (COF.abs (u (n + d + 1)))))

/-- Technical lemma used in the public import closure. -/
theorem abs_partialSum_sub_le (u : Nat → R) (m n : Nat) :
    Le (COF.abs (RSeq.partialSum u m - RSeq.partialSum u n))
       (COF.abs (RSeq.partialSum (fun k => COF.abs (u k)) m
                  - RSeq.partialSum (fun k => COF.abs (u k)) n)) := by
  rcases Nat.le_total n m with hnm | hmn
  · obtain ⟨d, rfl⟩ := Nat.le.dest hnm
    have hnn : Nonneg (RSeq.partialSum (fun k => COF.abs (u k)) (n + d)
                        - RSeq.partialSum (fun k => COF.abs (u k)) n) :=
      (partialSum_gap (fun j => abs_nonneg (u j)) (fun j => le_refl _) n d).1
    rw [COFO.abs_of_nonneg hnn]
    exact abs_partialSum_gap_le u n d
  · obtain ⟨d, rfl⟩ := Nat.le.dest hmn
    have hnn : Nonneg (RSeq.partialSum (fun k => COF.abs (u k)) (m + d)
                        - RSeq.partialSum (fun k => COF.abs (u k)) m) :=
      (partialSum_gap (fun j => abs_nonneg (u j)) (fun j => le_refl _) m d).1
    rw [show RSeq.partialSum u m - RSeq.partialSum u (m + d)
          = -(RSeq.partialSum u (m + d) - RSeq.partialSum u m) from by ring, COFO.abs_neg,
        show RSeq.partialSum (fun k => COF.abs (u k)) m
              - RSeq.partialSum (fun k => COF.abs (u k)) (m + d)
          = -(RSeq.partialSum (fun k => COF.abs (u k)) (m + d)
              - RSeq.partialSum (fun k => COF.abs (u k)) m) from by ring, COFO.abs_neg,
        COFO.abs_of_nonneg hnn]
    exact abs_partialSum_gap_le u m d

/-- Technical lemma used in the public import closure. -/
def seriesSum_of_abs {u : Nat → R} (h : RSeq.SeriesSum (fun k => COF.abs (u k))) :
    RSeq.SeriesSum u :=
  seriesSum_of_partialCauchy
    { cmod := (isCauchy_of_tendsto h.tends).cmod
      ccond := fun k m n hm hn =>
        lt_of_le_of_lt (abs_partialSum_sub_le u m n)
          ((isCauchy_of_tendsto h.tends).ccond k m n hm hn) }

end

/-! Technical auxiliary material for the public import closure. -/
section
variable {X R : Type*} [COFOC R] (S : IntSpaceRC X R)

/-- congr: I(|smul(-1)·g|) = I(|g|)。 -/
theorem I_absf_neg_eq {gk : BFunR X R} (hg : gk ∈ S.L) :
    S.I (BFunR.absf (BFunR.smul (-1) gk)) = S.I (BFunR.absf gk) := by
  refine S.toIntSpaceR.I_resp (S.abs_mem (S.smul_mem (-1) hg)) ⟨rfl, ?_⟩
  intro x hx
  show COF.abs ((-1) * gk.toFun x hx) = COF.abs (gk.toFun x hx)
  rw [show (-1) * gk.toFun x hx = - gk.toFun x hx from by ring, COFO.abs_neg]

/-- Technical lemma used in the public import closure. -/
theorem I1_well_defined {f g : Nat → BFunR X R}
    (hfmem : ∀ n, f n ∈ S.L) (hgmem : ∀ n, g n ∈ S.L)
    (hfabs : RSeq.SeriesSum (fun n => S.I (BFunR.absf (f n))))
    (hgabs : RSeq.SeriesSum (fun n => S.I (BFunR.absf (g n))))
    (hagree : ∀ x : X,
        ∀ (hfd : ∀ n, x ∈ (f n).dom) (hgd : ∀ n, x ∈ (g n).dom),
        RSeq.SeriesSum (fun n => COF.abs ((f n).toFun x (hfd n))) →
        RSeq.SeriesSum (fun n => COF.abs ((g n).toFun x (hgd n))) →
        ∀ (hfx : RSeq.SeriesSum (fun n => (f n).toFun x (hfd n)))
          (hgx : RSeq.SeriesSum (fun n => (g n).toFun x (hgd n))), hfx.sum = hgx.sum)
    (hfsum : RSeq.SeriesSum (fun n => S.I (f n)))
    (hgsum : RSeq.SeriesSum (fun n => S.I (g n))) :
    hfsum.sum = hgsum.sum := by
  -- Technical note.
  set negG : Nat → BFunR X R := fun k => BFunR.smul (-1) (g k) with hnegG
  -- (1) hmem: ∀n, (interleave f negG) n ∈ L
  have hmem : ∀ n, seqInterleave f negG n ∈ S.L := by
    intro n
    rcases natEvenOrOdd' n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [seqInterleave_even f negG k]; exact hfmem k
    · rw [seqInterleave_odd f negG k]; exact S.smul_mem (-1) (hgmem k)
  -- Technical note.
  have hnegGsum : RSeq.SeriesSum (fun k => S.I (negG k)) := by
    have heq : (fun k => S.I (negG k)) = (fun k => - S.I (g k)) :=
      funext fun k => S.toIntSpaceR.I_neg (hgmem k)
    rw [heq]; exact seriesSum_neg hgsum
  have hnegGsum_eq : hnegGsum.sum = - hgsum.sum :=
    seriesSum_sum_congr (fun k => S.toIntSpaceR.I_neg (hgmem k))
      hnegGsum (seriesSum_neg hgsum)
  -- Technical note.
  have hnegGabs : RSeq.SeriesSum (fun k => S.I (BFunR.absf (negG k))) := by
    have heq : (fun k => S.I (BFunR.absf (negG k))) = (fun k => S.I (BFunR.absf (g k))) :=
      funext fun k => I_absf_neg_eq S (hgmem k)
    rw [heq]; exact hgabs
  -- Technical note.
  have habs : RSeq.SeriesSum (fun n => S.I (BFunR.absf (seqInterleave f negG n))) := by
    have heq : (fun n => S.I (BFunR.absf (seqInterleave f negG n)))
             = seqInterleave (fun k => S.I (BFunR.absf (f k)))
                 (fun k => S.I (BFunR.absf (negG k))) := by
      funext n; rw [seqInterleave_map BFunR.absf f negG n, seqInterleave_map S.I _ _ n]
    rw [heq]; exact seriesSum_interleave hfabs hnegGabs
  -- Technical note.
  have hsum : RSeq.SeriesSum (fun n => S.I (seqInterleave f negG n)) := by
    have heq : (fun n => S.I (seqInterleave f negG n))
             = seqInterleave (fun k => S.I (f k)) (fun k => S.I (negG k)) := by
      funext n; rw [seqInterleave_map S.I f negG n]
    rw [heq]; exact seriesSum_interleave hfsum hnegGsum
  have hsum_eq : hsum.sum = hfsum.sum + hnegGsum.sum :=
    seriesSum_sum_congr
      (fun n => by rw [seqInterleave_map S.I f negG n] :
        ∀ n, S.I (seqInterleave f negG n)
           = seqInterleave (fun k => S.I (f k)) (fun k => S.I (negG k)) n)
      hsum (seriesSum_interleave hfsum hnegGsum)
  -- Technical note.
  have hzero : ∀ x : X,
      ∀ (hx : ∀ n, x ∈ (seqInterleave f negG n).dom),
      RSeq.SeriesSum
          (fun n => COF.abs ((seqInterleave f negG n).toFun x (hx n))) →
      ∀ (hhx : RSeq.SeriesSum
          (fun n => (seqInterleave f negG n).toFun x (hx n))), hhx.sum = 0 := by
    intro x hx habsx hhx
    let hfxdom : ∀ k, x ∈ (f k).dom := fun k => by
      simpa only [seqInterleave_even] using hx (2 * k)
    let hnegGdom : ∀ k, x ∈ (negG k).dom := fun k => by
      simpa only [seqInterleave_odd] using hx (2 * k + 1)
    let hgdom : ∀ k, x ∈ (g k).dom := fun k => by
      simpa only [negG, BFunR.smul] using hnegGdom k
    -- |interleave·x| = interleave (|f·x|) (|negG·x|)
    have heqabsx :
        (fun n => COF.abs ((seqInterleave f negG n).toFun x (hx n))) =
          seqInterleave (fun k => COF.abs ((f k).toFun x (hfxdom k)))
            (fun k => COF.abs ((negG k).toFun x (hnegGdom k))) := by
      funext n
      rcases natEvenOrOdd' n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · simp only [seqInterleave_even]
      · simp only [seqInterleave_odd]
    rw [heqabsx] at habsx
    -- Technical note.
    have hfabsx : RSeq.SeriesSum
        (fun k => COF.abs ((f k).toFun x (hfxdom k))) :=
      seriesSum_interleave_left (fun k => abs_nonneg _) (fun k => abs_nonneg _) habsx
    have hnegGabsx : RSeq.SeriesSum
        (fun k => COF.abs ((negG k).toFun x (hnegGdom k))) :=
      seriesSum_interleave_right (fun k => abs_nonneg _) (fun k => abs_nonneg _) habsx
    -- |negG·x| = |g·x|
    have hgabsx : RSeq.SeriesSum
        (fun k => COF.abs ((g k).toFun x (hgdom k))) := by
      have heq :
          (fun k => COF.abs ((negG k).toFun x (hnegGdom k))) =
            (fun k => COF.abs ((g k).toFun x (hgdom k))) := by
        funext k
        show COF.abs ((-1) * (g k).toFun x (hgdom k)) =
          COF.abs ((g k).toFun x (hgdom k))
        rw [show (-1) * (g k).toFun x (hgdom k) =
          - (g k).toFun x (hgdom k) from by ring, COFO.abs_neg]
      rw [heq] at hnegGabsx; exact hnegGabsx
    -- Technical note.
    have hfx : RSeq.SeriesSum (fun k => (f k).toFun x (hfxdom k)) :=
      seriesSum_of_abs hfabsx
    have hgx : RSeq.SeriesSum (fun k => (g k).toFun x (hgdom k)) :=
      seriesSum_of_abs hgabsx
    -- ΣnegG·x = -Σg·x
    have hnegGx : RSeq.SeriesSum
        (fun k => (negG k).toFun x (hnegGdom k)) := by
      have heq : (fun k => (negG k).toFun x (hnegGdom k)) =
          (fun k => - (g k).toFun x (hgdom k)) := by
        funext k
        show (-1) * (g k).toFun x (hgdom k) = - (g k).toFun x (hgdom k)
        ring
      rw [heq]; exact seriesSum_neg hgx
    have hnegGx_eq : hnegGx.sum = - hgx.sum :=
      seriesSum_sum_congr (fun k => by
        show (-1) * (g k).toFun x (hgdom k) = - (g k).toFun x (hgdom k)
        ring)
        hnegGx (seriesSum_neg hgx)
    -- hhx.sum = Σf·x + ΣnegG·x = Σf·x - Σg·x
    have hhx_eq : hhx.sum = hfx.sum + hnegGx.sum :=
      seriesSum_sum_congr
        (fun n => by
          rcases natEvenOrOdd' n with ⟨k, rfl⟩ | ⟨k, rfl⟩
          · simp only [seqInterleave_even]
          · simp only [seqInterleave_odd] :
          ∀ n, (seqInterleave f negG n).toFun x (hx n) =
            seqInterleave (fun k => (f k).toFun x (hfxdom k))
              (fun k => (negG k).toFun x (hnegGdom k)) n)
        hhx (seriesSum_interleave hfx hnegGx)
    -- hagree: Σf·x = Σg·x
    have hagx : hfx.sum = hgx.sum :=
      hagree x hfxdom hgdom hfabsx hgabsx hfx hgx
    rw [hhx_eq, hnegGx_eq, hagx]; ring
  -- Technical note.
  have hzero_res : hsum.sum = 0 := lemma_1_7_zero S hmem habs hzero hsum
  rw [hsum_eq, hnegGsum_eq] at hzero_res
  -- hfsum.sum + (-hgsum.sum) = 0 → hfsum.sum = hgsum.sum
  have : hfsum.sum - hgsum.sum = 0 := by rw [sub_eq_add_neg]; exact hzero_res
  exact sub_eq_zero.mp this

end

/-! Technical auxiliary material for the public import closure. -/
section
variable {X R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
structure IntegrableRep (S : IntSpaceRC X R) where
  fn : Nat → BFunR X R
  mem : ∀ n, fn n ∈ S.L
  absConv : RSeq.SeriesSum (fun n => S.I (BFunR.absf (fn n)))

variable {S : IntSpaceRC X R}

/-- Every component of `r` is defined at `x`. -/
def IntegrableRep.MemAt (r : IntegrableRep S) (x : X) : Prop :=
  ∀ n, x ∈ (r.fn n).dom

/-- Pointwise value of a representative at a point in all component domains. -/
def IntegrableRep.valueAt (r : IntegrableRep S) (x : X)
    (hx : r.MemAt x) (n : Nat) : R :=
  (r.fn n).toFun x (hx n)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.seriesSum_I (r : IntegrableRep S) :
    RSeq.SeriesSum (fun n => S.I (r.fn n)) :=
  seriesSum_of_abs
    (seriesSum_comparison (fun n => abs_nonneg _)
      (fun n => S.I_abs_ge (r.mem n)) r.absConv)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.integral (r : IntegrableRep S) : R := r.seriesSum_I.sum

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.integral_congr (r r' : IntegrableRep S)
    (hagree : ∀ x : X,
        ∀ (hrdom : ∀ n, x ∈ (r.fn n).dom)
          (hr'dom : ∀ n, x ∈ (r'.fn n).dom),
        RSeq.SeriesSum (fun n => COF.abs ((r.fn n).toFun x (hrdom n))) →
        RSeq.SeriesSum (fun n => COF.abs ((r'.fn n).toFun x (hr'dom n))) →
        ∀ (hx : RSeq.SeriesSum (fun n => (r.fn n).toFun x (hrdom n)))
          (hx' : RSeq.SeriesSum (fun n => (r'.fn n).toFun x (hr'dom n))),
          hx.sum = hx'.sum) :
    r.integral = r'.integral :=
  I1_well_defined S r.mem r'.mem r.absConv r'.absConv hagree r.seriesSum_I r'.seriesSum_I

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem partialSum_single (c : R) :
    ∀ n, RSeq.partialSum (fun m => if m = 0 then c else (0:R)) n = c := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
      show RSeq.partialSum (fun m => if m = 0 then c else (0:R)) n
            + (if n + 1 = 0 then c else (0:R)) = c
      rw [ih, if_neg (Nat.succ_ne_zero n), add_zero]

/-- Technical lemma used in the public import closure. -/
def seriesSum_single (c : R) : RSeq.SeriesSum (fun m => if m = 0 then c else (0:R)) where
  sum := c
  tends :=
    { mod := fun _ => 0
      close := by
        intro k n _
        show COF.lt (COF.abs (RSeq.partialSum (fun m => if m = 0 then c else (0:R)) n - c))
              (COF.halfPow k)
        rw [partialSum_single c n, show c - c = (0:R) from by ring, COFO.abs_zero]
        exact halfPow_pos k }

/-- Technical lemma used in the public import closure. -/
theorem I_abs_smul_zero {g : BFunR X R} (hg : g ∈ S.L) :
    S.I (BFunR.absf (BFunR.smul (0:R) g)) = 0 := by
  have hbe : BFunR.BEquiv (BFunR.absf (BFunR.smul (0:R) g)) (BFunR.smul (0:R) g) := by
    refine ⟨rfl, ?_⟩
    intro x hx
    show COF.abs ((0:R) * g.toFun x hx) = (0:R) * g.toFun x hx
    rw [show (0:R) * g.toFun x hx = (0:R) from by ring, COFO.abs_zero]
  rw [S.toIntSpaceR.I_resp (S.abs_mem (S.smul_mem 0 hg)) hbe, S.I_smul 0 hg]; ring

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.ofL {g : BFunR X R} (hg : g ∈ S.L) : IntegrableRep S where
  fn := fun n => if n = 0 then g else BFunR.smul (0:R) g
  mem := by
    intro n
    by_cases h : n = 0
    · rw [if_pos h]; exact hg
    · rw [if_neg h]; exact S.smul_mem 0 hg
  absConv := by
    have heq : (fun n => S.I (BFunR.absf (if n = 0 then g else BFunR.smul (0:R) g)))
             = (fun n => if n = 0 then S.I (BFunR.absf g) else (0:R)) := by
      funext n
      by_cases h : n = 0
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]; exact I_abs_smul_zero hg
    show RSeq.SeriesSum (fun n => S.I (BFunR.absf (if n = 0 then g else BFunR.smul (0:R) g)))
    rw [heq]; exact seriesSum_single (S.I (BFunR.absf g))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.ofL_integral {g : BFunR X R} (hg : g ∈ S.L) :
    (IntegrableRep.ofL hg).integral = S.I g := by
  have h : ∀ n, S.I ((IntegrableRep.ofL hg).fn n) = (if n = 0 then S.I g else (0:R)) := by
    intro n
    show S.I (if n = 0 then g else BFunR.smul (0:R) g) = if n = 0 then S.I g else (0:R)
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]
    · rw [if_neg hn, if_neg hn, S.I_smul 0 hg]; ring
  exact seriesSum_sum_congr h (IntegrableRep.ofL hg).seriesSum_I (seriesSum_single (S.I g))

/-- Domain membership for the one-term representative. -/
theorem IntegrableRep.ofL_memAt {g : BFunR X R} (hg : g ∈ S.L)
    {x : X} (hx : x ∈ g.dom) : (IntegrableRep.ofL hg).MemAt x := by
  intro n
  by_cases hn : n = 0
  · simpa [IntegrableRep.ofL, hn] using hx
  · simpa [IntegrableRep.ofL, hn, BFunR.smul] using hx

/-- Recover the source domain proof from a one-term representative. -/
theorem IntegrableRep.ofL_dom {g : BFunR X R} (hg : g ∈ S.L)
    {x : X} (hdom : (IntegrableRep.ofL hg).MemAt x) : x ∈ g.dom := by
  simpa [IntegrableRep.ofL] using hdom 0

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.add (r r' : IntegrableRep S) : IntegrableRep S where
  fn := seqInterleave r.fn r'.fn
  mem := by
    intro n
    rcases natEvenOrOdd' n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [seqInterleave_even r.fn r'.fn k]; exact r.mem k
    · rw [seqInterleave_odd r.fn r'.fn k]; exact r'.mem k
  absConv := by
    have heq : (fun n => S.I (BFunR.absf (seqInterleave r.fn r'.fn n)))
             = seqInterleave (fun k => S.I (BFunR.absf (r.fn k)))
                 (fun k => S.I (BFunR.absf (r'.fn k))) := by
      funext n
      rw [seqInterleave_map BFunR.absf r.fn r'.fn n, seqInterleave_map S.I _ _ n]
    show RSeq.SeriesSum (fun n => S.I (BFunR.absf (seqInterleave r.fn r'.fn n)))
    rw [heq]; exact seriesSum_interleave r.absConv r'.absConv

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.integral_add (r r' : IntegrableRep S) :
    (r.add r').integral = r.integral + r'.integral := by
  have heq : (fun n => S.I ((r.add r').fn n))
           = seqInterleave (fun k => S.I (r.fn k)) (fun k => S.I (r'.fn k)) := by
    funext n
    show S.I (seqInterleave r.fn r'.fn n)
       = seqInterleave (fun k => S.I (r.fn k)) (fun k => S.I (r'.fn k)) n
    rw [seqInterleave_map S.I r.fn r'.fn n]
  exact seriesSum_sum_congr (congrFun heq) (r.add r').seriesSum_I
    (seriesSum_interleave r.seriesSum_I r'.seriesSum_I)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.neg (r : IntegrableRep S) : IntegrableRep S where
  fn := fun n => BFunR.smul (-1) (r.fn n)
  mem := fun n => S.smul_mem (-1) (r.mem n)
  absConv := by
    have heq : (fun n => S.I (BFunR.absf (BFunR.smul (-1) (r.fn n))))
             = (fun n => S.I (BFunR.absf (r.fn n))) :=
      funext fun n => I_absf_neg_eq S (r.mem n)
    show RSeq.SeriesSum (fun n => S.I (BFunR.absf (BFunR.smul (-1) (r.fn n))))
    rw [heq]; exact r.absConv

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.integral_neg (r : IntegrableRep S) :
    r.neg.integral = - r.integral :=
  seriesSum_sum_congr (fun n => S.toIntSpaceR.I_neg (r.mem n))
    r.neg.seriesSum_I (seriesSum_neg r.seriesSum_I)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.sub (r r' : IntegrableRep S) : IntegrableRep S := r.add r'.neg

/-- I₁(r − r') = I₁(r) − I₁(r'). -/
theorem IntegrableRep.integral_sub (r r' : IntegrableRep S) :
    (r.sub r').integral = r.integral - r'.integral := by
  show (r.add r'.neg).integral = r.integral - r'.integral
  rw [IntegrableRep.integral_add, IntegrableRep.integral_neg]; ring

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem I_abs_smul (a : R) {f : BFunR X R} (hf : f ∈ S.L) :
    S.I (BFunR.absf (BFunR.smul a f)) = COF.abs a * S.I (BFunR.absf f) := by
  have hbe : BFunR.BEquiv (BFunR.absf (BFunR.smul a f))
                          (BFunR.smul (COF.abs a) (BFunR.absf f)) := by
    refine ⟨rfl, ?_⟩
    intro x hx
    show COF.abs (a * f.toFun x hx) = COF.abs a * COF.abs (f.toFun x hx)
    exact COFO.abs_mul a (f.toFun x hx)
  rw [S.toIntSpaceR.I_resp (S.abs_mem (S.smul_mem a hf)) hbe, S.I_smul (COF.abs a) (S.abs_mem hf)]

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.smul (a : R) (r : IntegrableRep S) : IntegrableRep S where
  fn := fun n => BFunR.smul a (r.fn n)
  mem := fun n => S.smul_mem a (r.mem n)
  absConv := by
    have heq : (fun n => S.I (BFunR.absf (BFunR.smul a (r.fn n))))
             = (fun n => COF.abs a * S.I (BFunR.absf (r.fn n))) :=
      funext fun n => I_abs_smul a (r.mem n)
    show RSeq.SeriesSum (fun n => S.I (BFunR.absf (BFunR.smul a (r.fn n))))
    rw [heq]; exact seriesSum_smul (COF.abs a) r.absConv

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.integral_smul (a : R) (r : IntegrableRep S) :
    (r.smul a).integral = a * r.integral :=
  seriesSum_sum_congr (fun n => S.I_smul a (r.mem n))
    (r.smul a).seriesSum_I (seriesSum_smul a r.seriesSum_I)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.domain (r : IntegrableRep S) : Set X :=
  {x | ∃ hx : r.MemAt x,
       Nonempty (RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hx n)))}

/-- Technical lemma used in the public import closure. -/
def seqMerge {α : Type*} (f g : Nat → α) : Nat → α :=
  fun n => if n % 2 = 0 then f (n / 2) else g (n / 2)

theorem seqMerge_even {α : Type*} (f g : Nat → α) (k : Nat) :
    seqMerge f g (2 * k) = f k := by
  unfold seqMerge; rw [if_pos (by omega : (2 * k) % 2 = 0)]; congr 1; omega

theorem seqMerge_odd {α : Type*} (f g : Nat → α) (k : Nat) :
    seqMerge f g (2 * k + 1) = g k := by
  unfold seqMerge; rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]; congr 1; omega

/-- Technical lemma used in the public import closure. -/
def IsFull (S : IntSpaceRC X R) (A : Set X) : Prop :=
  ∃ F : Nat → IntegrableRep S, {x | ∀ n, x ∈ (F n).domain} ⊆ A

/-- Technical lemma used in the public import closure. -/
theorem isFull_univ : IsFull S Set.univ :=
  ⟨fun _ => IntegrableRep.ofL S.normalized.2.1, fun _ _ => Set.mem_univ _⟩

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.domain_isFull (r : IntegrableRep S) : IsFull S r.domain :=
  ⟨fun _ => r, fun _ hx => hx 0⟩

/-- Technical lemma used in the public import closure. -/
theorem isFull_inter {A B : Set X} (hA : IsFull S A) (hB : IsFull S B) :
    IsFull S (A ∩ B) := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨G, hG⟩ := hB
  exact ⟨seqMerge F G, fun _ hx =>
    ⟨hF (fun k => by have h := hx (2 * k); rwa [seqMerge_even] at h),
     hG (fun k => by have h := hx (2 * k + 1); rwa [seqMerge_odd] at h)⟩⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.smul_absSum (a : R) (r : IntegrableRep S) :
    (r.smul a).absConv.sum = COF.abs a * r.absConv.sum :=
  seriesSum_sum_congr (fun n => I_abs_smul a (r.mem n))
    (r.smul a).absConv (seriesSum_smul (COF.abs a) r.absConv)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.absSum_nonneg (r : IntegrableRep S) : Nonneg r.absConv.sum :=
  seriesSum_nonneg
    (fun n => S.I_nonneg (S.abs_mem (r.mem n)) (fun x _ => abs_nonneg _)) r.absConv

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.exists_scale_absSum_le (r : IntegrableRep S) (j : Nat) :
    ∃ M : Nat, Le ((r.smul (COF.halfPow (j + M))).absConv.sum) (COF.halfPow j) := by
  refine ⟨(COFO.mul_archimedean r.absConv.sum).val, ?_⟩
  set M := (COFO.mul_archimedean r.absConv.sum).val with hM
  have harch : Le (COF.abs r.absConv.sum * COF.halfPow M) 1 :=
    (COFO.mul_archimedean r.absConv.sum).property
  have hkey : Le (COF.halfPow M * r.absConv.sum) 1 := by
    rw [mul_comm, ← COFO.abs_of_nonneg r.absSum_nonneg]; exact harch
  have he : (r.smul (COF.halfPow (j + M))).absConv.sum
          = COF.halfPow j * (COF.halfPow M * r.absConv.sum) := by
    rw [r.smul_absSum (COF.halfPow (j + M)),
        COFO.abs_of_nonneg (le_of_lt (halfPow_pos (j + M))), halfPow_add]; ring
  rw [he]
  have hstep := mul_le_mul_left hkey (le_of_lt (halfPow_pos (R := R) j))
  rwa [mul_one] at hstep

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem halfPow_antitone {m n : Nat} (h : m ≤ n) :
    Le (COF.halfPow (R := R) n) (COF.halfPow m) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  clear h
  induction d with
  | zero => exact le_refl _
  | succ d ih => exact le_trans (le_of_lt (halfPow_lt_succ (m + d))) ih

/-- Technical lemma used in the public import closure. -/
theorem partialSum_halfPow (N : Nat) :
    RSeq.partialSum (fun n => COF.halfPow (R := R) n) N = 2 - COF.halfPow N := by
  induction N with
  | zero =>
      show COF.halfPow (R := R) 0 = 2 - COF.halfPow 0
      rw [show COF.halfPow (R := R) 0 = (1 : R) from rfl]; ring
  | succ N ih =>
      show RSeq.partialSum (fun n => COF.halfPow n) N + COF.halfPow (N + 1)
         = 2 - COF.halfPow (N + 1)
      rw [ih]; linear_combination (halfPow_succ_add (R := R) N)

/-- Technical lemma used in the public import closure. -/
def seriesSum_halfPow : RSeq.SeriesSum (fun n => COF.halfPow (R := R) n) where
  sum := 2
  tends :=
    { mod := fun k => k + 1
      close := by
        intro k n hn
        show COF.lt (COF.abs (RSeq.partialSum (fun n => COF.halfPow n) n - 2)) (COF.halfPow k)
        rw [partialSum_halfPow n,
            show (2 - COF.halfPow (R := R) n) - 2 = - COF.halfPow n from by ring,
            COFO.abs_neg, COFO.abs_of_nonneg (le_of_lt (halfPow_pos n))]
        exact lt_of_le_of_lt (halfPow_antitone hn) (halfPow_lt_succ k) }

/-- Technical lemma used in the public import closure. -/
def seriesSum_of_le_halfPow {u : Nat → R} (hnn : ∀ n, Nonneg (u n))
    (hle : ∀ n, Le (u n) (COF.halfPow n)) : RSeq.SeriesSum u :=
  seriesSum_comparison hnn hle seriesSum_halfPow

/-! Technical auxiliary material for the public import closure. -/
def isCauchy_of_mono_bounded_gap {v : Nat → R} {T : R}
    (hmono : ∀ {p q : Nat}, p ≤ q → Le (v p) (v q))
    (hbd : ∀ q : Nat, Le (v q) T)
    (hgap : ∀ k : Nat, {M : Nat // COF.lt (T - v M) (COF.halfPow k)}) :
    IsCauchy v where
  cmod := fun k => (hgap k).val
  ccond := by
    intro k m n hm hn
    set M := (hgap k).val with hMdef
    have hgk : COF.lt (T - v M) (COF.halfPow k) := (hgap k).property
    rcases Nat.le_total m n with h | h
    · rw [show v m - v n = -(v n - v m) from by ring, COFO.abs_neg,
          COFO.abs_of_nonneg (nonneg_sub_of_le (hmono h))]
      exact lt_of_le_of_lt (le_trans (le_sub_right (hbd n)) (le_sub_left (hmono hm))) hgk
    · rw [COFO.abs_of_nonneg (nonneg_sub_of_le (hmono h))]
      exact lt_of_le_of_lt (le_trans (le_sub_right (hbd m)) (le_sub_left (hmono hn))) hgk

/-- Technical lemma used in the public import closure. -/
theorem partialSum_mono {u : Nat → R} (hnn : ∀ n, Nonneg (u n))
    {p q : Nat} (h : p ≤ q) : Le (RSeq.partialSum u p) (RSeq.partialSum u q) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  clear h
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
      refine le_trans ih ?_
      show Le (RSeq.partialSum u (p + d)) (RSeq.partialSum u (p + d) + u (p + d + 1))
      exact le_of_nonneg_sub
        (by rw [show RSeq.partialSum u (p + d) + u (p + d + 1) - RSeq.partialSum u (p + d)
                  = u (p + d + 1) from by ring]; exact hnn _)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem partialSum_le_of_termwise_le {u v : Nat → R} (h : ∀ n, Le (u n) (v n)) :
    ∀ N, Le (RSeq.partialSum u N) (RSeq.partialSum v N)
  | 0 => h 0
  | N + 1 => le_add (partialSum_le_of_termwise_le h N) (h (N + 1))

/-- Technical lemma used in the public import closure. -/
def gridSum (a : Nat → Nat → R) (N : Nat) : R :=
  RSeq.partialSum (fun i => RSeq.partialSum (a i) N) N

/-- Technical lemma used in the public import closure. -/
theorem gridSum_le_T {a : Nat → Nat → R} (ha : ∀ i j, Nonneg (a i j))
    (hrow : ∀ i, RSeq.SeriesSum (a i))
    (hrowsum : RSeq.SeriesSum (fun i => (hrow i).sum)) (N : Nat) :
    Le (gridSum a N) hrowsum.sum := by
  have hrs_nn : ∀ i, Nonneg ((hrow i).sum) :=
    fun i => seriesSum_nonneg (fun j => ha i j) (hrow i)
  have step1 : Le (gridSum a N) (RSeq.partialSum (fun i => (hrow i).sum) N) :=
    partialSum_le_of_termwise_le
      (fun i => partialSum_le_sum (fun j => ha i j) (hrow i) N) N
  exact le_trans step1 (partialSum_le_sum hrs_nn hrowsum N)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem partialSum_congr {u v : Nat → R} (h : ∀ i, u i = v i) :
    ∀ N, RSeq.partialSum u N = RSeq.partialSum v N
  | 0 => h 0
  | N + 1 => by
      show RSeq.partialSum u N + u (N + 1) = RSeq.partialSum v N + v (N + 1)
      rw [partialSum_congr h N, h (N + 1)]

/-- Technical lemma used in the public import closure. -/
theorem partialSum_nonneg {u : Nat → R} (hu : ∀ n, Nonneg (u n)) :
    ∀ N, Nonneg (RSeq.partialSum u N)
  | 0 => hu 0
  | N + 1 => nonneg_add (partialSum_nonneg hu N) (hu (N + 1))

/-- Technical lemma used in the public import closure. -/
theorem partialSum_le_of_termwise_le_upto {u v : Nat → R} :
    ∀ N, (∀ i, i ≤ N → Le (u i) (v i)) → Le (RSeq.partialSum u N) (RSeq.partialSum v N)
  | 0, h => h 0 (Nat.le_refl 0)
  | N + 1, h =>
      le_add (partialSum_le_of_termwise_le_upto N (fun i hi => h i (Nat.le_succ_of_le hi)))
        (h (N + 1) (Nat.le_refl _))

/-- Technical lemma used in the public import closure. -/
theorem halfPow_geom_tail (c M : Nat) :
    Le (RSeq.partialSum (fun i => COF.halfPow (R := R) (c + 1 + i)) M) (COF.halfPow c) := by
  rw [partialSum_congr (fun i => halfPow_add (c + 1) i) M, partialSum_smul, partialSum_halfPow,
      show COF.halfPow (R := R) c = COF.halfPow (c + 1) * 2 from by
        rw [← halfPow_succ_add (R := R) c]; ring]
  exact mul_le_mul_left
    (le_of_nonneg_sub (by
      rw [show (2 : R) - (2 - COF.halfPow M) = COF.halfPow M from by ring]
      exact le_of_lt (halfPow_pos M)))
    (le_of_lt (halfPow_pos (c + 1)))

/-- Technical lemma used in the public import closure. -/
def maxUpto (g : Nat → Nat) : Nat → Nat
  | 0 => g 0
  | M + 1 => Nat.max (maxUpto g M) (g (M + 1))

theorem le_maxUpto (g : Nat → Nat) : ∀ {M i : Nat}, i ≤ M → g i ≤ maxUpto g M := by
  intro M
  induction M with
  | zero => intro i hi; rw [Nat.le_zero.mp hi]; exact Nat.le_refl _
  | succ M ih =>
      intro i hi
      rcases Nat.lt_or_ge M i with hc | hc
      · have he : i = M + 1 := Nat.le_antisymm hi (Nat.succ_le_of_lt hc)
        subst he; exact Nat.le_max_right _ _
      · exact Nat.le_trans (ih hc) (Nat.le_max_left _ _)

/-- Technical lemma used in the public import closure. -/
theorem rowTail_lt {w : Nat → R} (h : RSeq.SeriesSum w) (L N : Nat)
    (hN : h.tends.mod L ≤ N) : COF.lt (h.sum - RSeq.partialSum w N) (COF.halfPow L) := by
  have hcl : COF.lt (COF.abs (RSeq.partialSum w N - h.sum)) (COF.halfPow L) := h.tends.close L N hN
  refine lt_of_le_of_lt (COFO.le_abs_self (h.sum - RSeq.partialSum w N)) ?_
  rwa [show COF.abs (h.sum - RSeq.partialSum w N)
        = COF.abs (RSeq.partialSum w N - h.sum) from by
        rw [show h.sum - RSeq.partialSum w N = -(RSeq.partialSum w N - h.sum) from by ring,
            COFO.abs_neg]]

/-- Technical lemma used in the public import closure. -/
theorem gridSum_gap_at {a : Nat → Nat → R} (ha : ∀ i j, Nonneg (a i j))
    (hrow : ∀ i, RSeq.SeriesSum (a i))
    (hrowsum : RSeq.SeriesSum (fun i => (hrow i).sum)) (k I₀ N : Nat)
    (hI₀ : hrowsum.tends.mod (k + 3) ≤ I₀)
    (hNI₀ : I₀ ≤ N)
    (hNA : hrowsum.tends.mod (k + 2) ≤ N)
    (hNrow : ∀ i, i ≤ I₀ → (hrow i).tends.mod (k + 4 + i) ≤ N) :
    COF.lt (hrowsum.sum - gridSum a N) (COF.halfPow k) := by
  -- Technical note.
  have hrt_eq : RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) N
              = RSeq.partialSum (fun i => (hrow i).sum) N - gridSum a N :=
    partialSum_sub (fun i => (hrow i).sum) (fun i => RSeq.partialSum (a i) N) N
  -- (1) P1 = T − Σ rowSum N < halfPow(k+2)
  have hP1 : COF.lt (hrowsum.sum - RSeq.partialSum (fun i => (hrow i).sum) N)
                    (COF.halfPow (k + 2)) :=
    rowTail_lt hrowsum (k + 2) N hNA
  -- Technical note.
  have hP2a : Le (RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) I₀)
                 (COF.halfPow (k + 3)) :=
    le_trans
      (partialSum_le_of_termwise_le_upto I₀
        (fun i hi => le_of_lt (rowTail_lt (hrow i) (k + 4 + i) N (hNrow i hi))))
      (halfPow_geom_tail (k + 3) I₀)
  -- Technical note.
  have hP2b : COF.lt (RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) N
                      - RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) I₀)
                     (COF.halfPow (k + 3)) := by
    obtain ⟨d, hd⟩ := Nat.le.dest hNI₀
    have hgap := (partialSum_gap
      (fun i => nonneg_sub_of_le (partialSum_le_sum (fun j => ha i j) (hrow i) N))
      (fun i => le_of_nonneg_sub (by
        rw [show (hrow i).sum - ((hrow i).sum - RSeq.partialSum (a i) N)
              = RSeq.partialSum (a i) N from by ring]
        exact partialSum_nonneg (fun j => ha i j) N))
      I₀ d).2
    rw [hd] at hgap
    refine lt_of_le_of_lt (le_trans hgap
      (le_sub_right (partialSum_le_sum
        (fun i => seriesSum_nonneg (fun j => ha i j) (hrow i)) hrowsum N))) ?_
    exact rowTail_lt hrowsum (k + 3) I₀ hI₀
  -- (4) P2 = Σ rt N = P2a + P2b < halfPow(k+2)
  have hP2 : COF.lt (RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) N)
                    (COF.halfPow (k + 2)) := by
    have hcomb := lt_of_le_of_lt (le_add hP2a (le_refl _))
      (COF.lt_add_left (COF.halfPow (R := R) (k + 3)) hP2b)
    rw [show COF.halfPow (R := R) (k + 3) + COF.halfPow (R := R) (k + 3)
          = COF.halfPow (k + 2) from halfPow_succ_add (k + 2),
        show RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) I₀
            + (RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) N
               - RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) I₀)
            = RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) N
          from by ring] at hcomb
    exact hcomb
  -- Technical note.
  have hfinal := lt_add hP1 hP2
  rw [show COF.halfPow (R := R) (k + 2) + COF.halfPow (R := R) (k + 2)
        = COF.halfPow (k + 1) from halfPow_succ_add (k + 1)] at hfinal
  rw [show hrowsum.sum - gridSum a N
        = (hrowsum.sum - RSeq.partialSum (fun i => (hrow i).sum) N)
          + RSeq.partialSum (fun i => (hrow i).sum - RSeq.partialSum (a i) N) N
        from by rw [hrt_eq]; ring]
  exact lt_of_lt_of_le hfinal (halfPow_antitone (Nat.le_succ k))

/-- Technical lemma used in the public import closure. -/
def gridSum_gap {a : Nat → Nat → R} (ha : ∀ i j, Nonneg (a i j))
    (hrow : ∀ i, RSeq.SeriesSum (a i))
    (hrowsum : RSeq.SeriesSum (fun i => (hrow i).sum)) (k : Nat) :
    { N : Nat // COF.lt (hrowsum.sum - gridSum a N) (COF.halfPow k) } :=
  let I₀ := hrowsum.tends.mod (k + 3)
  let B := maxUpto (fun i => (hrow i).tends.mod (k + 4 + i)) I₀
  ⟨I₀ + B + hrowsum.tends.mod (k + 2),
   gridSum_gap_at ha hrow hrowsum k I₀ (I₀ + B + hrowsum.tends.mod (k + 2))
     (Nat.le_refl _)
     (Nat.le_trans (Nat.le_add_right I₀ B) (Nat.le_add_right (I₀ + B) _))
     (Nat.le_add_left _ (I₀ + B))
     (fun i hi => Nat.le_trans (le_maxUpto (fun i => (hrow i).tends.mod (k + 4 + i)) hi)
       (Nat.le_trans (Nat.le_add_left B I₀) (Nat.le_add_right (I₀ + B) _)))⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def shellGo : Nat → Nat → Nat → Nat × Nat
  | 0,        N, rem => (N, rem)
  | fuel + 1, N, rem => if rem ≤ 2 * N then (N, rem) else shellGo fuel (N + 1) (rem - (2 * N + 1))

/-- Technical lemma used in the public import closure. -/
theorem shellGo_base (fuel N rem : Nat) (h : rem ≤ 2 * N) : shellGo fuel N rem = (N, rem) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      show (if rem ≤ 2 * N then (N, rem) else shellGo fuel (N + 1) (rem - (2 * N + 1))) = (N, rem)
      rw [if_pos h]

/-- Technical lemma used in the public import closure. -/
theorem shellGo_peel (n : Nat) : ∀ (s t fuel : Nat), t ≤ 2 * (s + n) → n ≤ fuel →
    shellGo fuel s (2 * s * n + n * n + t) = (s + n, t) := by
  induction n with
  | zero =>
      intro s t fuel ht _
      rw [show 2 * s * 0 + 0 * 0 + t = t from by ring]
      exact shellGo_base fuel s t (by omega)
  | succ n ih =>
      intro s t fuel ht hfuel
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_succ_le_zero n)
      | succ fuel' =>
          have hrem_eq : 2 * s * (n + 1) + (n + 1) * (n + 1) + t
                       = (2 * s + 1) + (2 * (s + 1) * n + n * n + t) := by ring
          show (if 2 * s * (n + 1) + (n + 1) * (n + 1) + t ≤ 2 * s
                then (s, 2 * s * (n + 1) + (n + 1) * (n + 1) + t)
                else shellGo fuel' (s + 1)
                       (2 * s * (n + 1) + (n + 1) * (n + 1) + t - (2 * s + 1)))
               = (s + (n + 1), t)
          rw [if_neg (by rw [hrem_eq]; omega),
              show 2 * s * (n + 1) + (n + 1) * (n + 1) + t - (2 * s + 1)
                 = 2 * (s + 1) * n + n * n + t from by rw [hrem_eq]; omega,
              show s + (n + 1) = (s + 1) + n from by omega]
          exact ih (s + 1) t fuel' (by omega) (by omega)

/-- Technical lemma used in the public import closure. -/
theorem self_le_sq_add (N t : Nat) : N ≤ N * N + t := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact Nat.zero_le _
  · exact Nat.le_trans (Nat.le_mul_of_pos_left N hN) (Nat.le_add_right _ _)

/-- Technical lemma used in the public import closure. -/
def shellDecomp (m : Nat) : Nat × Nat := shellGo m 0 m

/-- Technical lemma used in the public import closure. -/
theorem shellDecomp_block (N t : Nat) (ht : t ≤ 2 * N) : shellDecomp (N * N + t) = (N, t) := by
  show shellGo (N * N + t) 0 (N * N + t) = (N, t)
  have key := shellGo_peel N 0 t (N * N + t) (by omega) (self_le_sq_add N t)
  rwa [show 2 * 0 * N + N * N + t = N * N + t from by ring, Nat.zero_add] at key

/-- Technical lemma used in the public import closure. -/
def cellOf : Nat × Nat → Nat × Nat
  | (N, t) => if t ≤ N then (N, t) else (t - N - 1, N)

/-- Technical lemma used in the public import closure. -/
def cellAt (m : Nat) : Nat × Nat := cellOf (shellDecomp m)

/-- Technical lemma used in the public import closure. -/
theorem cellAt_block (N t : Nat) (ht : t ≤ 2 * N) :
    cellAt (N * N + t) = if t ≤ N then (N, t) else (t - N - 1, N) := by
  show cellOf (shellDecomp (N * N + t)) = _
  rw [shellDecomp_block N t ht]
  rfl

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem partialSum_split (u : Nat → R) (p : Nat) :
    ∀ d, RSeq.partialSum u (p + (d + 1))
       = RSeq.partialSum u p + RSeq.partialSum (fun j => u (p + 1 + j)) d := by
  intro d
  induction d with
  | zero =>
      show RSeq.partialSum u p + u (p + 1) = RSeq.partialSum u p + u (p + 1 + 0)
      rw [Nat.add_zero]
  | succ d ih =>
      show RSeq.partialSum u (p + (d + 1)) + u (p + (d + 1) + 1)
         = RSeq.partialSum u p
           + (RSeq.partialSum (fun j => u (p + 1 + j)) d + u (p + 1 + (d + 1)))
      rw [ih, show p + (d + 1) + 1 = p + 1 + (d + 1) from by omega]
      ring

/-- Technical lemma used in the public import closure. -/
theorem partialSum_congr_upto {u v : Nat → R} :
    ∀ N, (∀ j, j ≤ N → u j = v j) → RSeq.partialSum u N = RSeq.partialSum v N
  | 0, h => h 0 (Nat.le_refl 0)
  | N + 1, h => by
      show RSeq.partialSum u N + u (N + 1) = RSeq.partialSum v N + v (N + 1)
      rw [partialSum_congr_upto N (fun j hj => h j (Nat.le_succ_of_le hj)), h (N + 1) (Nat.le_refl _)]

/-- Technical lemma used in the public import closure. -/
theorem gridSum_succ (a : Nat → Nat → R) (N : Nat) :
    gridSum a (N + 1)
      = gridSum a N + (RSeq.partialSum (a (N + 1)) (N + 1)
                       + RSeq.partialSum (fun i => a i (N + 1)) N) := by
  have hrow : RSeq.partialSum (fun i => RSeq.partialSum (a i) (N + 1)) N
            = RSeq.partialSum (fun i => RSeq.partialSum (a i) N) N
              + RSeq.partialSum (fun i => a i (N + 1)) N := by
    show RSeq.partialSum (fun i => RSeq.partialSum (a i) N + a i (N + 1)) N = _
    exact partialSum_add (fun i => RSeq.partialSum (a i) N) (fun i => a i (N + 1)) N
  show RSeq.partialSum (fun i => RSeq.partialSum (a i) (N + 1)) N
       + RSeq.partialSum (a (N + 1)) (N + 1)
     = RSeq.partialSum (fun i => RSeq.partialSum (a i) N) N
       + (RSeq.partialSum (a (N + 1)) (N + 1) + RSeq.partialSum (fun i => a i (N + 1)) N)
  rw [hrow]; ring

/-- Technical lemma used in the public import closure. -/
theorem block_eq (a : Nat → Nat → R) (N : Nat) :
    RSeq.partialSum
        (fun j => a (cellAt ((N + 1) * (N + 1) + j)).1 (cellAt ((N + 1) * (N + 1) + j)).2)
        (2 * N + 2)
      = RSeq.partialSum (a (N + 1)) (N + 1) + RSeq.partialSum (fun i => a i (N + 1)) N := by
  have hA : RSeq.partialSum
        (fun j => a (cellAt ((N + 1) * (N + 1) + j)).1 (cellAt ((N + 1) * (N + 1) + j)).2)
        (N + 1)
      = RSeq.partialSum (a (N + 1)) (N + 1) :=
    partialSum_congr_upto (N + 1) (fun j hj => by
      show a (cellAt ((N + 1) * (N + 1) + j)).1 (cellAt ((N + 1) * (N + 1) + j)).2 = a (N + 1) j
      rw [cellAt_block (N + 1) j (by omega), if_pos hj])
  have hB : RSeq.partialSum
        (fun j => a (cellAt ((N + 1) * (N + 1) + ((N + 1) + 1 + j))).1
                    (cellAt ((N + 1) * (N + 1) + ((N + 1) + 1 + j))).2)
        N
      = RSeq.partialSum (fun i => a i (N + 1)) N :=
    partialSum_congr_upto N (fun j hj => by
      show a (cellAt ((N + 1) * (N + 1) + ((N + 1) + 1 + j))).1
             (cellAt ((N + 1) * (N + 1) + ((N + 1) + 1 + j))).2 = a j (N + 1)
      rw [cellAt_block (N + 1) ((N + 1) + 1 + j) (by omega), if_neg (by omega),
          show (N + 1) + 1 + j - (N + 1) - 1 = j from by omega])
  rw [show 2 * N + 2 = (N + 1) + (N + 1) from by ring,
      partialSum_split
        (fun j => a (cellAt ((N + 1) * (N + 1) + j)).1 (cellAt ((N + 1) * (N + 1) + j)).2)
        (N + 1) N,
      hA, hB]

/-- Technical lemma used in the public import closure. -/
theorem partialSum_cellAt_eq_gridSum (a : Nat → Nat → R) :
    ∀ N, RSeq.partialSum (fun m => a (cellAt m).1 (cellAt m).2) (N * N + 2 * N) = gridSum a N
  | 0 => rfl
  | N + 1 => by
      rw [show (N + 1) * (N + 1) + 2 * (N + 1) = (N * N + 2 * N) + ((2 * N + 2) + 1) from by ring,
          partialSum_split (fun m => a (cellAt m).1 (cellAt m).2) (N * N + 2 * N) (2 * N + 2),
          partialSum_cellAt_eq_gridSum a N,
          show N * N + 2 * N + 1 = (N + 1) * (N + 1) from by ring,
          block_eq a N, gridSum_succ a N]

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def cellAt_seriesSum {a : Nat → Nat → R} (ha : ∀ i j, Nonneg (a i j))
    (hrow : ∀ i, RSeq.SeriesSum (a i))
    (hrowsum : RSeq.SeriesSum (fun i => (hrow i).sum)) :
    RSeq.SeriesSum (fun m => a (cellAt m).1 (cellAt m).2) :=
  let hb_nn : ∀ m, Nonneg (a (cellAt m).1 (cellAt m).2) := fun m => ha (cellAt m).1 (cellAt m).2
  seriesSum_of_partialCauchy
    (isCauchy_of_mono_bounded_gap
      (v := RSeq.partialSum (fun m => a (cellAt m).1 (cellAt m).2)) (T := hrowsum.sum)
      (fun {_ _} h => partialSum_mono hb_nn h)
      (fun q => le_trans (partialSum_mono hb_nn (self_le_sq_add q (2 * q)))
        (by rw [partialSum_cellAt_eq_gridSum a q]; exact gridSum_le_T ha hrow hrowsum q))
      (fun k =>
        let g := gridSum_gap ha hrow hrowsum k
        ⟨g.val * g.val + 2 * g.val, by
          rw [partialSum_cellAt_eq_gridSum a g.val]; exact g.property⟩))

/-- Technical lemma used in the public import closure. -/
theorem cellAt_surj (m n : Nat) : ∃ k, cellAt k = (m, n) := by
  rcases Nat.lt_or_ge m n with h | h
  · exact ⟨n * n + (m + n + 1), by
      rw [cellAt_block n (m + n + 1) (by omega), if_neg (by omega),
          show m + n + 1 - n - 1 = m from by omega]⟩
  · exact ⟨m * m + n, by rw [cellAt_block m n (by omega), if_pos h]⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem single_le_partialSum {b : Nat → R} (hb : ∀ n, Nonneg (b n)) (q : Nat) :
    Le (b q) (RSeq.partialSum b q) := by
  cases q with
  | zero => exact le_refl _
  | succ q =>
      show Le (b (q + 1)) (RSeq.partialSum b q + b (q + 1))
      exact le_of_nonneg_sub (by
        rw [show RSeq.partialSum b q + b (q + 1) - b (q + 1) = RSeq.partialSum b q from by ring]
        exact partialSum_nonneg hb q)

/-- Technical lemma used in the public import closure. -/
theorem single_le_block {b : Nat → R} (hb : ∀ n, Nonneg (b n)) {p q : Nat} (hpq : p < q) :
    Le (b q) (RSeq.partialSum b q - RSeq.partialSum b p) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  show Le (b (q' + 1)) (RSeq.partialSum b q' + b (q' + 1) - RSeq.partialSum b p)
  rw [show RSeq.partialSum b q' + b (q' + 1) - RSeq.partialSum b p
        = b (q' + 1) + (RSeq.partialSum b q' - RSeq.partialSum b p) from by ring]
  exact le_of_nonneg_sub (by
    rw [show b (q' + 1) + (RSeq.partialSum b q' - RSeq.partialSum b p) - b (q' + 1)
          = RSeq.partialSum b q' - RSeq.partialSum b p from by ring]
    exact nonneg_sub_of_le (partialSum_mono hb (by omega)))

/-- Technical lemma used in the public import closure. -/
theorem partialSum_inj_le {b : Nat → R} (hb : ∀ n, Nonneg (b n)) {e : Nat → Nat}
    (he : ∀ l, e l < e (l + 1)) :
    ∀ N, Le (RSeq.partialSum (fun l => b (e l)) N) (RSeq.partialSum b (e N))
  | 0 => single_le_partialSum hb (e 0)
  | N + 1 => by
      show Le (RSeq.partialSum (fun l => b (e l)) N + b (e (N + 1))) (RSeq.partialSum b (e (N + 1)))
      have key := le_add (partialSum_inj_le hb he N) (single_le_block hb (he N))
      rwa [show RSeq.partialSum b (e N) + (RSeq.partialSum b (e (N + 1)) - RSeq.partialSum b (e N))
            = RSeq.partialSum b (e (N + 1)) from by ring] at key

/-- Technical lemma used in the public import closure. -/
theorem partialSum_inj_block_le {b : Nat → R} (hb : ∀ n, Nonneg (b n)) {e : Nat → Nat}
    (he : ∀ l, e l < e (l + 1)) (N : Nat) :
    ∀ d, Le (RSeq.partialSum (fun l => b (e l)) (N + d)
              - RSeq.partialSum (fun l => b (e l)) N)
            (RSeq.partialSum b (e (N + d)) - RSeq.partialSum b (e N))
  | 0 => by
      rw [Nat.add_zero,
          show RSeq.partialSum (fun l => b (e l)) N - RSeq.partialSum (fun l => b (e l)) N
            = 0 from by ring,
          show RSeq.partialSum b (e N) - RSeq.partialSum b (e N) = 0 from by ring]
      exact le_refl 0
  | d + 1 => by
      show Le (RSeq.partialSum (fun l => b (e l)) (N + d) + b (e (N + d + 1))
              - RSeq.partialSum (fun l => b (e l)) N)
              (RSeq.partialSum b (e (N + d + 1)) - RSeq.partialSum b (e N))
      have key := le_add (partialSum_inj_block_le hb he N d) (single_le_block hb (he (N + d)))
      rw [show RSeq.partialSum b (e (N + d)) - RSeq.partialSum b (e N)
            + (RSeq.partialSum b (e (N + d + 1)) - RSeq.partialSum b (e (N + d)))
            = RSeq.partialSum b (e (N + d + 1)) - RSeq.partialSum b (e N) from by ring] at key
      rw [show RSeq.partialSum (fun l => b (e l)) (N + d) + b (e (N + d + 1))
            - RSeq.partialSum (fun l => b (e l)) N
            = RSeq.partialSum (fun l => b (e l)) (N + d) - RSeq.partialSum (fun l => b (e l)) N
              + b (e (N + d + 1)) from by ring]
      exact key

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def twoPow : Nat → R
  | 0 => 1
  | n + 1 => 2 * twoPow n

/-- Technical lemma used in the public import closure. -/
theorem halfPow_mul_twoPow (n : Nat) : COF.halfPow (R := R) n * twoPow n = 1 := by
  induction n with
  | zero => show (1 : R) * 1 = 1; rw [mul_one]
  | succ n ih =>
      show COF.half * COF.halfPow (R := R) n * (2 * twoPow n) = 1
      rw [show COF.half * COF.halfPow (R := R) n * (2 * twoPow n)
            = (COF.half + COF.half) * (COF.halfPow (R := R) n * twoPow n) from by ring,
          COF.half_add_half, one_mul, ih]

/-- Technical lemma used in the public import closure. -/
def rowIdx (m n : Nat) : Nat := n * n + (m + n + 1)

theorem rowIdx_succ (m n : Nat) : rowIdx m (n + 1) = rowIdx m n + (2 * n + 2) := by
  show (n + 1) * (n + 1) + (m + (n + 1) + 1) = n * n + (m + n + 1) + (2 * n + 2); ring

theorem rowIdx_lt_succ (m n : Nat) : rowIdx m n < rowIdx m (n + 1) := by
  rw [rowIdx_succ]; omega

/-- Technical lemma used in the public import closure. -/
theorem cellAt_rowIdx {m n : Nat} (h : m < n) : cellAt (rowIdx m n) = (m, n) := by
  show cellAt (n * n + (m + n + 1)) = (m, n)
  rw [cellAt_block n (m + n + 1) (by omega), if_neg (by omega),
      show m + n + 1 - n - 1 = m from by omega]

theorem rowIdx_ge (m n : Nat) : n ≤ rowIdx m n := by show n ≤ n * n + (m + n + 1); omega

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def seriesSum_congr {u v : Nat → R} (h : ∀ n, u n = v n) (hu : RSeq.SeriesSum u) :
    RSeq.SeriesSum v where
  sum := hu.sum
  tends :=
    { mod := hu.tends.mod
      close := fun k n hn => by
        rw [← partialSum_congr h n]; exact hu.tends.close k n hn }

/-- Technical lemma used in the public import closure. -/
def seriesSum_of_tail {u : Nat → R} (p : Nat)
    (htail : RSeq.SeriesSum (fun l => u (p + 1 + l))) : RSeq.SeriesSum u where
  sum := RSeq.partialSum u p + htail.sum
  tends :=
    { mod := fun k => p + 1 + htail.tends.mod k
      close := fun k n hn => by
        obtain ⟨d, rfl⟩ : ∃ d, n = p + (d + 1) := ⟨n - p - 1, by omega⟩
        rw [partialSum_split u p d]
        show COF.lt (COF.abs (RSeq.partialSum u p + RSeq.partialSum (fun l => u (p + 1 + l)) d
              - (RSeq.partialSum u p + htail.sum))) (COF.halfPow k)
        rw [show RSeq.partialSum u p + RSeq.partialSum (fun l => u (p + 1 + l)) d
              - (RSeq.partialSum u p + htail.sum)
              = RSeq.partialSum (fun l => u (p + 1 + l)) d - htail.sum from by ring]
        exact htail.tends.close k d (by omega) }

/-- Technical lemma used in the public import closure. -/
def isCauchy_of_inj {b : Nat → R} (hb : ∀ n, Nonneg (b n)) {e : Nat → Nat}
    (he : ∀ l, e l < e (l + 1)) (hege : ∀ l, l ≤ e l)
    (hbc : IsCauchy (RSeq.partialSum b)) :
    IsCauchy (RSeq.partialSum (fun l => b (e l))) where
  cmod := fun k => hbc.cmod k
  ccond := by
    intro k L L' hL hL'
    rcases Nat.le_total L L' with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.le.dest hle
      have hnn : Nonneg (RSeq.partialSum (fun l => b (e l)) (L + d)
                  - RSeq.partialSum (fun l => b (e l)) L) :=
        nonneg_sub_of_le (partialSum_mono (fun l => hb (e l)) hle)
      rw [show RSeq.partialSum (fun l => b (e l)) L - RSeq.partialSum (fun l => b (e l)) (L + d)
            = -(RSeq.partialSum (fun l => b (e l)) (L + d)
                - RSeq.partialSum (fun l => b (e l)) L) from by ring,
          COFO.abs_neg, COFO.abs_of_nonneg hnn]
      refine lt_of_le_of_lt (partialSum_inj_block_le hb he L d) ?_
      refine lt_of_le_of_lt (COFO.le_abs_self _) (hbc.ccond k (e (L + d)) (e L) ?_ ?_)
      · exact Nat.le_trans hL' (hege (L + d))
      · exact Nat.le_trans hL (hege L)
    · obtain ⟨d, rfl⟩ := Nat.le.dest hle
      have hnn : Nonneg (RSeq.partialSum (fun l => b (e l)) (L' + d)
                  - RSeq.partialSum (fun l => b (e l)) L') :=
        nonneg_sub_of_le (partialSum_mono (fun l => hb (e l)) hle)
      rw [COFO.abs_of_nonneg hnn]
      refine lt_of_le_of_lt (partialSum_inj_block_le hb he L' d) ?_
      refine lt_of_le_of_lt (COFO.le_abs_self _) (hbc.ccond k (e (L' + d)) (e L') ?_ ?_)
      · exact Nat.le_trans hL (hege (L' + d))
      · exact Nat.le_trans hL' (hege L')

/-- Technical lemma used in the public import closure. -/
def row_seriesSum {A : Nat → Nat → R} (hA : ∀ i j, Nonneg (A i j))
    (hflat : RSeq.SeriesSum (fun k => A (cellAt k).1 (cellAt k).2)) (m : Nat) :
    RSeq.SeriesSum (A m) :=
  let he : ∀ l, rowIdx m (m + 1 + l) < rowIdx m (m + 1 + (l + 1)) :=
    fun l => rowIdx_lt_succ m (m + 1 + l)
  let hege : ∀ l, l ≤ rowIdx m (m + 1 + l) :=
    fun l => Nat.le_trans (by omega) (rowIdx_ge m (m + 1 + l))
  let tailFlat : RSeq.SeriesSum (fun l => A (cellAt (rowIdx m (m + 1 + l))).1
                                            (cellAt (rowIdx m (m + 1 + l))).2) :=
    seriesSum_of_partialCauchy
      (isCauchy_of_inj (fun k => hA (cellAt k).1 (cellAt k).2) he hege
        (isCauchy_of_tendsto hflat.tends))
  seriesSum_of_tail m
    (seriesSum_congr
      (fun l => by rw [cellAt_rowIdx (show m < m + 1 + l from by omega)])
      tailFlat)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def seriesIntegrable (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).absConv.sum)) : IntegrableRep S where
  fn := fun k => (F (cellAt k).1).fn (cellAt k).2
  mem := fun k => (F (cellAt k).1).mem (cellAt k).2
  absConv :=
    cellAt_seriesSum
      (fun i j => S.I_nonneg (S.abs_mem ((F i).mem j)) (fun x _ => abs_nonneg _))
      (fun i => (F i).absConv) hsum

/-- Technical lemma used in the public import closure. -/
theorem seriesIntegrable_domain_subset (F : Nat → IntegrableRep S)
    (hsum : RSeq.SeriesSum (fun m => (F m).absConv.sum)) :
    (seriesIntegrable F hsum).domain ⊆ {x | ∀ m, x ∈ (F m).domain} := by
  intro x hx m
  obtain ⟨hdom, hconv⟩ := hx
  let hrow : ∀ i j, x ∈ ((F i).fn j).dom := fun i j => by
    obtain ⟨k, hk⟩ := cellAt_surj i j
    have hd : x ∈ ((F (cellAt k).1).fn (cellAt k).2).dom := hdom k
    rw [hk] at hd
    exact hd
  refine ⟨hrow m, ?_⟩
  obtain ⟨flatSS⟩ := hconv
  have flatSS' : RSeq.SeriesSum
      (fun k => COF.abs (((F (cellAt k).1).fn (cellAt k).2).toFun x
        (hrow (cellAt k).1 (cellAt k).2))) := by
    simpa [seriesIntegrable, IntegrableRep.valueAt] using flatSS
  exact ⟨row_seriesSum
    (A := fun i j => COF.abs (((F i).fn j).toFun x (hrow i j)))
    (fun _ _ => abs_nonneg _) flatSS' m⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.scaleFactor (r : IntegrableRep S) : Nat :=
  (COFO.mul_archimedean r.absConv.sum).val

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.scaleFactor_spec (r : IntegrableRep S) (j : Nat) :
    Le ((r.smul (COF.halfPow (j + r.scaleFactor))).absConv.sum) (COF.halfPow j) := by
  have harch : Le (COF.abs r.absConv.sum * COF.halfPow r.scaleFactor) 1 :=
    (COFO.mul_archimedean r.absConv.sum).property
  have hkey : Le (COF.halfPow r.scaleFactor * r.absConv.sum) 1 := by
    rw [mul_comm, ← COFO.abs_of_nonneg r.absSum_nonneg]; exact harch
  have he : (r.smul (COF.halfPow (j + r.scaleFactor))).absConv.sum
          = COF.halfPow j * (COF.halfPow r.scaleFactor * r.absConv.sum) := by
    rw [r.smul_absSum (COF.halfPow (j + r.scaleFactor)),
        COFO.abs_of_nonneg (le_of_lt (halfPow_pos (j + r.scaleFactor))), halfPow_add]; ring
  rw [he]
  have hstep := mul_le_mul_left hkey (le_of_lt (halfPow_pos (R := R) j))
  rwa [mul_one] at hstep

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.smul_halfPow_domain_subset (r : IntegrableRep S) (K : Nat) :
    (r.smul (COF.halfPow K)).domain ⊆ r.domain := by
  intro x hx
  obtain ⟨hdom, hconv⟩ := hx
  let hrdom : r.MemAt x := fun n => hdom n
  refine ⟨hrdom, ?_⟩
  obtain ⟨ss⟩ := hconv
  refine ⟨seriesSum_congr (v := fun n => COF.abs (r.valueAt x hrdom n)) ?_
            (seriesSum_smul (twoPow K) ss)⟩
  intro n
  show twoPow K * COF.abs (COF.halfPow K * r.valueAt x hrdom n) =
    COF.abs (r.valueAt x hrdom n)
  rw [COFO.abs_mul, COFO.abs_of_nonneg (le_of_lt (halfPow_pos K)),
      show twoPow K * (COF.halfPow K * COF.abs (r.valueAt x hrdom n))
        = COF.halfPow K * twoPow K * COF.abs (r.valueAt x hrdom n) from by ring,
      halfPow_mul_twoPow, one_mul]

/-- Technical lemma used in the public import closure. -/
theorem lemma_1_10 (F : Nat → IntegrableRep S) :
    ∃ G : IntegrableRep S, G.domain ⊆ {x | ∀ m, x ∈ (F m).domain} := by
  have hsum' : RSeq.SeriesSum
      (fun m => ((F m).smul (COF.halfPow (m + (F m).scaleFactor))).absConv.sum) :=
    seriesSum_of_le_halfPow (fun m => IntegrableRep.absSum_nonneg _)
      (fun m => (F m).scaleFactor_spec m)
  refine ⟨seriesIntegrable
      (fun m => (F m).smul (COF.halfPow (m + (F m).scaleFactor))) hsum', ?_⟩
  intro x hx m
  exact (F m).smul_halfPow_domain_subset _
    (seriesIntegrable_domain_subset _ hsum' hx m)

/-- Technical lemma used in the public import closure. -/
theorem lemma_1_10_full {A : Set X} (hA : IsFull S A) :
    ∃ G : IntegrableRep S, G.domain ⊆ A := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨G, hG⟩ := lemma_1_10 F
  exact ⟨G, fun _ hx => hF (hG hx)⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def seriesSum_even_of_interleave_abs {u v : Nat → R}
    (h : RSeq.SeriesSum (fun n => COF.abs (seqInterleave u v n))) :
    RSeq.SeriesSum (fun k => COF.abs (u k)) :=
  seriesSum_congr (fun k => by rw [seqInterleave_even])
    (seriesSum_of_partialCauchy
      (isCauchy_of_inj (fun _ => abs_nonneg _) (e := fun k => 2 * k)
        (fun l => by show 2 * l < 2 * (l + 1); omega) (fun l => by show l ≤ 2 * l; omega)
        (isCauchy_of_tendsto h.tends)))

/-- Technical lemma used in the public import closure. -/
def seriesSum_odd_of_interleave_abs {u v : Nat → R}
    (h : RSeq.SeriesSum (fun n => COF.abs (seqInterleave u v n))) :
    RSeq.SeriesSum (fun k => COF.abs (v k)) :=
  seriesSum_congr (fun k => by rw [seqInterleave_odd])
    (seriesSum_of_partialCauchy
      (isCauchy_of_inj (fun _ => abs_nonneg _) (e := fun k => 2 * k + 1)
        (fun l => by show 2 * l + 1 < 2 * (l + 1) + 1; omega) (fun l => by show l ≤ 2 * l + 1; omega)
        (isCauchy_of_tendsto h.tends)))

/-- Technical lemma used in the public import closure. -/
theorem interleave_value {u v : Nat → R}
    (habs : RSeq.SeriesSum (fun n => COF.abs (seqInterleave u v n)))
    (hx : RSeq.SeriesSum (seqInterleave u v)) :
    hx.sum = (seriesSum_of_abs (seriesSum_even_of_interleave_abs habs)).sum
           + (seriesSum_of_abs (seriesSum_odd_of_interleave_abs habs)).sum :=
  seriesSum_unique hx
    (seriesSum_interleave (seriesSum_of_abs (seriesSum_even_of_interleave_abs habs))
      (seriesSum_of_abs (seriesSum_odd_of_interleave_abs habs)))

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.add_memAt {r r' : IntegrableRep S} {x : X}
    (hrdom : r.MemAt x) (hr'dom : r'.MemAt x) : (r.add r').MemAt x := by
  intro n
  rcases natEvenOrOdd' n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa [IntegrableRep.add, seqInterleave_even] using hrdom k
  · simpa [IntegrableRep.add, seqInterleave_odd] using hr'dom k

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.neg_memAt {r : IntegrableRep S} {x : X}
    (hrdom : r.MemAt x) : r.neg.MemAt x := by
  intro n
  simpa [IntegrableRep.neg, BFunR.smul] using hrdom n

/-- Technical lemma used in the public import closure. -/
theorem add_dom_left {r r' : IntegrableRep S} {x : X}
    (hd : (r.add r').MemAt x) (k : Nat) : x ∈ (r.fn k).dom := by
  have hk := hd (2 * k)
  rwa [show (r.add r').fn (2 * k) = r.fn k from seqInterleave_even r.fn r'.fn k] at hk

/-- Technical lemma used in the public import closure. -/
theorem add_dom_right {r r' : IntegrableRep S} {x : X}
    (hd : (r.add r').MemAt x) (k : Nat) : x ∈ (r'.fn k).dom := by
  have hk := hd (2 * k + 1)
  rwa [show (r.add r').fn (2 * k + 1) = r'.fn k from seqInterleave_odd r.fn r'.fn k] at hk

/-- Technical lemma used in the public import closure. -/
theorem neg_dom {r : IntegrableRep S} {x : X}
    (hd : r.neg.MemAt x) (k : Nat) : x ∈ (r.fn k).dom :=
  hd k

/-- Technical lemma used in the public import closure. -/
theorem add_fn_toFun (r r' : IntegrableRep S) (n : Nat) (x : X)
    (hrdom : r.MemAt x) (hr'dom : r'.MemAt x) :
    (r.add r').valueAt x (IntegrableRep.add_memAt hrdom hr'dom) n =
      seqInterleave (fun k => r.valueAt x hrdom k)
        (fun k => r'.valueAt x hr'dom k) n := by
  rcases natEvenOrOdd' n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simp only [IntegrableRep.valueAt, IntegrableRep.add, seqInterleave_even]
  · simp only [IntegrableRep.valueAt, IntegrableRep.add, seqInterleave_odd]

/-- Technical lemma used in the public import closure. -/
theorem neg_fn_toFun (r : IntegrableRep S) (n : Nat) (x : X)
    (hrdom : r.MemAt x) :
    r.neg.valueAt x (IntegrableRep.neg_memAt hrdom) n =
      -(r.valueAt x hrdom n) := by
  show (-1 : R) * r.valueAt x hrdom n = -(r.valueAt x hrdom n)
  ring

/-- Technical lemma used in the public import closure. -/
def add_seriesSum_value {r r' : IntegrableRep S} {x : X}
    (hrdom : r.MemAt x) (hr'dom : r'.MemAt x)
    (hr : RSeq.SeriesSum (fun k => r.valueAt x hrdom k))
    (hr' : RSeq.SeriesSum (fun k => r'.valueAt x hr'dom k)) :
    RSeq.SeriesSum
      (fun n => (r.add r').valueAt x (IntegrableRep.add_memAt hrdom hr'dom) n) :=
  seriesSum_congr (fun n => (add_fn_toFun r r' n x hrdom hr'dom).symm)
    (seriesSum_interleave hr hr')

/-- Technical lemma used in the public import closure. -/
def neg_seriesSum_value {r : IntegrableRep S} {x : X}
    (hrdom : r.MemAt x)
    (hr : RSeq.SeriesSum (fun k => r.valueAt x hrdom k)) :
    RSeq.SeriesSum
      (fun n => r.neg.valueAt x (IntegrableRep.neg_memAt hrdom) n) :=
  seriesSum_congr (fun n => (neg_fn_toFun r n x hrdom).symm) (seriesSum_neg hr)

/-- Technical lemma used in the public import closure. -/
def add_absSeriesSum_left {r r' : IntegrableRep S} {x : X}
    (hdom : (r.add r').MemAt x)
    (habs : RSeq.SeriesSum
      (fun n => COF.abs ((r.add r').valueAt x hdom n))) :
    RSeq.SeriesSum (fun k => COF.abs (r.valueAt x (add_dom_left hdom) k)) :=
  seriesSum_even_of_interleave_abs
    (seriesSum_congr (fun n => by
      rw [add_fn_toFun r r' n x (add_dom_left hdom) (add_dom_right hdom)]) habs)

/-- Technical lemma used in the public import closure. -/
def add_absSeriesSum_right {r r' : IntegrableRep S} {x : X}
    (hdom : (r.add r').MemAt x)
    (habs : RSeq.SeriesSum
      (fun n => COF.abs ((r.add r').valueAt x hdom n))) :
    RSeq.SeriesSum (fun k => COF.abs (r'.valueAt x (add_dom_right hdom) k)) :=
  seriesSum_odd_of_interleave_abs
    (seriesSum_congr (fun n => by
      rw [add_fn_toFun r r' n x (add_dom_left hdom) (add_dom_right hdom)]) habs)

/-- Technical lemma used in the public import closure. -/
def neg_absSeriesSum {r : IntegrableRep S} {x : X}
    (hdom : r.neg.MemAt x)
    (habs : RSeq.SeriesSum
      (fun n => COF.abs (r.neg.valueAt x hdom n))) :
    RSeq.SeriesSum (fun k => COF.abs (r.valueAt x (neg_dom hdom) k)) :=
  seriesSum_congr (fun n => by
    rw [neg_fn_toFun r n x (neg_dom hdom), COFO.abs_neg]) habs

/-- Technical lemma used in the public import closure. -/
theorem prop_1_11 {A : Set X} (hA : IsFull S A) (r r' : IntegrableRep S)
    (hle : ∀ x ∈ A, ∀ (hrdom : r.MemAt x) (hr'dom : r'.MemAt x)
            (hr : RSeq.SeriesSum (fun n => r.valueAt x hrdom n))
            (hr' : RSeq.SeriesSum (fun n => r'.valueAt x hr'dom n)),
            Le hr.sum hr'.sum) :
    Le r.integral r'.integral := by
  obtain ⟨h, hhA⟩ := lemma_1_10_full hA
  have hKnn : Nonneg ((r'.sub r).add (h.sub h)).integral := by
    show Nonneg ((r'.sub r).add (h.sub h)).seriesSum_I.sum
    refine lemma_1_7 S ((r'.sub r).add (h.sub h)).mem ((r'.sub r).add (h.sub h)).absConv
            ?_ ((r'.sub r).add (h.sub h)).seriesSum_I
    intro x hdomK habsK hKx
    let hsubRdom : (r'.sub r).MemAt x := add_dom_left hdomK
    let hsubHdom : (h.sub h).MemAt x := add_dom_right hdomK
    let hr'dom : r'.MemAt x := add_dom_left hsubRdom
    let hnegRdom : r.neg.MemAt x := add_dom_right hsubRdom
    let hrdom : r.MemAt x := neg_dom hnegRdom
    let hhdom : h.MemAt x := add_dom_left hsubHdom
    let hnegHdom : h.neg.MemAt x := add_dom_right hsubHdom
    have hsubRabs : RSeq.SeriesSum
        (fun k => COF.abs ((r'.sub r).valueAt x hsubRdom k)) :=
      add_absSeriesSum_left hdomK habsK
    have hsubHabs : RSeq.SeriesSum
        (fun k => COF.abs ((h.sub h).valueAt x hsubHdom k)) :=
      add_absSeriesSum_right hdomK habsK
    have hhabs : RSeq.SeriesSum (fun k => COF.abs (h.valueAt x hhdom k)) :=
      add_absSeriesSum_left hsubHdom hsubHabs
    have hxA : x ∈ A := hhA ⟨hhdom, ⟨hhabs⟩⟩
    have hr'v : RSeq.SeriesSum (fun n => r'.valueAt x hr'dom n) :=
      seriesSum_of_abs (add_absSeriesSum_left hsubRdom hsubRabs)
    have hrv : RSeq.SeriesSum (fun n => r.valueAt x hrdom n) :=
      seriesSum_of_abs
        (neg_absSeriesSum hnegRdom (add_absSeriesSum_right hsubRdom hsubRabs))
    have hhv : RSeq.SeriesSum (fun n => h.valueAt x hhdom n) :=
      seriesSum_of_abs hhabs
    let hsubRv := add_seriesSum_value hr'dom hnegRdom hr'v
      (neg_seriesSum_value hrdom hrv)
    let hsubHv := add_seriesSum_value hhdom hnegHdom hhv
      (neg_seriesSum_value hhdom hhv)
    let hKv := add_seriesSum_value hsubRdom hsubHdom hsubRv hsubHv
    rw [seriesSum_unique hKx hKv]
    show Nonneg ((hr'v.sum + (- hrv.sum)) + (hhv.sum + (- hhv.sum)))
    rw [show (hr'v.sum + (- hrv.sum)) + (hhv.sum + (- hhv.sum)) = hr'v.sum - hrv.sum from by ring]
    exact nonneg_sub_of_le (hle x hxA hrdom hr'dom hrv hr'v)
  rw [IntegrableRep.integral_add, IntegrableRep.integral_sub, IntegrableRep.integral_sub,
      show (r'.integral - r.integral) + (h.integral - h.integral) = r'.integral - r.integral
        from by ring] at hKnn
  exact le_of_nonneg_sub hKnn

/-- Technical lemma used in the public import closure. -/
theorem cor_1_12 {A : Set X} (hA : IsFull S A) (r r' : IntegrableRep S)
    (heq : ∀ x ∈ A, ∀ (hrdom : r.MemAt x) (hr'dom : r'.MemAt x)
            (hr : RSeq.SeriesSum (fun n => r.valueAt x hrdom n))
            (hr' : RSeq.SeriesSum (fun n => r'.valueAt x hr'dom n)),
            hr.sum = hr'.sum) :
    r.integral = r'.integral :=
  le_antisymm
    (prop_1_11 hA r r' (fun x hx hrdom hr'dom hr hr' => by
      rw [heq x hx hrdom hr'dom hr hr']; exact le_refl _))
    (prop_1_11 hA r' r (fun x hx hr'dom hrdom hr' hr => by
      rw [heq x hx hrdom hr'dom hr hr']; exact le_refl _))

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def seqMerge3 {α : Type*} (f g h : Nat → α) : Nat → α :=
  fun n => if n % 3 = 0 then f (n / 3) else if n % 3 = 1 then g (n / 3) else h (n / 3)

theorem natMod3 (n : Nat) :
    (∃ k, n = 3 * k) ∨ (∃ k, n = 3 * k + 1) ∨ (∃ k, n = 3 * k + 2) := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl ⟨n / 3, by omega⟩
  · exact Or.inr (Or.inl ⟨n / 3, by omega⟩)
  · exact Or.inr (Or.inr ⟨n / 3, by omega⟩)

theorem seqMerge3_zero {α : Type*} (f g h : Nat → α) (k : Nat) :
    seqMerge3 f g h (3 * k) = f k := by
  unfold seqMerge3; rw [if_pos (by omega : (3 * k) % 3 = 0)]; congr 1; omega

theorem seqMerge3_one {α : Type*} (f g h : Nat → α) (k : Nat) :
    seqMerge3 f g h (3 * k + 1) = g k := by
  unfold seqMerge3
  rw [if_neg (by omega : ¬ (3 * k + 1) % 3 = 0), if_pos (by omega : (3 * k + 1) % 3 = 1)]
  congr 1; omega

theorem seqMerge3_two {α : Type*} (f g h : Nat → α) (k : Nat) :
    seqMerge3 f g h (3 * k + 2) = h k := by
  unfold seqMerge3
  rw [if_neg (by omega : ¬ (3 * k + 2) % 3 = 0), if_neg (by omega : ¬ (3 * k + 2) % 3 = 1)]
  congr 1; omega

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.absDiffFn (r : IntegrableRep S) : Nat → BFunR X R
  | 0 => BFunR.absf (BFunR.seqSum r.fn 0)
  | (j+1) => BFunR.add (BFunR.absf (BFunR.seqSum r.fn (j+1)))
               (BFunR.smul (-1) (BFunR.absf (BFunR.seqSum r.fn j)))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.absDiffFn_mem (r : IntegrableRep S) :
    ∀ j, r.absDiffFn j ∈ S.L
  | 0 => S.abs_mem (S.toIntSpaceR.seqSum_mem r.mem 0)
  | (j+1) => S.add_mem (S.abs_mem (S.toIntSpaceR.seqSum_mem r.mem (j+1)))
               (S.smul_mem (-1) (S.abs_mem (S.toIntSpaceR.seqSum_mem r.mem j)))

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem partialSum_merge3_a (u v w : Nat → R) (N : Nat) :
    RSeq.partialSum (seqMerge3 u v w) (3 * N + 2)
      = RSeq.partialSum u N + RSeq.partialSum v N + RSeq.partialSum w N := by
  induction N with
  | zero =>
      show (seqMerge3 u v w 0 + seqMerge3 u v w 1) + seqMerge3 u v w 2 = u 0 + v 0 + w 0
      rw [seqMerge3_zero u v w 0, seqMerge3_one u v w 0, seqMerge3_two u v w 0]
  | succ N ih =>
      have e0 : seqMerge3 u v w (3 * N + 3) = u (N + 1) := by
        have := seqMerge3_zero u v w (N + 1); rwa [show 3 * (N + 1) = 3 * N + 3 from by ring] at this
      have e1 : seqMerge3 u v w (3 * N + 4) = v (N + 1) := by
        have := seqMerge3_one u v w (N + 1)
        rwa [show 3 * (N + 1) + 1 = 3 * N + 4 from by ring] at this
      have e2 : seqMerge3 u v w (3 * N + 5) = w (N + 1) := by
        have := seqMerge3_two u v w (N + 1)
        rwa [show 3 * (N + 1) + 2 = 3 * N + 5 from by ring] at this
      show (((RSeq.partialSum (seqMerge3 u v w) (3 * N + 2) + seqMerge3 u v w (3 * N + 3))
              + seqMerge3 u v w (3 * N + 4)) + seqMerge3 u v w (3 * N + 5))
         = RSeq.partialSum u (N + 1) + RSeq.partialSum v (N + 1) + RSeq.partialSum w (N + 1)
      rw [ih, e0, e1, e2]
      show (((RSeq.partialSum u N + RSeq.partialSum v N + RSeq.partialSum w N) + u (N + 1))
              + v (N + 1)) + w (N + 1)
         = (RSeq.partialSum u N + u (N + 1)) + (RSeq.partialSum v N + v (N + 1))
           + (RSeq.partialSum w N + w (N + 1))
      ring

/-- Technical lemma used in the public import closure. -/
theorem partialSum_merge3_b (u v w : Nat → R) (N : Nat) :
    RSeq.partialSum (seqMerge3 u v w) (3 * N + 3)
      = RSeq.partialSum u (N + 1) + RSeq.partialSum v N + RSeq.partialSum w N := by
  have e0 : seqMerge3 u v w (3 * N + 3) = u (N + 1) := by
    have := seqMerge3_zero u v w (N + 1); rwa [show 3 * (N + 1) = 3 * N + 3 from by ring] at this
  show RSeq.partialSum (seqMerge3 u v w) (3 * N + 2) + seqMerge3 u v w (3 * N + 3)
     = RSeq.partialSum u (N + 1) + RSeq.partialSum v N + RSeq.partialSum w N
  rw [partialSum_merge3_a u v w N, e0,
      show RSeq.partialSum u (N + 1) = RSeq.partialSum u N + u (N + 1) from rfl]
  ring

/-- Technical lemma used in the public import closure. -/
theorem partialSum_merge3_c (u v w : Nat → R) (N : Nat) :
    RSeq.partialSum (seqMerge3 u v w) (3 * N + 4)
      = RSeq.partialSum u (N + 1) + RSeq.partialSum v (N + 1) + RSeq.partialSum w N := by
  have e1 : seqMerge3 u v w (3 * N + 4) = v (N + 1) := by
    have := seqMerge3_one u v w (N + 1)
    rwa [show 3 * (N + 1) + 1 = 3 * N + 4 from by ring] at this
  show RSeq.partialSum (seqMerge3 u v w) (3 * N + 3) + seqMerge3 u v w (3 * N + 4)
     = RSeq.partialSum u (N + 1) + RSeq.partialSum v (N + 1) + RSeq.partialSum w N
  rw [partialSum_merge3_b u v w N, e1,
      show RSeq.partialSum v (N + 1) = RSeq.partialSum v N + v (N + 1) from rfl]
  ring

/-- Technical lemma used in the public import closure. -/
theorem close_of_three_close {pa pb pc su sv sw : R} (k : Nat)
    (ha : COF.lt (COF.abs (pa - su)) (COF.halfPow (k + 2)))
    (hb : COF.lt (COF.abs (pb - sv)) (COF.halfPow (k + 2)))
    (hc : COF.lt (COF.abs (pc - sw)) (COF.halfPow (k + 2))) :
    COF.lt (COF.abs ((pa + pb + pc) - (su + sv + sw))) (COF.halfPow k) := by
  have hab : COF.lt (COF.abs ((pa + pb) - (su + sv))) (COF.halfPow (k + 1)) :=
    close_of_two_close (k + 1) ha hb
  have hc' : COF.lt (COF.abs (pc - sw)) (COF.halfPow (k + 1)) :=
    lt_of_le_of_lt (le_of_lt hc) (halfPow_lt_succ (k + 1))
  have h := close_of_two_close k hab hc'
  rwa [show (pa + pb) + pc = pa + pb + pc from by ring,
       show (su + sv) + sw = su + sv + sw from by ring] at h

/-- Technical lemma used in the public import closure. -/
def seriesSum_merge3 {u v w : Nat → R}
    (hu : RSeq.SeriesSum u) (hv : RSeq.SeriesSum v) (hw : RSeq.SeriesSum w) :
    RSeq.SeriesSum (seqMerge3 u v w) where
  sum := hu.sum + hv.sum + hw.sum
  tends :=
    { mod := fun k =>
        3 * (hu.tends.mod (k + 2) + hv.tends.mod (k + 2) + hw.tends.mod (k + 2)) + 4
      close := by
        intro k m hm
        show COF.lt (COF.abs (RSeq.partialSum (seqMerge3 u v w) m - (hu.sum + hv.sum + hw.sum)))
              (COF.halfPow k)
        obtain ⟨N, hc2, hbu, hbv, hbw⟩ | ⟨N, hc3, hbu, hbv, hbw⟩ | ⟨N, hc4, hbu, hbv, hbw⟩ :
            (∃ N, m = 3 * N + 2 ∧ hu.tends.mod (k + 2) ≤ N ∧ hv.tends.mod (k + 2) ≤ N
                  ∧ hw.tends.mod (k + 2) ≤ N) ∨
            (∃ N, m = 3 * N + 3 ∧ hu.tends.mod (k + 2) ≤ N + 1 ∧ hv.tends.mod (k + 2) ≤ N
                  ∧ hw.tends.mod (k + 2) ≤ N) ∨
            (∃ N, m = 3 * N + 4 ∧ hu.tends.mod (k + 2) ≤ N + 1 ∧ hv.tends.mod (k + 2) ≤ N + 1
                  ∧ hw.tends.mod (k + 2) ≤ N) := by
          rcases natMod3 m with ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩
          · exact Or.inr (Or.inl ⟨t - 1, by omega, by omega, by omega, by omega⟩)
          · exact Or.inr (Or.inr ⟨t - 1, by omega, by omega, by omega, by omega⟩)
          · exact Or.inl ⟨t, by omega, by omega, by omega, by omega⟩
        · subst hc2
          rw [partialSum_merge3_a u v w N]
          exact close_of_three_close k (hu.tends.close (k + 2) N hbu)
                  (hv.tends.close (k + 2) N hbv) (hw.tends.close (k + 2) N hbw)
        · subst hc3
          rw [partialSum_merge3_b u v w N]
          exact close_of_three_close k (hu.tends.close (k + 2) (N + 1) hbu)
                  (hv.tends.close (k + 2) N hbv) (hw.tends.close (k + 2) N hbw)
        · subst hc4
          rw [partialSum_merge3_c u v w N]
          exact close_of_three_close k (hu.tends.close (k + 2) (N + 1) hbu)
                  (hv.tends.close (k + 2) (N + 1) hbv) (hw.tends.close (k + 2) N hbw) }

/-- Technical lemma used in the public import closure. -/
theorem seqMerge3_map {α β : Type*} (φ : α → β) (a b c : Nat → α) (n : Nat) :
    φ (seqMerge3 a b c n)
      = seqMerge3 (fun k => φ (a k)) (fun k => φ (b k)) (fun k => φ (c k)) n := by
  show φ (if n % 3 = 0 then a (n / 3) else if n % 3 = 1 then b (n / 3) else c (n / 3))
     = if n % 3 = 0 then φ (a (n / 3)) else if n % 3 = 1 then φ (b (n / 3)) else φ (c (n / 3))
  rw [apply_ite φ, apply_ite φ]

/-- Technical lemma used in the public import closure. -/
theorem I_absf_nonneg {g : BFunR X R} (hg : g ∈ S.L) : Nonneg (S.I (BFunR.absf g)) :=
  le_trans (abs_nonneg (S.I g)) (S.I_abs_ge hg)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.ofL_point_sum {g : BFunR X R} (hg : g ∈ S.L) (x : X)
    (hx : x ∈ g.dom)
    (hr : RSeq.SeriesSum (fun n => (IntegrableRep.ofL hg).valueAt x
      (IntegrableRep.ofL_memAt hg hx) n)) :
    hr.sum = g.toFun x hx := by
  have heq : ∀ n, (if n = 0 then g.toFun x hx else (0:R)) =
      (IntegrableRep.ofL hg).valueAt x (IntegrableRep.ofL_memAt hg hx) n := by
    intro n
    show (if n = 0 then g.toFun x hx else (0:R)) =
      (if n = 0 then g else BFunR.smul (0:R) g).toFun x
        ((IntegrableRep.ofL_memAt hg hx) n)
    by_cases hn : n = 0
    · simp only [if_pos hn]
    · simp only [if_neg hn, BFunR.smul]
      ring
  exact seriesSum_unique hr
    (seriesSum_congr heq (seriesSum_single (g.toFun x hx)))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.absDiffFn_abs_le (r : IntegrableRep S) (j : Nat) (x : X)
    (hdiff : x ∈ (r.absDiffFn j).dom) (hfn : x ∈ (r.fn j).dom) :
    Le (COF.abs ((r.absDiffFn j).toFun x hdiff))
      (COF.abs ((r.fn j).toFun x hfn)) := by
  cases j with
  | zero =>
      show Le (COF.abs (COF.abs ((BFunR.seqSum r.fn 0).toFun x hdiff)))
        (COF.abs ((r.fn 0).toFun x hfn))
      rw [show (BFunR.seqSum r.fn 0).toFun x hdiff =
            (r.fn 0).toFun x hfn from rfl,
          COFO.abs_of_nonneg (abs_nonneg ((r.fn 0).toFun x hfn))]
      exact le_refl _
  | succ j =>
      let s1 := (BFunR.seqSum r.fn (j + 1)).toFun x hdiff.1
      let s0 := (BFunR.seqSum r.fn j).toFun x hdiff.2
      let fj := (r.fn (j + 1)).toFun x hfn
      show Le (COF.abs (COF.abs s1 + (-1) * COF.abs s0)) (COF.abs fj)
      rw [show COF.abs s1 + (-1) * COF.abs s0 =
            COF.abs s1 - COF.abs s0 from by ring]
      have h := abs_abs_sub_abs_le s1 s0
      rwa [show s1 - s0 = fj from by
            show (BFunR.seqSum r.fn j).toFun x hdiff.1.1 +
                (r.fn (j + 1)).toFun x hdiff.1.2 -
                (BFunR.seqSum r.fn j).toFun x hdiff.2 =
                (r.fn (j + 1)).toFun x hfn
            ring] at h

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.I_absDiffFn_le (r : IntegrableRep S) (j : Nat) :
    Le (S.I (BFunR.absf (r.absDiffFn j))) (S.I (BFunR.absf (r.fn j))) := by
  rw [← IntegrableRep.ofL_integral (S.abs_mem (r.absDiffFn_mem j)),
      ← IntegrableRep.ofL_integral (S.abs_mem (r.mem j))]
  refine prop_1_11 isFull_univ
    (IntegrableRep.ofL (S.abs_mem (r.absDiffFn_mem j)))
    (IntegrableRep.ofL (S.abs_mem (r.mem j))) ?_
  intro x _ hrdiffdom hrfndom hr hr'
  let hdiff := IntegrableRep.ofL_dom
    (S.abs_mem (r.absDiffFn_mem j)) hrdiffdom
  let hfn := IntegrableRep.ofL_dom (S.abs_mem (r.mem j)) hrfndom
  rw [IntegrableRep.ofL_point_sum (S.abs_mem (r.absDiffFn_mem j)) x hdiff hr,
      IntegrableRep.ofL_point_sum (S.abs_mem (r.mem j)) x hfn hr']
  exact r.absDiffFn_abs_le j x hdiff hfn

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.absVal (r : IntegrableRep S) : IntegrableRep S where
  fn := seqMerge3 r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k))
  mem := by
    intro n
    rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [seqMerge3_zero]; exact r.absDiffFn_mem k
    · rw [seqMerge3_one]; exact r.mem k
    · rw [seqMerge3_two]; exact S.smul_mem (-1) (r.mem k)
  absConv := by
    have hmap : (fun n => S.I (BFunR.absf
                  (seqMerge3 r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) n)))
              = seqMerge3 (fun j => S.I (BFunR.absf (r.absDiffFn j)))
                  (fun k => S.I (BFunR.absf (r.fn k)))
                  (fun k => S.I (BFunR.absf (BFunR.smul (-1) (r.fn k)))) := by
      funext n
      exact seqMerge3_map (fun g => S.I (BFunR.absf g)) r.absDiffFn r.fn
              (fun k => BFunR.smul (-1) (r.fn k)) n
    show RSeq.SeriesSum (fun n => S.I (BFunR.absf
            (seqMerge3 r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) n)))
    rw [hmap]
    refine seriesSum_comparison ?_ ?_ (seriesSum_merge3 r.absConv r.absConv r.absConv)
    · intro n
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [seqMerge3_zero]; exact I_absf_nonneg (r.absDiffFn_mem k)
      · rw [seqMerge3_one]; exact I_absf_nonneg (r.mem k)
      · rw [seqMerge3_two]; exact I_absf_nonneg (S.smul_mem (-1) (r.mem k))
    · intro n
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [seqMerge3_zero, seqMerge3_zero]; exact r.I_absDiffFn_le k
      · rw [seqMerge3_one, seqMerge3_one]; exact le_refl _
      · rw [seqMerge3_two, seqMerge3_two, I_absf_neg_eq S (r.mem k)]; exact le_refl _

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.partialSum_absDiffFn_I (r : IntegrableRep S) (N : Nat) :
    RSeq.partialSum (fun j => S.I (r.absDiffFn j)) N
      = S.I (BFunR.absf (BFunR.seqSum r.fn N)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show RSeq.partialSum (fun j => S.I (r.absDiffFn j)) N + S.I (r.absDiffFn (N + 1))
         = S.I (BFunR.absf (BFunR.seqSum r.fn (N + 1)))
      rw [ih,
          show S.I (r.absDiffFn (N + 1))
             = S.I (BFunR.absf (BFunR.seqSum r.fn (N + 1)))
               - S.I (BFunR.absf (BFunR.seqSum r.fn N)) from
            S.toIntSpaceR.I_sub (S.abs_mem (S.toIntSpaceR.seqSum_mem r.mem (N + 1)))
              (S.abs_mem (S.toIntSpaceR.seqSum_mem r.mem N))]
      ring

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.seriesSum_absDiffFn_I (r : IntegrableRep S) :
    RSeq.SeriesSum (fun j => S.I (r.absDiffFn j)) :=
  seriesSum_of_abs
    (seriesSum_comparison (fun _ => abs_nonneg _)
      (fun j => S.I_abs_ge (r.absDiffFn_mem j))
      (seriesSum_comparison (fun j => I_absf_nonneg (r.absDiffFn_mem j))
        (fun j => r.I_absDiffFn_le j) r.absConv))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.absVal_integral_eq (r : IntegrableRep S) :
    r.absVal.integral = r.seriesSum_absDiffFn_I.sum := by
  have hneg : RSeq.SeriesSum (fun k => S.I (BFunR.smul (-1) (r.fn k))) :=
    seriesSum_congr (fun k => (S.toIntSpaceR.I_neg (r.mem k)).symm) (seriesSum_neg r.seriesSum_I)
  have hmap : ∀ n, S.I (r.absVal.fn n)
            = seqMerge3 (fun j => S.I (r.absDiffFn j)) (fun k => S.I (r.fn k))
                (fun k => S.I (BFunR.smul (-1) (r.fn k))) n := by
    intro n
    show S.I (seqMerge3 r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) n)
       = seqMerge3 (fun j => S.I (r.absDiffFn j)) (fun k => S.I (r.fn k))
           (fun k => S.I (BFunR.smul (-1) (r.fn k))) n
    exact seqMerge3_map S.I r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) n
  show r.absVal.seriesSum_I.sum = r.seriesSum_absDiffFn_I.sum
  rw [seriesSum_sum_congr hmap r.absVal.seriesSum_I
        (seriesSum_merge3 r.seriesSum_absDiffFn_I r.seriesSum_I hneg)]
  show r.seriesSum_absDiffFn_I.sum + r.seriesSum_I.sum + hneg.sum = r.seriesSum_absDiffFn_I.sum
  have hns : hneg.sum = - r.seriesSum_I.sum :=
    (seriesSum_sum_congr (fun k => S.toIntSpaceR.I_neg (r.mem k)) hneg
      (seriesSum_neg r.seriesSum_I)).trans (by rfl)
  rw [hns]; ring

/-- Technical lemma used in the public import closure. -/
def lemma_1_8 (r : IntegrableRep S) :
    RSeq.TendstoHalf (fun N => S.I (BFunR.absf (BFunR.seqSum r.fn N))) r.absVal.integral := by
  rw [r.absVal_integral_eq]
  refine { mod := r.seriesSum_absDiffFn_I.tends.mod, close := ?_ }
  intro k N hN
  have h := r.seriesSum_absDiffFn_I.tends.close k N hN
  rwa [r.partialSum_absDiffFn_I N] at h

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def tendstoHalf_abs {u : Nat → R} {l : R} (h : RSeq.TendstoHalf u l) :
    RSeq.TendstoHalf (fun n => COF.abs (u n)) (COF.abs l) :=
  { mod := h.mod
    close := by
      intro k n hn
      show COF.lt (COF.abs (COF.abs (u n) - COF.abs l)) (COF.halfPow k)
      exact lt_of_le_of_lt (abs_abs_sub_abs_le (u n) l) (h.close k n hn) }

/-- Domain membership for every absolute-value telescope difference. -/
theorem IntegrableRep.absDiffFn_memAt {r : IntegrableRep S} {x : X}
    (hdom : r.MemAt x) : ∀ j, x ∈ (r.absDiffFn j).dom := by
  intro j
  cases j with
  | zero => exact BFunR.seqSum_mem r.fn x hdom 0
  | succ j => exact ⟨BFunR.seqSum_mem r.fn x hdom (j + 1),
      BFunR.seqSum_mem r.fn x hdom j⟩

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.partialSum_absDiffFn_value (r : IntegrableRep S) (x : X)
    (hdom : r.MemAt x) (N : Nat) :
    RSeq.partialSum
        (fun j => (r.absDiffFn j).toFun x (r.absDiffFn_memAt hdom j)) N =
      COF.abs ((BFunR.seqSum r.fn N).toFun x
        (BFunR.seqSum_mem r.fn x hdom N)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show RSeq.partialSum
          (fun j => (r.absDiffFn j).toFun x (r.absDiffFn_memAt hdom j)) N +
          (r.absDiffFn (N + 1)).toFun x (r.absDiffFn_memAt hdom (N + 1)) =
        COF.abs ((BFunR.seqSum r.fn (N + 1)).toFun x
          (BFunR.seqSum_mem r.fn x hdom (N + 1)))
      rw [ih]
      show COF.abs ((BFunR.seqSum r.fn N).toFun x
              (BFunR.seqSum_mem r.fn x hdom N)) +
            (COF.abs ((BFunR.seqSum r.fn (N + 1)).toFun x
              (BFunR.seqSum_mem r.fn x hdom (N + 1))) +
             (-1) * COF.abs ((BFunR.seqSum r.fn N).toFun x
              (BFunR.seqSum_mem r.fn x hdom N))) =
        COF.abs ((BFunR.seqSum r.fn (N + 1)).toFun x
          (BFunR.seqSum_mem r.fn x hdom (N + 1)))
      ring

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.absVal_value (r : IntegrableRep S) (x : X)
    (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { hd : RSeq.SeriesSum (fun j => (r.absDiffFn j).toFun x
        (r.absDiffFn_memAt hdom j)) // hd.sum = COF.abs hx.sum } :=
  ⟨{ sum := COF.abs hx.sum
     tends :=
       { mod := (tendstoHalf_abs hx.tends).mod
         close := by
           intro k N hN
           have h := (tendstoHalf_abs hx.tends).close k N hN
           rw [r.partialSum_absDiffFn_value x hdom N,
             BFunR.seqSum_toFun r.fn x hdom N]
           exact h } },
   rfl⟩

/-- Technical lemma used in the public import closure. -/
theorem mem_seqSum_dom {r : IntegrableRep S} {x : X} (hdom : ∀ k, x ∈ (r.fn k).dom) :
    ∀ m, x ∈ (BFunR.seqSum r.fn m).dom :=
  BFunR.seqSum_mem r.fn x hdom

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.mem_absDiffFn_dom {r : IntegrableRep S} {x : X}
    (hdom : ∀ k, x ∈ (r.fn k).dom) : ∀ j, x ∈ (r.absDiffFn j).dom :=
  r.absDiffFn_memAt hdom

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.mem_absVal_dom {r : IntegrableRep S} {x : X}
    (hdom : ∀ k, x ∈ (r.fn k).dom) : ∀ n, x ∈ (r.absVal.fn n).dom := by
  intro n
  rcases natMod3 n with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show r.absVal.fn (3 * m) = r.absDiffFn m from
          seqMerge3_zero r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact mem_absDiffFn_dom hdom m
  · rw [show r.absVal.fn (3 * m + 1) = r.fn m from
          seqMerge3_one r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact hdom m
  · rw [show r.absVal.fn (3 * m + 2) = BFunR.smul (-1) (r.fn m) from
          seqMerge3_two r.absDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact hdom m

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.absVal_absSeries (r : IntegrableRep S) {x : X}
    (hdom : r.MemAt x)
    (hconv : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hdom n))) :
    RSeq.SeriesSum (fun n => COF.abs ((r.absVal.fn n).toFun x
      (r.mem_absVal_dom hdom n))) := by
  have ad : RSeq.SeriesSum (fun j => COF.abs ((r.absDiffFn j).toFun x
      (r.mem_absDiffFn_dom hdom j))) :=
    seriesSum_comparison (fun _ => abs_nonneg _)
      (fun j => r.absDiffFn_abs_le j x (r.mem_absDiffFn_dom hdom j) (hdom j)) hconv
  have anf : RSeq.SeriesSum (fun k => COF.abs
      ((BFunR.smul (-1) (r.fn k)).toFun x (hdom k))) :=
    seriesSum_congr (fun k => by
      show COF.abs (r.valueAt x hdom k) =
        COF.abs ((-1) * r.valueAt x hdom k)
      rw [show (-1 : R) * r.valueAt x hdom k =
        - r.valueAt x hdom k from by ring, COFO.abs_neg]) hconv
  have key : ∀ n,
      seqMerge3
          (fun j => COF.abs ((r.absDiffFn j).toFun x
            (r.mem_absDiffFn_dom hdom j)))
          (fun k => COF.abs (r.valueAt x hdom k))
          (fun k => COF.abs ((BFunR.smul (-1) (r.fn k)).toFun x (hdom k))) n =
        COF.abs ((r.absVal.fn n).toFun x (r.mem_absVal_dom hdom n)) := by
    intro n
    rcases natMod3 n with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · simp only [seqMerge3_zero]
      show COF.abs ((r.absDiffFn m).toFun x (r.mem_absDiffFn_dom hdom m)) =
        COF.abs ((seqMerge3 r.absDiffFn r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m)).toFun x
            (r.mem_absVal_dom hdom (3 * m)))
      simp only [seqMerge3_zero]
    · simp only [seqMerge3_one]
      show COF.abs (r.valueAt x hdom m) =
        COF.abs ((seqMerge3 r.absDiffFn r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m + 1)).toFun x
            (r.mem_absVal_dom hdom (3 * m + 1)))
      simp only [seqMerge3_one, IntegrableRep.valueAt]
    · simp only [seqMerge3_two]
      show COF.abs ((BFunR.smul (-1) (r.fn m)).toFun x (hdom m)) =
        COF.abs ((seqMerge3 r.absDiffFn r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m + 2)).toFun x
            (r.mem_absVal_dom hdom (3 * m + 2)))
      simp only [seqMerge3_two]
  exact seriesSum_congr key (seriesSum_merge3 ad hconv anf)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.domain_subset_absVal_domain (r : IntegrableRep S) :
    r.domain ⊆ r.absVal.domain := by
  intro x hx
  obtain ⟨hdom, ⟨hconv⟩⟩ := hx
  exact ⟨mem_absVal_dom hdom, ⟨r.absVal_absSeries hdom hconv⟩⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.normL1 (r : IntegrableRep S) : R := r.absVal.integral

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.normL1_nonneg (r : IntegrableRep S) : Nonneg r.normL1 := by
  show Nonneg r.absVal.integral
  rw [r.absVal_integral_eq]
  refine nonneg_of_tendstoHalf_nonnegseq _ (fun N => ?_) r.seriesSum_absDiffFn_I.tends
  rw [r.partialSum_absDiffFn_I N]
  exact I_absf_nonneg (S.toIntSpaceR.seqSum_mem r.mem N)

/-- Technical lemma used in the public import closure. -/
theorem Le_of_tendstoHalf_le {u v : Nat → R} {a b : R}
    (hu : RSeq.TendstoHalf u a) (hv : RSeq.TendstoHalf v b)
    (hle : ∀ n, Le (u n) (v n)) : Le a b := by
  intro hlt
  have hpos : COF.lt 0 (a - b) := by
    have t := neg_pos_of_neg (sub_neg_of_lt hlt)
    rwa [show -(b - a) = a - b from by ring] at t
  obtain ⟨k, hk⟩ := COFO.archimedean _ hpos
  set N := max (hu.mod (k + 1)) (hv.mod (k + 1)) with hN
  have hcu : COF.lt (COF.abs (u N - a)) (COF.halfPow (k + 1)) :=
    hu.close (k + 1) N (le_max_left _ _)
  have hcv : COF.lt (COF.abs (v N - b)) (COF.halfPow (k + 1)) :=
    hv.close (k + 1) N (le_max_right _ _)
  have e1 : COF.lt (a - u N) (COF.halfPow (k + 1)) := by
    refine lt_of_le_of_lt (COFO.le_abs_self (a - u N)) ?_
    rw [show COF.abs (a - u N) = COF.abs (u N - a) from by
          rw [show a - u N = -(u N - a) from by ring, COFO.abs_neg]]
    exact hcu
  have e3 : COF.lt (v N - b) (COF.halfPow (k + 1)) :=
    lt_of_le_of_lt (COFO.le_abs_self (v N - b)) hcv
  have e13 : COF.lt ((a - u N) + (v N - b)) (COF.halfPow k) := by
    have t := lt_add e1 e3
    rwa [halfPow_succ_add] at t
  have e2 : Le (a - b) ((a - u N) + (v N - b)) := by
    apply le_of_nonneg_sub
    rw [show ((a - u N) + (v N - b)) - (a - b) = v N - u N from by ring]
    exact nonneg_sub_of_le (hle N)
  exact COF.lt_irrefl _ (COFO.lt_trans (lt_of_le_of_lt e2 e13) hk)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.integral_tendsto (r : IntegrableRep S) :
    RSeq.TendstoHalf (fun N => S.I (BFunR.seqSum r.fn N)) r.integral :=
  { mod := r.seriesSum_I.tends.mod
    close := by
      intro k N hN
      have h := r.seriesSum_I.tends.close k N hN
      rw [← S.toIntSpaceR.I_seqSum r.mem N] at h
      exact h }

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.abs_integral_le_normL1 (r : IntegrableRep S) :
    Le (COF.abs r.integral) r.normL1 :=
  Le_of_tendstoHalf_le (tendstoHalf_abs r.integral_tendsto) (lemma_1_8 r)
    (fun N => S.I_abs_ge (S.toIntSpaceR.seqSum_mem r.mem N))

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem seqSum_absf_dom_eq {r : IntegrableRep S} (N : Nat) :
    (BFunR.seqSum r.fn N).dom = (BFunR.seqSum (fun k => BFunR.absf (r.fn k)) N).dom := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show (BFunR.seqSum r.fn N).dom ∩ (r.fn (N + 1)).dom
         = (BFunR.seqSum (fun k => BFunR.absf (r.fn k)) N).dom ∩ (r.fn (N + 1)).dom
      rw [ih]

/-- Technical lemma used in the public import closure. -/
theorem abs_seqSum_le {r : IntegrableRep S} (x : X) (N : Nat)
    (hx : x ∈ (BFunR.seqSum r.fn N).dom) :
    Le (COF.abs ((BFunR.seqSum r.fn N).toFun x hx))
       ((BFunR.seqSum (fun k => BFunR.absf (r.fn k)) N).toFun x
        (seqSum_absf_dom_eq (r := r) N ▸ hx)) := by
  induction N with
  | zero => exact le_refl _
  | succ N ih =>
      show Le (COF.abs ((BFunR.seqSum r.fn N).toFun x hx.1 +
              (r.fn (N + 1)).toFun x hx.2))
            ((BFunR.seqSum (fun k => BFunR.absf (r.fn k)) N).toFun x
              (seqSum_absf_dom_eq (r := r) N ▸ hx.1) +
              COF.abs ((r.fn (N + 1)).toFun x hx.2))
      refine le_trans (COFO.abs_add_le _ _) ?_
      apply le_of_nonneg_sub
      rw [show ((BFunR.seqSum (fun k => BFunR.absf (r.fn k)) N).toFun x
                (seqSum_absf_dom_eq (r := r) N ▸ hx.1) +
                COF.abs ((r.fn (N + 1)).toFun x hx.2)) -
              (COF.abs ((BFunR.seqSum r.fn N).toFun x hx.1) +
                COF.abs ((r.fn (N + 1)).toFun x hx.2)) =
            (BFunR.seqSum (fun k => BFunR.absf (r.fn k)) N).toFun x
                (seqSum_absf_dom_eq (r := r) N ▸ hx.1) -
              COF.abs ((BFunR.seqSum r.fn N).toFun x hx.1) from by ring]
      exact nonneg_sub_of_le (ih hx.1)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.absSeqSum_pointwiseLE (r : IntegrableRep S) (N : Nat) :
    BFunR.PointwiseLE (BFunR.absf (BFunR.seqSum r.fn N))
      (BFunR.seqSum (fun k => BFunR.absf (r.fn k)) N) where
  dom_eq := seqSum_absf_dom_eq (r := r) N
  le_val := fun x hx => abs_seqSum_le x N hx

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.normL1_le_absConv (r : IntegrableRep S) : Le r.normL1 r.absConv.sum := by
  show Le r.absVal.integral r.absConv.sum
  rw [r.absVal_integral_eq]
  refine le_of_tendsto_le r.seriesSum_absDiffFn_I r.absConv.sum (fun N => ?_)
  rw [r.partialSum_absDiffFn_I N]
  refine le_trans (S.I_mono (S.abs_mem (S.toIntSpaceR.seqSum_mem r.mem N))
      (S.toIntSpaceR.seqSum_mem (fun k => S.abs_mem (r.mem k)) N)
      (r.absSeqSum_pointwiseLE N)) ?_
  rw [S.toIntSpaceR.I_seqSum (fun k => S.abs_mem (r.mem k)) N]
  exact partialSum_le_sum (fun k => I_absf_nonneg (r.mem k)) r.absConv N

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def seriesSum_tail {u : Nat → R} (h : RSeq.SeriesSum u) (p : Nat) :
    RSeq.SeriesSum (fun l => u (p + 1 + l)) where
  sum := h.sum - RSeq.partialSum u p
  tends :=
    { mod := h.tends.mod
      close := fun k M hM => by
        show COF.lt (COF.abs (RSeq.partialSum (fun l => u (p + 1 + l)) M
              - (h.sum - RSeq.partialSum u p))) (COF.halfPow k)
        rw [show RSeq.partialSum (fun l => u (p + 1 + l)) M - (h.sum - RSeq.partialSum u p)
              = RSeq.partialSum u (p + (M + 1)) - h.sum from by
              rw [partialSum_split u p M]; ring]
        exact h.tends.close k (p + (M + 1)) (by omega) }

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.tailFrom (r : IntegrableRep S) (p : Nat) : IntegrableRep S where
  fn := fun k => r.fn (p + 1 + k)
  mem := fun k => r.mem (p + 1 + k)
  absConv := seriesSum_tail r.absConv p

/-- Technical lemma used in the public import closure. -/
def lemma_1_15 (r : IntegrableRep S) :
    RSeq.TendstoHalf (fun p => (r.tailFrom p).normL1) 0 :=
  { mod := r.absConv.tends.mod
    close := fun k p hp => by
      show COF.lt (COF.abs ((r.tailFrom p).normL1 - 0)) (COF.halfPow k)
      rw [show (r.tailFrom p).normL1 - 0 = (r.tailFrom p).normL1 from by ring,
          COFO.abs_of_nonneg (r.tailFrom p).normL1_nonneg]
      refine lt_of_le_of_lt (r.tailFrom p).normL1_le_absConv ?_
      show COF.lt (r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) p)
            (COF.halfPow k)
      refine lt_of_le_of_lt (COFO.le_abs_self _) ?_
      rw [show COF.abs (r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) p)
            = COF.abs (RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) p - r.absConv.sum) from by
            rw [show r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) p
                  = -(RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) p - r.absConv.sum)
                  from by ring, COFO.abs_neg]]
      exact r.absConv.tends.close k p hp }

/-- Technical lemma used in the public import closure. -/
theorem cor_1_17 (r : IntegrableRep S) (k : Nat) :
    ∃ N, BFunR.seqSum r.fn N ∈ S.L ∧ COF.lt ((r.tailFrom N).normL1) (COF.halfPow k) := by
  refine ⟨r.absConv.tends.mod k, S.toIntSpaceR.seqSum_mem r.mem _, ?_⟩
  have h := (lemma_1_15 r).close k (r.absConv.tends.mod k) (Nat.le_refl _)
  have he : COF.abs ((r.tailFrom (r.absConv.tends.mod k)).normL1 - 0)
          = (r.tailFrom (r.absConv.tends.mod k)).normL1 := by
    rw [sub_zero]
    exact COFO.abs_of_nonneg (r.tailFrom (r.absConv.tends.mod k)).normL1_nonneg
  rw [← he]; exact h

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem abs_min_sub_min_le (a b c : R) :
    Le (COF.abs (COF.min a c - COF.min b c)) (COF.abs (a - b)) := by
  have hrev : Le (COF.abs (COF.abs (a - c) - COF.abs (b - c))) (COF.abs (a - b)) := by
    have h := abs_abs_sub_abs_le (a - c) (b - c)
    rwa [show (a - c) - (b - c) = a - b from by ring] at h
  have htri : Le (COF.abs ((a - b) - (COF.abs (a - c) - COF.abs (b - c))))
                 (COF.abs (a - b) + COF.abs (COF.abs (a - c) - COF.abs (b - c))) := by
    have h := COFO.abs_add_le (a - b) (-(COF.abs (a - c) - COF.abs (b - c)))
    rwa [show (a - b) + (-(COF.abs (a - c) - COF.abs (b - c)))
          = (a - b) - (COF.abs (a - c) - COF.abs (b - c)) from by ring,
        COFO.abs_neg] at h
  have hX : Le (COF.abs ((a - b) - (COF.abs (a - c) - COF.abs (b - c))))
               (COF.abs (a - b) + COF.abs (a - b)) :=
    le_trans htri (by
      apply le_of_nonneg_sub
      rw [show (COF.abs (a - b) + COF.abs (a - b))
            - (COF.abs (a - b) + COF.abs (COF.abs (a - c) - COF.abs (b - c)))
          = COF.abs (a - b) - COF.abs (COF.abs (a - c) - COF.abs (b - c)) from by ring]
      exact nonneg_sub_of_le hrev)
  have hfinal : COF.half * (COF.abs (a - b) + COF.abs (a - b)) = COF.abs (a - b) := by
    rw [show COF.half * (COF.abs (a - b) + COF.abs (a - b))
          = (COF.half + COF.half) * COF.abs (a - b) from by ring, COF.half_add_half, one_mul]
  rw [COF.min_halfsum a c, COF.min_halfsum b c,
      show COF.half * (a + c - COF.abs (a - c)) - COF.half * (b + c - COF.abs (b - c))
        = COF.half * ((a - b) - (COF.abs (a - c) - COF.abs (b - c))) from by ring,
      COFO.abs_mul, COFO.abs_of_nonneg (le_of_lt COFO.half_pos), ← hfinal]
  exact mul_le_mul_left hX (le_of_lt COFO.half_pos)

/-- min(0,1)=0(min_halfsum 0 1=½(0+1−|0−1|), |0−1|=|−1|=1)。 -/
theorem min_zero_one : COF.min (0 : R) 1 = 0 := by
  rw [COF.min_halfsum,
      show (0:R) - 1 = -(1) from by ring, COFO.abs_neg,
      COFO.abs_of_nonneg (le_of_lt COFO.one_pos),
      show (0:R) + 1 - 1 = 0 from by ring, mul_zero]

/-- Technical lemma used in the public import closure. -/
theorem abs_min_one_le (a : R) : Le (COF.abs (COF.min a 1)) (COF.abs a) := by
  have h := abs_min_sub_min_le a 0 1
  rwa [min_zero_one, sub_zero, sub_zero] at h

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.minDiffFn (r : IntegrableRep S) : Nat → BFunR X R
  | 0 => BFunR.cutConst (BFunR.seqSum r.fn 0) 1
  | (j+1) => BFunR.add (BFunR.cutConst (BFunR.seqSum r.fn (j+1)) 1)
               (BFunR.smul (-1) (BFunR.cutConst (BFunR.seqSum r.fn j) 1))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.minDiffFn_mem (r : IntegrableRep S) :
    ∀ j, r.minDiffFn j ∈ S.L
  | 0 => S.cutConst_mem 1 (S.toIntSpaceR.seqSum_mem r.mem 0)
  | (j+1) => S.add_mem (S.cutConst_mem 1 (S.toIntSpaceR.seqSum_mem r.mem (j+1)))
               (S.smul_mem (-1) (S.cutConst_mem 1 (S.toIntSpaceR.seqSum_mem r.mem j)))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.minDiffFn_abs_le (r : IntegrableRep S) (j : Nat) (x : X)
    (hdiff : x ∈ (r.minDiffFn j).dom) (hfn : x ∈ (r.fn j).dom) :
    Le (COF.abs ((r.minDiffFn j).toFun x hdiff))
      (COF.abs ((r.fn j).toFun x hfn)) := by
  cases j with
  | zero =>
      show Le (COF.abs (COF.min ((BFunR.seqSum r.fn 0).toFun x hdiff) 1))
        (COF.abs ((r.fn 0).toFun x hfn))
      rw [show (BFunR.seqSum r.fn 0).toFun x hdiff =
        (r.fn 0).toFun x hfn from rfl]
      exact abs_min_one_le ((r.fn 0).toFun x hfn)
  | succ j =>
      let s1 := (BFunR.seqSum r.fn (j + 1)).toFun x hdiff.1
      let s0 := (BFunR.seqSum r.fn j).toFun x hdiff.2
      let fj := (r.fn (j + 1)).toFun x hfn
      show Le (COF.abs (COF.min s1 1 + (-1) * COF.min s0 1)) (COF.abs fj)
      rw [show COF.min s1 1 + (-1) * COF.min s0 1 =
        COF.min s1 1 - COF.min s0 1 from by ring]
      have h := abs_min_sub_min_le s1 s0 1
      rwa [show s1 - s0 = fj from by
            show (BFunR.seqSum r.fn j).toFun x hdiff.1.1 +
                (r.fn (j + 1)).toFun x hdiff.1.2 -
                (BFunR.seqSum r.fn j).toFun x hdiff.2 =
              (r.fn (j + 1)).toFun x hfn
            ring] at h

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.I_minDiffFn_le (r : IntegrableRep S) (j : Nat) :
    Le (S.I (BFunR.absf (r.minDiffFn j))) (S.I (BFunR.absf (r.fn j))) := by
  rw [← IntegrableRep.ofL_integral (S.abs_mem (r.minDiffFn_mem j)),
      ← IntegrableRep.ofL_integral (S.abs_mem (r.mem j))]
  refine prop_1_11 isFull_univ
    (IntegrableRep.ofL (S.abs_mem (r.minDiffFn_mem j)))
    (IntegrableRep.ofL (S.abs_mem (r.mem j))) ?_
  intro x _ hrdiffdom hrfndom hr hr'
  let hdiff := IntegrableRep.ofL_dom (S.abs_mem (r.minDiffFn_mem j)) hrdiffdom
  let hfn := IntegrableRep.ofL_dom (S.abs_mem (r.mem j)) hrfndom
  rw [IntegrableRep.ofL_point_sum (S.abs_mem (r.minDiffFn_mem j)) x hdiff hr,
      IntegrableRep.ofL_point_sum (S.abs_mem (r.mem j)) x hfn hr']
  exact r.minDiffFn_abs_le j x hdiff hfn

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.minVal (r : IntegrableRep S) : IntegrableRep S where
  fn := seqMerge3 r.minDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k))
  mem := by
    intro n
    rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [seqMerge3_zero]; exact r.minDiffFn_mem k
    · rw [seqMerge3_one]; exact r.mem k
    · rw [seqMerge3_two]; exact S.smul_mem (-1) (r.mem k)
  absConv := by
    have hmap : (fun n => S.I (BFunR.absf
                  (seqMerge3 r.minDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) n)))
              = seqMerge3 (fun j => S.I (BFunR.absf (r.minDiffFn j)))
                  (fun k => S.I (BFunR.absf (r.fn k)))
                  (fun k => S.I (BFunR.absf (BFunR.smul (-1) (r.fn k)))) := by
      funext n
      exact seqMerge3_map (fun g => S.I (BFunR.absf g)) r.minDiffFn r.fn
              (fun k => BFunR.smul (-1) (r.fn k)) n
    show RSeq.SeriesSum (fun n => S.I (BFunR.absf
            (seqMerge3 r.minDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) n)))
    rw [hmap]
    refine seriesSum_comparison ?_ ?_ (seriesSum_merge3 r.absConv r.absConv r.absConv)
    · intro n
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [seqMerge3_zero]; exact I_absf_nonneg (r.minDiffFn_mem k)
      · rw [seqMerge3_one]; exact I_absf_nonneg (r.mem k)
      · rw [seqMerge3_two]; exact I_absf_nonneg (S.smul_mem (-1) (r.mem k))
    · intro n
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [seqMerge3_zero, seqMerge3_zero]; exact r.I_minDiffFn_le k
      · rw [seqMerge3_one, seqMerge3_one]; exact le_refl _
      · rw [seqMerge3_two, seqMerge3_two, I_absf_neg_eq S (r.mem k)]; exact le_refl _

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def tendstoHalf_min_one {u : Nat → R} {l : R} (h : RSeq.TendstoHalf u l) :
    RSeq.TendstoHalf (fun n => COF.min (u n) 1) (COF.min l 1) :=
  { mod := h.mod
    close := by
      intro k n hn
      show COF.lt (COF.abs (COF.min (u n) 1 - COF.min l 1)) (COF.halfPow k)
      exact lt_of_le_of_lt (abs_min_sub_min_le (u n) l 1) (h.close k n hn) }

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.minDiffFn_memAt {r : IntegrableRep S} {x : X}
    (hdom : r.MemAt x) : ∀ j, x ∈ (r.minDiffFn j).dom := by
  intro j
  cases j with
  | zero => exact BFunR.seqSum_mem r.fn x hdom 0
  | succ j => exact ⟨BFunR.seqSum_mem r.fn x hdom (j + 1),
      BFunR.seqSum_mem r.fn x hdom j⟩

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.partialSum_minDiffFn_value (r : IntegrableRep S) (x : X)
    (hdom : r.MemAt x) (N : Nat) :
    RSeq.partialSum
        (fun j => (r.minDiffFn j).toFun x (r.minDiffFn_memAt hdom j)) N =
      COF.min ((BFunR.seqSum r.fn N).toFun x
        (BFunR.seqSum_mem r.fn x hdom N)) 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show RSeq.partialSum
          (fun j => (r.minDiffFn j).toFun x (r.minDiffFn_memAt hdom j)) N +
          (r.minDiffFn (N + 1)).toFun x (r.minDiffFn_memAt hdom (N + 1)) =
        COF.min ((BFunR.seqSum r.fn (N + 1)).toFun x
          (BFunR.seqSum_mem r.fn x hdom (N + 1))) 1
      rw [ih]
      show COF.min ((BFunR.seqSum r.fn N).toFun x
              (BFunR.seqSum_mem r.fn x hdom N)) 1 +
            (COF.min ((BFunR.seqSum r.fn (N + 1)).toFun x
              (BFunR.seqSum_mem r.fn x hdom (N + 1))) 1 +
             (-1) * COF.min ((BFunR.seqSum r.fn N).toFun x
              (BFunR.seqSum_mem r.fn x hdom N)) 1) =
        COF.min ((BFunR.seqSum r.fn (N + 1)).toFun x
          (BFunR.seqSum_mem r.fn x hdom (N + 1))) 1
      ring

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.minVal_value (r : IntegrableRep S) (x : X)
    (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { hd : RSeq.SeriesSum (fun j => (r.minDiffFn j).toFun x
        (r.minDiffFn_memAt hdom j)) // hd.sum = COF.min hx.sum 1 } :=
  ⟨{ sum := COF.min hx.sum 1
     tends :=
       { mod := (tendstoHalf_min_one hx.tends).mod
         close := by
           intro k N hN
           have h := (tendstoHalf_min_one hx.tends).close k N hN
           rw [r.partialSum_minDiffFn_value x hdom N,
             BFunR.seqSum_toFun r.fn x hdom N]
           exact h } },
   rfl⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.mem_minDiffFn_dom {r : IntegrableRep S} {x : X}
    (hdom : ∀ k, x ∈ (r.fn k).dom) : ∀ j, x ∈ (r.minDiffFn j).dom :=
  r.minDiffFn_memAt hdom

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.mem_minVal_dom {r : IntegrableRep S} {x : X}
    (hdom : ∀ k, x ∈ (r.fn k).dom) : ∀ n, x ∈ (r.minVal.fn n).dom := by
  intro n
  rcases natMod3 n with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show r.minVal.fn (3 * m) = r.minDiffFn m from
          seqMerge3_zero r.minDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact mem_minDiffFn_dom hdom m
  · rw [show r.minVal.fn (3 * m + 1) = r.fn m from
          seqMerge3_one r.minDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact hdom m
  · rw [show r.minVal.fn (3 * m + 2) = BFunR.smul (-1) (r.fn m) from
          seqMerge3_two r.minDiffFn r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact hdom m

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.minVal_absSeries (r : IntegrableRep S) {x : X}
    (hdom : r.MemAt x)
    (hconv : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hdom n))) :
    RSeq.SeriesSum (fun n => COF.abs ((r.minVal.fn n).toFun x
      (r.mem_minVal_dom hdom n))) := by
  have ad : RSeq.SeriesSum (fun j => COF.abs ((r.minDiffFn j).toFun x
      (r.mem_minDiffFn_dom hdom j))) :=
    seriesSum_comparison (fun _ => abs_nonneg _)
      (fun j => r.minDiffFn_abs_le j x (r.mem_minDiffFn_dom hdom j) (hdom j)) hconv
  have anf : RSeq.SeriesSum (fun k => COF.abs
      ((BFunR.smul (-1) (r.fn k)).toFun x (hdom k))) :=
    seriesSum_congr (fun k => by
      show COF.abs (r.valueAt x hdom k) =
        COF.abs ((-1) * r.valueAt x hdom k)
      rw [show (-1 : R) * r.valueAt x hdom k =
        - r.valueAt x hdom k from by ring, COFO.abs_neg]) hconv
  have key : ∀ n,
      seqMerge3
          (fun j => COF.abs ((r.minDiffFn j).toFun x
            (r.mem_minDiffFn_dom hdom j)))
          (fun k => COF.abs (r.valueAt x hdom k))
          (fun k => COF.abs ((BFunR.smul (-1) (r.fn k)).toFun x (hdom k))) n =
        COF.abs ((r.minVal.fn n).toFun x (r.mem_minVal_dom hdom n)) := by
    intro n
    rcases natMod3 n with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · simp only [seqMerge3_zero]
      show COF.abs ((r.minDiffFn m).toFun x (r.mem_minDiffFn_dom hdom m)) =
        COF.abs ((seqMerge3 r.minDiffFn r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m)).toFun x
            (r.mem_minVal_dom hdom (3 * m)))
      simp only [seqMerge3_zero]
    · simp only [seqMerge3_one]
      show COF.abs (r.valueAt x hdom m) =
        COF.abs ((seqMerge3 r.minDiffFn r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m + 1)).toFun x
            (r.mem_minVal_dom hdom (3 * m + 1)))
      simp only [seqMerge3_one, IntegrableRep.valueAt]
    · simp only [seqMerge3_two]
      show COF.abs ((BFunR.smul (-1) (r.fn m)).toFun x (hdom m)) =
        COF.abs ((seqMerge3 r.minDiffFn r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m + 2)).toFun x
            (r.mem_minVal_dom hdom (3 * m + 2)))
      simp only [seqMerge3_two]
  exact seriesSum_congr key (seriesSum_merge3 ad hconv anf)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.domain_subset_minVal_domain (r : IntegrableRep S) :
    r.domain ⊆ r.minVal.domain := by
  intro x hx
  obtain ⟨hdom, ⟨hconv⟩⟩ := hx
  exact ⟨mem_minVal_dom hdom, ⟨r.minVal_absSeries hdom hconv⟩⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.normalized_rep : {ρ : IntegrableRep S // ρ.integral = 1} :=
  ⟨IntegrableRep.ofL S.normalized.2.1,
   by rw [IntegrableRep.ofL_integral S.normalized.2.1]; exact S.normalized.2.2⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem min_zero_const {a : R} (ha : ¬ COF.lt a 0) : COF.min (0 : R) a = 0 := by
  rw [COF.min_halfsum,
      show (0:R) - a = -a from by ring, COFO.abs_neg, COFO.abs_of_nonneg ha,
      show (0:R) + a - a = 0 from by ring, mul_zero]

/-- Technical lemma used in the public import closure. -/
theorem abs_min_const_le {a : R} (ha : ¬ COF.lt a 0) (x : R) :
    Le (COF.abs (COF.min x a)) (COF.abs x) := by
  have h := abs_min_sub_min_le x 0 a
  rwa [min_zero_const ha, sub_zero, sub_zero] at h

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutConstDiffFn (r : IntegrableRep S) (a : R) : Nat → BFunR X R
  | 0 => BFunR.cutConst (BFunR.seqSum r.fn 0) a
  | (j+1) => BFunR.add (BFunR.cutConst (BFunR.seqSum r.fn (j+1)) a)
               (BFunR.smul (-1) (BFunR.cutConst (BFunR.seqSum r.fn j) a))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.cutConstDiffFn_mem (r : IntegrableRep S) (a : R) :
    ∀ j, r.cutConstDiffFn a j ∈ S.L
  | 0 => S.cutConst_mem a (S.toIntSpaceR.seqSum_mem r.mem 0)
  | (j+1) => S.add_mem (S.cutConst_mem a (S.toIntSpaceR.seqSum_mem r.mem (j+1)))
               (S.smul_mem (-1) (S.cutConst_mem a (S.toIntSpaceR.seqSum_mem r.mem j)))

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.cutConstDiffFn_abs_le (r : IntegrableRep S) (a : R) (ha : ¬ COF.lt a 0)
    (j : Nat) (x : X) (hdiff : x ∈ (r.cutConstDiffFn a j).dom)
    (hfn : x ∈ (r.fn j).dom) :
    Le (COF.abs ((r.cutConstDiffFn a j).toFun x hdiff))
      (COF.abs ((r.fn j).toFun x hfn)) := by
  cases j with
  | zero =>
      show Le (COF.abs (COF.min ((BFunR.seqSum r.fn 0).toFun x hdiff) a))
        (COF.abs ((r.fn 0).toFun x hfn))
      rw [show (BFunR.seqSum r.fn 0).toFun x hdiff =
        (r.fn 0).toFun x hfn from rfl]
      exact abs_min_const_le ha ((r.fn 0).toFun x hfn)
  | succ j =>
      let s1 := (BFunR.seqSum r.fn (j + 1)).toFun x hdiff.1
      let s0 := (BFunR.seqSum r.fn j).toFun x hdiff.2
      let fj := (r.fn (j + 1)).toFun x hfn
      show Le (COF.abs (COF.min s1 a + (-1) * COF.min s0 a)) (COF.abs fj)
      rw [show COF.min s1 a + (-1) * COF.min s0 a =
        COF.min s1 a - COF.min s0 a from by ring]
      have h := abs_min_sub_min_le s1 s0 a
      rwa [show s1 - s0 = fj from by
            show (BFunR.seqSum r.fn j).toFun x hdiff.1.1 +
                (r.fn (j + 1)).toFun x hdiff.1.2 -
                (BFunR.seqSum r.fn j).toFun x hdiff.2 =
              (r.fn (j + 1)).toFun x hfn
            ring] at h

/-- I(|m_j|) ≤ I(|f_j|)(ofL+prop_1_11 on isFull_univ)。 -/
theorem IntegrableRep.I_cutConstDiffFn_le (r : IntegrableRep S) (a : R) (ha : ¬ COF.lt a 0)
    (j : Nat) :
    Le (S.I (BFunR.absf (r.cutConstDiffFn a j))) (S.I (BFunR.absf (r.fn j))) := by
  rw [← IntegrableRep.ofL_integral (S.abs_mem (r.cutConstDiffFn_mem a j)),
      ← IntegrableRep.ofL_integral (S.abs_mem (r.mem j))]
  refine prop_1_11 isFull_univ
    (IntegrableRep.ofL (S.abs_mem (r.cutConstDiffFn_mem a j)))
    (IntegrableRep.ofL (S.abs_mem (r.mem j))) ?_
  intro x _ hrdiffdom hrfndom hr hr'
  let hdiff := IntegrableRep.ofL_dom
    (S.abs_mem (r.cutConstDiffFn_mem a j)) hrdiffdom
  let hfn := IntegrableRep.ofL_dom (S.abs_mem (r.mem j)) hrfndom
  rw [IntegrableRep.ofL_point_sum (S.abs_mem (r.cutConstDiffFn_mem a j)) x hdiff hr,
      IntegrableRep.ofL_point_sum (S.abs_mem (r.mem j)) x hfn hr']
  exact r.cutConstDiffFn_abs_le a ha j x hdiff hfn

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutConstVal (r : IntegrableRep S) (a : R) (ha : ¬ COF.lt a 0) : IntegrableRep S where
  fn := seqMerge3 (r.cutConstDiffFn a) r.fn (fun k => BFunR.smul (-1) (r.fn k))
  mem := by
    intro n
    rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [seqMerge3_zero]; exact r.cutConstDiffFn_mem a k
    · rw [seqMerge3_one]; exact r.mem k
    · rw [seqMerge3_two]; exact S.smul_mem (-1) (r.mem k)
  absConv := by
    have hmap : (fun n => S.I (BFunR.absf
                  (seqMerge3 (r.cutConstDiffFn a) r.fn (fun k => BFunR.smul (-1) (r.fn k)) n)))
              = seqMerge3 (fun j => S.I (BFunR.absf (r.cutConstDiffFn a j)))
                  (fun k => S.I (BFunR.absf (r.fn k)))
                  (fun k => S.I (BFunR.absf (BFunR.smul (-1) (r.fn k)))) := by
      funext n
      exact seqMerge3_map (fun g => S.I (BFunR.absf g)) (r.cutConstDiffFn a) r.fn
              (fun k => BFunR.smul (-1) (r.fn k)) n
    show RSeq.SeriesSum (fun n => S.I (BFunR.absf
            (seqMerge3 (r.cutConstDiffFn a) r.fn (fun k => BFunR.smul (-1) (r.fn k)) n)))
    rw [hmap]
    refine seriesSum_comparison ?_ ?_ (seriesSum_merge3 r.absConv r.absConv r.absConv)
    · intro n
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [seqMerge3_zero]; exact I_absf_nonneg (r.cutConstDiffFn_mem a k)
      · rw [seqMerge3_one]; exact I_absf_nonneg (r.mem k)
      · rw [seqMerge3_two]; exact I_absf_nonneg (S.smul_mem (-1) (r.mem k))
    · intro n
      rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rw [seqMerge3_zero, seqMerge3_zero]; exact r.I_cutConstDiffFn_le a ha k
      · rw [seqMerge3_one, seqMerge3_one]; exact le_refl _
      · rw [seqMerge3_two, seqMerge3_two, I_absf_neg_eq S (r.mem k)]; exact le_refl _

/-- Technical lemma used in the public import closure. -/
theorem natCast_nonneg (n : Nat) : ¬ COF.lt ((n : R)) 0 := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact COF.lt_irrefl 0
  | succ n ih =>
      rw [Nat.cast_succ]
      have hb : Le ((n : R)) ((n : R) + 1) := by
        apply le_of_nonneg_sub
        rw [show ((n : R) + 1) - (n : R) = 1 from by ring]
        exact le_of_lt COFO.one_pos
      exact le_trans ih hb

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutNatVal (r : IntegrableRep S) (n : Nat) : IntegrableRep S :=
  r.cutConstVal ((n : R)) (natCast_nonneg n)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.absVal_signed_value (r : IntegrableRep S) (x : X)
    (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { hs : RSeq.SeriesSum (fun n => r.absVal.valueAt x
        (r.mem_absVal_dom hdom) n) // hs.sum = COF.abs hx.sum } := by
  obtain ⟨hd, hdeq⟩ := r.absVal_value x hdom hx
  refine ⟨seriesSum_congr (fun n => ?_)
            (seriesSum_merge3 hd hx (seriesSum_smul (-1 : R) hx)), ?_⟩
  · rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_zero]
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, seqMerge3_one]
    · simp only [IntegrableRep.valueAt, IntegrableRep.absVal, BFunR.smul,
        seqMerge3_two]
  · show hd.sum + hx.sum + (-1) * hx.sum = COF.abs hx.sum
    rw [hdeq]; ring

/-- Technical lemma used in the public import closure. -/
theorem normL1_mono {A : Set X} (hA : IsFull S A) (u v : IntegrableRep S)
    (hle : ∀ x ∈ A, ∀ (hudom : u.MemAt x) (hvdom : v.MemAt x)
            (hu : RSeq.SeriesSum (fun n => u.valueAt x hudom n))
            (hv : RSeq.SeriesSum (fun n => v.valueAt x hvdom n)),
            Le (COF.abs hu.sum) (COF.abs hv.sum)) :
    Le u.normL1 v.normL1 := by
  show Le u.absVal.integral v.absVal.integral
  refine prop_1_11 (isFull_inter (isFull_inter hA u.domain_isFull) v.domain_isFull)
    u.absVal v.absVal ?_
  intro x hx huAbsDom hvAbsDom hr hr'
  obtain ⟨⟨hxA, hxu⟩, hxv⟩ := hx
  obtain ⟨hudom, ⟨huabs⟩⟩ := hxu
  obtain ⟨hvdom, ⟨hvabs⟩⟩ := hxv
  have hu := seriesSum_of_abs huabs
  have hv := seriesSum_of_abs hvabs
  obtain ⟨hsu, hsueq⟩ := u.absVal_signed_value x hudom hu
  obtain ⟨hsv, hsveq⟩ := v.absVal_signed_value x hvdom hv
  rw [seriesSum_unique hr hsu, seriesSum_unique hr' hsv, hsueq, hsveq]
  exact hle x hxA hudom hvdom hu hv

/-- Technical lemma used in the public import closure. -/
def tendstoHalf_min_const (a : R) {u : Nat → R} {l : R} (h : RSeq.TendstoHalf u l) :
    RSeq.TendstoHalf (fun n => COF.min (u n) a) (COF.min l a) :=
  { mod := h.mod
    close := by
      intro k n hn
      show COF.lt (COF.abs (COF.min (u n) a - COF.min l a)) (COF.halfPow k)
      exact lt_of_le_of_lt (abs_min_sub_min_le (u n) l a) (h.close k n hn) }

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.cutConstDiffFn_memAt {r : IntegrableRep S} {x : X}
    (a : R) (hdom : r.MemAt x) : ∀ j, x ∈ (r.cutConstDiffFn a j).dom := by
  intro j
  cases j with
  | zero => exact BFunR.seqSum_mem r.fn x hdom 0
  | succ j => exact ⟨BFunR.seqSum_mem r.fn x hdom (j + 1),
      BFunR.seqSum_mem r.fn x hdom j⟩

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.partialSum_cutConstDiffFn_value (r : IntegrableRep S) (a : R) (x : X)
    (hdom : r.MemAt x) (N : Nat) :
    RSeq.partialSum (fun j => (r.cutConstDiffFn a j).toFun x
        (r.cutConstDiffFn_memAt a hdom j)) N =
      COF.min ((BFunR.seqSum r.fn N).toFun x
        (BFunR.seqSum_mem r.fn x hdom N)) a := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show RSeq.partialSum (fun j => (r.cutConstDiffFn a j).toFun x
              (r.cutConstDiffFn_memAt a hdom j)) N +
            (r.cutConstDiffFn a (N + 1)).toFun x
              (r.cutConstDiffFn_memAt a hdom (N + 1)) =
        COF.min ((BFunR.seqSum r.fn (N + 1)).toFun x
          (BFunR.seqSum_mem r.fn x hdom (N + 1))) a
      rw [ih]
      show COF.min ((BFunR.seqSum r.fn N).toFun x
              (BFunR.seqSum_mem r.fn x hdom N)) a +
            (COF.min ((BFunR.seqSum r.fn (N + 1)).toFun x
              (BFunR.seqSum_mem r.fn x hdom (N + 1))) a +
             (-1) * COF.min ((BFunR.seqSum r.fn N).toFun x
              (BFunR.seqSum_mem r.fn x hdom N)) a) =
        COF.min ((BFunR.seqSum r.fn (N + 1)).toFun x
          (BFunR.seqSum_mem r.fn x hdom (N + 1))) a
      ring

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutConstVal_value (r : IntegrableRep S) (a : R) (x : X)
    (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { hd : RSeq.SeriesSum (fun j => (r.cutConstDiffFn a j).toFun x
        (r.cutConstDiffFn_memAt a hdom j)) // hd.sum = COF.min hx.sum a } :=
  ⟨{ sum := COF.min hx.sum a
     tends :=
       { mod := (tendstoHalf_min_const a hx.tends).mod
         close := by
           intro k N hN
           have h := (tendstoHalf_min_const a hx.tends).close k N hN
           rw [r.partialSum_cutConstDiffFn_value a x hdom N,
             BFunR.seqSum_toFun r.fn x hdom N]
           exact h } },
   rfl⟩

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.mem_cutConstDiffFn_dom {r : IntegrableRep S} {x : X} (a : R)
    (hdom : ∀ k, x ∈ (r.fn k).dom) : ∀ j, x ∈ (r.cutConstDiffFn a j).dom :=
  r.cutConstDiffFn_memAt a hdom

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.mem_cutConstVal_dom {r : IntegrableRep S} {x : X} (a : R)
    (ha : ¬ COF.lt a 0) (hdom : ∀ k, x ∈ (r.fn k).dom) :
    ∀ n, x ∈ ((r.cutConstVal a ha).fn n).dom := by
  intro n
  rcases natMod3 n with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show (r.cutConstVal a ha).fn (3 * m) = r.cutConstDiffFn a m from
          seqMerge3_zero (r.cutConstDiffFn a) r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact mem_cutConstDiffFn_dom a hdom m
  · rw [show (r.cutConstVal a ha).fn (3 * m + 1) = r.fn m from
          seqMerge3_one (r.cutConstDiffFn a) r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact hdom m
  · rw [show (r.cutConstVal a ha).fn (3 * m + 2) = BFunR.smul (-1) (r.fn m) from
          seqMerge3_two (r.cutConstDiffFn a) r.fn (fun k => BFunR.smul (-1) (r.fn k)) m]
    exact hdom m

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutConstVal_absSeries (r : IntegrableRep S) (a : R) (ha : ¬ COF.lt a 0) {x : X}
    (hdom : r.MemAt x)
    (hconv : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hdom n))) :
    RSeq.SeriesSum (fun n => COF.abs (((r.cutConstVal a ha).fn n).toFun x
      (r.mem_cutConstVal_dom a ha hdom n))) := by
  have ad : RSeq.SeriesSum (fun j => COF.abs ((r.cutConstDiffFn a j).toFun x
      (r.mem_cutConstDiffFn_dom a hdom j))) :=
    seriesSum_comparison (fun _ => abs_nonneg _)
      (fun j => r.cutConstDiffFn_abs_le a ha j x
        (r.mem_cutConstDiffFn_dom a hdom j) (hdom j)) hconv
  have anf : RSeq.SeriesSum (fun k => COF.abs
      ((BFunR.smul (-1) (r.fn k)).toFun x (hdom k))) :=
    seriesSum_congr (fun k => by
      show COF.abs (r.valueAt x hdom k) =
        COF.abs ((-1) * r.valueAt x hdom k)
      rw [show (-1 : R) * r.valueAt x hdom k =
        - r.valueAt x hdom k from by ring, COFO.abs_neg]) hconv
  have key : ∀ n,
      seqMerge3
          (fun j => COF.abs ((r.cutConstDiffFn a j).toFun x
            (r.mem_cutConstDiffFn_dom a hdom j)))
          (fun k => COF.abs (r.valueAt x hdom k))
          (fun k => COF.abs ((BFunR.smul (-1) (r.fn k)).toFun x (hdom k))) n =
        COF.abs (((r.cutConstVal a ha).fn n).toFun x
          (r.mem_cutConstVal_dom a ha hdom n)) := by
    intro n
    rcases natMod3 n with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · simp only [seqMerge3_zero]
      show COF.abs ((r.cutConstDiffFn a m).toFun x
          (r.mem_cutConstDiffFn_dom a hdom m)) =
        COF.abs ((seqMerge3 (r.cutConstDiffFn a) r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m)).toFun x
            (r.mem_cutConstVal_dom a ha hdom (3 * m)))
      simp only [seqMerge3_zero]
    · simp only [seqMerge3_one]
      show COF.abs (r.valueAt x hdom m) =
        COF.abs ((seqMerge3 (r.cutConstDiffFn a) r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m + 1)).toFun x
            (r.mem_cutConstVal_dom a ha hdom (3 * m + 1)))
      simp only [seqMerge3_one, IntegrableRep.valueAt]
    · simp only [seqMerge3_two]
      show COF.abs ((BFunR.smul (-1) (r.fn m)).toFun x (hdom m)) =
        COF.abs ((seqMerge3 (r.cutConstDiffFn a) r.fn
          (fun k => BFunR.smul (-1) (r.fn k)) (3 * m + 2)).toFun x
            (r.mem_cutConstVal_dom a ha hdom (3 * m + 2)))
      simp only [seqMerge3_two]
  exact seriesSum_congr key (seriesSum_merge3 ad hconv anf)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.domain_subset_cutConstVal_domain (r : IntegrableRep S) (a : R)
    (ha : ¬ COF.lt a 0) : r.domain ⊆ (r.cutConstVal a ha).domain := by
  intro x hx
  obtain ⟨hdom, ⟨hconv⟩⟩ := hx
  exact ⟨mem_cutConstVal_dom a ha hdom,
    ⟨r.cutConstVal_absSeries a ha hdom hconv⟩⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.tailFrom_normL1_lt (r : IntegrableRep S) (k : Nat) :
    COF.lt ((r.tailFrom (r.absConv.tends.mod k)).normL1) (COF.halfPow k) := by
  have h := (lemma_1_15 r).close k (r.absConv.tends.mod k) (Nat.le_refl _)
  have he : COF.abs ((r.tailFrom (r.absConv.tends.mod k)).normL1 - 0)
          = (r.tailFrom (r.absConv.tends.mod k)).normL1 := by
    rw [sub_zero]
    exact COFO.abs_of_nonneg (r.tailFrom (r.absConv.tends.mod k)).normL1_nonneg
  rw [← he]; exact h

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutConstVal_signed_value (r : IntegrableRep S) (a : R) (ha : ¬ COF.lt a 0)
    (x : X) (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { hs : RSeq.SeriesSum (fun n => (r.cutConstVal a ha).valueAt x
        (r.mem_cutConstVal_dom a ha hdom) n) //
        hs.sum = COF.min hx.sum a } := by
  obtain ⟨hd, hdeq⟩ := r.cutConstVal_value a x hdom hx
  refine ⟨seriesSum_congr (fun n => ?_)
            (seriesSum_merge3 hd hx (seriesSum_smul (-1 : R) hx)), ?_⟩
  · rcases natMod3 n with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp only [IntegrableRep.valueAt, IntegrableRep.cutConstVal, seqMerge3_zero]
    · simp only [IntegrableRep.valueAt, IntegrableRep.cutConstVal, seqMerge3_one]
    · simp only [IntegrableRep.valueAt, IntegrableRep.cutConstVal, BFunR.smul,
        seqMerge3_two]
  · show hd.sum + hx.sum + (-1) * hx.sum = COF.min hx.sum a
    rw [hdeq]; ring

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.ofL_value {g : BFunR X R} (hg : g ∈ S.L) (x : X)
    (hx : x ∈ g.dom) :
    { hs : RSeq.SeriesSum (fun n => (IntegrableRep.ofL hg).valueAt x
        (IntegrableRep.ofL_memAt hg hx) n) // hs.sum = g.toFun x hx } := by
  refine ⟨seriesSum_congr (fun n => ?_)
    (seriesSum_single (g.toFun x hx)), rfl⟩
  show (if n = 0 then g.toFun x hx else (0:R)) =
    (if n = 0 then g else BFunR.smul (0:R) g).toFun x
      ((IntegrableRep.ofL_memAt hg hx) n)
  by_cases hn : n = 0
  · simp only [if_pos hn]
  · simp only [if_neg hn, BFunR.smul]
    ring

/-- Domain membership for a tail representative. -/
theorem IntegrableRep.tailFrom_memAt {r : IntegrableRep S} {x : X} (M : Nat)
    (hdom : r.MemAt x) : (r.tailFrom M).MemAt x :=
  fun k => hdom (M + 1 + k)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.tailFrom_value (r : IntegrableRep S) (M : Nat) (x : X)
    (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { hs : RSeq.SeriesSum (fun k => (r.tailFrom M).valueAt x
        (r.tailFrom_memAt M hdom) k) //
        hs.sum = hx.sum - (BFunR.seqSum r.fn M).toFun x
          (BFunR.seqSum_mem r.fn x hdom M) } := by
  refine ⟨seriesSum_tail hx M, ?_⟩
  show hx.sum - RSeq.partialSum (fun n => r.valueAt x hdom n) M =
    hx.sum - (BFunR.seqSum r.fn M).toFun x
      (BFunR.seqSum_mem r.fn x hdom M)
  have hs : (BFunR.seqSum r.fn M).toFun x
        (BFunR.seqSum_mem r.fn x hdom M) =
      RSeq.partialSum (fun n => r.valueAt x hdom n) M := by
    simpa only [IntegrableRep.valueAt] using
      BFunR.seqSum_toFun r.fn x hdom M
  exact congrArg (fun z => hx.sum - z) hs.symm

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.tailFrom_integral (r : IntegrableRep S) (M : Nat) :
    (r.tailFrom M).integral = r.integral - S.I (BFunR.seqSum r.fn M) := by
  show (r.tailFrom M).seriesSum_I.sum = r.seriesSum_I.sum - S.I (BFunR.seqSum r.fn M)
  rw [seriesSum_unique (r.tailFrom M).seriesSum_I (seriesSum_tail r.seriesSum_I M)]
  show r.seriesSum_I.sum - RSeq.partialSum (fun k => S.I (r.fn k)) M
     = r.seriesSum_I.sum - S.I (BFunR.seqSum r.fn M)
  rw [S.toIntSpaceR.I_seqSum r.mem M]

/-- Technical lemma used in the public import closure. -/
theorem three_halfPow_add2_lt (k : Nat) :
    COF.lt (COF.halfPow (R := R) (k + 2) + COF.halfPow (k + 2) + COF.halfPow (k + 2))
      (COF.halfPow k) := by
  rw [halfPow_succ_add (k + 1)]
  have h := COF.lt_add_left (COF.halfPow (R := R) (k + 1)) (halfPow_lt_succ (R := R) (k + 1))
  rwa [halfPow_succ_add k] at h

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.cutNat_tendsto_aux (r : IntegrableRep S) (k M n : Nat)
    (hSM : BFunR.seqSum r.fn M ∈ S.L)
    (htail : COF.lt ((r.tailFrom M).normL1) (COF.halfPow (k + 2)))
    (hn : (S.cutNat_tendsto hSM).mod (k + 2) ≤ n) :
    COF.lt (COF.abs ((r.cutNatVal n).integral - r.integral)) (COF.halfPow k) := by
  -- Term2: base cutNat_tendsto(S_M∈L)
  have ht2 : COF.lt (COF.abs (S.I (BFunR.cutNat n (BFunR.seqSum r.fn M))
                - S.I (BFunR.seqSum r.fn M))) (COF.halfPow (k + 2)) :=
    (S.cutNat_tendsto hSM).close (k + 2) n hn
  -- Term3: |I(S_M) − I₁(f)| = |(tailFrom M).integral| ≤ ‖tail_M‖₁ < ½^(k+2)
  have ht3 : COF.lt (COF.abs (S.I (BFunR.seqSum r.fn M) - r.integral)) (COF.halfPow (k + 2)) := by
    have heq : S.I (BFunR.seqSum r.fn M) - r.integral = -(r.tailFrom M).integral := by
      rw [r.tailFrom_integral M]; ring
    rw [heq, COFO.abs_neg]
    exact lt_of_le_of_lt (r.tailFrom M).abs_integral_le_normL1 htail
  -- Technical note.
  have ht1 : COF.lt (COF.abs ((r.cutNatVal n).integral
                - S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)))) (COF.halfPow (k + 2)) := by
    have hcsI : S.I (BFunR.cutNat n (BFunR.seqSum r.fn M))
              = (IntegrableRep.ofL (S.cutConst_mem ((n:R)) hSM)).integral :=
      (IntegrableRep.ofL_integral (S.cutConst_mem ((n:R)) hSM)).symm
    rw [hcsI, ← IntegrableRep.integral_sub]
    refine lt_of_le_of_lt
      ((r.cutNatVal n).sub (IntegrableRep.ofL (S.cutConst_mem ((n:R)) hSM))).abs_integral_le_normL1 ?_
    refine lt_of_le_of_lt
      (normL1_mono r.domain_isFull
        ((r.cutNatVal n).sub (IntegrableRep.ofL (S.cutConst_mem ((n:R)) hSM)))
        (r.tailFrom M) ?_) htail
    intro x hx hudom hvdom hu hv
    obtain ⟨hrdom, ⟨habs⟩⟩ := hx
    have hxv := seriesSum_of_abs habs
    let hSMx : x ∈ (BFunR.seqSum r.fn M).dom :=
      BFunR.seqSum_mem r.fn x hrdom M
    let hcutdom := r.mem_cutConstVal_dom ((n : R)) (natCast_nonneg n) hrdom
    let hofdom := IntegrableRep.ofL_memAt (S.cutConst_mem ((n:R)) hSM) hSMx
    obtain ⟨hcv, hcveq⟩ :=
      r.cutConstVal_signed_value ((n:R)) (natCast_nonneg n) x hrdom hxv
    obtain ⟨hov, hoveq⟩ :=
      IntegrableRep.ofL_value (S.cutConst_mem ((n:R)) hSM) x hSMx
    obtain ⟨htv, htveq⟩ := r.tailFrom_value M x hrdom hxv
    rw [seriesSum_unique hu (add_seriesSum_value hcutdom
          (IntegrableRep.neg_memAt hofdom) hcv (neg_seriesSum_value hofdom hov)),
        seriesSum_unique hv htv]
    show Le (COF.abs (hcv.sum + -hov.sum)) (COF.abs htv.sum)
    rw [hcveq, hoveq, htveq]
    show Le (COF.abs (COF.min hxv.sum ((n:R))
            + -(COF.min ((BFunR.seqSum r.fn M).toFun x hSMx) ((n:R)))))
            (COF.abs (hxv.sum - (BFunR.seqSum r.fn M).toFun x hSMx))
    rw [show COF.min hxv.sum ((n:R)) +
          -(COF.min ((BFunR.seqSum r.fn M).toFun x hSMx) ((n:R))) =
        COF.min hxv.sum ((n:R)) -
          COF.min ((BFunR.seqSum r.fn M).toFun x hSMx) ((n:R)) from by ring]
    exact abs_min_sub_min_le hxv.sum
      ((BFunR.seqSum r.fn M).toFun x hSMx) ((n:R))
  -- Technical note.
  have htri : Le (COF.abs ((r.cutNatVal n).integral - r.integral))
        (COF.abs ((r.cutNatVal n).integral - S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)))
          + COF.abs (S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)) - S.I (BFunR.seqSum r.fn M))
          + COF.abs (S.I (BFunR.seqSum r.fn M) - r.integral)) := by
    rw [show (r.cutNatVal n).integral - r.integral
          = ((r.cutNatVal n).integral - S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)))
            + (S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)) - S.I (BFunR.seqSum r.fn M))
            + (S.I (BFunR.seqSum r.fn M) - r.integral) from by ring]
    refine le_trans (COFO.abs_add_le _ _) ?_
    apply le_of_nonneg_sub
    rw [show (COF.abs ((r.cutNatVal n).integral - S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)))
            + COF.abs (S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)) - S.I (BFunR.seqSum r.fn M))
            + COF.abs (S.I (BFunR.seqSum r.fn M) - r.integral))
          - (COF.abs (((r.cutNatVal n).integral - S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)))
              + (S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)) - S.I (BFunR.seqSum r.fn M)))
            + COF.abs (S.I (BFunR.seqSum r.fn M) - r.integral))
          = (COF.abs ((r.cutNatVal n).integral - S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)))
              + COF.abs (S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)) - S.I (BFunR.seqSum r.fn M)))
            - COF.abs (((r.cutNatVal n).integral - S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)))
                + (S.I (BFunR.cutNat n (BFunR.seqSum r.fn M)) - S.I (BFunR.seqSum r.fn M)))
          from by ring]
    exact nonneg_sub_of_le (COFO.abs_add_le _ _)
  exact lt_of_le_of_lt htri
    (COFO.lt_trans (lt_add (lt_add ht1 ht2) ht3) (three_halfPow_add2_lt k))

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutNat_tendsto_rep (r : IntegrableRep S) :
    RSeq.TendstoHalf (fun n => (r.cutNatVal n).integral) r.integral where
  mod := fun k =>
    (S.cutNat_tendsto (S.toIntSpaceR.seqSum_mem r.mem (r.absConv.tends.mod (k + 2)))).mod (k + 2)
  close := fun k n hn =>
    r.cutNat_tendsto_aux k (r.absConv.tends.mod (k + 2)) n
      (S.toIntSpaceR.seqSum_mem r.mem _) (r.tailFrom_normL1_lt (k + 2)) hn

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem halfPow_nonneg (k : Nat) : ¬ COF.lt (COF.halfPow (R := R) k) 0 :=
  fun h => COF.lt_irrefl 0 (COFO.lt_trans (halfPow_pos k) h)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutSmallVal (r : IntegrableRep S) (k : Nat) : IntegrableRep S :=
  r.absVal.cutConstVal (COF.halfPow k) (halfPow_nonneg k)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.cutSmall_tendsto_aux (r : IntegrableRep S) (p M k : Nat)
    (hSM : BFunR.seqSum r.fn M ∈ S.L)
    (htail : COF.lt ((r.tailFrom M).normL1) (COF.halfPow (p + 2)))
    (hk : (S.cutSmall_tendsto hSM).mod (p + 2) ≤ k) :
    COF.lt (COF.abs ((r.cutSmallVal k).integral)) (COF.halfPow p) := by
  -- Term2: base cutSmall(S_M∈L): |I(min{|S_M|,2⁻ᵏ})| < ½^(p+2)
  have ht2 : COF.lt (COF.abs (S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M))
                (COF.halfPow k)))) (COF.halfPow (p + 2)) := by
    have h : COF.lt (COF.abs (S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M))
                (COF.halfPow k)) - 0)) (COF.halfPow (p + 2)) :=
      (S.cutSmall_tendsto hSM).close (p + 2) k hk
    rwa [sub_zero] at h
  -- Technical note.
  have ht1 : COF.lt (COF.abs ((r.cutSmallVal k).integral
                - S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k))))
                (COF.halfPow (p + 2)) := by
    have hcsI : S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k))
              = (IntegrableRep.ofL (S.cutConst_mem (COF.halfPow k) (S.abs_mem hSM))).integral :=
      (IntegrableRep.ofL_integral (S.cutConst_mem (COF.halfPow k) (S.abs_mem hSM))).symm
    rw [hcsI, ← IntegrableRep.integral_sub]
    refine lt_of_le_of_lt
      ((r.cutSmallVal k).sub
        (IntegrableRep.ofL (S.cutConst_mem (COF.halfPow k) (S.abs_mem hSM)))).abs_integral_le_normL1 ?_
    refine lt_of_le_of_lt
      (normL1_mono r.domain_isFull
        ((r.cutSmallVal k).sub (IntegrableRep.ofL (S.cutConst_mem (COF.halfPow k) (S.abs_mem hSM))))
        (r.tailFrom M) ?_) htail
    intro x hx hudom hvdom hu hv
    obtain ⟨hrdom, ⟨habs⟩⟩ := hx
    have hxv := seriesSum_of_abs habs
    let hSMx : x ∈ (BFunR.seqSum r.fn M).dom :=
      BFunR.seqSum_mem r.fn x hrdom M
    let habsdom := r.mem_absVal_dom hrdom
    let hcutdom := r.absVal.mem_cutConstVal_dom
      (COF.halfPow k) (halfPow_nonneg k) habsdom
    let hofdom := IntegrableRep.ofL_memAt
      (S.cutConst_mem (COF.halfPow k) (S.abs_mem hSM)) hSMx
    obtain ⟨hav, haveq⟩ := r.absVal_signed_value x hrdom hxv
    obtain ⟨hcv, hcveq⟩ := r.absVal.cutConstVal_signed_value
      (COF.halfPow k) (halfPow_nonneg k) x habsdom hav
    obtain ⟨hov, hoveq⟩ :=
      IntegrableRep.ofL_value
        (S.cutConst_mem (COF.halfPow k) (S.abs_mem hSM)) x hSMx
    obtain ⟨htv, htveq⟩ := r.tailFrom_value M x hrdom hxv
    rw [seriesSum_unique hu (add_seriesSum_value hcutdom
          (IntegrableRep.neg_memAt hofdom) hcv (neg_seriesSum_value hofdom hov)),
        seriesSum_unique hv htv]
    show Le (COF.abs (hcv.sum + -hov.sum)) (COF.abs htv.sum)
    rw [hcveq, haveq, hoveq, htveq]
    show Le (COF.abs (COF.min (COF.abs hxv.sum) (COF.halfPow k)
            + -(COF.min (COF.abs ((BFunR.seqSum r.fn M).toFun x hSMx))
              (COF.halfPow k))))
            (COF.abs (hxv.sum - (BFunR.seqSum r.fn M).toFun x hSMx))
    rw [show COF.min (COF.abs hxv.sum) (COF.halfPow k)
            + -(COF.min (COF.abs ((BFunR.seqSum r.fn M).toFun x hSMx))
              (COF.halfPow k))
          = COF.min (COF.abs hxv.sum) (COF.halfPow k)
            - COF.min (COF.abs ((BFunR.seqSum r.fn M).toFun x hSMx))
              (COF.halfPow k) from by ring]
    refine le_trans (abs_min_sub_min_le (COF.abs hxv.sum)
      (COF.abs ((BFunR.seqSum r.fn M).toFun x hSMx)) (COF.halfPow k)) ?_
    exact abs_abs_sub_abs_le hxv.sum ((BFunR.seqSum r.fn M).toFun x hSMx)
  -- Technical note.
  have htri : Le (COF.abs ((r.cutSmallVal k).integral))
        (COF.abs ((r.cutSmallVal k).integral
          - S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k)))
          + COF.abs (S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k)))) := by
    have h := COFO.abs_add_le
      ((r.cutSmallVal k).integral
        - S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k)))
      (S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k)))
    rwa [show ((r.cutSmallVal k).integral
            - S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k)))
          + S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k))
          = (r.cutSmallVal k).integral from by ring] at h
  have hsum2 : COF.lt (COF.abs ((r.cutSmallVal k).integral
        - S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k)))
        + COF.abs (S.I (BFunR.cutConst (BFunR.absf (BFunR.seqSum r.fn M)) (COF.halfPow k))))
        (COF.halfPow (p + 1)) := by
    have h := lt_add ht1 ht2
    rwa [halfPow_succ_add (p + 1)] at h
  exact lt_of_le_of_lt htri (COFO.lt_trans hsum2 (halfPow_lt_succ p))

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.cutSmall_tendsto_rep (r : IntegrableRep S) :
    RSeq.TendstoHalf (fun k => (r.cutSmallVal k).integral) 0 where
  mod := fun p =>
    (S.cutSmall_tendsto (S.toIntSpaceR.seqSum_mem r.mem (r.absConv.tends.mod (p + 2)))).mod (p + 2)
  close := fun p k hk => by
    have h := r.cutSmall_tendsto_aux p (r.absConv.tends.mod (p + 2)) k
      (S.toIntSpaceR.seqSum_mem r.mem _) (r.tailFrom_normL1_lt (p + 2)) hk
    show COF.lt (COF.abs ((r.cutSmallVal k).integral - 0)) (COF.halfPow p)
    rwa [sub_zero]

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.collapseFirst (r : IntegrableRep S) (N : Nat) : IntegrableRep S where
  fn := fun k => if k = 0 then BFunR.seqSum r.fn N else r.fn (N + k)
  mem := fun k => by
    by_cases h : k = 0
    · rw [if_pos h]; exact S.toIntSpaceR.seqSum_mem r.mem N
    · rw [if_neg h]; exact r.mem (N + k)
  absConv := by
    refine seriesSum_of_tail 0 ?_
    refine seriesSum_congr (fun l => ?_) (seriesSum_tail r.absConv N)
    show S.I (BFunR.absf (r.fn (N + 1 + l)))
       = S.I (BFunR.absf (if 0 + 1 + l = 0 then BFunR.seqSum r.fn N else r.fn (N + (0 + 1 + l))))
    rw [if_neg (by omega : ¬ 0 + 1 + l = 0),
        show N + (0 + 1 + l) = N + 1 + l from by omega]

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.collapseFirst_absConv_sum (r : IntegrableRep S) (N : Nat) :
    (r.collapseFirst N).absConv.sum
      = S.I (BFunR.absf (BFunR.seqSum r.fn N))
        + (r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) N) := by
  rfl

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.collapseFirst_dense (r : IntegrableRep S) (k : Nat) :
    COF.lt
      ((r.collapseFirst (max ((lemma_1_8 r).mod (k + 1)) (r.absConv.tends.mod (k + 1)))).absConv.sum)
      (r.normL1 + COF.halfPow k) := by
  set N := max ((lemma_1_8 r).mod (k + 1)) (r.absConv.tends.mod (k + 1)) with hN
  rw [r.collapseFirst_absConv_sum N]
  have h1 : COF.lt (S.I (BFunR.absf (BFunR.seqSum r.fn N))) (r.normL1 + COF.halfPow (k + 1)) := by
    have hc := (lemma_1_8 r).close (k + 1) N (le_max_left _ _)
    have e1 : COF.lt (S.I (BFunR.absf (BFunR.seqSum r.fn N)) - r.normL1) (COF.halfPow (k + 1)) :=
      lt_of_le_of_lt (COFO.le_abs_self _) hc
    have := COF.lt_add_left (r.normL1) e1
    rwa [show r.normL1 + (S.I (BFunR.absf (BFunR.seqSum r.fn N)) - r.normL1)
          = S.I (BFunR.absf (BFunR.seqSum r.fn N)) from by ring] at this
  have h2 : COF.lt (r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) N)
              (COF.halfPow (k + 1)) := by
    have hc := r.absConv.tends.close (k + 1) N (le_max_right _ _)
    refine lt_of_le_of_lt (COFO.le_abs_self _) ?_
    rw [show r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) N
          = -(RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) N - r.absConv.sum) from by ring,
        COFO.abs_neg]
    exact hc
  have hsum := lt_add h1 h2
  rw [show (r.normL1 + COF.halfPow (k + 1)) + COF.halfPow (k + 1)
        = r.normL1 + (COF.halfPow (k + 1) + COF.halfPow (k + 1)) from by ring,
      halfPow_succ_add k] at hsum
  exact hsum

/-- Technical lemma used in the public import closure. -/
def tendstoHalf_const (c : R) : RSeq.TendstoHalf (fun _ => c) c where
  mod := fun _ => 0
  close := fun k _ _ => by
    change COF.lt (COF.abs (c - c)) (COF.halfPow k)
    rw [show c - c = 0 from by ring, COFO.abs_zero]; exact halfPow_pos k

/-- Technical lemma used in the public import closure. -/
def tendstoHalf_add {u v : Nat → R} {a b : R}
    (hu : RSeq.TendstoHalf u a) (hv : RSeq.TendstoHalf v b) :
    RSeq.TendstoHalf (fun n => u n + v n) (a + b) where
  mod := fun k => max (hu.mod (k + 1)) (hv.mod (k + 1))
  close := fun k n hn => by
    change COF.lt (COF.abs (u n + v n - (a + b))) (COF.halfPow k)
    have h1 := hu.close (k + 1) n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have h2 := hv.close (k + 1) n (Nat.le_trans (Nat.le_max_right _ _) hn)
    refine lt_of_le_of_lt
      (show Le (COF.abs (u n + v n - (a + b))) (COF.abs (u n - a) + COF.abs (v n - b)) from by
        rw [show u n + v n - (a + b) = (u n - a) + (v n - b) from by ring]
        exact COFO.abs_add_le _ _) ?_
    have h := lt_add h1 h2
    rwa [halfPow_succ_add] at h

/-- Technical lemma used in the public import closure. -/
def tendstoHalf_partialSum {f : Nat → Nat → R} {l : Nat → R}
    (h : ∀ a, RSeq.TendstoHalf (f a) (l a)) :
    ∀ N, RSeq.TendstoHalf (fun M => RSeq.partialSum (fun a => f a M) N) (RSeq.partialSum l N)
  | 0 => h 0
  | N + 1 => tendstoHalf_add (tendstoHalf_partialSum h N) (h (N + 1))

/-- Technical lemma used in the public import closure. -/
def cellAt_rowsum {A : Nat → Nat → R} (hA : ∀ i j, Nonneg (A i j))
    (hflat : RSeq.SeriesSum (fun m => A (cellAt m).1 (cellAt m).2)) :
    RSeq.SeriesSum (fun a => (row_seriesSum hA hflat a).sum) := by
  set g : Nat → R := fun a => (row_seriesSum hA hflat a).sum with hg
  have hg_nn : ∀ a, Nonneg (g a) :=
    fun a => seriesSum_nonneg (fun j => hA a j) (row_seriesSum hA hflat a)
  have hgrid_le : ∀ P, Le (gridSum A P) hflat.sum := fun P => by
    rw [← partialSum_cellAt_eq_gridSum A P]
    exact partialSum_le_sum (fun m => hA (cellAt m).1 (cellAt m).2) hflat (P * P + 2 * P)
  have hgrid_le_psg : ∀ N, Le (gridSum A N) (RSeq.partialSum g N) := fun N =>
    partialSum_le_of_termwise_le_upto N
      (fun i _ => partialSum_le_sum (fun j => hA i j) (row_seriesSum hA hflat i) N)
  refine seriesSum_of_partialCauchy (isCauchy_of_mono_bounded_gap (T := hflat.sum)
    (fun {_ _} hpq => partialSum_mono hg_nn hpq) ?_ ?_)
  · intro N
    refine Le_of_tendstoHalf_le
      (tendstoHalf_partialSum (fun a => (row_seriesSum hA hflat a).tends) N)
      (tendstoHalf_const hflat.sum) (fun M' => ?_)
    refine le_trans ?_ (hgrid_le (max N M'))
    refine le_trans
      (partialSum_le_of_termwise_le_upto N
        (fun a _ => partialSum_mono (fun j => hA a j) (le_max_right N M'))) ?_
    exact partialSum_mono (fun a => partialSum_nonneg (fun j => hA a j) (max N M'))
      (le_max_left N M')
  · intro k
    refine ⟨hflat.tends.mod k, ?_⟩
    set M := hflat.tends.mod k with hM
    have hc : COF.lt (COF.abs (gridSum A M - hflat.sum)) (COF.halfPow k) := by
      rw [← partialSum_cellAt_eq_gridSum A M]
      exact hflat.tends.close k (M * M + 2 * M) (by omega)
    have hstep1 : Le (hflat.sum - RSeq.partialSum g M) (hflat.sum - gridSum A M) := by
      apply le_of_nonneg_sub
      rw [show (hflat.sum - gridSum A M) - (hflat.sum - RSeq.partialSum g M)
            = RSeq.partialSum g M - gridSum A M from by ring]
      exact nonneg_sub_of_le (hgrid_le_psg M)
    have hstep2 : Le (hflat.sum - gridSum A M) (COF.abs (gridSum A M - hflat.sum)) := by
      have h := COFO.neg_le_abs (gridSum A M - hflat.sum)
      rwa [show -(gridSum A M - hflat.sum) = hflat.sum - gridSum A M from by ring] at h
    exact lt_of_le_of_lt (le_trans hstep1 hstep2) hc

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.absVal_pointSum (r : IntegrableRep S) (x : X)
    (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { h : RSeq.SeriesSum (fun n => r.absVal.valueAt x
        (r.mem_absVal_dom hdom) n) // h.sum = COF.abs hx.sum } :=
  r.absVal_signed_value x hdom hx

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.normL1_eq_integral_of_nonneg (r : IntegrableRep S)
    (hnn : ∀ x : X, ∀ (hdom : r.MemAt x)
              (_habs : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hdom n)))
              (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)), Nonneg hx.sum) :
    r.normL1 = r.integral := by
  show r.absVal.integral = r.integral
  refine IntegrableRep.integral_congr r.absVal r ?_
  intro x _hAbsDom hdom _hAbs hRAbs hAbsSum hRSum
  rw [seriesSum_unique hAbsSum (r.absVal_pointSum x hdom hRSum).1,
    (r.absVal_pointSum x hdom hRSum).2]
  exact COFO.abs_of_nonneg (hnn x hdom hRAbs hRSum)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.truncK (r : IntegrableRep S) (k : Nat) : Nat :=
  max ((lemma_1_8 r).mod k) (r.absConv.tends.mod k)

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.truncK_headsum_lt (r : IntegrableRep S)
    (hnn : ∀ x : X, ∀ (hdom : r.MemAt x)
              (_habs : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hdom n)))
              (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)), Nonneg hx.sum)
    (k : Nat) :
    COF.lt (r.integral - COF.halfPow k)
      (S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k)))) := by
  rw [show r.integral = r.absVal.integral from (r.normL1_eq_integral_of_nonneg hnn).symm]
  have hclose : COF.lt (COF.abs
      (S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k))) - r.absVal.integral)) (COF.halfPow k) :=
    (lemma_1_8 r).close k (r.truncK k) (le_max_left _ _)
  have hba : COF.lt (r.absVal.integral - S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k))))
      (COF.halfPow k) := by
    refine lt_of_le_of_lt ?_ hclose
    have hh := COFO.neg_le_abs
      (S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k))) - r.absVal.integral)
    rwa [show -(S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k))) - r.absVal.integral)
          = r.absVal.integral - S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k))) from by ring] at hh
  refine lt_of_sub_neg ?_
  rw [show (r.absVal.integral - COF.halfPow k)
        - S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k)))
      = (r.absVal.integral - S.I (BFunR.absf (BFunR.seqSum r.fn (r.truncK k)))) - COF.halfPow k
      from by ring]
  exact sub_neg_of_lt hba

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.truncK_tail (r : IntegrableRep S) (k : Nat) :
    { h : RSeq.SeriesSum (fun b => S.I (BFunR.absf (r.fn (r.truncK k + 1 + b)))) //
        COF.lt h.sum (COF.halfPow k) } := by
  refine ⟨seriesSum_tail r.absConv (r.truncK k), ?_⟩
  show COF.lt
    (r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) (r.truncK k))
    (COF.halfPow k)
  have hclose := r.absConv.tends.close k (r.truncK k) (le_max_right _ _)
  refine lt_of_le_of_lt ?_ hclose
  have hh := COFO.neg_le_abs
    (RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) (r.truncK k) - r.absConv.sum)
  rwa [show -(RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) (r.truncK k) - r.absConv.sum)
        = r.absConv.sum - RSeq.partialSum (fun n => S.I (BFunR.absf (r.fn n))) (r.truncK k)
        from by ring] at hh

/-- Technical lemma used in the public import closure. -/
@[reducible] def IntegrableRep.contNf (r : IntegrableRep S) (j : Nat) : Nat :=
  max ((lemma_1_8 r).mod (j + 1)) (r.absConv.tends.mod (j + 1))

/-- Technical lemma used in the public import closure. -/
def contΦ (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) :
    Nat → Nat → BFunR X R :=
  fun a => Nat.rec
    (fun b => BFunR.absf (rg.fn (b + (rg.truncK k + 1))))
    (fun n _ b => BFunR.absf (((rn n).collapseFirst ((rn n).contNf (k + n + 2))).fn b))
    a

theorem contΦ_zero (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k b : Nat) :
    contΦ rg rn k 0 b = BFunR.absf (rg.fn (b + (rg.truncK k + 1))) := rfl

theorem contΦ_succ (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k n b : Nat) :
    contΦ rg rn k (n + 1) b
      = BFunR.absf (((rn n).collapseFirst ((rn n).contNf (k + n + 2))).fn b) := rfl

theorem contΦ_mem (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) :
    ∀ a b, contΦ rg rn k a b ∈ S.L := by
  rintro (_ | n) b
  · exact S.abs_mem (rg.mem _)
  · exact S.abs_mem (((rn n).collapseFirst ((rn n).contNf (k + n + 2))).mem b)

theorem contΦ_pwnn (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) :
    ∀ a b, BFunR.PointwiseNonneg (contΦ rg rn k a b) := by
  rintro (_ | n) b <;> intro x hx <;> exact abs_nonneg _

theorem contΦ_val_nn (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) :
    ∀ a b y, ∀ hy : y ∈ (contΦ rg rn k a b).dom,
      Nonneg ((contΦ rg rn k a b).toFun y hy) := by
  rintro (_ | n) b y hy <;> exact abs_nonneg _

/-- Technical lemma used in the public import closure. -/
def RepNonneg (r : IntegrableRep S) : Prop :=
  ∀ x : X, ∀ (hdom : r.MemAt x)
    (_habs : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hdom n)))
    (hx : RSeq.SeriesSum (fun n => r.valueAt x hdom n)), Nonneg hx.sum

/-- Technical lemma used in the public import closure. -/
def contGeom (k : Nat) : RSeq.SeriesSum (fun n => COF.halfPow (R := R) (k + n + 2)) := by
  refine seriesSum_congr (fun n => ?_)
    (seriesSum_smul (COF.halfPow (R := R) (k + 2)) seriesSum_halfPow)
  rw [← halfPow_add (k + 2) n, show (k + 2) + n = k + n + 2 from by omega]

/-- Technical lemma used in the public import closure. -/
theorem contRow_bound (r : IntegrableRep S) (hnn : RepNonneg r) (j : Nat) :
    COF.lt ((r.collapseFirst (r.contNf j)).absConv.sum) (r.integral + COF.halfPow j) :=
  (r.normL1_eq_integral_of_nonneg hnn) ▸ (r.collapseFirst_dense j)

/-- Technical lemma used in the public import closure. -/
def contRowSeries (rn : Nat → IntegrableRep S) (hnn : ∀ n, RepNonneg (rn n)) (k : Nat)
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) :
    RSeq.SeriesSum (fun n => ((rn n).collapseFirst ((rn n).contNf (k + n + 2))).absConv.sum) :=
  seriesSum_comparison
    (fun n => ((rn n).collapseFirst ((rn n).contNf (k + n + 2))).absSum_nonneg)
    (fun n => le_of_lt (contRow_bound (rn n) (hnn n) (k + n + 2)))
    (seriesSum_add hsumI (contGeom k))

/-- Technical lemma used in the public import closure. -/
def contΦ_row (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) :
    ∀ a, RSeq.SeriesSum (fun b => S.I (contΦ rg rn k a b))
  | 0 => seriesSum_congr (fun b => by rw [contΦ_zero, Nat.add_comm b (rg.truncK k + 1)])
            (rg.truncK_tail k).1
  | n + 1 => ((rn n).collapseFirst ((rn n).contNf (k + n + 2))).absConv

/-- Technical lemma used in the public import closure. -/
def contΦ_rowsum (rg : IntegrableRep S) (rn : Nat → IntegrableRep S)
    (hnn : ∀ n, RepNonneg (rn n)) (k : Nat)
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) :
    RSeq.SeriesSum (fun a => (contΦ_row rg rn k a).sum) := by
  refine seriesSum_of_tail 0 ?_
  refine seriesSum_congr (fun l => ?_) (contRowSeries rn hnn k hsumI)
  show ((rn l).collapseFirst ((rn l).contNf (k + l + 2))).absConv.sum
     = (contΦ_row rg rn k (0 + 1 + l)).sum
  rw [show (0 : Nat) + 1 + l = l + 1 from by omega]
  rfl

/-- Technical lemma used in the public import closure. -/
def contΦ_flat (rg : IntegrableRep S) (rn : Nat → IntegrableRep S)
    (hnn : ∀ n, RepNonneg (rn n)) (k : Nat)
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) :
    RSeq.SeriesSum (fun m => S.I (contΦ rg rn k (cellAt m).1 (cellAt m).2)) :=
  cellAt_seriesSum
    (fun a b => S.I_nonneg (contΦ_mem rg rn k a b) (contΦ_pwnn rg rn k a b))
    (contΦ_row rg rn k)
    (contΦ_rowsum rg rn hnn k hsumI)

/-- Technical lemma used in the public import closure. -/
theorem seriesSum_comparison_le {a b : Nat → R} (ha : ∀ n, Nonneg (a n)) (hab : ∀ n, Le (a n) (b n))
    (hb : RSeq.SeriesSum b) : Le (seriesSum_comparison ha hab hb).sum hb.sum := by
  refine le_of_tendsto_le (seriesSum_comparison ha hab hb) hb.sum (fun n => ?_)
  refine le_trans (partialSum_le_of_termwise_le_upto n (fun i _ => hab i)) ?_
  exact partialSum_le_sum (fun i => le_trans (ha i) (hab i)) hb n

/-- Technical lemma used in the public import closure. -/
theorem cellAt_seriesSum_le {a : Nat → Nat → R} (ha : ∀ i j, Nonneg (a i j))
    (hrow : ∀ i, RSeq.SeriesSum (a i)) (hrowsum : RSeq.SeriesSum (fun i => (hrow i).sum)) :
    Le (cellAt_seriesSum ha hrow hrowsum).sum hrowsum.sum := by
  refine le_of_tendsto_le (cellAt_seriesSum ha hrow hrowsum) hrowsum.sum (fun q => ?_)
  refine le_trans
    (partialSum_mono (fun m => ha (cellAt m).1 (cellAt m).2) (self_le_sq_add q (2 * q))) ?_
  rw [partialSum_cellAt_eq_gridSum a q]
  exact gridSum_le_T ha hrow hrowsum q

/-- Technical lemma used in the public import closure. -/
theorem contΦ_flat_lt (rg : IntegrableRep S) (rn : Nat → IntegrableRep S)
    (hgnn : RepNonneg rg) (hnn : ∀ n, RepNonneg (rn n))
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) (k : Nat)
    (hbudget : COF.lt (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1))
                      (rg.integral - hsumI.sum)) :
    COF.lt (contΦ_flat rg rn hnn k hsumI).sum
           (S.I (BFunR.absf (BFunR.seqSum rg.fn (rg.truncK k)))) := by
  -- Step 3: row0 < ½^k
  have hrow0 : COF.lt (contΦ_row rg rn k 0).sum (COF.halfPow k) := (rg.truncK_tail k).2
  -- Step 4: contGeom.sum = ½^{k+1}, contRowSeries.sum ≤ hsumI.sum + ½^{k+1}
  have hgeom_sum : (contGeom k).sum = COF.halfPow (R := R) (k + 1) := by
    show COF.halfPow (R := R) (k + 2) * (2 : R) = COF.halfPow (k + 1)
    rw [show (2 : R) = 1 + 1 from by ring, mul_add, mul_one, halfPow_succ_add]
  have hrow_le : Le (contRowSeries rn hnn k hsumI).sum (hsumI.sum + COF.halfPow (k + 1)) := by
    refine le_trans (seriesSum_comparison_le _ _ _) ?_
    show Le (hsumI.sum + (contGeom k).sum) (hsumI.sum + COF.halfPow (k + 1))
    rw [hgeom_sum]; exact le_refl _
  -- Step 5: I(f) > rg.integral - ½^k
  have hIf : COF.lt (rg.integral - COF.halfPow k)
              (S.I (BFunR.absf (BFunR.seqSum rg.fn (rg.truncK k)))) := rg.truncK_headsum_lt hgnn k
  -- Technical note.
  have hterm1 : COF.lt 0 (COF.halfPow k - (contΦ_row rg rn k 0).sum) := by
    have h := COF.lt_add_left (-(contΦ_row rg rn k 0).sum) hrow0
    rwa [show -(contΦ_row rg rn k 0).sum + (contΦ_row rg rn k 0).sum = (0 : R) from by ring,
         show -(contΦ_row rg rn k 0).sum + COF.halfPow k
            = COF.halfPow k - (contΦ_row rg rn k 0).sum from by ring] at h
  have hterm2 : COF.lt 0
      (rg.integral - hsumI.sum - (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1))) := by
    have h := COF.lt_add_left (-(COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1))) hbudget
    rwa [show -(COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1))
            + (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1)) = (0 : R) from by ring,
         show -(COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1)) + (rg.integral - hsumI.sum)
            = rg.integral - hsumI.sum - (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1))
            from by ring] at h
  have hterm3 : Nonneg
      (hsumI.sum + COF.halfPow (k + 1) - (contRowSeries rn hnn k hsumI).sum) :=
    nonneg_sub_of_le hrow_le
  -- Technical note.
  have hpos : COF.lt 0
      ((COF.halfPow k - (contΦ_row rg rn k 0).sum)
        + (rg.integral - hsumI.sum - (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1)))
        + (hsumI.sum + COF.halfPow (k + 1) - (contRowSeries rn hnn k hsumI).sum)) := by
    have h12 := lt_add hterm1 hterm2
    rw [show (0 : R) + 0 = 0 from by ring] at h12
    refine lt_of_lt_of_le h12 (le_of_nonneg_sub ?_)
    rw [show ((COF.halfPow k - (contΦ_row rg rn k 0).sum)
              + (rg.integral - hsumI.sum - (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1)))
              + (hsumI.sum + COF.halfPow (k + 1) - (contRowSeries rn hnn k hsumI).sum))
            - ((COF.halfPow k - (contΦ_row rg rn k 0).sum)
              + (rg.integral - hsumI.sum - (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1))))
          = hsumI.sum + COF.halfPow (k + 1) - (contRowSeries rn hnn k hsumI).sum from by ring]
    exact hterm3
  -- main: contΦ_rowsum.sum(=row0+contRowSeries)< rg.integral - ½^k
  have hmain : COF.lt (contΦ_rowsum rg rn hnn k hsumI).sum (rg.integral - COF.halfPow k) := by
    show COF.lt ((contΦ_row rg rn k 0).sum + (contRowSeries rn hnn k hsumI).sum)
            (rg.integral - COF.halfPow k)
    have h := COF.lt_add_left
      ((contΦ_row rg rn k 0).sum + (contRowSeries rn hnn k hsumI).sum) hpos
    rwa [show ((contΦ_row rg rn k 0).sum + (contRowSeries rn hnn k hsumI).sum) + 0
            = (contΦ_row rg rn k 0).sum + (contRowSeries rn hnn k hsumI).sum from by ring,
         show ((contΦ_row rg rn k 0).sum + (contRowSeries rn hnn k hsumI).sum)
              + ((COF.halfPow k - (contΦ_row rg rn k 0).sum)
                + (rg.integral - hsumI.sum - (COF.halfPow k + COF.halfPow k + COF.halfPow (k + 1)))
                + (hsumI.sum + COF.halfPow (k + 1) - (contRowSeries rn hnn k hsumI).sum))
            = rg.integral - COF.halfPow k from by ring] at h
  exact lt_of_le_of_lt (cellAt_seriesSum_le _ _ _) (lt_of_lt_of_le hmain (le_of_lt hIf))

end

section
variable {X R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
def cellIdx (m n : Nat) : Nat := if m < n then n * n + (m + n + 1) else m * m + n

theorem cellAt_cellIdx (m n : Nat) : cellAt (cellIdx m n) = (m, n) := by
  unfold cellIdx
  rcases Nat.lt_or_ge m n with h | h
  · rw [if_pos h, cellAt_block n (m + n + 1) (by omega), if_neg (by omega),
        show m + n + 1 - n - 1 = m from by omega]
  · rw [if_neg (Nat.not_lt.mpr h), cellAt_block m n (by omega), if_pos h]

/-- Technical lemma used in the public import closure. -/
theorem rowsum_partialSum_le_flat {A : Nat → Nat → R} (hA : ∀ i j, Nonneg (A i j))
    (hflat : RSeq.SeriesSum (fun m => A (cellAt m).1 (cellAt m).2)) (N : Nat) :
    Le (RSeq.partialSum (fun a => (row_seriesSum hA hflat a).sum) N) hflat.sum := by
  have hgrid_le : ∀ P, Le (gridSum A P) hflat.sum := fun P => by
    rw [← partialSum_cellAt_eq_gridSum A P]
    exact partialSum_le_sum (fun m => hA (cellAt m).1 (cellAt m).2) hflat (P * P + 2 * P)
  refine Le_of_tendstoHalf_le
    (tendstoHalf_partialSum (fun a => (row_seriesSum hA hflat a).tends) N)
    (tendstoHalf_const hflat.sum) (fun M' => ?_)
  refine le_trans ?_ (hgrid_le (max N M'))
  refine le_trans
    (partialSum_le_of_termwise_le_upto N
      (fun a _ => partialSum_mono (fun j => hA a j) (le_max_right N M'))) ?_
  exact partialSum_mono (fun a => partialSum_nonneg (fun j => hA a j) (max N M'))
    (le_max_left N M')

/-- Technical lemma used in the public import closure. -/
theorem cellAt_rowsum_le {A : Nat → Nat → R} (hA : ∀ i j, Nonneg (A i j))
    (hflat : RSeq.SeriesSum (fun m => A (cellAt m).1 (cellAt m).2)) :
    Le (cellAt_rowsum hA hflat).sum hflat.sum :=
  le_of_tendsto_le (cellAt_rowsum hA hflat) hflat.sum (rowsum_partialSum_le_flat hA hflat)

/-- Technical lemma used in the public import closure. -/
structure PointwiseDoubleBelow {X R : Type*} [COF R]
    (Φ : Nat → Nat → BFunR X R) (f : BFunR X R) where
  x : X
  hx_f : x ∈ f.dom
  hx_Φ : ∀ a b, x ∈ (Φ a b).dom
  fiber : ∀ a, RSeq.SeriesSum (fun b => (Φ a b).toFun x (hx_Φ a b))
  row : RSeq.SeriesSum (fun a => (fiber a).sum)
  below : COF.lt row.sum (f.toFun x hx_f)

/-- Technical lemma used in the public import closure. -/
def continuity_double (S : IntSpaceRC X R)
    (f : BFunR X R) (hf : f ∈ S.L)
    (Φ : Nat → Nat → BFunR X R) (hΦmem : ∀ a b, Φ a b ∈ S.L)
    (hΦnn : ∀ a b, BFunR.PointwiseNonneg (Φ a b))
    (hΦval : ∀ a b y, ∀ hy : y ∈ (Φ a b).dom,
      Nonneg ((Φ a b).toFun y hy))
    (hGsum : RSeq.SeriesSum (fun m => S.I (Φ (cellAt m).1 (cellAt m).2)))
    (hlt : COF.lt hGsum.sum (S.I f)) :
    PointwiseDoubleBelow Φ f :=
  let psb := S.continuity hf
    (fs := fun m => Φ (cellAt m).1 (cellAt m).2)
    (fun m => hΦmem (cellAt m).1 (cellAt m).2)
    (fun m => hΦnn (cellAt m).1 (cellAt m).2) hGsum hlt
  let hxΦ : ∀ a b, psb.x ∈ (Φ a b).dom := fun a b => by
    have h := psb.hx_fs (cellIdx a b)
    rw [cellAt_cellIdx a b] at h
    exact h
  let hA : ∀ i j, Nonneg ((Φ i j).toFun psb.x (hxΦ i j)) :=
    fun i j => hΦval i j psb.x (hxΦ i j)
  let hflat : RSeq.SeriesSum
      (fun m => (Φ (cellAt m).1 (cellAt m).2).toFun psb.x
        (hxΦ (cellAt m).1 (cellAt m).2)) := by
    simpa using psb.point_sum
  { x := psb.x
    hx_f := psb.hx_f
    hx_Φ := hxΦ
    fiber := fun a => row_seriesSum hA hflat a
    row := cellAt_rowsum hA hflat
    below := lt_of_le_of_lt (cellAt_rowsum_le hA hflat) psb.below }

/-- Technical lemma used in the public import closure. -/
theorem seriesSum_le_termwise {a b : Nat → R} (hx : RSeq.SeriesSum a) (hy : RSeq.SeriesSum b)
    (hbnn : ∀ k, Nonneg (b k)) (hab : ∀ k, Le (a k) (b k)) : Le hx.sum hy.sum := by
  refine le_of_tendsto_le hx hy.sum (fun N => ?_)
  exact le_trans (partialSum_le_of_termwise_le_upto N (fun k _ => hab k))
    (partialSum_le_sum hbnn hy N)

/-- Technical lemma used in the public import closure. -/
theorem seriesSum_abs_le {a : Nat → R} (hx : RSeq.SeriesSum a)
    (habs : RSeq.SeriesSum (fun k => COF.abs (a k))) :
    Le (COF.abs hx.sum) habs.sum := by
  refine COFO.abs_le_of ?_ ?_
  · exact seriesSum_le_termwise hx habs (fun k => abs_nonneg _) (fun k => COFO.le_abs_self _)
  · have hneg : Le ((seriesSum_smul (-1) hx).sum) habs.sum :=
      seriesSum_le_termwise (seriesSum_smul (-1) hx) habs (fun k => abs_nonneg _)
        (fun k => by
          rw [show (-1 : R) * a k = -(a k) from by ring]; exact COFO.neg_le_abs (a k))
    rwa [show (seriesSum_smul (-1) hx).sum = -hx.sum from by
      show (-1 : R) * hx.sum = -hx.sum; ring] at hneg

/-- Technical lemma used in the public import closure. -/
theorem abs_sub_le (a b : R) : Le (COF.abs (a - b)) (COF.abs a + COF.abs b) := by
  have h := COFO.abs_add_le a (-b)
  rwa [show a + (-b) = a - b from by ring, COFO.abs_neg] at h

/-- Technical lemma used in the public import closure. -/
def seriesSum_collapse {a : Nat → R} (h : RSeq.SeriesSum a) (N : Nat) :
    {hc : RSeq.SeriesSum (fun k => if k = 0 then RSeq.partialSum a N else a (N + k)) //
      hc.sum = h.sum} := by
  refine ⟨seriesSum_of_tail 0 (seriesSum_congr (fun l => ?_) (seriesSum_tail h N)), ?_⟩
  · show a (N + 1 + l)
        = (if 0 + 1 + l = 0 then RSeq.partialSum a N else a (N + (0 + 1 + l)))
    rw [if_neg (by omega), show N + (0 + 1 + l) = N + 1 + l from by omega]
  · show RSeq.partialSum (fun k => if k = 0 then RSeq.partialSum a N else a (N + k)) 0
          + (seriesSum_tail h N).sum = h.sum
    have hc0 : RSeq.partialSum (fun k => if k = 0 then RSeq.partialSum a N else a (N + k)) 0
        = RSeq.partialSum a N := rfl
    rw [hc0]
    show RSeq.partialSum a N + (h.sum - RSeq.partialSum a N) = h.sum
    ring

variable {S : IntSpaceRC X R}

/-- Domain membership for the collapsed representative. -/
theorem IntegrableRep.collapseFirst_memAt {r : IntegrableRep S} {x : X}
    (N : Nat) (hdom : r.MemAt x) : (r.collapseFirst N).MemAt x := by
  intro k
  by_cases hk : k = 0
  · simpa [IntegrableRep.collapseFirst, hk] using
      BFunR.seqSum_mem r.fn x hdom N
  · simpa [IntegrableRep.collapseFirst, hk] using hdom (N + k)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.collapseFirst_toFun_seriesSum (r : IntegrableRep S) (N : Nat) (x : X)
    (hdom : r.MemAt x)
    (hx : RSeq.SeriesSum (fun i => r.valueAt x hdom i)) :
    {hc : RSeq.SeriesSum (fun k => (r.collapseFirst N).valueAt x
        (r.collapseFirst_memAt N hdom) k) // hc.sum = hx.sum} := by
  refine ⟨seriesSum_congr (fun k => ?_) (seriesSum_collapse hx N).1, ?_⟩
  · show (if k = 0 then RSeq.partialSum (fun i => r.valueAt x hdom i) N
        else r.valueAt x hdom (N + k)) =
      (if k = 0 then BFunR.seqSum r.fn N else r.fn (N + k)).toFun x
        ((r.collapseFirst_memAt N hdom) k)
    by_cases h : k = 0
    · subst k
      simpa only [if_pos rfl, IntegrableRep.valueAt,
        IntegrableRep.collapseFirst] using
          (BFunR.seqSum_toFun r.fn x hdom N).symm
    · simp only [if_neg h, IntegrableRep.valueAt,
        IntegrableRep.collapseFirst]
  · exact (seriesSum_collapse hx N).2

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.toFun_seriesSum_of_absTail (r : IntegrableRep S) (x : X) (p : Nat)
    (hdom : r.MemAt x)
    (htail : RSeq.SeriesSum
      (fun l => COF.abs (r.valueAt x hdom (p + 1 + l)))) :
    RSeq.SeriesSum (fun m => r.valueAt x hdom m) :=
  seriesSum_of_abs
    (seriesSum_of_tail (u := fun m => COF.abs (r.valueAt x hdom m)) p htail)

/-- Technical lemma used in the public import closure. -/
def rg_sum_of_fiber0 (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) (x : X)
    (hrdom : rg.MemAt x)
    (hΦdom : ∀ b, x ∈ (contΦ rg rn k 0 b).dom)
    (fiber0 : RSeq.SeriesSum
      (fun b => (contΦ rg rn k 0 b).toFun x (hΦdom b))) :
    RSeq.SeriesSum (fun m => rg.valueAt x hrdom m) :=
  rg.toFun_seriesSum_of_absTail x (rg.truncK k) hrdom
    (seriesSum_congr (fun l => by
      change COF.abs (rg.valueAt x hrdom (l + (rg.truncK k + 1))) =
        COF.abs (rg.valueAt x hrdom (rg.truncK k + 1 + l))
      rw [show l + (rg.truncK k + 1) = rg.truncK k + 1 + l from by omega]) fiber0)

/-- Technical lemma used in the public import closure. -/
def rn_sum_of_fiber (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k n : Nat) (x : X)
    (hndom : (rn n).MemAt x)
    (hΦdom : ∀ b, x ∈ (contΦ rg rn k (n + 1) b).dom)
    (fibern : RSeq.SeriesSum
      (fun b => (contΦ rg rn k (n + 1) b).toFun x (hΦdom b))) :
    RSeq.SeriesSum (fun m => (rn n).valueAt x hndom m) :=
  (rn n).toFun_seriesSum_of_absTail x ((rn n).contNf (k + n + 2)) hndom
    (seriesSum_congr (fun l => by
      simp only [contΦ_succ]
      show COF.abs (((rn n).collapseFirst ((rn n).contNf (k + n + 2))).valueAt x
            ((rn n).collapseFirst_memAt ((rn n).contNf (k + n + 2)) hndom)
            (0 + 1 + l)) =
        COF.abs ((rn n).valueAt x hndom
          ((rn n).contNf (k + n + 2) + 1 + l))
      simp only [IntegrableRep.valueAt, IntegrableRep.collapseFirst,
        if_neg (by omega : ¬0 + 1 + l = 0),
        show (rn n).contNf (k + n + 2) + (0 + 1 + l) =
          (rn n).contNf (k + n + 2) + 1 + l by omega])
      (seriesSum_tail fibern 0))

/-- Technical lemma used in the public import closure. -/
def rg_abs_of_fiber0 (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) (x : X)
    (hrdom : rg.MemAt x)
    (hΦdom : ∀ b, x ∈ (contΦ rg rn k 0 b).dom)
    (fiber0 : RSeq.SeriesSum
      (fun b => (contΦ rg rn k 0 b).toFun x (hΦdom b))) :
    RSeq.SeriesSum (fun m => COF.abs (rg.valueAt x hrdom m)) :=
  seriesSum_of_tail (rg.truncK k)
    (seriesSum_congr (fun l => by
      change COF.abs (rg.valueAt x hrdom (l + (rg.truncK k + 1))) =
        COF.abs (rg.valueAt x hrdom (rg.truncK k + 1 + l))
      rw [show l + (rg.truncK k + 1) = rg.truncK k + 1 + l from by omega]) fiber0)

/-- Technical lemma used in the public import closure. -/
def rn_abs_of_fiber (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k n : Nat) (x : X)
    (hndom : (rn n).MemAt x)
    (hΦdom : ∀ b, x ∈ (contΦ rg rn k (n + 1) b).dom)
    (fibern : RSeq.SeriesSum
      (fun b => (contΦ rg rn k (n + 1) b).toFun x (hΦdom b))) :
    RSeq.SeriesSum (fun m => COF.abs ((rn n).valueAt x hndom m)) :=
  seriesSum_of_tail ((rn n).contNf (k + n + 2))
    (seriesSum_congr (fun l => by
      simp only [contΦ_succ]
      show COF.abs (((rn n).collapseFirst ((rn n).contNf (k + n + 2))).valueAt x
            ((rn n).collapseFirst_memAt ((rn n).contNf (k + n + 2)) hndom)
            (0 + 1 + l)) =
        COF.abs ((rn n).valueAt x hndom
          ((rn n).contNf (k + n + 2) + 1 + l))
      simp only [IntegrableRep.valueAt, IntegrableRep.collapseFirst,
        if_neg (by omega : ¬0 + 1 + l = 0),
        show (rn n).contNf (k + n + 2) + (0 + 1 + l) =
          (rn n).contNf (k + n + 2) + 1 + l by omega])
      (seriesSum_tail fibern 0))

/-- Technical lemma used in the public import closure. -/
theorem absSK_le_rg_add_fiber0 (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat) (x : X)
    (hgnn : RepNonneg rg)
    (hrdom : rg.MemAt x)
    (rg_abs : RSeq.SeriesSum (fun m => COF.abs (rg.valueAt x hrdom m)))
    (rg_sum : RSeq.SeriesSum (fun m => rg.valueAt x hrdom m))
    (hΦdom : ∀ b, x ∈ (contΦ rg rn k 0 b).dom)
    (fiber0 : RSeq.SeriesSum
      (fun b => (contΦ rg rn k 0 b).toFun x (hΦdom b))) :
    Le (COF.abs ((BFunR.seqSum rg.fn (rg.truncK k)).toFun x
        (BFunR.seqSum_mem rg.fn x hrdom (rg.truncK k))))
      (rg_sum.sum + fiber0.sum) := by
  rw [BFunR.seqSum_toFun rg.fn x hrdom (rg.truncK k)]
  change Le
    (COF.abs (RSeq.partialSum (fun n => rg.valueAt x hrdom n) (rg.truncK k)))
    (rg_sum.sum + fiber0.sum)
  have htail : Le (COF.abs ((seriesSum_tail rg_sum (rg.truncK k)).sum)) fiber0.sum :=
    seriesSum_abs_le (a := fun l => rg.valueAt x hrdom (rg.truncK k + 1 + l))
      (seriesSum_tail rg_sum (rg.truncK k))
      (seriesSum_congr (fun l => by
        change COF.abs (rg.valueAt x hrdom (l + (rg.truncK k + 1))) =
          COF.abs (rg.valueAt x hrdom (rg.truncK k + 1 + l))
        rw [show l + (rg.truncK k + 1) = rg.truncK k + 1 + l from by omega]) fiber0)
  have hps : RSeq.partialSum (fun m => rg.valueAt x hrdom m) (rg.truncK k)
      = rg_sum.sum - (seriesSum_tail rg_sum (rg.truncK k)).sum := by
    show RSeq.partialSum (fun m => rg.valueAt x hrdom m) (rg.truncK k) =
      rg_sum.sum - (rg_sum.sum -
        RSeq.partialSum (fun m => rg.valueAt x hrdom m) (rg.truncK k))
    ring
  rw [hps]
  refine le_trans (abs_sub_le rg_sum.sum (seriesSum_tail rg_sum (rg.truncK k)).sum) ?_
  rw [COFO.abs_of_nonneg (hgnn x hrdom rg_abs rg_sum)]
  exact le_add (le_refl _) htail

/-- Technical lemma used in the public import closure. -/
theorem mem_seqSum_dom_le {u : Nat → BFunR X R} {x : X} :
    ∀ {N : Nat}, x ∈ (BFunR.seqSum u N).dom → ∀ m, m ≤ N → x ∈ (u m).dom := by
  intro N
  induction N with
  | zero => intro h m hm; rw [Nat.le_zero.mp hm]; exact h
  | succ N ih =>
    intro h m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · exact ih h.1 m (Nat.le_of_lt_succ hlt)
    · rw [heq]; exact h.2

/-- Technical lemma used in the public import closure. -/
theorem rg_dom_of_pdb (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat)
    (pdb : PointwiseDoubleBelow (contΦ rg rn k)
      (BFunR.absf (BFunR.seqSum rg.fn (rg.truncK k)))) :
    ∀ m, pdb.x ∈ (rg.fn m).dom := fun m => by
  rcases Nat.lt_or_ge m (rg.truncK k + 1) with hlt | hge
  · exact mem_seqSum_dom_le pdb.hx_f m (Nat.le_of_lt_succ hlt)
  · have h := pdb.hx_Φ 0 (m - (rg.truncK k + 1))
    rw [contΦ_zero,
        show (m - (rg.truncK k + 1)) + (rg.truncK k + 1) = m from by omega] at h
    exact h

-- Technical note.
set_option maxHeartbeats 1000000 in
/-- Technical lemma used in the public import closure. -/
theorem rn_dom_of_pdb (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) (k : Nat)
    (pdb : PointwiseDoubleBelow (contΦ rg rn k)
      (BFunR.absf (BFunR.seqSum rg.fn (rg.truncK k)))) :
    ∀ n m, pdb.x ∈ ((rn n).fn m).dom := fun n m => by
  rcases Nat.lt_or_ge m ((rn n).contNf (k + n + 2) + 1) with hlt | hge
  · have h := pdb.hx_Φ (n + 1) 0
    rw [contΦ_succ] at h
    exact mem_seqSum_dom_le
      (show pdb.x ∈ (BFunR.seqSum (rn n).fn ((rn n).contNf (k + n + 2))).dom from h) m
      (Nat.le_of_lt_succ hlt)
  · have h := pdb.hx_Φ (n + 1) (m - (rn n).contNf (k + n + 2))
    have hcol : ((rn n).collapseFirst ((rn n).contNf (k + n + 2))).fn
        (m - (rn n).contNf (k + n + 2)) = (rn n).fn m := by
      show (if m - (rn n).contNf (k + n + 2) = 0
            then BFunR.seqSum (rn n).fn ((rn n).contNf (k + n + 2))
            else (rn n).fn ((rn n).contNf (k + n + 2) + (m - (rn n).contNf (k + n + 2))))
          = (rn n).fn m
      rw [if_neg (by omega),
          show (rn n).contNf (k + n + 2) + (m - (rn n).contNf (k + n + 2)) = m from by omega]
    rw [contΦ_succ, hcol] at h
    exact h

/-- Technical lemma used in the public import closure. -/
structure RepSeriesBelow (rg : IntegrableRep S) (rn : Nat → IntegrableRep S) where
  x : X
  rg_dom : rg.MemAt x
  rn_dom : ∀ n, (rn n).MemAt x
  rg_sum : RSeq.SeriesSum (fun m => rg.valueAt x rg_dom m)
  rn_sum : ∀ n, RSeq.SeriesSum (fun m => (rn n).valueAt x (rn_dom n) m)
  total : RSeq.SeriesSum (fun n => (rn_sum n).sum)
  below : COF.lt total.sum rg_sum.sum
  /-- Technical lemma used in the public import closure. -/
  rg_abs : RSeq.SeriesSum (fun m => COF.abs (rg.valueAt x rg_dom m))
  /-- Technical lemma used in the public import closure. -/
  rn_abs : ∀ n, RSeq.SeriesSum (fun m => COF.abs ((rn n).valueAt x (rn_dom n) m))
  /-- Technical lemma used in the public import closure. -/
  total_nonneg : Nonneg total.sum

/-- Technical lemma used in the public import closure. -/
theorem contSlack_pos (rg : IntegrableRep S) {rn : Nat → IntegrableRep S}
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) (hslt : COF.lt hsumI.sum rg.integral) :
    COF.lt 0 (rg.integral - hsumI.sum) := by
  have h := COF.lt_add_left (-hsumI.sum) hslt
  rwa [show -hsumI.sum + hsumI.sum = (0 : R) from by ring,
       show -hsumI.sum + rg.integral = rg.integral - hsumI.sum from by ring] at h

/-- Technical lemma used in the public import closure. -/
def contLevel (rg : IntegrableRep S) {rn : Nat → IntegrableRep S}
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) (hslt : COF.lt hsumI.sum rg.integral) :
    Nat :=
  (COFO.archimedean_pos (rg.integral - hsumI.sum) (contSlack_pos rg hsumI hslt)).val + 2

/-- Technical lemma used in the public import closure. -/
theorem contBudget (rg : IntegrableRep S) {rn : Nat → IntegrableRep S}
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) (hslt : COF.lt hsumI.sum rg.integral) :
    COF.lt (COF.halfPow (contLevel rg hsumI hslt) + COF.halfPow (contLevel rg hsumI hslt)
            + COF.halfPow (contLevel rg hsumI hslt + 1)) (rg.integral - hsumI.sum) := by
  unfold contLevel
  set p := (COFO.archimedean_pos (rg.integral - hsumI.sum) (contSlack_pos rg hsumI hslt)).val
    with hpdef
  have hp : COF.lt (COF.halfPow p) (rg.integral - hsumI.sum) :=
    (COFO.archimedean_pos (rg.integral - hsumI.sum) (contSlack_pos rg hsumI hslt)).property
  refine lt_of_lt_of_le (lt_of_lt_of_le ?_ (le_of_lt (three_halfPow_add2_lt p))) (le_of_lt hp)
  have h := COF.lt_add_left (COF.halfPow (R := R) (p + 2) + COF.halfPow (p + 2))
    (halfPow_lt_succ (R := R) (p + 2))
  rwa [show COF.halfPow (R := R) (p + 2) + COF.halfPow (p + 2) + COF.halfPow (p + 2 + 1)
        = (COF.halfPow (p + 2) + COF.halfPow (p + 2)) + COF.halfPow (p + 2 + 1) from by ring,
       show COF.halfPow (R := R) (p + 2) + COF.halfPow (p + 2) + COF.halfPow (p + 2)
        = (COF.halfPow (p + 2) + COF.halfPow (p + 2)) + COF.halfPow (p + 2) from by ring] at h

/-- Technical lemma used in the public import closure. -/
def continuity_rep_double (rg : IntegrableRep S) (rn : Nat → IntegrableRep S)
    (hgnn : RepNonneg rg) (hnn : ∀ n, RepNonneg (rn n))
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) (hslt : COF.lt hsumI.sum rg.integral) :
    PointwiseDoubleBelow (contΦ rg rn (contLevel rg hsumI hslt))
      (BFunR.absf (BFunR.seqSum rg.fn (rg.truncK (contLevel rg hsumI hslt)))) :=
  continuity_double S
    (BFunR.absf (BFunR.seqSum rg.fn (rg.truncK (contLevel rg hsumI hslt))))
    (S.abs_mem (S.toIntSpaceR.seqSum_mem rg.mem (rg.truncK (contLevel rg hsumI hslt))))
    (contΦ rg rn (contLevel rg hsumI hslt))
    (contΦ_mem rg rn (contLevel rg hsumI hslt))
    (contΦ_pwnn rg rn (contLevel rg hsumI hslt))
    (contΦ_val_nn rg rn (contLevel rg hsumI hslt))
    (contΦ_flat rg rn hnn (contLevel rg hsumI hslt) hsumI)
    (contΦ_flat_lt rg rn hgnn hnn hsumI (contLevel rg hsumI hslt) (contBudget rg hsumI hslt))

/-- Technical lemma used in the public import closure. -/
def continuity_rep (rg : IntegrableRep S) (rn : Nat → IntegrableRep S)
    (hgnn : RepNonneg rg) (hnn : ∀ n, RepNonneg (rn n))
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) (hslt : COF.lt hsumI.sum rg.integral) :
    RepSeriesBelow rg rn := by
  let k := contLevel rg hsumI hslt
  let pdb := continuity_rep_double rg rn hgnn hnn hsumI hslt
  let rgdom : rg.MemAt pdb.x := rg_dom_of_pdb rg rn k pdb
  let rndom : ∀ n, (rn n).MemAt pdb.x := rn_dom_of_pdb rg rn k pdb
  let rowdom : ∀ a b, pdb.x ∈ (contΦ rg rn k a b).dom := pdb.hx_Φ
  let rgs := rg_sum_of_fiber0 rg rn k pdb.x rgdom (rowdom 0) (pdb.fiber 0)
  let rns := fun n => rn_sum_of_fiber rg rn k n pdb.x (rndom n)
    (rowdom (n + 1)) (pdb.fiber (n + 1))
  have h2 : ∀ n, Le (rns n).sum (pdb.fiber (n + 1)).sum := fun n => by
    have cs := (rn n).collapseFirst_toFun_seriesSum
      ((rn n).contNf (k + n + 2)) pdb.x (rndom n) (rns n)
    rw [← cs.2]
    exact seriesSum_le_termwise cs.1 (pdb.fiber (n + 1))
      (fun b => abs_nonneg _) (fun b => COFO.le_abs_self _)
  let rowtail : RSeq.SeriesSum (fun n => (pdb.fiber (n + 1)).sum) :=
    seriesSum_congr (fun n => by rw [show (0 + 1 + n) = n + 1 from by omega])
      (seriesSum_tail pdb.row 0)
  have hnns : ∀ n, Nonneg (rns n).sum :=
    fun n => (hnn n) pdb.x (rndom n)
      (rn_abs_of_fiber rg rn k n pdb.x (rndom n)
        (rowdom (n + 1)) (pdb.fiber (n + 1))) (rns n)
  let total := seriesSum_comparison hnns h2 rowtail
  refine
    { x := pdb.x
      rg_dom := rgdom
      rn_dom := rndom
      rg_sum := rgs
      rn_sum := rns
      total := total
      below := ?_
      rg_abs := rg_abs_of_fiber0 rg rn k pdb.x rgdom (rowdom 0) (pdb.fiber 0)
      rn_abs := fun n => rn_abs_of_fiber rg rn k n pdb.x (rndom n)
        (rowdom (n + 1)) (pdb.fiber (n + 1))
      total_nonneg := seriesSum_nonneg hnns total }
  have hA : Le total.sum (pdb.row.sum - (pdb.fiber 0).sum) := by
    refine le_trans (seriesSum_comparison_le hnns h2 rowtail) ?_
    show Le (pdb.row.sum - RSeq.partialSum (fun a => (pdb.fiber a).sum) 0)
            (pdb.row.sum - (pdb.fiber 0).sum)
    exact le_refl _
  have hrow_lt : COF.lt pdb.row.sum (rgs.sum + (pdb.fiber 0).sum) :=
    lt_of_lt_of_le pdb.below (absSK_le_rg_add_fiber0 rg rn k pdb.x hgnn
      rgdom (rg_abs_of_fiber0 rg rn k pdb.x rgdom (rowdom 0) (pdb.fiber 0))
      rgs (rowdom 0) (pdb.fiber 0))
  have hB : COF.lt (pdb.row.sum - (pdb.fiber 0).sum) rgs.sum := by
    have h := COF.lt_add_left (-(pdb.fiber 0).sum) hrow_lt
    rwa [show -(pdb.fiber 0).sum + pdb.row.sum = pdb.row.sum - (pdb.fiber 0).sum from by ring,
         show -(pdb.fiber 0).sum + (rgs.sum + (pdb.fiber 0).sum) = rgs.sum from by ring] at h
  exact lt_of_le_of_lt hA hB

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.smul_memAt {a : R} {r : IntegrableRep S} {x : X}
    (hdom : r.MemAt x) : (r.smul a).MemAt x := hdom

/-- Technical lemma used in the public import closure. -/
theorem smul_fn_toFun (a : R) (r : IntegrableRep S) (n : Nat) (x : X)
    (hdom : r.MemAt x) :
    (r.smul a).valueAt x (IntegrableRep.smul_memAt hdom) n =
      a * r.valueAt x hdom n := rfl

/-- Technical lemma used in the public import closure. -/
def smul_seriesSum_value (a : R) {r : IntegrableRep S} {x : X}
    (hdom : r.MemAt x)
    (hr : RSeq.SeriesSum (fun k => r.valueAt x hdom k)) :
    RSeq.SeriesSum
      (fun n => (r.smul a).valueAt x (IntegrableRep.smul_memAt hdom) n) :=
  seriesSum_congr (fun n => (smul_fn_toFun a r n x hdom).symm)
    (seriesSum_smul a hr)

/-- Technical lemma used in the public import closure. -/
theorem smul_dom {a : R} {r : IntegrableRep S} {x : X}
    (hd : (r.smul a).MemAt x) : r.MemAt x := hd

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.posPart (r : IntegrableRep S) : IntegrableRep S :=
  (r.add r.absVal).smul COF.half

/-- Domain membership for the positive-part representative. -/
theorem IntegrableRep.posPart_memAt {r : IntegrableRep S} {x : X}
    (hdom : r.MemAt x) : r.posPart.MemAt x :=
  IntegrableRep.smul_memAt
    (IntegrableRep.add_memAt hdom (r.mem_absVal_dom hdom))

/-- I(rg⁺) = ½(I(rg) + ‖rg‖₁)。 -/
theorem IntegrableRep.posPart_integral (r : IntegrableRep S) :
    r.posPart.integral = COF.half * (r.integral + r.normL1) := by
  show ((r.add r.absVal).smul COF.half).integral = COF.half * (r.integral + r.normL1)
  rw [IntegrableRep.integral_smul, IntegrableRep.integral_add]
  rfl

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.integral_le_posPart (r : IntegrableRep S) :
    Le r.integral r.posPart.integral := by
  rw [r.posPart_integral]
  apply le_of_nonneg_sub
  have hin : Le r.integral r.normL1 :=
    le_trans (COFO.le_abs_self r.integral) r.abs_integral_le_normL1
  have key : COF.half * (r.integral + r.normL1) - r.integral
           = COF.half * (r.normL1 - r.integral) := by
    have h2 : (1 : R) = COF.half + COF.half := COF.half_add_half.symm
    calc COF.half * (r.integral + r.normL1) - r.integral
        = COF.half * (r.integral + r.normL1) - (1 : R) * r.integral := by ring
      _ = COF.half * (r.integral + r.normL1) - (COF.half + COF.half) * r.integral := by rw [← h2]
      _ = COF.half * (r.normL1 - r.integral) := by ring
  rw [key]
  exact COFO.mul_nonneg (le_of_lt COFO.half_pos) (nonneg_sub_of_le hin)

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.posPart_value (r : IntegrableRep S) (x : X)
    (hdom : r.MemAt x)
    (hr : RSeq.SeriesSum (fun n => r.valueAt x hdom n)) :
    { hP : RSeq.SeriesSum (fun n => r.posPart.valueAt x
        (r.posPart_memAt hdom) n) // hP.sum = COF.max hr.sum 0 } := by
  let habsdom := r.mem_absVal_dom hdom
  obtain ⟨habs, habseq⟩ := r.absVal_signed_value x hdom hr
  refine ⟨smul_seriesSum_value COF.half
    (IntegrableRep.add_memAt hdom habsdom)
    (add_seriesSum_value hdom habsdom hr habs), ?_⟩
  show COF.half * (hr.sum + habs.sum) = COF.max hr.sum 0
  rw [habseq, COF.max_halfsum, sub_zero]; ring

/-- 2·½ = 1。 -/
theorem two_mul_half : (2 : R) * COF.half = 1 := by
  rw [show (2 : R) = 1 + 1 from by ring, add_mul, one_mul, COF.half_add_half]

/-- Technical lemma used in the public import closure. -/
def posPart_add_absSeriesSum {r : IntegrableRep S} {x : X}
    (hposdom : r.posPart.MemAt x)
    (habs : RSeq.SeriesSum
      (fun n => COF.abs (r.posPart.valueAt x hposdom n))) :
    RSeq.SeriesSum (fun n => COF.abs ((r.add r.absVal).valueAt x
      (smul_dom hposdom) n)) := by
  refine seriesSum_congr (fun n => ?_) (seriesSum_smul (2 : R) habs)
  show (2 : R) * COF.abs (r.posPart.valueAt x hposdom n) =
    COF.abs ((r.add r.absVal).valueAt x (smul_dom hposdom) n)
  have hp : r.posPart.valueAt x hposdom n =
      COF.half * (r.add r.absVal).valueAt x (smul_dom hposdom) n := rfl
  rw [hp, COFO.abs_mul, COFO.abs_of_nonneg (le_of_lt COFO.half_pos),
      show (2 : R) * (COF.half *
          COF.abs ((r.add r.absVal).valueAt x (smul_dom hposdom) n)) =
        ((2 : R) * COF.half) *
          COF.abs ((r.add r.absVal).valueAt x (smul_dom hposdom) n) from by ring,
      two_mul_half, one_mul]

/-- Technical lemma used in the public import closure. -/
def posPart_absSeriesSum_rg {r : IntegrableRep S} {x : X}
    (hposdom : r.posPart.MemAt x)
    (habs : RSeq.SeriesSum
      (fun n => COF.abs (r.posPart.valueAt x hposdom n))) :
    RSeq.SeriesSum (fun k => COF.abs
      (r.valueAt x (add_dom_left (smul_dom hposdom)) k)) :=
  add_absSeriesSum_left (smul_dom hposdom)
    (posPart_add_absSeriesSum hposdom habs)

/-- Technical lemma used in the public import closure. -/
theorem posPart_dom_rg {r : IntegrableRep S} {x : X}
    (hd : r.posPart.MemAt x) : r.MemAt x :=
  add_dom_left (smul_dom hd)

/-- 0 ≤ a ⟹ max(a,0) = a。 -/
theorem max_zero_of_nonneg {a : R} (ha : Nonneg a) : COF.max a 0 = a := by
  rw [COF.max_halfsum, sub_zero, COFO.abs_of_nonneg ha,
      show COF.half * (a + 0 + a) = (COF.half + COF.half) * a from by ring,
      COF.half_add_half, one_mul]

/-- a < 0 ⟹ max(a,0) = 0。 -/
theorem max_zero_of_neg {a : R} (ha : COF.lt a 0) : COF.max a 0 = 0 := by
  have habs : COF.abs a = -a := by
    rw [← COFO.abs_neg a, COFO.abs_of_nonneg (le_of_lt (neg_pos_of_neg ha))]
  rw [COF.max_halfsum, sub_zero, habs, show COF.half * (a + 0 + -a) = (0 : R) from by ring]

/-- Technical lemma used in the public import closure. -/
theorem lt_of_lt_max_zero_of_nonneg {a t : R} (ht : Nonneg t) (h : COF.lt t (COF.max a 0)) :
    COF.lt t a := by
  have hmaxpos : COF.lt 0 (COF.max a 0) := lt_of_nonneg_of_lt ht h
  have habspos : COF.lt 0 (COF.abs a) := lt_of_lt_of_le hmaxpos (COFO.max_le_abs a)
  rcases COFO.lt_or_lt_of_abs_pos habspos with hpos | hneg
  · rwa [max_zero_of_nonneg (le_of_lt hpos)] at h
  · exact absurd (max_zero_of_neg hneg ▸ hmaxpos) (COF.lt_irrefl 0)

/-- Technical lemma used in the public import closure. -/
theorem repNonneg_posPart (r : IntegrableRep S) : RepNonneg r.posPart := by
  intro x hposdom habs hx
  let hrdom := posPart_dom_rg hposdom
  have hr : RSeq.SeriesSum (fun n => r.valueAt x hrdom n) :=
    seriesSum_of_abs (posPart_absSeriesSum_rg hposdom habs)
  obtain ⟨hP, hPeq⟩ := r.posPart_value x hrdom hr
  rw [seriesSum_unique hx hP, hPeq]
  exact COFO.max_zero_nonneg hr.sum

/-- Technical lemma used in the public import closure. -/
def continuity_rep_general (rg : IntegrableRep S) (rn : Nat → IntegrableRep S)
    (hnn : ∀ n, RepNonneg (rn n))
    (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)) (hslt : COF.lt hsumI.sum rg.integral) :
    RepSeriesBelow rg rn := by
  have hsltP : COF.lt hsumI.sum rg.posPart.integral := lt_of_lt_of_le hslt rg.integral_le_posPart
  let rsb := continuity_rep rg.posPart rn (repNonneg_posPart rg) hnn hsumI hsltP
  let rgdom : rg.MemAt rsb.x := posPart_dom_rg rsb.rg_dom
  let rg_absx : RSeq.SeriesSum
      (fun m => COF.abs (rg.valueAt rsb.x rgdom m)) :=
    posPart_absSeriesSum_rg rsb.rg_dom rsb.rg_abs
  let rg_sumx : RSeq.SeriesSum (fun m => rg.valueAt rsb.x rgdom m) :=
    seriesSum_of_abs rg_absx
  refine
    { x := rsb.x
      rg_dom := rgdom
      rn_dom := rsb.rn_dom
      rg_sum := rg_sumx
      rn_sum := rsb.rn_sum
      total := rsb.total
      below := ?_
      rg_abs := rg_absx
      rn_abs := rsb.rn_abs
      total_nonneg := rsb.total_nonneg }
  obtain ⟨hP, hPeq⟩ := rg.posPart_value rsb.x rgdom rg_sumx
  have hrgeq : rsb.rg_sum.sum = COF.max rg_sumx.sum 0 := by
    rw [seriesSum_unique rsb.rg_sum hP, hPeq]
  exact lt_of_lt_max_zero_of_nonneg rsb.total_nonneg (hrgeq ▸ rsb.below)

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
structure RepIntegrationSpace (S : IntSpaceRC X R) where
  /-- Technical lemma used in the public import closure. -/
  integral_add : ∀ r r' : IntegrableRep S, (r.add r').integral = r.integral + r'.integral
  /-- Technical lemma used in the public import closure. -/
  integral_smul : ∀ (a : R) (r : IntegrableRep S), (r.smul a).integral = a * r.integral
  /-- Technical lemma used in the public import closure. -/
  continuity : ∀ (rg : IntegrableRep S) (rn : Nat → IntegrableRep S),
    (∀ n, RepNonneg (rn n)) →
    ∀ (hsumI : RSeq.SeriesSum (fun n => (rn n).integral)),
    COF.lt hsumI.sum rg.integral → RepSeriesBelow rg rn
  /-- Technical lemma used in the public import closure. -/
  normalized : {ρ : IntegrableRep S // ρ.integral = 1}
  /-- Technical lemma used in the public import closure. -/
  cutNat_tendsto : ∀ r : IntegrableRep S,
    RSeq.TendstoHalf (fun n => (r.cutNatVal n).integral) r.integral
  /-- Technical lemma used in the public import closure. -/
  cutSmall_tendsto : ∀ r : IntegrableRep S,
    RSeq.TendstoHalf (fun k => (r.cutSmallVal k).integral) 0

/-- Technical lemma used in the public import closure. -/
def repIntegrationSpace (S : IntSpaceRC X R) : RepIntegrationSpace S where
  integral_add := IntegrableRep.integral_add
  integral_smul := IntegrableRep.integral_smul
  continuity := fun rg rn hnn hsumI hslt => continuity_rep_general rg rn hnn hsumI hslt
  normalized := IntegrableRep.normalized_rep
  cutNat_tendsto := IntegrableRep.cutNat_tendsto_rep
  cutSmall_tendsto := IntegrableRep.cutSmall_tendsto_rep

/-- Technical lemma used in the public import closure. -/
theorem thm_1_18 (S : IntSpaceRC X R) : Nonempty (RepIntegrationSpace S) :=
  ⟨repIntegrationSpace S⟩

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem IntegrableRep.integral_eq_of_normL1_sub_zero (r s : IntegrableRep S)
    (h : (r.sub s).normL1 = 0) : r.integral = s.integral := by
  apply COFO.eq_of_small
  intro k hlt
  have h1 : COF.abs (r.integral - s.integral) = COF.abs ((r.sub s).integral) := by
    rw [IntegrableRep.integral_sub]
  have h2 : Le (COF.abs ((r.sub s).integral)) (r.sub s).normL1 :=
    (r.sub s).abs_integral_le_normL1
  rw [h] at h2
  rw [h1] at hlt
  exact COF.lt_irrefl 0 (COFO.lt_trans (halfPow_pos k) (lt_of_lt_of_le hlt h2))

/-- Technical lemma used in the public import closure. -/
def IntegrableRep.NullRel (r s : IntegrableRep S) : Prop := (r.sub s).normL1 = 0

/-- Technical lemma used in the public import closure. -/
def L1 (S : IntSpaceRC X R) : Type _ := Quot (@IntegrableRep.NullRel X R _ S)

/-- Technical lemma used in the public import closure. -/
def L1.integral (c : L1 S) : R :=
  Quot.lift IntegrableRep.integral
    (fun r s h => IntegrableRep.integral_eq_of_normL1_sub_zero r s h) c

/-- Technical lemma used in the public import closure. -/
theorem L1.integral_mk (r : IntegrableRep S) :
    L1.integral (Quot.mk _ r) = r.integral := rfl

end

end BishopC
