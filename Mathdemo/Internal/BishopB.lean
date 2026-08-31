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
def absf (f : BFunR X R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => COF.abs (f.toFun x hx)
def smul (a : R) (f : BFunR X R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => a * f.toFun x hx
def add (f g : BFunR X R) : BFunR X R where
  dom := f.dom ∩ g.dom
  toFun := fun x hx => f.toFun x hx.1 + g.toFun x hx.2
def cutConst (f : BFunR X R) (a : R) : BFunR X R where
  dom := f.dom
  toFun := fun x hx => COF.min (f.toFun x hx) a
def cutNat (n : Nat) (f : BFunR X R) : BFunR X R := cutConst f (n : R)
def PointwiseNonneg (f : BFunR X R) : Prop :=
  ∀ x : X, ∀ hx : x ∈ f.dom, ¬ COF.lt (f.toFun x hx) 0
end BFunR

namespace COF
variable {R : Type*} [COF R]
abbrev halfPow : Nat → R := COF_core.halfPow
abbrev Close (k : Nat) (a b : R) : Prop := COF_core.Close k a b
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


/-- Technical lemma used in the public import closure. -/
theorem lt_of_lt_of_le {a b c : R} (hab : COF.lt a b) (hbc : Le b c) : COF.lt a c := by
  rcases COF.lt_cotrans hab c with h | h
  · exact h
  · exact absurd h hbc

/-- a < 0 ⟹ 0 < -a。 -/
theorem neg_pos_of_neg {a : R} (h : COF.lt a 0) : COF.lt 0 (-a) := by
  have key := COF.lt_add_left (-a) h
  rwa [show (-a + a) = (0:R) from by ring, show (-a + (0:R)) = -a from by ring] at key
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
end Order

/-! Technical auxiliary material for the public import closure. -/
section OrderO
variable {R : Type*} [COFO R]



/-! Technical auxiliary material for the public import closure. -/
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
end RSeq_core

section CauchyCore
variable {R : Type*} [COF_core R]
end CauchyCore


/-- Technical lemma used in the public import closure. -/
class COFOC (R : Type*) extends COFO R where
  complete : ∀ {v : Nat → R}, IsCauchy v → HasLim v

section Complete
variable {R : Type*} [COFOC R]
end Complete

/-! Technical auxiliary material for the public import closure. -/
section Comparison
variable {R : Type*} [COFOC R]
end Comparison

/-! Technical auxiliary material for the public import closure. -/
section SeriesAlg
variable {R : Type*} [COFO R]
end SeriesAlg

/-! Technical auxiliary material for the public import closure. -/
section SeriesSmul
variable {R : Type*} [COFO R]








end SeriesSmul

/-! Technical auxiliary material for the public import closure. -/
namespace IntSpaceRC
variable {X R : Type*} [COFO R] (S : IntSpaceRC X R)





end IntSpaceRC

/-! Technical auxiliary material for the public import closure. -/
section PosNeg
variable {X R : Type*} [COFO R]
end PosNeg

section CapstonePrep
variable {X R : Type*} [COFOC R] (S : IntSpaceRC X R)
end CapstonePrep

/-! Technical auxiliary material for the public import closure. -/
section Capstone
variable {X R : Type*} [COFOC R] (S : IntSpaceRC X R)

end Capstone







section
variable {R : Type*} [COF R]



end

section
variable {R : Type*} [COFO R]





end

section
variable {R : Type*} [COFOC R]






end

/-! Technical auxiliary material for the public import closure. -/
section
variable {X R : Type*} [COFOC R] (S : IntSpaceRC X R)



end

/-! Technical auxiliary material for the public import closure. -/
section
variable {X R : Type*} [COFOC R]


variable {S : IntSpaceRC X R}






/-! Technical auxiliary material for the public import closure. -/








/-! Technical auxiliary material for the public import closure. -/



/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/




/-! Technical auxiliary material for the public import closure. -/









/-! Technical auxiliary material for the public import closure. -/




/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/


/-! Technical auxiliary material for the public import closure. -/




/-! Technical auxiliary material for the public import closure. -/










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






/-! Technical auxiliary material for the public import closure. -/


/-- Technical lemma used in the public import closure. -/
theorem cellAt_surj (m n : Nat) : ∃ k, cellAt k = (m, n) := by
  rcases Nat.lt_or_ge m n with h | h
  · exact ⟨n * n + (m + n + 1), by
      rw [cellAt_block n (m + n + 1) (by omega), if_neg (by omega),
          show m + n + 1 - n - 1 = m from by omega]⟩
  · exact ⟨m * m + n, by rw [cellAt_block m n (by omega), if_pos h]⟩

/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/



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





/-! Technical auxiliary material for the public import closure. -/



/-! Technical auxiliary material for the public import closure. -/






/-! Technical auxiliary material for the public import closure. -/




/-! Technical auxiliary material for the public import closure. -/















/-! Technical auxiliary material for the public import closure. -/








/-! Technical auxiliary material for the public import closure. -/












/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/










/-! Technical auxiliary material for the public import closure. -/






/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/




/-! Technical auxiliary material for the public import closure. -/






/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/


/-! Technical auxiliary material for the public import closure. -/



/-! Technical auxiliary material for the public import closure. -/








/-! Technical auxiliary material for the public import closure. -/











/-! Technical auxiliary material for the public import closure. -/










/-! Technical auxiliary material for the public import closure. -/





/-! Technical auxiliary material for the public import closure. -/






























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









variable {S : IntSpaceRC X R}











-- Technical note.
set_option maxHeartbeats 1000000 in







/-! Technical auxiliary material for the public import closure. -/



















/-! Technical auxiliary material for the public import closure. -/




/-! Technical auxiliary material for the public import closure. -/






end

end BishopC
