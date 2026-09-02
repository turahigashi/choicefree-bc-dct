import Mathdemo.Internal.BishopSec2_L1
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Pairing
import Init.Data.List.OfFn

namespace BishopC

variable {X R : Type*} [COFOC R]

universe u

/-- Technical lemma used in the public import closure. -/
structure Profile (a b : R) (hab : COF.lt a b) where
  /-- Technical lemma used in the public import closure. -/
  Code : Type u
  /-- Technical lemma used in the public import closure. -/
  embed : Code → R → R
  /-- Technical lemma used in the public import closure. -/
  F : Set Code
  /-- (a) 0 ≤ f ≤ 1 -/
  bound : ∀ f : Code, f ∈ F → ∀ x : R, Le a x → Le x b →
    Nonneg (embed f x) ∧ Le (embed f x) 1
  /-- Technical lemma used in the public import closure. -/
  zeroCode : Code
  has_zero : zeroCode ∈ F
  embed_zero : embed zeroCode = (fun _ => 0)
  oneCode : Code
  has_one : oneCode ∈ F
  embed_one : embed oneCode = (fun _ => 1)
  /-- Technical lemma used in the public import closure. -/
  separating : ∀ u v : R, Le a u → COF.lt u v → Le v b →
    { f : Code //
      f ∈ F ∧
      (∀ t : R, Le a t → Le t u → embed f t = 0) ∧
      (∀ t : R, Le v t → Le t b → embed f t = 1) }
  /-- Technical lemma used in the public import closure. -/
  lambda : Code → R
  /-- Technical lemma used in the public import closure. -/
  mono : ∀ f g : Code, f ∈ F → g ∈ F →
    (∀ x : R, Le a x → Le x b → Le (embed f x) (embed g x)) →
    Le (lambda f) (lambda g)

/-- Tagged profile elements coerce to their represented functions. -/
instance Profile.instCoeFun {a b : R} {hab : COF.lt a b} (P : Profile a b hab) :
    CoeFun P.Code (fun _ => R → R) where
  coe := P.embed

@[simp] theorem Profile.zeroCode_apply {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (x : R) : P.zeroCode x = 0 := by
  simpa using congrFun P.embed_zero x

@[simp] theorem Profile.oneCode_apply {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (x : R) : P.oneCode x = 1 := by
  simpa using congrFun P.embed_one x

/-- Technical lemma used in the public import closure. -/
structure Profile.p_lt {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (u v : R) (delta : R) : Type _ where
  f1 : P.Code
  f1_mem : f1 ∈ P.F
  f2 : P.Code
  f2_mem : f2 ∈ P.F
  cond1 : ∀ t : R, Le a t → Le t b → Le t v → f1 t = 0
  cond2 : ∀ t : R, Le a t → Le t b → Le u t → f2 t = 1
  gap : COF.lt (P.lambda f2 - P.lambda f1) delta

/-- Technical lemma used in the public import closure. -/
structure Profile.p_prime_lt {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (u v : R) (delta : R) : Type _ where
  alpha : R
  alpha_pos : COF.lt 0 alpha
  inner : P.p_lt (COF.max a (u - alpha)) (COF.min b (v + alpha)) delta


/-! Technical auxiliary material for the public import closure. -/

/-! Technical auxiliary material for the public import closure. -/

/-- Le x y ⟹ min x y = x。 -/
theorem cof_min_eq_left_of_le {x y : R} (h : Le x y) : COF.min x y = x := by
  have hxy : Nonneg (y - x) := nonneg_sub_of_le h
  rw [COF.min_halfsum, show x - y = -(y - x) from by ring, COFO.abs_neg, COFO.abs_of_nonneg hxy]
  calc COF.half * (x + y - (y - x)) = (2 * COF.half) * x := by ring
    _ = 1 * x := by rw [two_mul_half]
    _ = x := by ring

/-- Le y x ⟹ min x y = y。 -/
theorem cof_min_eq_right_of_le {x y : R} (h : Le y x) : COF.min x y = y := by
  have hyx : Nonneg (x - y) := nonneg_sub_of_le h
  rw [COF.min_halfsum, COFO.abs_of_nonneg hyx]
  calc COF.half * (x + y - (x - y)) = (2 * COF.half) * y := by ring
    _ = 1 * y := by rw [two_mul_half]
    _ = y := by ring

/-- Le x y ⟹ max x y = y。 -/
theorem cof_max_eq_right_of_le {x y : R} (h : Le x y) : COF.max x y = y := by
  have hxy : Nonneg (y - x) := nonneg_sub_of_le h
  rw [COF.max_halfsum, show x - y = -(y - x) from by ring, COFO.abs_neg, COFO.abs_of_nonneg hxy]
  calc COF.half * (x + y + (y - x)) = (2 * COF.half) * y := by ring
    _ = 1 * y := by rw [two_mul_half]
    _ = y := by ring

/-- Le y x ⟹ max x y = x。 -/
theorem cof_max_eq_left_of_le {x y : R} (h : Le y x) : COF.max x y = x := by
  have hyx : Nonneg (x - y) := nonneg_sub_of_le h
  rw [COF.max_halfsum, COFO.abs_of_nonneg hyx]
  calc COF.half * (x + y + (x - y)) = (2 * COF.half) * x := by ring
    _ = 1 * x := by rw [two_mul_half]
    _ = x := by ring

/-- Technical lemma used in the public import closure. -/
theorem cof_max_le {a b c : R} (ha : Le a c) (hb : Le b c) : Le (COF.max a b) c := by
  apply le_of_nonneg_sub
  rw [COF.max_halfsum]
  have hca : Nonneg (c - a) := nonneg_sub_of_le ha
  have hcb : Nonneg (c - b) := nonneg_sub_of_le hb
  have htri : Le (COF.abs (a - b)) ((c - b) + (c - a)) := by
    have h1 : Le (COF.abs ((c - b) + (-(c - a)))) (COF.abs (c - b) + COF.abs (-(c - a))) :=
      COFO.abs_add_le _ _
    rw [COFO.abs_neg, COFO.abs_of_nonneg hcb, COFO.abs_of_nonneg hca,
        show (c - b) + (-(c - a)) = a - b from by ring] at h1
    exact h1
  have hZ : Nonneg (((c - b) + (c - a)) - COF.abs (a - b)) := nonneg_sub_of_le htri
  have key : c - COF.half * (a + b + COF.abs (a - b))
           = COF.half * (((c - b) + (c - a)) - COF.abs (a - b)) := by
    calc c - COF.half * (a + b + COF.abs (a - b))
        = COF.half * (((c - b) + (c - a)) - COF.abs (a - b)) + (1 - 2 * COF.half) * c := by ring
      _ = COF.half * (((c - b) + (c - a)) - COF.abs (a - b)) + (1 - 1) * c := by rw [two_mul_half]
      _ = COF.half * (((c - b) + (c - a)) - COF.abs (a - b)) := by ring
  rw [key]
  exact COFO.mul_nonneg (le_of_lt COFO.half_pos) hZ

/-- Technical lemma used in the public import closure. -/
theorem sub_min_eq_max_sub (x u : R) : x - COF.min x u = COF.max (x - u) 0 := by
  rw [COF.min_halfsum, COF.max_halfsum, sub_zero, add_zero]
  calc x - COF.half * (x + u - COF.abs (x - u))
      = COF.half * ((x - u) + COF.abs (x - u)) + (1 - 2 * COF.half) * x := by ring
    _ = COF.half * ((x - u) + COF.abs (x - u)) + (1 - 1) * x := by rw [two_mul_half]
    _ = COF.half * ((x - u) + COF.abs (x - u)) := by ring

/-! Technical auxiliary material for the public import closure. -/


/-- Prefix sum with exactly the indexing used in Lemma 3.3. -/
def lemma33Prefix {A : Type*} [Zero A] [Add A] (u : Nat → A) : Nat → A
  | 0 => 0
  | N + 1 => lemma33Prefix u N + u N


/-! ### Elementary order algebra derived from the digest API -/

theorem lemma33_add_le_add_right {a b c : R} (h : Le a b) :
    Le (a + c) (b + c) := by
  apply le_of_nonneg_sub
  have hs := nonneg_sub_of_le h
  convert hs using 1 <;> ring


theorem lemma33_add_le_add_left {a b c : R} (h : Le a b) :
    Le (c + a) (c + b) := by
  have key := lemma33_add_le_add_right (c := c) h
  have e1 : a + c = c + a := by ring
  have e2 : b + c = c + b := by ring
  rw [e1, e2] at key; exact key


theorem lemma33_add_le_add {a b c d : R} (hab : Le a b) (hcd : Le c d) :
    Le (a + c) (b + d) := by
  exact le_trans (lemma33_add_le_add_right (c := c) hab)
    (lemma33_add_le_add_left (c := b) hcd)


theorem lemma33_add_lt_add_right {a b c : R} (h : COF.lt a b) :
    COF.lt (a + c) (b + c) := by
  -- Technical note.
  have key := COF.lt_add_left c h
  have e1 : c + a = a + c := by ring
  have e2 : c + b = b + c := by ring
  rw [e1, e2] at key; exact key


theorem lemma33_add_lt_add_left {a b c : R} (h : COF.lt a b) :
    COF.lt (c + a) (c + b) := by
  exact COF.lt_add_left c h


theorem lemma33_add_lt_add {a b c d : R}
    (hab : COF.lt a b) (hcd : COF.lt c d) :
    COF.lt (a + c) (b + d) := by
  exact COFO.lt_trans (lemma33_add_lt_add_right (c := c) hab)
    (lemma33_add_lt_add_left (c := b) hcd)


theorem lemma33_neg_le_neg {a b : R} (h : Le a b) : Le (-b) (-a) := by
  apply le_of_nonneg_sub
  have hs := nonneg_sub_of_le h
  convert hs using 1 <;> ring


/-- If `a ≤ b` and `c ≤ d`, then `a-d ≤ b-c`. -/
theorem lemma33_sub_le_sub {a b c d : R} (hab : Le a b) (hcd : Le c d) :
    Le (a - d) (b - c) := by
  have h := lemma33_add_le_add hab (lemma33_neg_le_neg hcd)
  convert h using 1 <;> ring


theorem lemma33_sub_le_sub_right {a b c : R} (h : Le a b) :
    Le (a - c) (b - c) := by
  exact lemma33_sub_le_sub h (le_refl c)


theorem lemma33_sub_pos_of_lt {a b : R} (h : COF.lt a b) :
    COF.lt 0 (b - a) := by
  have h' := lemma33_add_lt_add_left (c := -a) h
  convert h' using 1 <;> ring




theorem lemma33_mul_le_mul_right {a b c : R} (hab : Le a b) (hc : Nonneg c) :
    Le (a * c) (b * c) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_left (c := c) hab hc)


theorem lemma33_mul_le_cancel_left {a b c : R} (hc : COF.lt 0 c)
    (h : Le (c * a) (c * b)) : Le a b := by
  have hinv : Nonneg (COFO.inv c) := le_of_lt (COFO.inv_pos hc)
  have hm := mul_le_mul_left (c := COFO.inv c) h hinv
  have hcancel : COFO.inv c * c = (1 : R) := by
    calc
      COFO.inv c * c = c * COFO.inv c := by ring
      _ = 1 := COFO.mul_inv_cancel hc
  simpa [← mul_assoc, hcancel] using hm


/-- Technical lemma used in the public import closure. -/
theorem lemma33_inv_mul_cancel_left {c : R} (hc : COF.lt 0 c) (x : R) :
    COFO.inv c * (c * x) = x := by
  have h : COFO.inv c * c = 1 := by rw [mul_comm]; exact COFO.mul_inv_cancel hc
  calc COFO.inv c * (c * x) = (COFO.inv c * c) * x := by ring
    _ = 1 * x := by rw [h]
    _ = x := by ring


theorem lemma33_mul_lt_mul_left {a b c : R} (hab : COF.lt a b)
    (hc : COF.lt 0 c) : COF.lt (c * a) (c * b) := by
  -- Technical note.
  have hpos : COF.lt 0 (b - a) := by
    have h := COF.lt_add_left (-a) hab
    have e1 : -a + a = (0 : R) := by ring
    have e2 : -a + b = b - a := by ring
    rwa [e1, e2] at h
  have hmul : COF.lt 0 (c * (b - a)) := COFO.mul_pos hc hpos
  have hcc : COF.lt 0 (c * b - c * a) := by
    have e : c * (b - a) = c * b - c * a := by ring
    rwa [e] at hmul
  have h := COF.lt_add_left (c * a) hcc
  have e3 : c * a + 0 = c * a := by ring
  have e4 : c * a + (c * b - c * a) = c * b := by ring
  rwa [e3, e4] at h


theorem lemma33_mul_lt_mul_right {a b c : R} (hab : COF.lt a b)
    (hc : COF.lt 0 c) : COF.lt (a * c) (b * c) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (lemma33_mul_lt_mul_left (c := c) hab hc)


theorem lemma33_natCast_nonneg (m : Nat) : Nonneg (m : R) := by
  induction m with
  | zero => simpa using (nonneg_zero : Nonneg (0 : R))
  | succ m ih =>
      have h1 : Nonneg (1 : R) := le_of_lt COFO.one_pos
      have h := lemma33_add_le_add ih h1
      simpa [Nat.cast_succ] using h


theorem lemma33_natCast_succ_pos (m : Nat) : COF.lt 0 ((m + 1 : Nat) : R) := by
  have hm : Nonneg (m : R) := lemma33_natCast_nonneg m
  have hstep : COF.lt (m : R) ((m : R) + 1) := by
    simpa using (lemma33_add_lt_add_left (c := (m : R)) COFO.one_pos)
  have h := lt_of_le_of_lt hm hstep
  simpa [Nat.cast_succ] using h


theorem lemma33_natCast_mono {m k : Nat} (h : m ≤ k) : Le (m : R) (k : R) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hd : Nonneg (d : R) := lemma33_natCast_nonneg d
  have hs := lemma33_add_le_add_left (c := (m : R)) hd
  simpa [Nat.cast_add] using hs








/-- Nat `2^m` and the scalar `twoPow m` agree. -/
theorem lemma33_natCast_twoPow (m : Nat) : (((2 ^ m : Nat) : R)) = twoPow m := by
  induction m with
  | zero => simp [twoPow]
  | succ m ih =>
      rw [pow_succ, Nat.cast_mul, ih]
      simp [twoPow]
      ring


/-! ### `min`/`max` one-sided order, derived by a located split -/

theorem lemma33_min_le_left (x y : R) : Le (COF.min x y) x := cof_min_le_left x y


theorem lemma33_min_le_right (x y : R) : Le (COF.min x y) y := cof_min_le_right x y


theorem lemma33_le_max_left (x y : R) : Le x (COF.max x y) := by
  -- Technical note.
  apply le_of_nonneg_sub
  have heq : COF.max x y - x = COF.half * (COF.abs (x - y) - (x - y)) := by
    rw [COF.max_halfsum,
        show COF.half * (x + y + COF.abs (x - y)) - x
           = COF.half * (COF.abs (x - y) - (x - y)) + ((COF.half + COF.half) * x - x) from by ring,
        COF.half_add_half, one_mul, sub_self, add_zero]
  rw [heq]
  have hle : Le (x - y) (COF.abs (x - y)) := COFO.le_abs_self (x - y)
  exact COFO.mul_nonneg (le_of_lt COFO.half_pos) (nonneg_sub_of_le hle)


theorem lemma33_le_max_right (x y : R) : Le y (COF.max x y) := by
  -- Technical note.
  apply le_of_nonneg_sub
  have heq : COF.max x y - y = COF.half * (COF.abs (x - y) + (x - y)) := by
    rw [COF.max_halfsum,
        show COF.half * (x + y + COF.abs (x - y)) - y
           = COF.half * (COF.abs (x - y) + (x - y)) + ((COF.half + COF.half) * y - y) from by ring,
        COF.half_add_half, one_mul, sub_self, add_zero]
  rw [heq]
  have hle : Le (-(x - y)) (COF.abs (x - y)) := COFO.neg_le_abs (x - y)
  have hn0 : Nonneg (COF.abs (x - y) - (-(x - y))) := nonneg_sub_of_le hle
  have hn : Nonneg (COF.abs (x - y) + (x - y)) := by
    have he : COF.abs (x - y) - (-(x - y)) = COF.abs (x - y) + (x - y) := by ring
    rwa [he] at hn0
  exact COFO.mul_nonneg (le_of_lt COFO.half_pos) hn


/-! ### Finite sums -/

theorem lemma33_prefix_le (u v : Nat → R) (N : Nat)
    (h : ∀ j, j < N → Le (u j) (v j)) :
    Le (lemma33Prefix u N) (lemma33Prefix v N) := by
  induction N with
  | zero =>
      simpa [lemma33Prefix] using (le_refl (0 : R))
  | succ N ih =>
      have hpre : Le (lemma33Prefix u N) (lemma33Prefix v N) :=
        ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N)))
      have hlast : Le (u N) (v N) := h N (Nat.lt_succ_self N)
      simpa [lemma33Prefix] using lemma33_add_le_add hpre hlast




theorem lemma33_prefix_natCast_mul (u : Nat → Nat) (eps : R) (N : Nat) :
    ((lemma33Prefix u N : Nat) : R) * eps =
      lemma33Prefix (fun j => ((u j : Nat) : R) * eps) N := by
  induction N with
  | zero => simp [lemma33Prefix]
  | succ N ih =>
      simp only [lemma33Prefix, Nat.cast_add, add_mul, ih]


theorem lemma33_foldl_range_eq_prefix (u : Nat → Nat) (N : Nat) :
    (List.range N).foldl (fun acc j => acc + u j) 0 = lemma33Prefix u N := by
  induction N with
  | zero => simp [lemma33Prefix]
  | succ N ih =>
      rw [List.range_succ, List.foldl_append]
      simp [ih, lemma33Prefix]


theorem lemma33_prefix_update_zero (u : Nat → Nat) (r N : Nat) (hN : 0 < N) :
    lemma33Prefix (fun j => if j = 0 then u j + r else u j) N =
      lemma33Prefix u N + r := by
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0; simp [lemma33Prefix]
      · have hwN : (fun j => if j = 0 then u j + r else u j) N = u N := by
          simp only []; rw [if_neg (by omega : ¬ N = 0)]
        simp only [lemma33Prefix, hwN, ih hpos]; omega


/-- Two-step telescoping identity. -/
theorem lemma33_two_step_telescope (u : Nat → R) (k N : Nat) :
    lemma33Prefix (fun r => u (k + r) - u (k + r + 2)) N =
      u k + u (k + 1) - u (k + N) - u (k + N + 1) := by
  induction N with
  | zero => simp [lemma33Prefix]
  | succ N ih =>
      rw [lemma33Prefix, ih]
      have h1 : k + N + 1 = k + (N + 1) := by omega
      have h2 : k + N + 2 = k + (N + 1) + 1 := by omega
      rw [h1, h2]
      ring


theorem lemma33_four_term_le_two_gap
    {ell x0 x1 y0 y1 upper : R}
    (hx0 : Le x0 upper) (hx1 : Le x1 upper)
    (hy0 : Le ell y0) (hy1 : Le ell y1) :
    Le (x0 + x1 - y0 - y1) (2 * (upper - ell)) := by
  have hx : Le (x0 + x1) (upper + upper) := lemma33_add_le_add hx0 hx1
  have hy : Le (ell + ell) (y0 + y1) := lemma33_add_le_add hy0 hy1
  have hs := lemma33_sub_le_sub hx hy
  convert hs using 1 <;> ring


/-! ### Monotonicity of `p` in its numeric bound -/

def lemma33_p_lt_mono {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) {u v d e : R}
    (h : P.p_lt u v d) (hde : Le d e) : P.p_lt u v e := by
  rcases h with ⟨f1, hf1, f2, hf2, hz, ho, hlt⟩
  exact ⟨f1, hf1, f2, hf2, hz, ho, lt_of_lt_of_le hlt hde⟩


def lemma33_p_prime_lt_mono {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) {u v d e : R}
    (h : P.p_prime_lt u v d) (hde : Le d e) : P.p_prime_lt u v e := by
  rcases h with ⟨alpha, halpha, hp⟩
  exact ⟨alpha, halpha, lemma33_p_lt_mono P hp hde⟩


/-!
The theorem body follows below.  It uses a dyadic uniform grid, the original
`f_i/alpha_i` construction, the `A/B` cotransitive split, and the original
subsequence condition.  Exact finite floors are used in step 9.  The audited
public route replaces the earlier selector-style finite-location branch by
explicit data.
-/


/-- Iterate a successor selector from the left endpoint. -/
def lemma33Iter (next : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => next (lemma33Iter next j)


/-- A positive summand is strictly smaller than the sum. -/
theorem lemma33_lt_add_of_pos_right {a c : R} (hc : COF.lt 0 c) :
    COF.lt a (a + c) := by
  simpa using lemma33_add_lt_add_left (c := a) hc


/-- Weak subtraction is antitone in the subtracted argument. -/
theorem lemma33_sub_le_sub_left {a b c : R} (h : Le a b) :
    Le (c - b) (c - a) := by
  exact lemma33_sub_le_sub (le_refl c) h


/-- Strict Nat casts preserve strict order. -/
theorem lemma33_natCast_lt {m k : Nat} (h : m < k) :
    COF.lt (m : R) (k : R) := by
  have hmk : m + 1 ≤ k := h
  have hstep : COF.lt (m : R) (((m + 1 : Nat) : R)) := by
    have hs := lemma33_add_lt_add_left (c := (m : R)) COFO.one_pos
    simpa [Nat.cast_succ] using hs
  exact lt_of_lt_of_le hstep (lemma33_natCast_mono hmk)



/-- Minimality of `Nat.find`, in the negative form used below. -/
theorem lemma33_not_of_lt_find {p : Nat → Prop} [DecidablePred p]
    (H : ∃ n, p n) {m : Nat} (hm : m < Nat.find H) : ¬ p m := by
  intro hpm
  exact (Nat.not_le_of_lt hm) (Nat.find_min' H hpm)


/-! Technical auxiliary material for the public import closure. -/

/--
Data-valued cotransitive classification used by the hardness-4 rewrite.

`false` records the big branch `theta < x`; `true` records the small branch
`x < eps`.  The two branches may overlap mathematically, but the returned
Boolean is a single piece of data and hence restores the exclusivity required
by the finite combinatorics without deciding an order proposition.
-/
def lemma33H4_classify {theta eps : R} (h : COF.lt theta eps) (x : R) :
    {c : Bool //
      (c = true → COF.lt x eps) ∧
      (c = false → COF.lt theta x)} :=
  match COF.lt_cotrans_data h x with
  | .inl hbig =>
      ⟨false, by
        constructor
        · intro hbad
          cases hbad
        · intro _
          exact hbig⟩
  | .inr hsmall =>
      ⟨true, by
        constructor
        · intro _
          exact hsmall
        · intro hbad
          cases hbad⟩



/--
Constructive approximate floor data.  `val` is bounded by `cap`; its upper
bracket uses `eps`, while its lower bracket uses the strictly smaller safe
unit `theta`.  A positive value carries a strict lower bracket.
-/
structure Lemma33H4ApproxFloor (theta eps beta : R) (cap : Nat) where
  val : Nat
  val_le : val ≤ cap
  lower : Le (((val : Nat) : R) * theta) beta
  lower_strict : 0 < val → COF.lt (((val : Nat) : R) * theta) beta
  upper : COF.lt beta ((((val + 1 : Nat) : R)) * eps)


/--
A Bishop-style approximate floor, obtained by descending recursion from a
known upper cap.  The only data-valued branch is `COF.lt_cotrans_data` applied
to the gap `(k+1) * theta < (k+1) * eps`.
-/
def lemma33H4_approxFloor (theta eps beta : R)
    (htheta_eps : COF.lt theta eps) (hbeta_nn : Nonneg beta) :
    (cap : Nat) →
      COF.lt beta ((((cap + 1 : Nat) : R)) * eps) →
      Lemma33H4ApproxFloor theta eps beta cap
  | 0, hupper =>
      { val := 0
        val_le := Nat.le_refl 0
        lower := by rw [Nat.cast_zero, zero_mul]; exact hbeta_nn
        lower_strict := by intro hbad; exfalso; omega
        upper := hupper }
  | cap + 1, hupper =>
      let c : R := (((cap + 1 : Nat) : R))
      have hc : COF.lt 0 c := by
        dsimp [c]
        exact lemma33_natCast_succ_pos cap
      have hgap : COF.lt (c * theta) (c * eps) :=
        lemma33_mul_lt_mul_left htheta_eps hc
      match COF.lt_cotrans_data hgap beta with
      | .inl hbig =>
          { val := cap + 1
            val_le := Nat.le_refl (cap + 1)
            lower := le_of_lt hbig
            lower_strict := fun _ => hbig
            upper := hupper }
      | .inr hsmall =>
          let r := lemma33H4_approxFloor theta eps beta htheta_eps hbeta_nn cap
            hsmall
          { val := r.val
            val_le := Nat.le_trans r.val_le (Nat.le_succ cap)
            lower := r.lower
            lower_strict := r.lower_strict
            upper := r.upper }


/-- A strict term in a finite pointwise comparison makes the whole prefix sum strict. -/
theorem lemma33H4_prefix_lt_of_le_of_exists_lt
    (u v : Nat → R) (N : Nat)
    (hle : ∀ j, j < N → Le (u j) (v j))
    (hstrict : ∃ j, j < N ∧ COF.lt (u j) (v j)) :
    COF.lt (lemma33Prefix u N) (lemma33Prefix v N) := by
  induction N with
  | zero =>
      rcases hstrict with ⟨j, hj, _⟩
      exact absurd hj (Nat.not_lt_zero j)
  | succ N ih =>
      rcases hstrict with ⟨j, hj, hjlt⟩
      by_cases hjlast : j = N
      · subst j
        have hpre : Le (lemma33Prefix u N) (lemma33Prefix v N) :=
          lemma33_prefix_le u v N
            (fun r hr => hle r (Nat.lt_trans hr (Nat.lt_succ_self N)))
        have hleft : Le
            (lemma33Prefix u N + u N)
            (lemma33Prefix v N + u N) :=
          lemma33_add_le_add_right hpre
        have hright : COF.lt
            (lemma33Prefix v N + u N)
            (lemma33Prefix v N + v N) :=
          lemma33_add_lt_add_left hjlt
        simpa [lemma33Prefix] using lt_of_le_of_lt hleft hright
      · have hjN : j < N := by omega
        have hpre : COF.lt (lemma33Prefix u N) (lemma33Prefix v N) :=
          ih
            (fun r hr => hle r (Nat.lt_trans hr (Nat.lt_succ_self N)))
            ⟨j, hjN, hjlt⟩
        have hlast : Le (u N) (v N) := hle N (Nat.lt_succ_self N)
        have hleft : COF.lt
            (lemma33Prefix u N + u N)
            (lemma33Prefix v N + u N) :=
          lemma33_add_lt_add_right hpre
        have hright : Le
            (lemma33Prefix v N + u N)
            (lemma33Prefix v N + v N) :=
          lemma33_add_le_add_left hlast
        simpa [lemma33Prefix] using lt_of_lt_of_le hleft hright


/-- A positive finite Nat prefix contains a positive summand. -/
theorem lemma33H4_exists_pos_of_prefix_pos (u : Nat → Nat) (N : Nat)
    (hpos : 0 < lemma33Prefix u N) :
    ∃ j, j < N ∧ 0 < u j := by
  induction N with
  | zero => simpa [lemma33Prefix] using hpos
  | succ N ih =>
      by_cases hlast : 0 < u N
      · exact ⟨N, Nat.lt_succ_self N, hlast⟩
      · have hzero : u N = 0 := Nat.eq_zero_of_not_pos hlast
        have hpre : 0 < lemma33Prefix u N := by
          simpa [lemma33Prefix, hzero] using hpos
        rcases ih hpre with ⟨j, hj, hjpos⟩
        exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self N), hjpos⟩


/-- Choice-free dyadic estimate.  The imported `lemma33_succ_le_two_pow_succ`
    pulls `selector-style construction` via `norm_num` in its base case; this replacement
    uses `decide` for the base case and is choice-free. -/
theorem lemma33H4_succ_le_two_pow_succ (m : Nat) : m + 1 ≤ 2 ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hone : 1 ≤ 2 ^ (m + 1) := by omega
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ]
      omega


/-- Choice-free version of `lemma33_two_mul_succ_le_two_pow` (uses the
    choice-free sub-lemma above; proof body otherwise identical). -/
theorem lemma33H4_two_mul_succ_le_two_pow (n : Nat) : 2 * (n + 1) ≤ 2 ^ (n + 2) := by
  have h := Nat.mul_le_mul_left 2 (lemma33H4_succ_le_two_pow_succ n)
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h


/-- Choice-free `0 < 2^m` (imported version uses `simp` in base case → choice). -/
theorem lemma33H4_two_pow_pos (m : Nat) : 0 < 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [pow_succ]
      omega


/-- Choice-free `(N:R)*theta < prefix u N` for a positive constant lower bound.
    The imported version closes its `N=0` base with a non-arithmetic `omega`
    (goal `COF.lt`), which pulls `selector-style construction`; here `exfalso; omega`. -/
theorem lemma33H4_prefix_const_lt (theta : R) (u : Nat → R) (N : Nat)
    (hN : 0 < N) (h : ∀ j, j < N → COF.lt theta (u j)) :
    COF.lt ((N : R) * theta) (lemma33Prefix u N) := by
  induction N with
  | zero => exfalso; omega
  | succ N ih =>
      by_cases hNz : N = 0
      · subst N
        simpa [lemma33Prefix] using h 0 (by omega)
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hNz
        have hpre : COF.lt ((N : R) * theta) (lemma33Prefix u N) :=
          ih hNpos (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N)))
        have hlast : COF.lt theta (u N) := h N (Nat.lt_succ_self N)
        have hs := lemma33_add_lt_add hpre hlast
        convert hs using 1 <;> simp [lemma33Prefix, Nat.cast_succ] <;> ring





/-! Technical auxiliary material for the public import closure. -/

/-- Relative form of `Lemma33Result`: the partition endpoints are an arbitrary
    proper subinterval `[a',b']` of the ambient profile interval `[a,b]`, while
    every `p'` conclusion is still taken in the original profile `P`. -/
structure Lemma33RelResult {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (a' b' : R) (n : Nat) (eps delta : R) where
  N : Nat
  pts : Nat → R
  pts_zero : pts 0 = a'
  pts_N : pts N = b'
  pts_mono : ∀ i, i < N → COF.lt (pts i) (pts (i + 1))
  width_le : ∀ i, i < N → Le (pts (i + 1) - pts i) delta
  M : Nat → Nat
  sum_M : (List.range N).foldl (fun acc i => acc + M (i + 1)) 0 = n
  p_prime_cond : ∀ i, i < N →
    P.p_prime_lt (pts i) (pts (i + 1)) (((M (i + 1) + 1 : Nat) : R) * eps)


/-- Lower bound for the constructive minimum. -/
theorem lemma34_le_min {x y z : R} (hx : Le z x) (hy : Le z y) :
    Le z (COF.min x y) := by
  -- Technical note.
  -- Technical note.
  apply le_of_nonneg_sub
  have heq : COF.min x y - z = COF.half * (((x - z) + (y - z)) - COF.abs (x - y)) := by
    rw [COF.min_halfsum,
        show COF.half * (x + y - COF.abs (x - y)) - z
           = COF.half * (((x - z) + (y - z)) - COF.abs (x - y))
             + ((COF.half + COF.half) * z - z) from by ring,
        COF.half_add_half, one_mul, sub_self, add_zero]
  rw [heq]
  have ha : Nonneg (x - z) := nonneg_sub_of_le hx
  have hb : Nonneg (y - z) := nonneg_sub_of_le hy
  have habs : Le (COF.abs (x - y)) ((x - z) + (y - z)) := by
    have hadd : Le (COF.abs ((x - z) + (-(y - z))))
        (COF.abs (x - z) + COF.abs (-(y - z))) := COFO.abs_add_le (x - z) (-(y - z))
    have hax : COF.abs (x - z) = x - z := COFO.abs_of_nonneg ha
    have hay : COF.abs (-(y - z)) = y - z := by
      rw [COFO.abs_neg]; exact COFO.abs_of_nonneg hb
    have e1 : (x - z) + (-(y - z)) = x - y := by ring
    rw [e1, hax, hay] at hadd
    exact hadd
  have hn : Nonneg (((x - z) + (y - z)) - COF.abs (x - y)) := nonneg_sub_of_le habs
  exact COFO.mul_nonneg (le_of_lt COFO.half_pos) hn


/-- The minimum of two strictly positive constructive reals is strictly positive. -/
theorem lemma34_min_pos {x y : R} (hx : COF.lt 0 x) (hy : COF.lt 0 y) :
    COF.lt 0 (COF.min x y) := by
  -- Technical note.
  have hsum : COF.lt 0 (x + y) :=
    COFO.lt_trans hx (lemma33_lt_add_of_pos_right hy)
  have habs : COF.lt (COF.abs (x - y)) (x + y) := by
    rcases COF.lt_cotrans hsum (COF.abs (x - y)) with hpos | hgoal
    · rcases COFO.lt_or_lt_of_abs_pos hpos with hsgn | hsgn
      · have he : COF.abs (x - y) = x - y := COFO.abs_of_nonneg (le_of_lt hsgn)
        rw [he]
        have h2y : COF.lt 0 (y + y) :=
          COFO.lt_trans hy (lemma33_lt_add_of_pos_right hy)
        have hlt : COF.lt (x - y) ((x - y) + (y + y)) :=
          lemma33_lt_add_of_pos_right h2y
        have e : (x - y) + (y + y) = x + y := by ring
        rw [e] at hlt; exact hlt
      · have hneg : COF.lt 0 (-(x - y)) := by
          have h := COF.lt_add_left (-(x - y)) hsgn
          have e1 : -(x - y) + (x - y) = 0 := by ring
          have e2 : -(x - y) + 0 = -(x - y) := by ring
          rw [e1, e2] at h; exact h
        have he : COF.abs (x - y) = -(x - y) := by
          rw [← COFO.abs_neg (x - y)]
          exact COFO.abs_of_nonneg (le_of_lt hneg)
        rw [he]
        have h2x : COF.lt 0 (x + x) :=
          COFO.lt_trans hx (lemma33_lt_add_of_pos_right hx)
        have hlt : COF.lt (-(x - y)) ((-(x - y)) + (x + x)) :=
          lemma33_lt_add_of_pos_right h2x
        have e : (-(x - y)) + (x + x) = x + y := by ring
        rw [e] at hlt; exact hlt
    · exact hgoal
  rw [COF.min_halfsum]
  exact COFO.mul_pos COFO.half_pos (lemma33_sub_pos_of_lt habs)


/-- Subtracting a nonnegative quantity weakly decreases a number. -/
theorem lemma34_sub_le_self (x y : R) (hy : Nonneg y) : Le (x - y) x := by
  have h := lemma33_sub_le_sub_left (a := 0) (b := y) (c := x) hy
  convert h using 1 <;> ring


/-- Adding a nonnegative quantity weakly increases a number. -/
theorem lemma34_self_le_add (x y : R) (hy : Nonneg y) : Le x (x + y) := by
  have h := lemma33_add_le_add_left (c := x) hy
  simpa using h


/-- Relative Bishop--Cheng Lemma 3.3.

The hypothesis is already the ambient-profile statement
`p'_P([a',b']) < (n+1) eps`.  The proof extracts its two endpoint witnesses
`z0,z1`, uses them in place of the literal constants in the verified proof of
`lemma_3_3`, and keeps all output `p'` estimates in the original profile `P`.
This avoids constructing a restricted profile with a non-well-defined
functional. -/
noncomputable def lemma_3_3_rel {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) {a' b' : R}
    (ha' : Le a a') (ha'b' : COF.lt a' b') (hb' : Le b' b)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat)
    (hbudget : P.p_prime_lt a' b' ((((n + 1 : Nat) : R)) * eps))
    (delta : R) (hdelta : COF.lt 0 delta) :
    Lemma33RelResult P a' b' n eps delta := by

  rcases hbudget with ⟨rho, hrho, hpBudget⟩
  rcases hpBudget with
    ⟨z0, hz0F, z1, hz1F, hz0_zero, hz1_one, hbudgetGap⟩

  have hrho_nn : Nonneg rho := le_of_lt hrho

  have hz0_zero_to_b' (t : R) (hat : Le a t) (htb : Le t b)
      (htb' : Le t b') : z0 t = 0 := by
    have hb'rho : Le b' (b' + rho) := lemma34_self_le_add b' rho hrho_nn
    have htmin : Le t (COF.min b (b' + rho)) :=
      lemma34_le_min htb (le_trans htb' hb'rho)
    exact hz0_zero t hat htb htmin

  have hz1_one_from_a' (t : R) (hat : Le a t) (htb : Le t b)
      (ha't : Le a' t) : z1 t = 1 := by
    have hsub : Le (a' - rho) a' := lemma34_sub_le_self a' rho hrho_nn
    have hmax : Le (COF.max a (a' - rho)) a' := cof_max_le ha' hsub
    exact hz1_one t hat htb (le_trans hmax ha't)

  have hz0_le_z1 : ∀ t, Le a t → Le t b → Le (z0 t) (z1 t) := by
    intro t hat htb
    rcases COF.lt_cotrans ha'b' t with ha't | htb'
    · have hz1 : z1 t = 1 := hz1_one_from_a' t hat htb (le_of_lt ha't)
      rw [hz1]
      exact (P.bound z0 hz0F t hat htb).2
    · have hz0 : z0 t = 0 := hz0_zero_to_b' t hat htb (le_of_lt htb')
      rw [hz0]
      exact (P.bound z1 hz1F t hat htb).1

  let lamTop : R := P.lambda z1
  let lamBot : R := P.lambda z0
  let D : R := lamTop - lamBot
  let q : R := (((n + 1 : Nat) : R))

  have hq : COF.lt 0 q := by
    dsimp [q]
    exact lemma33_natCast_succ_pos n

  have hlam01 : Le lamBot lamTop := by
    dsimp [lamBot, lamTop]
    exact P.mono z0 z1 hz0F hz1F hz0_le_z1
  have hD : Nonneg D := by
    dsimp [D]
    exact nonneg_sub_of_le hlam01

  let theta : R := COFO.inv q * D
  have htheta : Nonneg theta := by
    dsimp [theta]
    exact COFO.mul_nonneg (le_of_lt (COFO.inv_pos hq)) hD
  have htheta_eps : COF.lt theta eps := by
    have hm : COF.lt theta (COFO.inv q * (q * eps)) :=
      lemma33_mul_lt_mul_left hbudgetGap (COFO.inv_pos hq)
    rwa [lemma33_inv_mul_cancel_left hq eps] at hm

  /- Step 1: choose a dyadic grid that is simultaneously fine enough for
     `delta` and small enough that the endpoint margin `sigma` stays inside
     the `rho` supplied by the ambient `p'` witness. -/
  let small0 : R := COF.halfPow (n + 2) * delta
  have hsmall0 : COF.lt 0 small0 := by
    dsimp [small0]
    exact COFO.mul_pos (halfPow_pos (n + 2)) hdelta

  let small : R := COF.min small0 rho
  have hsmall : COF.lt 0 small := by
    dsimp [small]
    exact lemma34_min_pos hsmall0 hrho
  have hsmall_nn : Nonneg small := le_of_lt hsmall
  have hsmall_le0 : Le small small0 := by
    dsimp [small]
    exact lemma33_min_le_left small0 rho
  have hsmall_le_rho : Le small rho := by
    dsimp [small]
    exact lemma33_min_le_right small0 rho

  let xarch : R := (b' - a') * COFO.inv small
  have hxarch : COF.lt 0 xarch := by
    dsimp [xarch]
    exact COFO.mul_pos (lemma33_sub_pos_of_lt ha'b') (COFO.inv_pos hsmall)
  have hxarch_nn : Nonneg xarch := le_of_lt hxarch

  let m0 : Nat := (COFO.mul_archimedean xarch).1
  have hm0_arch : Le (COF.abs xarch * COF.halfPow m0) 1 := by
    exact (COFO.mul_archimedean xarch).2
  have hm0_arch' : Le (xarch * COF.halfPow m0) 1 := by
    rw [COFO.abs_of_nonneg hxarch_nn] at hm0_arch
    exact hm0_arch

  have hparent : Le ((b' - a') * COF.halfPow m0) small := by
    have hm := lemma33_mul_le_mul_right hm0_arch' hsmall_nn
    have hcancel : COFO.inv small * small = (1 : R) := by
      calc
        COFO.inv small * small = small * COFO.inv small := by ring
        _ = 1 := COFO.mul_inv_cancel hsmall
    have hleft :
        (xarch * COF.halfPow m0) * small =
          (b' - a') * COF.halfPow m0 := by
      dsimp [xarch]
      calc
        (((b' - a') * COFO.inv small) * COF.halfPow m0) * small =
            ((b' - a') * COF.halfPow m0) * (COFO.inv small * small) := by ring
        _ = (b' - a') * COF.halfPow m0 := by rw [hcancel]; ring
    have hright : (1 : R) * small = small := by ring
    rwa [hleft, hright] at hm

  let e : Nat := m0 + 1
  let d : R := (b' - a') * COF.halfPow e
  have hd : COF.lt 0 d := by
    dsimp [d, e]
    exact COFO.mul_pos (lemma33_sub_pos_of_lt ha'b') (halfPow_pos (m0 + 1))
  have hd_nn : Nonneg d := le_of_lt hd
  have hdouble_d : d + d = (b' - a') * COF.halfPow m0 := by
    dsimp [d, e]
    calc
      (b' - a') * COF.halfPow (m0 + 1) +
          (b' - a') * COF.halfPow (m0 + 1) =
          (b' - a') * (COF.halfPow (m0 + 1) + COF.halfPow (m0 + 1)) := by ring
      _ = (b' - a') * COF.halfPow m0 := by rw [halfPow_succ_add]
  have hd_small : COF.lt d small := by
    have hdd : COF.lt d (d + d) := lemma33_lt_add_of_pos_right hd
    rw [hdouble_d] at hdd
    exact lt_of_lt_of_le hdd hparent
  have hd_small_le : Le d small := le_of_lt hd_small
  have hd_rho : Le d rho := le_trans hd_small_le hsmall_le_rho

  let K : Nat := 2 ^ e
  have hKpos : 0 < K := by
    dsimp [K]
    exact lemma33H4_two_pow_pos e

  let bpt : Nat → R := fun i => a' + (i : R) * d
  have hbpt_zero : bpt 0 = a' := by
    simp [bpt]
  have hbpt_K : bpt K = b' := by
    have hpow : ((K : Nat) : R) = twoPow e := by
      dsimp [K]
      exact lemma33_natCast_twoPow e
    have hunit : twoPow e * COF.halfPow e = (1 : R) := by
      calc
        twoPow e * COF.halfPow e = COF.halfPow e * twoPow e := by ring
        _ = 1 := halfPow_mul_twoPow e
    dsimp [bpt, d]
    rw [hpow]
    calc
      a' + twoPow e * ((b' - a') * COF.halfPow e) =
          a' + (b' - a') * (twoPow e * COF.halfPow e) := by ring
      _ = a' + (b' - a') * 1 := by rw [hunit]
      _ = b' := by ring

  have hbpt_sub (i k : Nat) (hki : k ≤ i) :
      bpt i - bpt k = ((i - k : Nat) : R) * d := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hki
    have hr : (k + r - k : Nat) = r := by omega
    rw [hr]
    dsimp [bpt]
    rw [Nat.cast_add]
    ring

  have hbpt_lt (i k : Nat) (hik : i < k) : COF.lt (bpt i) (bpt k) := by
    have hcast : COF.lt (i : R) (k : R) := lemma33_natCast_lt hik
    have hm : COF.lt ((i : R) * d) ((k : R) * d) :=
      lemma33_mul_lt_mul_right hcast hd
    exact lemma33_add_lt_add_left (c := a') hm

  have hbpt_le (i k : Nat) (hik : i ≤ k) : Le (bpt i) (bpt k) := by
    have hcast : Le (i : R) (k : R) := lemma33_natCast_mono hik
    have hm : Le ((i : R) * d) ((k : R) * d) :=
      lemma33_mul_le_mul_right hcast hd_nn
    exact lemma33_add_le_add_left hm

  have ha'_bpt (i : Nat) (hi : i ≤ K) : Le a' (bpt i) := by
    have hi0 : Nonneg (i : R) := lemma33_natCast_nonneg i
    have hprod : Nonneg ((i : R) * d) := COFO.mul_nonneg hi0 hd_nn
    have h := lemma33_add_le_add_left (c := a') hprod
    simpa [bpt] using h

  have hbpt_b' (i : Nat) (hi : i ≤ K) : Le (bpt i) b' := by
    have h := hbpt_le i K hi
    rwa [hbpt_K] at h

  have ha_bpt (i : Nat) (hi : i ≤ K) : Le a (bpt i) :=
    le_trans ha' (ha'_bpt i hi)

  have hbpt_b (i : Nat) (hi : i ≤ K) : Le (bpt i) b :=
    le_trans (hbpt_b' i hi) hb'

  /- The grid width after at most `2(n+1)` steps is at most `delta`. -/
  let L : Nat := 2 * (n + 1)
  have hLsmall0 : Le ((L : R) * small0) delta := by
    have hnat : L ≤ 2 ^ (n + 2) := by
      dsimp [L]
      exact lemma33H4_two_mul_succ_le_two_pow n
    have hcast : Le (L : R) ((2 ^ (n + 2) : Nat) : R) :=
      lemma33_natCast_mono hnat
    have hm := lemma33_mul_le_mul_right hcast (le_of_lt hsmall0)
    have hpow : (((2 ^ (n + 2) : Nat) : R)) = twoPow (n + 2) :=
      lemma33_natCast_twoPow (n + 2)
    have hunit : twoPow (n + 2) * COF.halfPow (n + 2) = (1 : R) := by
      calc
        twoPow (n + 2) * COF.halfPow (n + 2) =
            COF.halfPow (n + 2) * twoPow (n + 2) := by ring
        _ = 1 := halfPow_mul_twoPow (n + 2)
    have hright : (((2 ^ (n + 2) : Nat) : R)) * small0 = delta := by
      dsimp [small0]
      rw [hpow]
      calc
        twoPow (n + 2) * (COF.halfPow (n + 2) * delta) =
            (twoPow (n + 2) * COF.halfPow (n + 2)) * delta := by ring
        _ = delta := by rw [hunit]; ring
    rwa [hright] at hm

  have hLsmall : Le ((L : R) * small) delta := by
    have hmul : Le ((L : R) * small) ((L : R) * small0) :=
      mul_le_mul_left hsmall_le0 (lemma33_natCast_nonneg L)
    exact le_trans hmul hLsmall0

  /- Step 2: sigma is one quarter of the common grid width. -/
  let sigma : R := COF.half * (COF.half * d)
  have hsigma : COF.lt 0 sigma := by
    dsimp [sigma]
    exact COFO.mul_pos COFO.half_pos (COFO.mul_pos COFO.half_pos hd)
  have hsigma_nn : Nonneg sigma := le_of_lt hsigma
  have hsigma2 : sigma + sigma = COF.half * d := by
    dsimp [sigma]
    calc
      COF.half * (COF.half * d) + COF.half * (COF.half * d) =
          (COF.half + COF.half) * (COF.half * d) := by ring
      _ = COF.half * d := by rw [COF.half_add_half]; ring
  have hsigma4 : (sigma + sigma) + (sigma + sigma) = d := by
    rw [hsigma2]
    calc
      COF.half * d + COF.half * d = (COF.half + COF.half) * d := by ring
      _ = d := by rw [COF.half_add_half]; ring
  have hsigma2_pos : COF.lt 0 (sigma + sigma) := by
    rw [hsigma2]
    exact COFO.mul_pos COFO.half_pos hd
  have hsigma2_lt_d : COF.lt (sigma + sigma) d := by
    have h := lemma33_lt_add_of_pos_right (a := sigma + sigma) hsigma2_pos
    rwa [hsigma4] at h
  have hsigma_lt_d : COF.lt sigma d := by
    exact COFO.lt_trans (lemma33_lt_add_of_pos_right (a := sigma) hsigma) hsigma2_lt_d
  have hsigma_rho : Le sigma rho :=
    le_trans (le_of_lt hsigma_lt_d) hd_rho

  /- Steps 3--4: separator family.  The relative endpoint functions `z1,z0`
     replace the literal constants `1,0`. -/
  let Slot : Nat → P.Code → Prop := fun i g =>
    g ∈ P.F ∧
    (i = 0 → g = z1) ∧
    (i = K + 1 → g = z0) ∧
    (∀ (_hi0 : 0 < i) (_hiK : i ≤ K),
      (∀ t, Le a t → Le t (bpt (i - 1) + sigma) → g t = 0) ∧
      (∀ t, Le (bpt i - sigma) t → Le t b → g t = 1))

  have hSlot : ∀ i : Nat, {g : P.Code // Slot i g} := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      refine ⟨z1, hz1F, ?_, ?_, ?_⟩
      · intro; rfl
      · intro hbad; exact Nat.noConfusion hbad
      · intro hpos; exact absurd hpos (Nat.lt_irrefl 0)
    by_cases hiMid : 0 < i ∧ i ≤ K
    · rcases hiMid with ⟨hiPos, hiK⟩
      let u : R := bpt (i - 1) + sigma
      let v : R := bpt i - sigma
      have him1 : i - 1 ≤ K := by omega
      have hau : Le a u := by
        have hbase := ha_bpt (i - 1) him1
        have hs : Le (bpt (i - 1)) (bpt (i - 1) + sigma) :=
          lemma34_self_le_add (bpt (i - 1)) sigma hsigma_nn
        exact le_trans hbase hs
      have huv : COF.lt u v := by
        have hstep : bpt i - bpt (i - 1) = d := by
          rw [hbpt_sub i (i - 1) (by omega)]
          have hone : (i - (i - 1) : Nat) = 1 := by omega
          rw [hone, Nat.cast_one, one_mul]
        have hraw : COF.lt (bpt (i - 1) + sigma) (bpt i - sigma) := by
          have h := lemma33_add_lt_add_left (c := bpt (i - 1)) hsigma2_lt_d
          have h2 := lemma33_add_lt_add_right (c := -sigma) h
          have e1 : (bpt (i - 1) + (sigma + sigma)) + (-sigma) =
              bpt (i - 1) + sigma := by ring
          have e2 : (bpt (i - 1) + d) + (-sigma) = bpt i - sigma := by
            rw [← hstep]
            ring
          rw [e1, e2] at h2
          exact h2
        exact hraw
      have hvb : Le v b := by
        have hbi := hbpt_b i hiK
        have hminus : Le (bpt i - sigma) (bpt i) :=
          lemma34_sub_le_self (bpt i) sigma hsigma_nn
        exact le_trans hminus hbi
      rcases P.separating u v hau huv hvb with ⟨g, hg, hgz, hgo⟩
      refine ⟨g, hg, ?_, ?_, ?_⟩
      · intro h; exact (hi0 h).elim
      · intro hK1
        subst hK1
        exact absurd hiK (by omega)
      · intro _ _
        constructor
        · intro t hat htu
          exact hgz t hat htu
        · intro t hvt htb
          exact hgo t hvt htb
    · refine ⟨z0, hz0F, ?_, ?_, ?_⟩
      · intro h; exact (hi0 h).elim
      · intro _; rfl
      · intro hiPos hiK
        exact (hiMid ⟨hiPos, hiK⟩).elim

  let f : Nat → P.Code := fun i => (hSlot i).val
  have hf_spec (i : Nat) : Slot i (f i) := (hSlot i).property
  have hf_mem (i : Nat) : f i ∈ P.F := (hf_spec i).1
  have hf_zero : f 0 = z1 := (hf_spec 0).2.1 rfl
  have hf_last : f (K + 1) = z0 := (hf_spec (K + 1)).2.2.1 rfl
  have hf_left (i : Nat) (hi0 : 0 < i) (hiK : i ≤ K) :
      ∀ t, Le a t → Le t (bpt (i - 1) + sigma) → f i t = 0 :=
    (hf_spec i).2.2.2 hi0 hiK |>.1
  have hf_right (i : Nat) (hi0 : 0 < i) (hiK : i ≤ K) :
      ∀ t, Le (bpt i - sigma) t → Le t b → f i t = 1 :=
    (hf_spec i).2.2.2 hi0 hiK |>.2

  have hf_le_top (j : Nat) (hj : j ≤ K + 1) :
      ∀ t, Le a t → Le t b → Le (f j t) (z1 t) := by
    intro t hat htb
    by_cases hj0 : j = 0
    · subst j
      rw [hf_zero]
      exact le_refl _
    by_cases hjlast : j = K + 1
    · subst j
      rw [hf_last]
      exact hz0_le_z1 t hat htb
    have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjK : j ≤ K := by omega
    have him1 : j - 1 ≤ K := by omega
    have hgap : COF.lt a' (bpt (j - 1) + sigma) :=
      lt_of_le_of_lt (ha'_bpt (j - 1) him1)
        (lemma33_lt_add_of_pos_right (a := bpt (j - 1)) hsigma)
    rcases COF.lt_cotrans hgap t with ha't | htlt
    · have ho : z1 t = 1 := hz1_one_from_a' t hat htb (le_of_lt ha't)
      rw [ho]
      exact (P.bound (f j) (hf_mem j) t hat htb).2
    · have hz : f j t = 0 := hf_left j hjPos hjK t hat (le_of_lt htlt)
      rw [hz]
      exact (P.bound z1 hz1F t hat htb).1

  have hbot_le_f (i : Nat) (hi : i ≤ K + 1) :
      ∀ t, Le a t → Le t b → Le (z0 t) (f i t) := by
    intro t hat htb
    by_cases hi0 : i = 0
    · subst i
      rw [hf_zero]
      exact hz0_le_z1 t hat htb
    by_cases hilast : i = K + 1
    · subst i
      rw [hf_last]
      exact le_refl _
    have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hiK : i ≤ K := by omega
    have hsub_lt : COF.lt (bpt i - sigma) (bpt i) := by
      have h := lemma33_lt_add_of_pos_right (a := bpt i - sigma) hsigma
      have he : (bpt i - sigma) + sigma = bpt i := by ring
      rwa [he] at h
    have hgap : COF.lt (bpt i - sigma) b' :=
      lt_of_lt_of_le hsub_lt (hbpt_b' i hiK)
    rcases COF.lt_cotrans hgap t with hlt | htb'
    · have hit : Le (bpt i - sigma) t := le_of_lt hlt
      have ho : f i t = 1 := hf_right i hiPos hiK t hit htb
      rw [ho]
      exact (P.bound z0 hz0F t hat htb).2
    · have hz : z0 t = 0 := hz0_zero_to_b' t hat htb (le_of_lt htb')
      rw [hz]
      exact (P.bound (f i) (hf_mem i) t hat htb).1

  have hf_anti (i j : Nat) (hij : i ≤ j) (hj : j ≤ K + 1) :
      ∀ t, Le a t → Le t b → Le (f j t) (f i t) := by
    intro t hat htb
    by_cases hi0 : i = 0
    · subst i
      rw [hf_zero]
      exact hf_le_top j hj t hat htb
    by_cases hjlast : j = K + 1
    · subst j
      rw [hf_last]
      exact hbot_le_f i (Nat.le_trans hij (Nat.le_refl (K + 1))) t hat htb
    by_cases hijEq : i = j
    · subst j
      exact le_refl (f i t)
    have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hjK : j ≤ K := by omega
    have hijlt : i < j := by omega
    have hjPos : 0 < j := Nat.lt_trans hiPos hijlt
    have hiK : i ≤ K := Nat.le_trans (Nat.le_of_lt hijlt) hjK
    have hgap : COF.lt (bpt i - sigma) (bpt (j - 1) + sigma) := by
      have hijm : i ≤ j - 1 := by omega
      have hbase : Le (bpt i) (bpt (j - 1)) := hbpt_le i (j - 1) hijm
      have hnegpos : COF.lt (-sigma) sigma := by
        have hneg0 : COF.lt (-sigma) 0 := by
          have h := lemma33_add_lt_add_right (c := -sigma) hsigma
          convert h using 1 <;> ring
        exact COFO.lt_trans hneg0 hsigma
      have hlocal : COF.lt (bpt i - sigma) (bpt i + sigma) := by
        convert lemma33_add_lt_add_left (c := bpt i) hnegpos using 1 <;> ring
      have hshift : Le (bpt i + sigma) (bpt (j - 1) + sigma) :=
        lemma33_add_le_add_right hbase
      exact lt_of_lt_of_le hlocal hshift
    rcases COF.lt_cotrans hgap t with htRight | htLeft
    · have hfi : f i t = 1 :=
        hf_right i hiPos hiK t (le_of_lt htRight) htb
      rw [hfi]
      exact (P.bound (f j) (hf_mem j) t hat htb).2
    · have hfj : f j t = 0 :=
        hf_left j hjPos hjK t hat (le_of_lt htLeft)
      rw [hfj]
      exact (P.bound (f i) (hf_mem i) t hat htb).1

  have hlam_anti (i j : Nat) (hij : i ≤ j) (hj : j ≤ K + 1) :
      Le (P.lambda (f j)) (P.lambda (f i)) :=
    P.mono (f j) (f i) (hf_mem j) (hf_mem i) (hf_anti i j hij hj)

  let lam : Nat → R := fun i => P.lambda (f i)
  have hlam_zero : lam 0 = lamTop := by dsimp only [lam, lamTop]; rw [hf_zero]
  have hlam_last : lam (K + 1) = lamBot := by dsimp only [lam, lamBot]; rw [hf_last]
  have hlam_upper (i : Nat) (hi : i ≤ K + 1) : Le (lam i) lamTop := by
    have h := hlam_anti 0 i (Nat.zero_le i) hi
    rw [hf_zero] at h
    exact h
  have hlam_lower (i : Nat) (hi : i ≤ K + 1) : Le lamBot (lam i) := by
    have h := hlam_anti i (K + 1) hi (Nat.le_refl (K + 1))
    rw [hf_last] at h
    exact h
  let alpha : Nat → R := fun i => lam (i - 1) - lam (i + 1)
  have halpha_nn (i : Nat) (hi0 : 0 < i) (hiK : i ≤ K) : Nonneg (alpha i) := by
    have hidx : i - 1 ≤ i + 1 := by omega
    have hle : Le (lam (i + 1)) (lam (i - 1)) :=
      hlam_anti (i - 1) (i + 1) hidx (by omega)
    dsimp [alpha]
    exact nonneg_sub_of_le hle

  let cls : Nat → Bool := fun i =>
    (lemma33H4_classify htheta_eps (alpha i)).1
  have hcls_small (i : Nat) (hci : cls i = true) :
      COF.lt (alpha i) eps := by
    change (lemma33H4_classify htheta_eps (alpha i)).1 = true at hci
    exact (lemma33H4_classify htheta_eps (alpha i)).2.1 hci
  have hcls_big (i : Nat) (hci : cls i = false) :
      COF.lt theta (alpha i) := by
    change (lemma33H4_classify htheta_eps (alpha i)).1 = false at hci
    exact (lemma33H4_classify htheta_eps (alpha i)).2.2 hci

  /- Step 6: retain exactly the grid indices
       i=0 or i=K or cls i=true or cls (i+1)=true.
     `next` is the least retained index strictly to the right. -/
  let Good : Nat → Prop := fun i =>
    i = 0 ∨ i = K ∨
      (0 < i ∧ i ≤ K ∧ cls i = true) ∨
      (i < K ∧ cls (i + 1) = true)

  have hGoodK : Good K := by
    dsimp [Good]
    exact Or.inr (Or.inl rfl)

  have hCand (k : Nat) (hk : k < K) :
      ∃ i : Nat, k < i ∧ i ≤ K ∧ Good i :=
    ⟨K, hk, Nat.le_refl K, hGoodK⟩

  let next : Nat → Nat := fun k =>
    if hk : k < K then Nat.find (hCand k hk) else K

  have hnext_spec (k : Nat) (hk : k < K) :
      k < next k ∧ next k ≤ K ∧ Good (next k) := by
    dsimp [next]
    rw [dif_pos hk]
    exact Nat.find_spec (hCand k hk)

  have hnext_eq_K (k : Nat) (hk : ¬ k < K) : next k = K := by
    dsimp [next]
    rw [dif_neg hk]

  have hnext_le (k : Nat) : next k ≤ K := by
    by_cases hk : k < K
    · exact (hnext_spec k hk).2.1
    · rw [hnext_eq_K k hk]

  have hnext_min (k m : Nat) (hk : k < K)
      (hkm : k < m) (hmn : m < next k) : ¬ Good m := by
    have hnle : next k ≤ K := (hnext_spec k hk).2.1
    have hmK : m ≤ K := Nat.le_trans (Nat.le_of_lt hmn) hnle
    have hnot : ¬ (k < m ∧ m ≤ K ∧ Good m) := by
      dsimp [next] at hmn
      rw [dif_pos hk] at hmn
      exact lemma33_not_of_lt_find (hCand k hk) hmn
    intro hgm
    exact hnot ⟨hkm, hmK, hgm⟩

  let s : Nat → Nat := lemma33Iter next
  have hs_zero : s 0 = 0 := by
    rfl
  have hs_succ (j : Nat) : s (j + 1) = next (s j) := by
    rfl

  have hs_le_K (j : Nat) : s j ≤ K := by
    induction j with
    | zero =>
        rw [hs_zero]
        exact Nat.zero_le K
    | succ j ih =>
        rw [hs_succ]
        exact hnext_le (s j)

  have hs_step (j : Nat) (hj : s j < K) : s j < s (j + 1) := by
    rw [hs_succ]
    exact (hnext_spec (s j) hj).1

  have hs_ge_index (j : Nat) (hjK : j ≤ K) : j ≤ s j := by
    induction j with
    | zero => exact Nat.zero_le (s 0)
    | succ j ih =>
        have hjK' : j ≤ K := Nat.le_trans (Nat.le_succ j) hjK
        have hij : j ≤ s j := ih hjK'
        by_cases hsj : s j < K
        · have hstrict := hs_step j hsj
          omega
        · rw [hs_succ, hnext_eq_K (s j) hsj]
          exact hjK

  have hs_K : s K = K :=
    Nat.le_antisymm (hs_le_K K) (hs_ge_index K (Nat.le_refl K))

  let N : Nat := Nat.find (show ∃ j : Nat, s j = K from ⟨K, hs_K⟩)
  have hs_N : s N = K := by
    dsimp [N]
    exact Nat.find_spec (show ∃ j : Nat, s j = K from ⟨K, hs_K⟩)
  have hN_le_K : N ≤ K := by
    by_contra hbad
    have hKN : K < N := Nat.lt_of_not_ge hbad
    have hnot : s K ≠ K := by
      dsimp [N] at hKN
      exact lemma33_not_of_lt_find (show ∃ j : Nat, s j = K from ⟨K, hs_K⟩) hKN
    exact hnot hs_K
  have hNpos : 0 < N := by
    by_contra hbad
    have hNz : N = 0 := Nat.eq_zero_of_not_pos hbad
    have : (0 : Nat) = K := by simpa [hNz, hs_zero] using hs_N
    omega

  have hs_lt_K_of_lt_N (j : Nat) (hjN : j < N) : s j < K := by
    have hnot : s j ≠ K := by
      dsimp [N] at hjN
      exact lemma33_not_of_lt_find (show ∃ r : Nat, s r = K from ⟨K, hs_K⟩) hjN
    have hle := hs_le_K j
    omega

  have hs_strict (j : Nat) (hjN : j < N) : s j < s (j + 1) :=
    hs_step j (hs_lt_K_of_lt_N j hjN)

  have hs_good_succ (j : Nat) (hjN : j < N) : Good (s (j + 1)) := by
    rw [hs_succ]
    exact (hnext_spec (s j) (hs_lt_K_of_lt_N j hjN)).2.2

  have hs_no_good_between (j m : Nat) (hjN : j < N)
      (hleft : s j < m) (hright : m < s (j + 1)) : ¬ Good m := by
    rw [hs_succ] at hright
    exact hnext_min (s j) m (hs_lt_K_of_lt_N j hjN) hleft hright

  have hs_endpoint_pos (j : Nat) (hjN : j < N) : 0 < s (j + 1) := by
    have h := hs_strict j hjN
    omega

  have hs_endpoint_le_K (j : Nat) : s (j + 1) ≤ K := hs_le_K (j + 1)

  /- If a retained right endpoint is in A, the preceding retained endpoint is
     exactly its immediate predecessor. -/
  have hs_prev_of_small (j : Nat) (hjN : j < N)
      (hSmallEnd : cls (s (j + 1)) = true) :
      s (j + 1) = s j + 1 := by
    have hki := hs_strict j hjN
    by_contra hbad
    have hgap : s j + 1 < s (j + 1) := by omega
    let m : Nat := s (j + 1) - 1
    have hm_eq : m + 1 = s (j + 1) := by
      dsimp [m]
      omega
    have hkm : s j < m := by
      dsimp [m]
      omega
    have hmi : m < s (j + 1) := by
      dsimp [m]
      omega
    have hmK : m < K := by
      have hiK := hs_endpoint_le_K j
      dsimp [m]
      omega
    have hGoodm : Good m := by
      dsimp [Good]
      exact Or.inr (Or.inr
        (Or.inr ⟨hmK, by simpa [hm_eq] using hSmallEnd⟩))
    exact hs_no_good_between j m hjN hkm hmi hGoodm

  /- For a B endpoint, every original grid index crossed by the selected
     interval belongs to B. -/
  have hs_all_big (j m : Nat) (hjN : j < N)
      (hBigEnd : cls (s (j + 1)) = false)
      (hleft : s j < m) (hright : m ≤ s (j + 1)) :
      cls m = false := by
    by_cases hmi : m = s (j + 1)
    · subst m
      exact hBigEnd
    · cases hcm : cls m with
      | false => rfl
      | true =>
          have hmlt : m < s (j + 1) := by omega
          have hmPos : 0 < m := by omega
          have hmK : m ≤ K :=
            Nat.le_trans hright (hs_endpoint_le_K j)
          have hGoodm : Good m := by
            dsimp [Good]
            exact Or.inr (Or.inr
              (Or.inl ⟨hmPos, hmK, hcm⟩))
          exact (hs_no_good_between j m hjN hleft hmlt hGoodm).elim

  /- The common p' witness carried by a selected interval. -/
  have hpprime_of_gap (k i : Nat) (hki : k < i) (hiK : i ≤ K)
      (upper : R) (hgap : COF.lt (lam k - lam (i + 1)) upper) :
      P.p_prime_lt (bpt k) (bpt i) upper := by
    refine ⟨sigma, hsigma, ?_⟩
    refine ⟨f (i + 1), hf_mem (i + 1), f k, hf_mem k, ?_, ?_, ?_⟩
    · intro t hat htb htv
      have htv' : Le t (bpt i + sigma) :=
        le_trans htv (lemma33_min_le_right b (bpt i + sigma))
      by_cases hi : i = K
      · subst i
        rw [hf_last]
        have htbs : Le t (b' + sigma) := by
          rw [hbpt_K] at htv'; exact htv'
        have hsr : Le (b' + sigma) (b' + rho) :=
          lemma33_add_le_add_left hsigma_rho
        have htbr : Le t (b' + rho) := le_trans htbs hsr
        exact hz0_zero t hat htb (lemma34_le_min htb htbr)
      · have hiLt : i < K := by omega
        have hz := hf_left (i + 1) (by omega) (by omega) t hat
          (by rw [Nat.add_sub_cancel]; exact htv')
        exact hz
    · intro t hat htb hut
      have hbase : Le (bpt k - sigma)
          (COF.max a (bpt k - sigma)) := lemma33_le_max_right a (bpt k - sigma)
      have hkt : Le (bpt k - sigma) t := le_trans hbase hut
      by_cases hk : k = 0
      · subst k
        rw [hf_zero]
        have hrs : Le (a' - rho) (a' - sigma) :=
          lemma33_sub_le_sub_left hsigma_rho
        have hrs' : Le (a' - rho) (bpt 0 - sigma) := by
          rw [hbpt_zero]; exact hrs
        have hright : Le (a' - rho) (COF.max a (bpt 0 - sigma)) :=
          le_trans hrs' (lemma33_le_max_right a (bpt 0 - sigma))
        have hleft : Le a (COF.max a (bpt 0 - sigma)) :=
          lemma33_le_max_left a (bpt 0 - sigma)
        have hmax : Le (COF.max a (a' - rho))
            (COF.max a (bpt 0 - sigma)) := cof_max_le hleft hright
        exact hz1_one t hat htb (le_trans hmax hut)
      · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
        have hkK : k ≤ K := Nat.le_trans (Nat.le_of_lt hki) hiK
        exact hf_right k hkPos hkK t hkt htb
    · dsimp only [lam] at hgap; exact hgap

  /- Step 7(a): every retained interval has width at most delta. -/
  have hwidth (j : Nat) (hjN : j < N) :
      Le (bpt (s (j + 1)) - bpt (s j)) delta := by
    let k : Nat := s j
    let i : Nat := s (j + 1)
    have hki : k < i := hs_strict j hjN
    have hiK : i ≤ K := hs_endpoint_le_K j
    have hdist : bpt i - bpt k = ((i - k : Nat) : R) * d :=
      hbpt_sub i k (Nat.le_of_lt hki)
    by_cases hshort : i - k ≤ L
    · have hcast : Le ((i - k : Nat) : R) (L : R) :=
        lemma33_natCast_mono hshort
      have h1 : Le (((i - k : Nat) : R) * d)
          (((i - k : Nat) : R) * small) :=
        mul_le_mul_left hd_small_le (lemma33_natCast_nonneg (i - k))
      have h2 : Le (((i - k : Nat) : R) * small) ((L : R) * small) :=
        lemma33_mul_le_mul_right hcast hsmall_nn
      rw [hdist]
      exact le_trans (le_trans h1 h2) hLsmall
    · have hlong : L < i - k := Nat.lt_of_not_ge hshort
      have hBigEnd : cls i = false := by
        cases hci : cls i with
        | false => rfl
        | true =>
            have hprev := hs_prev_of_small j hjN hci
            dsimp [i, k] at hlong hprev
            exfalso; omega
      let ell : Nat := i - k
      have hellPos : 0 < ell := by dsimp [ell]; omega
      have hAllBig : ∀ r : Nat, r < ell →
          cls (k + r + 1) = false := by
        intro r hr
        apply hs_all_big j (k + r + 1) hjN hBigEnd
        · omega
        · dsimp [ell] at hr
          omega
      have hAllTheta : ∀ r : Nat, r < ell →
          COF.lt theta (alpha (k + r + 1)) := by
        intro r hr
        exact hcls_big (k + r + 1) (hAllBig r hr)
      have hlower : COF.lt ((ell : R) * theta)
          (lemma33Prefix (fun r => alpha (k + r + 1)) ell) :=
        lemma33H4_prefix_const_lt theta (fun r => alpha (k + r + 1)) ell
          hellPos hAllTheta
      have hLell : Le (L : R) (ell : R) :=
        lemma33_natCast_mono (Nat.le_of_lt hlong)
      have hscale : Le ((L : R) * theta) ((ell : R) * theta) :=
        lemma33_mul_le_mul_right hLell htheta
      have hqcancel : q * COFO.inv q = (1 : R) := COFO.mul_inv_cancel hq
      have hLtheta : (L : R) * theta = 2 * D := by
        have hLq : (L : R) * COFO.inv q = 2 := by
          have e : (L : R) = 2 * q := by
            show ((2 * (n + 1) : Nat) : R) = 2 * (((n + 1 : Nat) : R))
            push_cast; ring
          rw [e, mul_assoc, hqcancel, mul_one]
        show (L : R) * (COFO.inv q * D) = 2 * D
        rw [← mul_assoc, hLq]
      have htwo_lower : COF.lt (2 * D)
          (lemma33Prefix (fun r => alpha (k + r + 1)) ell) := by
        rw [← hLtheta]
        exact lt_of_le_of_lt hscale hlower

      have htel :
          lemma33Prefix (fun r => alpha (k + r + 1)) ell =
            lam k + lam (k + 1) - lam i - lam (i + 1) := by
        have hi : k + ell = i := by dsimp [ell]; omega
        have hbase := lemma33_two_step_telescope lam k ell
        have hfun : (fun r => alpha (k + r + 1))
            = (fun r => lam (k + r) - lam (k + r + 2)) := by
          funext r
          dsimp [alpha]
        rw [hfun, hbase, hi]
      have hkK1 : k ≤ K + 1 := by omega
      have hk1K1 : k + 1 ≤ K + 1 := by omega
      have hiK1 : i ≤ K + 1 := by omega
      have hi1K1 : i + 1 ≤ K + 1 := by omega
      have hupper : Le
          (lam k + lam (k + 1) - lam i - lam (i + 1)) (2 * D) := by
        dsimp [D]
        exact lemma33_four_term_le_two_gap
          (hlam_upper k hkK1) (hlam_upper (k + 1) hk1K1)
          (hlam_lower i hiK1) (hlam_lower (i + 1) hi1K1)
      rw [htel] at htwo_lower
      exact (hupper htwo_lower).elim

  /- Step 7(c): on small intervals the two-step increment is already < eps. -/
  have hp_small (j : Nat) (hjN : j < N)
      (hSmallEnd : cls (s (j + 1)) = true) :
      P.p_prime_lt (bpt (s j)) (bpt (s (j + 1))) eps := by
    have hprev := hs_prev_of_small j hjN hSmallEnd
    have hki := hs_strict j hjN
    have hiK := hs_endpoint_le_K j
    apply hpprime_of_gap (s j) (s (j + 1)) hki hiK eps
    have halphaSmall := hcls_small (s (j + 1)) hSmallEnd
    dsimp [alpha] at halphaSmall
    rw [hprev] at halphaSmall
    rw [Nat.add_sub_cancel] at halphaSmall
    rw [hprev]
    exact halphaSmall

  /- The big-interval charge beta_j. -/
  let beta : Nat → R := fun j => lam (s j) - lam (s (j + 1) + 1)
  have hbeta_nn (j : Nat) (hjN : j < N) : Nonneg (beta j) := by
    have hstrict := hs_strict j hjN
    have hbnd := hs_le_K (j + 1)
    have hle : Le (lam (s (j + 1) + 1)) (lam (s j)) :=
      hlam_anti (s j) (s (j + 1) + 1) (by omega) (by omega)
    dsimp [beta]
    exact nonneg_sub_of_le hle
  have hbeta_D (j : Nat) (hjN : j < N) : Le (beta j) D := by
    have hbnd0 := hs_le_K j
    have hbnd1 := hs_le_K (j + 1)
    have hkU := hlam_upper (s j) (by omega)
    have hiL := hlam_lower (s (j + 1) + 1) (by omega)
    dsimp [beta, D]
    exact lemma33_sub_le_sub hkU hiL

  have hp_B_bound (j : Nat) (hjN : j < N) (upper : R)
      (hup : COF.lt (beta j) upper) :
      P.p_prime_lt (bpt (s j)) (bpt (s (j + 1))) upper := by
    apply hpprime_of_gap (s j) (s (j + 1)) (hs_strict j hjN)
      (hs_endpoint_le_K j) upper
    simpa [beta, Nat.add_assoc] using hup

  /- Step 8: big charges are disjoint along the monotone lambda chain. -/
  let Bint : Nat → Prop := fun j =>
    j < N ∧ cls (s (j + 1)) = false

  have hafter_big_small (j : Nat) (hj1N : j + 1 < N)
      (hBj : Bint j) : cls (s (j + 2)) = true := by
    have hjN : j < N := Nat.lt_trans (Nat.lt_succ_self j) hj1N
    have hiGood := hs_good_succ j hjN
    have hiPos := hs_endpoint_pos j hjN
    have hiLtK := hs_lt_K_of_lt_N (j + 1) hj1N
    have hnextSmall : cls (s (j + 1) + 1) = true := by
      rcases hiGood with h0 | hK | hSmallCase | hsucc
      · exfalso; omega
      · exfalso; omega
      · rw [hBj.2] at hSmallCase
        exact Bool.noConfusion hSmallCase.2.2
      · exact hsucc.2
    have hGoodNext : Good (s (j + 1) + 1) := by
      dsimp [Good]
      exact Or.inr (Or.inr
        (Or.inl ⟨by omega, by omega, hnextSmall⟩))
    have hs2 : s (j + 2) = s (j + 1) + 1 := by
      rw [hs_succ]
      have hspec := hnext_spec (s (j + 1)) hiLtK
      have hle : next (s (j + 1)) ≤ s (j + 1) + 1 := by
        by_contra hbad
        have hlt : s (j + 1) + 1 < next (s (j + 1)) :=
          Nat.lt_of_not_ge hbad
        exact hnext_min (s (j + 1)) (s (j + 1) + 1) hiLtK
          (Nat.lt_succ_self _) hlt hGoodNext
      omega
    rw [hs2]
    exact hnextSmall

  have hB_not_consecutive (j : Nat) (hj1N : j + 1 < N)
      (hBj : Bint j) : ¬ Bint (j + 1) := by
    intro hnextB
    have hsmall := hafter_big_small j hj1N hBj
    have h2 : cls (s (j + 2)) = false := hnextB.2
    rw [hsmall] at h2
    exact Bool.noConfusion h2

  let charge : Nat → R := fun j => if Bint j then beta j else 0
  have hcharge_of_B (j : Nat) (hBj : Bint j) : charge j = beta j := by
    dsimp only [charge]
    rw [if_pos hBj]
  have hcharge_of_notB (j : Nat) (hBj : ¬ Bint j) : charge j = 0 := by
    dsimp only [charge]
    rw [if_neg hBj]
  have hcharge_nn (j : Nat) (hjN : j < N) : Nonneg (charge j) := by
    by_cases hBj : Bint j
    · rw [hcharge_of_B j hBj]
      exact hbeta_nn j hjN
    · rw [hcharge_of_notB j hBj]
      exact nonneg_zero

  let cursor : Nat → Nat := fun r =>
    if hr : r = 0 then 0
    else if Bint (r - 1) then s r + 1 else s r

  have hcursor_zero : cursor 0 = 0 := by
    rfl
  have hcursor_succ_B (j : Nat) (hBj : Bint j) :
      cursor (j + 1) = s (j + 1) + 1 := by
    change (if Bint j then s (j + 1) + 1 else s (j + 1)) =
      s (j + 1) + 1
    rw [if_pos hBj]
  have hcursor_succ_notB (j : Nat) (hBj : ¬ Bint j) :
      cursor (j + 1) = s (j + 1) := by
    change (if Bint j then s (j + 1) + 1 else s (j + 1)) = s (j + 1)
    rw [if_neg hBj]

  have hcursor_before_B (j : Nat) (hjN : j < N) (hBj : Bint j) :
      cursor j = s j := by
    by_cases hj0 : j = 0
    · subst j
      rw [hcursor_zero, hs_zero]
    · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
      by_cases hprev : Bint (j - 1)
      · have hnc := hB_not_consecutive (j - 1) (by omega) hprev
        have hji : j - 1 + 1 = j := Nat.sub_add_cancel hjPos
        exact (hnc (by rw [hji]; exact hBj)).elim
      · dsimp only [cursor]
        rw [dif_neg hj0, if_neg hprev]

  have hcursor_after_small (j : Nat) (hjN : j < N)
      (hBj : ¬ Bint j) :
      Le (lamTop - lam (cursor j)) (lamTop - lam (s (j + 1))) := by
    by_cases hj0 : j = 0
    · subst j
      rw [hcursor_zero]
      have hle : Le (lam (s 1)) (lam 0) :=
        hlam_anti 0 (s 1) (Nat.zero_le _)
          (by have := hs_le_K 1; omega)
      exact lemma33_sub_le_sub_left hle
    · by_cases hprev : Bint (j - 1)
      · have hjm1N : j - 1 + 1 < N := by omega
        have hSmallEnd : cls (s ((j - 1) + 2)) = true :=
          hafter_big_small (j - 1) hjm1N hprev
        have hsimm : s (j + 1) = s j + 1 := by
          apply hs_prev_of_small j hjN
          have hidx : (j - 1) + 2 = j + 1 := by omega
          rwa [hidx] at hSmallEnd
        have hc : cursor j = s j + 1 := by
          have hj1 : (j - 1) + 1 = j := by omega
          have hcs := hcursor_succ_B (j - 1) hprev
          rwa [hj1] at hcs
        rw [hc, hsimm]
        exact le_refl (lamTop - lam (s j + 1))
      · have hc : cursor j = s j := by
          dsimp only [cursor]
          rw [dif_neg hj0, if_neg hprev]
        rw [hc]
        have hbnd := hs_le_K (j + 1)
        have hle : Le (lam (s (j + 1))) (lam (s j)) :=
          hlam_anti (s j) (s (j + 1))
            (Nat.le_of_lt (hs_strict j hjN)) (by omega)
        exact lemma33_sub_le_sub_left hle

  have hcharge_prefix (r : Nat) (hrN : r ≤ N) :
      Le (lemma33Prefix charge r) (lamTop - lam (cursor r)) := by
    induction r with
    | zero =>
        rw [hcursor_zero, hlam_zero]
        have h0 : lemma33Prefix charge 0 = (0 : R) := by
          rfl
        have he : lamTop - lamTop = (0 : R) := by ring
        rw [h0, he]
        exact le_refl 0
    | succ j ih =>
        have hjN : j < N := by omega
        have hpre := ih (Nat.le_of_lt hjN)
        by_cases hBj : Bint j
        · have hcBefore := hcursor_before_B j hjN hBj
          have hcAfter := hcursor_succ_B j hBj
          have hch := hcharge_of_B j hBj
          have hpsucc : lemma33Prefix charge (j + 1)
              = lemma33Prefix charge j + charge j := rfl
          rw [hpsucc, hch, hcAfter]
          rw [hcBefore] at hpre
          have hstep : Le (lemma33Prefix charge j + beta j)
              ((lamTop - lam (s j)) + beta j) :=
            lemma33_add_le_add hpre (le_refl (beta j))
          have he : (lamTop - lam (s j)) + beta j
              = lamTop - lam (s (j + 1) + 1) := by
            dsimp [beta]; ring
          rw [he] at hstep
          exact hstep
        · have hcAfter := hcursor_succ_notB j hBj
          have hch := hcharge_of_notB j hBj
          have hpsucc : lemma33Prefix charge (j + 1)
              = lemma33Prefix charge j + charge j := rfl
          rw [hpsucc, hch, add_zero, hcAfter]
          exact le_trans hpre (hcursor_after_small j hjN hBj)

  have hcursorN_le : cursor N ≤ K + 1 := by
    by_cases hNz : N = 0
    · subst N
      have hcz : cursor 0 = 0 := hcursor_zero
      omega
    · by_cases hlastB : Bint (N - 1)
      · have hc : cursor N = s N + 1 := by
          have hNm : (N - 1) + 1 = N := by omega
          have hcs := hcursor_succ_B (N - 1) hlastB
          rwa [hNm] at hcs
        rw [hc]
        have := hs_N
        omega
      · have hc : cursor N = s N := by
          dsimp only [cursor]
          rw [dif_neg hNz, if_neg hlastB]
        rw [hc]
        have := hs_N
        omega

  have hcharge_total : Le (lemma33Prefix charge N) D := by
    have hpref := hcharge_prefix N (Nat.le_refl N)
    have hlowerCursor : Le lamBot (lam (cursor N)) :=
      hlam_lower (cursor N) hcursorN_le
    have htail : Le (lamTop - lam (cursor N)) (lamTop - lamBot) :=
      lemma33_sub_le_sub_left hlowerCursor
    dsimp [D]
    exact le_trans hpref htail

  /- Step 9 (iteration 2): a constructive approximate floor.  Its upper
     unit is `eps`; its lower unit is `theta < eps`. -/
  have hCondD : COF.lt D (((n + 1 : Nat) : R) * eps) := by
    dsimp only [D, lamTop, lamBot]; exact hbudgetGap

  have hqtheta : q * theta = D := by
    dsimp [theta]
    calc
      q * (COFO.inv q * D) = (q * COFO.inv q) * D := by ring
      _ = 1 * D := by rw [COFO.mul_inv_cancel hq]
      _ = D := by ring

  have hnTheta : (((n + 1 : Nat) : R) * theta) = D := by
    dsimp only [q] at hqtheta; exact hqtheta

  have hfloor_upper (j : Nat) (hjN : j < N) :
      COF.lt (beta j) ((((n + 1 : Nat) : R)) * eps) :=
    lt_of_le_of_lt (hbeta_D j hjN) hCondD

  let afloorData : (j : Nat) → j < N →
      Lemma33H4ApproxFloor theta eps (beta j) n :=
    fun j hjN => lemma33H4_approxFloor theta eps (beta j)
      htheta_eps (hbeta_nn j hjN) n (hfloor_upper j hjN)

  let afloor : Nat → Nat := fun j =>
    if hj : j < N then (afloorData j hj).val else 0

  have hafloor_le (j : Nat) (hjN : j < N) : afloor j ≤ n := by
    dsimp [afloor]
    rw [dif_pos hjN]
    exact (afloorData j hjN).val_le

  have hafloor_upper (j : Nat) (hjN : j < N) :
      COF.lt (beta j) ((((afloor j + 1 : Nat) : R)) * eps) := by
    dsimp [afloor]
    rw [dif_pos hjN]
    exact (afloorData j hjN).upper

  have hafloor_lower (j : Nat) (hjN : j < N) :
      Le (((afloor j : Nat) : R) * theta) (beta j) := by
    dsimp [afloor]
    rw [dif_pos hjN]
    exact (afloorData j hjN).lower

  have hafloor_lower_strict (j : Nat) (hjN : j < N)
      (hpos : 0 < afloor j) :
      COF.lt (((afloor j : Nat) : R) * theta) (beta j) := by
    dsimp [afloor] at hpos ⊢
    rw [dif_pos hjN] at hpos ⊢
    exact (afloorData j hjN).lower_strict hpos

  let mraw : Nat → Nat := fun j =>
    if hj : j < N then
      if hSmallEnd : cls (s (j + 1)) = true then 0
      else afloor j
    else 0

  have hmraw_small (j : Nat) (hjN : j < N)
      (hSmallEnd : cls (s (j + 1)) = true) :
      mraw j = 0 := by
    dsimp only [mraw]
    rw [dif_pos hjN, dif_pos hSmallEnd]

  have hmraw_big (j : Nat) (hjN : j < N)
      (hBigEnd : cls (s (j + 1)) = false) :
      mraw j = afloor j := by
    have hnotSmall : ¬ cls (s (j + 1)) = true := by
      intro hsmall
      rw [hBigEnd] at hsmall
      exact Bool.noConfusion hsmall
    dsimp only [mraw]
    rw [dif_pos hjN, dif_neg hnotSmall]

  have hmraw_upper (j : Nat) (hjN : j < N)
      (hBigEnd : cls (s (j + 1)) = false) :
      COF.lt (beta j) ((((mraw j) + 1 : Nat) : R) * eps) := by
    rw [hmraw_big j hjN hBigEnd]
    exact hafloor_upper j hjN

  have hmraw_lower_big_theta (j : Nat) (hjN : j < N)
      (hBigEnd : cls (s (j + 1)) = false) :
      Le (((mraw j : Nat) : R) * theta) (beta j) := by
    rw [hmraw_big j hjN hBigEnd]
    exact hafloor_lower j hjN

  have hmraw_lower_strict_big_theta (j : Nat) (hjN : j < N)
      (hBigEnd : cls (s (j + 1)) = false) (hpos : 0 < mraw j) :
      COF.lt (((mraw j : Nat) : R) * theta) (beta j) := by
    rw [hmraw_big j hjN hBigEnd] at hpos ⊢
    exact hafloor_lower_strict j hjN hpos

  have hmraw_charge_theta (j : Nat) (hjN : j < N) :
      Le (((mraw j : Nat) : R) * theta) (charge j) := by
    cases hEnd : cls (s (j + 1)) with
    | true =>
        have hm := hmraw_small j hjN hEnd
        have hnotB : ¬ Bint j := by
          intro hBint
          have h2 : cls (s (j + 1)) = false := hBint.2
          rw [hEnd] at h2
          exact Bool.noConfusion h2
        rw [hm, hcharge_of_notB j hnotB]
        simpa using (le_refl (0 : R))
    | false =>
        have hBint : Bint j := ⟨hjN, hEnd⟩
        rw [hcharge_of_B j hBint]
        exact hmraw_lower_big_theta j hjN hEnd

  have hmraw_charge_strict_theta (j : Nat) (hjN : j < N)
      (hpos : 0 < mraw j) :
      COF.lt (((mraw j : Nat) : R) * theta) (charge j) := by
    cases hEnd : cls (s (j + 1)) with
    | true =>
        have hm := hmraw_small j hjN hEnd
        rw [hm] at hpos
        exfalso; omega
    | false =>
        have hBint : Bint j := ⟨hjN, hEnd⟩
        rw [hcharge_of_B j hBint]
        exact hmraw_lower_strict_big_theta j hjN hEnd hpos

  let mSum : Nat := lemma33Prefix mraw N

  have hmSum_scale_theta : Le (((mSum : Nat) : R) * theta) D := by
    have hpref : Le
        (lemma33Prefix (fun j => ((mraw j : Nat) : R) * theta) N)
        (lemma33Prefix charge N) :=
      lemma33_prefix_le _ _ N hmraw_charge_theta
    have hcast : ((mSum : Nat) : R) * theta =
        lemma33Prefix (fun j => ((mraw j : Nat) : R) * theta) N := by
      dsimp [mSum]
      exact lemma33_prefix_natCast_mul mraw theta N
    rw [hcast]
    exact le_trans hpref hcharge_total

  have hmSum_le : mSum ≤ n := by
    by_contra hbad
    have hn1 : n + 1 ≤ mSum := by omega
    have hmSumPos : 0 < mSum := by omega
    have hprefPos : 0 < lemma33Prefix mraw N := by
      dsimp only [mSum] at hmSumPos; exact hmSumPos
    rcases lemma33H4_exists_pos_of_prefix_pos mraw N hprefPos with
      ⟨j0, hj0N, hj0pos⟩
    have hprefStrict : COF.lt
        (lemma33Prefix (fun j => ((mraw j : Nat) : R) * theta) N)
        (lemma33Prefix charge N) :=
      lemma33H4_prefix_lt_of_le_of_exists_lt
        (fun j => ((mraw j : Nat) : R) * theta) charge N
        hmraw_charge_theta
        ⟨j0, hj0N, hmraw_charge_strict_theta j0 hj0N hj0pos⟩
    have hcast : ((mSum : Nat) : R) * theta =
        lemma33Prefix (fun j => ((mraw j : Nat) : R) * theta) N := by
      dsimp [mSum]
      exact lemma33_prefix_natCast_mul mraw theta N
    rw [← hcast] at hprefStrict
    have hmD : COF.lt (((mSum : Nat) : R) * theta) D :=
      lt_of_lt_of_le hprefStrict hcharge_total
    have hnat : Le (((n + 1 : Nat) : R)) (mSum : R) :=
      lemma33_natCast_mono hn1
    have hmul : Le
        ((((n + 1 : Nat) : R)) * theta)
        (((mSum : Nat) : R) * theta) :=
      lemma33_mul_le_mul_right hnat htheta
    rw [hnTheta] at hmul
    exact (hmul hmD).elim

  let rem : Nat := n - mSum
  let M : Nat → Nat := fun t =>
    if t = 1 then mraw 0 + rem else mraw (t - 1)

  have hM_shift (j : Nat) :
      M (j + 1) = if j = 0 then mraw j + rem else mraw j := by
    by_cases hj0 : j = 0
    · subst j
      rfl
    · have hj1 : j + 1 ≠ 1 := by omega
      change (if j + 1 = 1 then mraw 0 + rem else mraw j) =
        (if j = 0 then mraw j + rem else mraw j)
      rw [if_neg hj1, if_neg hj0]

  have hM_ge (j : Nat) : mraw j ≤ M (j + 1) := by
    rw [hM_shift]
    split
    · omega
    · exact Nat.le_refl _

  have hsum_M :
      (List.range N).foldl (fun acc j => acc + M (j + 1)) 0 = n := by
    rw [lemma33_foldl_range_eq_prefix (fun j => M (j + 1)) N]
    have hfun : (fun j => M (j + 1)) =
        (fun j => if j = 0 then mraw j + rem else mraw j) := by
      funext j
      exact hM_shift j
    rw [hfun, lemma33_prefix_update_zero mraw rem N hNpos]
    dsimp [mSum, rem]
    exact Nat.add_sub_of_le hmSum_le

  have hp_raw (j : Nat) (hjN : j < N) :
      P.p_prime_lt (bpt (s j)) (bpt (s (j + 1)))
        ((((mraw j) + 1 : Nat) : R) * eps) := by
    cases hEnd : cls (s (j + 1)) with
    | true =>
        have hp := hp_small j hjN hEnd
        have hm := hmraw_small j hjN hEnd
        rw [hm]
        simpa using hp
    | false =>
        exact hp_B_bound j hjN _
          (hmraw_upper j hjN hEnd)

  have hp_final (j : Nat) (hjN : j < N) :
      P.p_prime_lt (bpt (s j)) (bpt (s (j + 1)))
        ((((M (j + 1)) + 1 : Nat) : R) * eps) := by
    have hnat : mraw j + 1 ≤ M (j + 1) + 1 := Nat.add_le_add_right (hM_ge j) 1
    have hcast : Le ((((mraw j) + 1 : Nat) : R))
        (((M (j + 1) + 1 : Nat) : R)) := lemma33_natCast_mono hnat
    have hbound : Le
        ((((mraw j) + 1 : Nat) : R) * eps)
        (((M (j + 1) + 1 : Nat) : R) * eps) :=
      lemma33_mul_le_mul_right hcast (le_of_lt heps)
    exact lemma33_p_prime_lt_mono P (hp_raw j hjN) hbound

  let pts : Nat → R := fun j => bpt (s j)
  refine {
    N := N
    pts := pts
    pts_zero := ?_
    pts_N := ?_
    pts_mono := ?_
    width_le := ?_
    M := M
    sum_M := hsum_M
    p_prime_cond := ?_
  }
  · dsimp [pts]; rw [hs_zero]; exact hbpt_zero
  · dsimp [pts]; rw [hs_N]; exact hbpt_K
  · intro j hjN
    dsimp [pts]
    exact hbpt_lt (s j) (s (j + 1)) (hs_strict j hjN)
  · intro j hjN
    dsimp [pts]
    exact hwidth j hjN
  · intro j hjN
    dsimp [pts]
    exact hp_final j hjN


/-! Technical auxiliary material for the public import closure. -/

/-!
P2a for Bishop--Cheng Lemma 3.4.

Encoding choice: a hybrid representation.  `Lemma34Tower.blocks` is the
finite left-to-right family of distinct retained intervals, each carrying its
positive multiplicity and the local `p'` budget.  `segments` is the flattened
list obtained by repeating each block by its multiplicity.  Thus the flattened
list is already the source proof's enumeration `I₁ᵏ,…,Iₙᵏ`; later refinement
can replace one block by the concatenation supplied by `lemma_3_3_rel` without
having to recover maximal constant runs from a function `Nat → R × R`.

Level `k = 0` represents the source proof's initial family `𝔉₁`.  Its dyadic
width bound is

  halfPow k * max {1, b-a},

so the initial bound is simply `max {1,b-a}` and every successor level halves
that bound.
-/

/-- Dyadic width bound used for the tower at level `k`. -/
noncomputable def lemma34_widthScale (a b : R) (k : Nat) : R :=
  COF.halfPow k * COF.max 1 (b - a)


/-- The dyadic tower width is strictly positive. -/
theorem lemma34_widthScale_pos (a b : R) (k : Nat) :
    COF.lt 0 (lemma34_widthScale a b k) := by
  have hmax : COF.lt 0 (COF.max (1 : R) (b - a)) :=
    lt_of_lt_of_le COFO.one_pos (lemma33_le_max_left (1 : R) (b - a))
  exact COFO.mul_pos (halfPow_pos k) hmax




/-- For every positive `beta`, some tower level has width bound below `beta`. -/
noncomputable def lemma34_widthScale_eventually_lt (a b beta : R)
    (hbeta : COF.lt 0 beta) :
    {k : Nat // COF.lt (lemma34_widthScale a b k) beta} := by
  let H : R := COF.max 1 (b - a)
  have hH : COF.lt 0 H := by
    dsimp [H]
    exact lt_of_lt_of_le COFO.one_pos (lemma33_le_max_left (1 : R) (b - a))
  let q : R := beta * COFO.inv H
  have hq : COF.lt 0 q := by
    dsimp [q]
    exact COFO.mul_pos hbeta (COFO.inv_pos hH)
  let k : Nat := (COFO.archimedean_pos q hq).1
  have hk : COF.lt (COF.halfPow k) q :=
    (COFO.archimedean_pos q hq).2
  have hmul : COF.lt (COF.halfPow k * H) (q * H) :=
    lemma33_mul_lt_mul_right hk hH
  have hinv : COFO.inv H * H = (1 : R) := by
    calc
      COFO.inv H * H = H * COFO.inv H := by ring
      _ = 1 := COFO.mul_inv_cancel hH
  have hqH : q * H = beta := by
    dsimp [q]
    calc
      (beta * COFO.inv H) * H = beta * (COFO.inv H * H) := by ring
      _ = beta * 1 := by rw [hinv]
      _ = beta := by ring
  refine ⟨k, ?_⟩
  change COF.lt (COF.halfPow k * H) beta
  rwa [hqH] at hmul


/-- One retained block of the finite family at tower level `k`.  Zero-charge
subintervals are deliberately absent: the successor construction will use
those transiently to prove `outside`, while only positive multiplicities are
stored as retained blocks. -/
structure Lemma34Block {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (eps : R) (k : Nat) where
  left : R
  right : R
  mult : Nat
  mult_pos : 0 < mult
  left_bound : Le a left
  proper : COF.lt left right
  right_bound : Le right b
  width : Le (right - left) (lemma34_widthScale a b k)
  budget : P.p_prime_lt left right ((((mult + 1 : Nat) : R)) * eps)


/-- Repeat a retained interval according to its positive multiplicity. -/
def Lemma34Block.expand {a b : R} {hab : COF.lt a b}
    {P : Profile a b hab} {eps : R} {k : Nat}
    (B : Lemma34Block P eps k) : List (R × R) :=
  List.replicate B.mult (B.left, B.right)


/-- Total multiplicity of a block family. -/
def lemma34_totalMultiplicity {a b : R} {hab : COF.lt a b}
    {P : Profile a b hab} {eps : R} {k : Nat}
    (blocks : List (Lemma34Block P eps k)) : Nat :=
  (blocks.map (fun B => B.mult)).sum


/-- Flatten a block family into the source proof's repeated enumeration
`I₁ᵏ,…,Iₙᵏ`. -/
def lemma34_flattenBlocks {a b : R} {hab : COF.lt a b}
    {P : Profile a b hab} {eps : R} {k : Nat}
    (blocks : List (Lemma34Block P eps k)) : List (R × R) :=
  blocks.flatMap (fun B => B.expand)


/-- Ordering relation for two entries of the repeated interval enumeration.
Earlier entries have monotone endpoints; they are either literally the same
repeated block or the earlier interval lies weakly to the left. -/
def lemma34_segOrdered (I J : R × R) : Prop :=
  Le I.1 J.1 ∧ Le I.2 J.2 ∧ (Le I.2 J.1 ∨ I = J)


/-- P2 tower state.  The block fields carry invariant (b), while `segments`
carries the repeated enumeration needed for positionwise nesting and the
limit extraction in P3. -/
structure Lemma34Tower {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (n : Nat) (eps : R) (k : Nat) where
  blocks : List (Lemma34Block P eps k)
  blocks_ordered : blocks.Pairwise (fun I J => Le I.right J.left)
  total_mult : lemma34_totalMultiplicity blocks = n
  segments : List (R × R)
  flatten_segments : segments = lemma34_flattenBlocks blocks
  segments_length : segments.length = n
  segments_ordered : segments.Pairwise lemma34_segOrdered
  segment_proper : ∀ I, I ∈ segments →
    Le a I.1 ∧ COF.lt I.1 I.2 ∧ Le I.2 b
  segment_width : ∀ I, I ∈ segments →
    Le (I.2 - I.1) (lemma34_widthScale a b k)
  sigma : R
  sigma_pos : COF.lt 0 sigma
  outside : ∀ x, Le a x → Le x b →
    (∀ I, I ∈ segments → COF.lt I.2 x ∨ COF.lt x I.1) →
    P.p_lt (COF.max a (x - sigma)) (COF.min b (x + sigma)) eps


/-- Positionwise access to the repeated interval enumeration. -/
def Lemma34Tower.segAt {a b : R} {hab : COF.lt a b}
    {P : Profile a b hab} {n : Nat} {eps : R} {k : Nat}
    (T : Lemma34Tower P n eps k) (j : Fin n) : R × R :=
  T.segments.get ⟨j.1, by rw [T.segments_length]; exact j.2⟩


/-- Left endpoint of the interval occupying position `j`. -/
def Lemma34Tower.segL {a b : R} {hab : COF.lt a b}
    {P : Profile a b hab} {n : Nat} {eps : R} {k : Nat}
    (T : Lemma34Tower P n eps k) (j : Fin n) : R :=
  (T.segAt j).1


/-- Right endpoint of the interval occupying position `j`. -/
def Lemma34Tower.segR {a b : R} {hab : COF.lt a b}
    {P : Profile a b hab} {n : Nat} {eps : R} {k : Nat}
    (T : Lemma34Tower P n eps k) (j : Fin n) : R :=
  (T.segAt j).2


/-- Positionwise containment witness returned by the future successor step. -/
structure Lemma34Refines {a b : R} {hab : COF.lt a b}
    {P : Profile a b hab} {n : Nat} {eps : R} {k : Nat}
    (T : Lemma34Tower P n eps k)
    (T' : Lemma34Tower P n eps (k + 1)) : Prop where
  nested : ∀ j : Fin n,
    Le (T.segL j) (T'.segL j) ∧ Le (T'.segR j) (T.segR j)


/-- Every member of a repeated singleton list is the repeated element. -/
theorem lemma34_eq_of_mem_replicate {A : Type*} {x y : A} {n : Nat}
    (h : y ∈ List.replicate n x) : y = x := by
  induction n with
  | zero => simp at h
  | succ n ih =>
      simp only [List.replicate_succ, List.mem_cons] at h
      rcases h with h | h
      · exact h
      · exact ih h


/-- A positive-length repetition contains its repeated element. -/
theorem lemma34_mem_replicate_self {A : Type*} (x : A) {n : Nat}
    (hn : 0 < n) : x ∈ List.replicate n x := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ n =>
      rw [List.replicate_succ]
      apply List.mem_cons_self


/-- A reflexive relation is pairwise true on a repeated singleton list. -/
theorem lemma34_pairwise_replicate {A : Type*} (r : A → A → Prop)
    (x : A) (hxx : r x x) (n : Nat) :
    (List.replicate n x).Pairwise r := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.replicate_succ, ih, hxx]


/-- Initial local `p'` budget on the whole interval. -/
def p2_base_pprime {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (eps : R) (n : Nat)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) :
    P.p_prime_lt a b (((n + 1 : Nat) : R) * eps) := by
  refine ⟨1, COFO.one_pos, ?_⟩
  have hmax : COF.max a (a - 1) = a :=
    cof_max_eq_left_of_le
      (lemma34_sub_le_self a 1 (le_of_lt COFO.one_pos))
  have hmin : COF.min b (b + 1) = b :=
    cof_min_eq_left_of_le
      (lemma34_self_le_add b 1 (le_of_lt COFO.one_pos))
  rw [hmax, hmin]
  refine ⟨P.zeroCode, P.has_zero, P.oneCode, P.has_one, ?_, ?_, h_cond⟩
  · intro t _ _ _
    exact P.zeroCode_apply t
  · intro t _ _ _
    exact P.oneCode_apply t


/-- Base of the outer induction (`k=0`, corresponding to source level `1`).
The single retained block `[a,b]` has multiplicity `n`, and the repeated
segment list consists of `n` copies of `[a,b]`.  Positivity of `n` is exactly
what makes invariant (c) vacuous at the base level. -/
noncomputable def lemma34_tower_base {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (eps : R) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) :
    Lemma34Tower P n eps 0 := by
  have hwidth0 : Le (b - a) (lemma34_widthScale a b 0) := by
    have he : lemma34_widthScale a b 0 = COF.max 1 (b - a) := by
      show COF.halfPow 0 * COF.max (1 : R) (b - a) = COF.max 1 (b - a)
      rw [show (COF.halfPow 0 : R) = 1 from rfl, one_mul]
    rw [he]
    exact lemma33_le_max_right (1 : R) (b - a)
  let B0 : Lemma34Block P eps 0 := {
    left := a
    right := b
    mult := n
    mult_pos := hn
    left_bound := le_refl a
    proper := hab
    right_bound := le_refl b
    width := hwidth0
    budget := p2_base_pprime P eps n h_cond
  }
  refine {
    blocks := [B0]
    blocks_ordered := ?_
    total_mult := ?_
    segments := List.replicate n (a, b)
    flatten_segments := ?_
    segments_length := ?_
    segments_ordered := ?_
    segment_proper := ?_
    segment_width := ?_
    sigma := 1
    sigma_pos := COFO.one_pos
    outside := ?_
  }
  · simp
  · simp [lemma34_totalMultiplicity, B0]
  · simp [lemma34_flattenBlocks, Lemma34Block.expand, B0]
  · simp
  · exact lemma34_pairwise_replicate lemma34_segOrdered (a, b)
      ⟨le_refl a, le_refl b, Or.inr rfl⟩ n
  · intro I hI
    have hEq : I = (a, b) := lemma34_eq_of_mem_replicate hI
    subst I
    exact ⟨le_refl a, hab, le_refl b⟩
  · intro I hI
    have hEq : I = (a, b) := lemma34_eq_of_mem_replicate hI
    subst I
    exact hwidth0
  · intro x hax hxb hout
    have hmem : (a, b) ∈ List.replicate n (a, b) :=
      lemma34_mem_replicate_self (a, b) hn
    exact False.elim
      ((hout (a, b) hmem).elim (fun hbx => hxb hbx) (fun hxa => hax hxa))


/- Technical proof note. -/


/-!
P2b-alpha for Bishop--Cheng Lemma 3.4.

This file constructs all successor-level data except the source proof's
`σ_{k+1}` / `outside` clause.  In particular it:

* applies the verified relative Lemma 3.3 to every retained parent block;
* drops exactly the zero-multiplicity subintervals;
* preserves the total multiplicity `n`;
* proves left-to-right block and segment ordering;
* proves every new segment has the successor width bound and ambient bounds;
* proves positionwise containment of the repeated successor enumeration in
  the previous enumeration.

The remaining P2b-beta task is isolated as the construction of positive
`sigma` and the `outside` field from the discarded zero-multiplicity gaps.

Important signature correction: the successor operation needs
`heps : COF.lt 0 eps`, because every local invocation of `lemma_3_3_rel`
requires it.  This hypothesis is available in `lemma_3_4`.
-/

/-- One interval is contained in another, expressed by endpoint order. -/
def lemma34_intervalNested (I J : R × R) : Prop :=
  Le I.1 J.1 ∧ Le J.2 I.2


/-- Positionwise containment of two equal-length segment lists. -/
inductive Lemma34SegmentsRefine : List (R × R) → List (R × R) → Prop
  | nil : Lemma34SegmentsRefine [] []
  | cons {I J : R × R} {Is Js : List (R × R)} :
      lemma34_intervalNested I J →
      Lemma34SegmentsRefine Is Js →
      Lemma34SegmentsRefine (I :: Is) (J :: Js)




/-- Concatenation preserves positionwise refinement. -/
theorem lemma34_segmentsRefine_append
    {xs ys us vs : List (R × R)}
    (hxy : Lemma34SegmentsRefine xs ys)
    (huv : Lemma34SegmentsRefine us vs) :
    Lemma34SegmentsRefine (xs ++ us) (ys ++ vs) := by
  induction hxy with
  | nil => simpa using huv
  | cons hIJ htail ih =>
      simpa using Lemma34SegmentsRefine.cons hIJ ih


/-- Read a positionwise containment witness at a common list index. -/
theorem lemma34_segmentsRefine_get
    {xs ys : List (R × R)}
    (h : Lemma34SegmentsRefine xs ys) {i : Nat}
    (hix : i < xs.length) (hiy : i < ys.length) :
    lemma34_intervalNested
      (xs.get ⟨i, hix⟩) (ys.get ⟨i, hiy⟩) := by
  induction h generalizing i with
  | nil => exact absurd hix (Nat.not_lt_zero i)
  | cons hIJ htail ih =>
      cases i with
      | zero => exact hIJ
      | succ i =>
          exact ih (Nat.lt_of_succ_lt_succ hix) (Nat.lt_of_succ_lt_succ hiy)


/-- If every member of `ys` lies in `I`, then the list of repeated copies of
`I` refines positionwise to `ys`. -/
theorem lemma34_segmentsRefine_replicate
    (I : R × R) (ys : List (R × R))
    (hmem : ∀ J, J ∈ ys → lemma34_intervalNested I J) :
    Lemma34SegmentsRefine (List.replicate ys.length I) ys := by
  revert hmem
  induction ys with
  | nil =>
      intro _
      exact Lemma34SegmentsRefine.nil
  | cons J Js ih =>
      intro hmem
      rw [List.length_cons, List.replicate_succ]
      exact Lemma34SegmentsRefine.cons
        (hmem J (by simp))
        (ih (fun K hK => hmem K (by simp [hK])))


/-- Monotonicity of the point sequence returned by relative Lemma 3.3. -/
theorem lemma34_rel_pts_le_add
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {a' b' : R} {n : Nat} {eps delta : R}
    (r : Lemma33RelResult P a' b' n eps delta)
    (i m : Nat) (h : i + m ≤ r.N) :
    Le (r.pts i) (r.pts (i + m)) := by
  revert h
  induction m with
  | zero =>
      intro _
      simpa using le_refl (r.pts i)
  | succ m ih =>
      intro h
      have hprev : i + m ≤ r.N := by omega
      have hstepIndex : i + m < r.N := by omega
      have hstep : Le (r.pts (i + m)) (r.pts (i + m + 1)) :=
        le_of_lt (r.pts_mono (i + m) hstepIndex)
      exact le_trans (ih hprev) (by simpa [Nat.add_assoc] using hstep)


/-- Arbitrary-index form of monotonicity for a relative Lemma 3.3 result. -/
theorem lemma34_rel_pts_le
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {a' b' : R} {n : Nat} {eps delta : R}
    (r : Lemma33RelResult P a' b' n eps delta)
    {i j : Nat} (hij : i ≤ j) (hjN : j ≤ r.N) :
    Le (r.pts i) (r.pts j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact lemma34_rel_pts_le_add r i d hjN


/-- Chosen relative Lemma 3.3 output for one retained parent block. -/
noncomputable def lemma34_blockRefinementResult
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) :
    Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)) :=
  lemma_3_3_rel P
    (a' := B.left) (b' := B.right)
    B.left_bound B.proper B.right_bound
    eps heps B.mult B.budget
    (lemma34_widthScale a b (k + 1))
    (lemma34_widthScale_pos a b (k + 1))


/-- A positive-charge subinterval of one relative Lemma 3.3 output, packaged
as a successor-level retained block. -/
noncomputable def lemma34_childBlockOfResult
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (i : Nat) (hi : i < r.N) (hm : 0 < r.M (i + 1)) :
    Lemma34Block P eps (k + 1) := by
  have hparentLeft : Le B.left (r.pts i) := by
    have h0 : Le (r.pts 0) (r.pts i) :=
      lemma34_rel_pts_le r (Nat.zero_le i) (Nat.le_of_lt hi)
    rw [r.pts_zero] at h0; exact h0
  have hparentRight : Le (r.pts (i + 1)) B.right := by
    have hN : Le (r.pts (i + 1)) (r.pts r.N) :=
      lemma34_rel_pts_le r (by omega) (Nat.le_refl r.N)
    rw [r.pts_N] at hN; exact hN
  exact {
    left := r.pts i
    right := r.pts (i + 1)
    mult := r.M (i + 1)
    mult_pos := hm
    left_bound := le_trans B.left_bound hparentLeft
    proper := r.pts_mono i hi
    right_bound := le_trans hparentRight B.right_bound
    width := r.width_le i hi
    budget := r.p_prime_cond i hi
  }


@[simp] theorem lemma34_childBlock_left
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (i : Nat) (hi : i < r.N) (hm : 0 < r.M (i + 1)) :
    (lemma34_childBlockOfResult B r i hi hm).left = r.pts i := rfl


@[simp] theorem lemma34_childBlock_right
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (i : Nat) (hi : i < r.N) (hm : 0 < r.M (i + 1)) :
    (lemma34_childBlockOfResult B r i hi hm).right = r.pts (i + 1) := rfl


@[simp] theorem lemma34_childBlock_mult
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (i : Nat) (hi : i < r.N) (hm : 0 < r.M (i + 1)) :
    (lemma34_childBlockOfResult B r i hi hm).mult = r.M (i + 1) := rfl


/-- Every child block is contained in its parent block. -/
theorem lemma34_childBlock_inside
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (i : Nat) (hi : i < r.N) (hm : 0 < r.M (i + 1)) :
    Le B.left (lemma34_childBlockOfResult B r i hi hm).left ∧
      Le (lemma34_childBlockOfResult B r i hi hm).right B.right := by
  constructor
  · change Le B.left (r.pts i)
    have h0 : Le (r.pts 0) (r.pts i) :=
      lemma34_rel_pts_le r (Nat.zero_le i) (Nat.le_of_lt hi)
    rw [r.pts_zero] at h0; exact h0
  · change Le (r.pts (i + 1)) B.right
    have hN : Le (r.pts (i + 1)) (r.pts r.N) :=
      lemma34_rel_pts_le r (by omega) (Nat.le_refl r.N)
    rw [r.pts_N] at hN; exact hN


/-- Filter a list of interval indices, retaining precisely the indices whose
relative Lemma 3.3 charge is positive. -/
noncomputable def lemma34_childBlocksOfResult
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1))) :
    List Nat → List (Lemma34Block P eps (k + 1))
  | [] => []
  | i :: is =>
      if hi : i < r.N then
        if hm : 0 < r.M (i + 1) then
          lemma34_childBlockOfResult B r i hi hm ::
            lemma34_childBlocksOfResult B r is
        else
          lemma34_childBlocksOfResult B r is
      else
        lemma34_childBlocksOfResult B r is


/-- The positive-index filter commutes with list append. -/
theorem lemma34_childBlocks_append
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (xs ys : List Nat) :
    lemma34_childBlocksOfResult B r (xs ++ ys) =
      lemma34_childBlocksOfResult B r xs ++
        lemma34_childBlocksOfResult B r ys := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      by_cases hi : i < r.N
      · by_cases hm : 0 < r.M (i + 1)
        · simp [lemma34_childBlocksOfResult, hi, hm, ih]
        · simp [lemma34_childBlocksOfResult, hi, hm, ih]
      · simp [lemma34_childBlocksOfResult, hi, ih]


/-- Membership in the filtered child list remembers its source interval
index and the positivity proof for its charge. -/
theorem lemma34_mem_childBlocks
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    {xs : List Nat} {C : Lemma34Block P eps (k + 1)}
    (hC : C ∈ lemma34_childBlocksOfResult B r xs) :
    ∃ i, i ∈ xs ∧
      ∃ (hi : i < r.N) (hm : 0 < r.M (i + 1)),
        C = lemma34_childBlockOfResult B r i hi hm := by
  induction xs with
  | nil => simp [lemma34_childBlocksOfResult] at hC
  | cons i xs ih =>
      by_cases hi : i < r.N
      · by_cases hm : 0 < r.M (i + 1)
        · simp [lemma34_childBlocksOfResult, hi, hm] at hC
          rcases hC with hEq | hTail
          · exact ⟨i, by simp, hi, hm, hEq⟩
          · rcases ih hTail with ⟨j, hj, hjN, hjM, hEq⟩
            exact ⟨j, by simp [hj], hjN, hjM, hEq⟩
        · have hTail : C ∈ lemma34_childBlocksOfResult B r xs := by
            simpa [lemma34_childBlocksOfResult, hi, hm] using hC
          rcases ih hTail with ⟨j, hj, hjN, hjM, hEq⟩
          exact ⟨j, by simp [hj], hjN, hjM, hEq⟩
      · have hTail : C ∈ lemma34_childBlocksOfResult B r xs := by
          simpa [lemma34_childBlocksOfResult, hi] using hC
        rcases ih hTail with ⟨j, hj, hjN, hjM, hEq⟩
        exact ⟨j, by simp [hj], hjN, hjM, hEq⟩


/-- Total multiplicity is additive under block-list append. -/
theorem lemma34_totalMultiplicity_append
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat}
    (xs ys : List (Lemma34Block P eps k)) :
    lemma34_totalMultiplicity (xs ++ ys) =
      lemma34_totalMultiplicity xs + lemma34_totalMultiplicity ys := by
  simp [lemma34_totalMultiplicity]


/-- On the first `m` source intervals, filtering zero charges preserves the
prefix sum of all charges. -/
theorem lemma34_childBlocks_total_prefix
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (m : Nat) (hm : m ≤ r.N) :
    lemma34_totalMultiplicity
        (lemma34_childBlocksOfResult B r (List.range m)) =
      lemma33Prefix (fun i => r.M (i + 1)) m := by
  revert hm
  induction m with
  | zero =>
      intro _
      simp [lemma34_childBlocksOfResult, lemma34_totalMultiplicity,
        lemma33Prefix]
  | succ m ih =>
      intro hm
      have hmN : m < r.N := by omega
      rw [List.range_succ, lemma34_childBlocks_append,
        lemma34_totalMultiplicity_append, ih (by omega)]
      by_cases hM : 0 < r.M (m + 1)
      · simp [lemma34_childBlocksOfResult, hmN, hM,
          lemma34_totalMultiplicity, lemma33Prefix]
      · have hMz : r.M (m + 1) = 0 := Nat.eq_zero_of_not_pos hM
        simp [lemma34_childBlocksOfResult, hmN, hM, hMz,
          lemma34_totalMultiplicity, lemma33Prefix]


/-- The retained child blocks have exactly the parent multiplicity. -/
theorem lemma34_childBlocks_total
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1))) :
    lemma34_totalMultiplicity
        (lemma34_childBlocksOfResult B r (List.range r.N)) = B.mult := by
  calc
    lemma34_totalMultiplicity
        (lemma34_childBlocksOfResult B r (List.range r.N)) =
        lemma33Prefix (fun i => r.M (i + 1)) r.N :=
      lemma34_childBlocks_total_prefix B r r.N (Nat.le_refl r.N)
    _ = (List.range r.N).foldl
        (fun acc i => acc + r.M (i + 1)) 0 := by
      symm
      exact lemma33_foldl_range_eq_prefix (fun i => r.M (i + 1)) r.N
    _ = B.mult := r.sum_M


/-- Every retained child block lies inside its parent. -/
theorem lemma34_childBlocks_inside
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    {C : Lemma34Block P eps (k + 1)}
    (hC : C ∈ lemma34_childBlocksOfResult B r (List.range r.N)) :
    Le B.left C.left ∧ Le C.right B.right := by
  rcases lemma34_mem_childBlocks B r hC with
    ⟨i, hiRange, hiN, hiM, hEq⟩
  subst C
  exact lemma34_childBlock_inside B r i hiN hiM


/-- Every child among the first `m` source intervals ends no later than
`r.pts m`. -/
theorem lemma34_childBlocks_upper
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (m : Nat) (hm : m ≤ r.N)
    {C : Lemma34Block P eps (k + 1)}
    (hC : C ∈ lemma34_childBlocksOfResult B r (List.range m)) :
    Le C.right (r.pts m) := by
  rcases lemma34_mem_childBlocks B r hC with
    ⟨i, hiRange, hiN, hiM, hEq⟩
  subst C
  have him : i < m := List.mem_range.mp hiRange
  change Le (r.pts (i + 1)) (r.pts m)
  exact lemma34_rel_pts_le r (by omega) hm


/-- Append one final element to a pairwise list. -/
theorem lemma34_pairwise_append_single
    {A : Type*} {rel : A → A → Prop} {xs : List A} {y : A}
    (hxs : xs.Pairwise rel) (hxy : ∀ x, x ∈ xs → rel x y) :
    (xs ++ [y]).Pairwise rel := by
  apply List.pairwise_append.2
  refine ⟨hxs, by simp, ?_⟩
  intro x hx z hz
  have hzEq : z = y := by simpa using hz
  subst z
  exact hxy x hx


/-- Child blocks obtained from the first `m` source intervals are ordered from
left to right. -/
theorem lemma34_childBlocks_pairwise_prefix
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    (m : Nat) (hm : m ≤ r.N) :
    (lemma34_childBlocksOfResult B r (List.range m)).Pairwise
      (fun I J => Le I.right J.left) := by
  revert hm
  induction m with
  | zero =>
      intro _
      simp [lemma34_childBlocksOfResult]
  | succ m ih =>
      intro hm
      have hmN : m < r.N := by omega
      rw [List.range_succ, lemma34_childBlocks_append]
      by_cases hM : 0 < r.M (m + 1)
      · have hsingle :
          lemma34_childBlocksOfResult B r [m] =
            [lemma34_childBlockOfResult B r m hmN hM] := by
          simp [lemma34_childBlocksOfResult, hmN, hM]
        rw [hsingle]
        apply lemma34_pairwise_append_single (ih (by omega))
        intro C hC
        have hu := lemma34_childBlocks_upper B r m (by omega) hC
        simpa using hu
      · have hsingle : lemma34_childBlocksOfResult B r [m] = [] := by
          simp [lemma34_childBlocksOfResult, hmN, hM]
        rw [hsingle]
        simpa using ih (by omega)


/-- All retained children of one parent are pairwise ordered. -/
theorem lemma34_childBlocks_pairwise
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1))) :
    (lemma34_childBlocksOfResult B r (List.range r.N)).Pairwise
      (fun I J => Le I.right J.left) :=
  lemma34_childBlocks_pairwise_prefix B r r.N (Nat.le_refl r.N)


/-- Flattening preserves total multiplicity as list length. -/
theorem lemma34_flattenBlocks_length
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (blocks : List (Lemma34Block P eps k)) :
    (lemma34_flattenBlocks blocks).length =
      lemma34_totalMultiplicity blocks := by
  induction blocks with
  | nil => simp [lemma34_flattenBlocks, lemma34_totalMultiplicity]
  | cons B blocks ih =>
      simp [lemma34_flattenBlocks, Lemma34Block.expand,
        lemma34_totalMultiplicity, ih]


/-- Flattening commutes with block-list append. -/
theorem lemma34_flattenBlocks_append
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat}
    (xs ys : List (Lemma34Block P eps k)) :
    lemma34_flattenBlocks (xs ++ ys) =
      lemma34_flattenBlocks xs ++ lemma34_flattenBlocks ys := by
  simp [lemma34_flattenBlocks]


/-- A flattened segment comes from a unique stored block value (uniqueness of
which occurrence is not needed). -/
theorem lemma34_mem_flattenBlocks
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} {blocks : List (Lemma34Block P eps k)}
    {I : R × R} (hI : I ∈ lemma34_flattenBlocks blocks) :
    ∃ B, B ∈ blocks ∧ I = (B.left, B.right) := by
  unfold lemma34_flattenBlocks at hI
  rcases List.mem_flatMap.mp hI with ⟨B, hB, hIB⟩
  have hEq : I = (B.left, B.right) :=
    lemma34_eq_of_mem_replicate
      (by simpa [Lemma34Block.expand] using hIB)
  exact ⟨B, hB, hEq⟩


/-- Ordered blocks flatten to an ordered repeated segment enumeration. -/
theorem lemma34_flattenBlocks_pairwise
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} {blocks : List (Lemma34Block P eps k)}
    (horder : blocks.Pairwise (fun I J => Le I.right J.left)) :
    (lemma34_flattenBlocks blocks).Pairwise lemma34_segOrdered := by
  change (blocks.flatMap (fun B => B.expand)).Pairwise lemma34_segOrdered
  rw [List.pairwise_flatMap]
  constructor
  · intro B hB
    simpa [Lemma34Block.expand] using
      lemma34_pairwise_replicate lemma34_segOrdered
        (B.left, B.right)
        ⟨le_refl B.left, le_refl B.right, Or.inr rfl⟩ B.mult
  · refine horder.imp ?_
    intro B C hBC I hI J hJ
    have hIEq : I = (B.left, B.right) :=
      lemma34_eq_of_mem_replicate
        (by simpa [Lemma34Block.expand] using hI)
    have hJEq : J = (C.left, C.right) :=
      lemma34_eq_of_mem_replicate
        (by simpa [Lemma34Block.expand] using hJ)
    subst I
    subst J
    exact ⟨
      le_trans (le_of_lt B.proper) hBC,
      le_trans hBC (le_of_lt C.proper),
      Or.inl hBC
    ⟩


/-- Every flattened successor segment satisfies the ambient endpoint bounds
and is proper. -/
theorem lemma34_flattenBlocks_proper
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} {blocks : List (Lemma34Block P eps k)}
    {I : R × R} (hI : I ∈ lemma34_flattenBlocks blocks) :
    Le a I.1 ∧ COF.lt I.1 I.2 ∧ Le I.2 b := by
  rcases lemma34_mem_flattenBlocks hI with ⟨B, hB, hEq⟩
  subst I
  exact ⟨B.left_bound, B.proper, B.right_bound⟩


/-- Every flattened segment has the width bound stored in its block. -/
theorem lemma34_flattenBlocks_width
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} {blocks : List (Lemma34Block P eps k)}
    {I : R × R} (hI : I ∈ lemma34_flattenBlocks blocks) :
    Le (I.2 - I.1) (lemma34_widthScale a b k) := by
  rcases lemma34_mem_flattenBlocks hI with ⟨B, hB, hEq⟩
  subst I
  exact B.width


/-- The repeated parent interval refines positionwise to the repeated retained
children of one relative Lemma 3.3 result. -/
theorem lemma34_childSegments_refine
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1))) :
    Lemma34SegmentsRefine B.expand
      (lemma34_flattenBlocks
        (lemma34_childBlocksOfResult B r (List.range r.N))) := by
  let children := lemma34_childBlocksOfResult B r (List.range r.N)
  let childSegments := lemma34_flattenBlocks children
  have hlen : childSegments.length = B.mult := by
    dsimp [childSegments, children]
    calc
      (lemma34_flattenBlocks
          (lemma34_childBlocksOfResult B r (List.range r.N))).length =
          lemma34_totalMultiplicity
            (lemma34_childBlocksOfResult B r (List.range r.N)) :=
        lemma34_flattenBlocks_length _
      _ = B.mult := lemma34_childBlocks_total B r
  have hnested : ∀ I, I ∈ childSegments →
      lemma34_intervalNested (B.left, B.right) I := by
    intro I hI
    dsimp [childSegments, children] at hI
    rcases lemma34_mem_flattenBlocks hI with ⟨C, hC, hEq⟩
    subst I
    exact lemma34_childBlocks_inside B r hC
  have href := lemma34_segmentsRefine_replicate
    (I := (B.left, B.right)) childSegments hnested
  have href' : Lemma34SegmentsRefine
      (List.replicate B.mult (B.left, B.right)) childSegments := by
    simpa [hlen] using href
  simpa [Lemma34Block.expand, childSegments, children] using href'


/-- Successor blocks contributed by one parent block. -/
noncomputable def lemma34_refinedBlocksFor
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) :
    List (Lemma34Block P eps (k + 1)) :=
  let r := lemma34_blockRefinementResult P eps heps k B
  lemma34_childBlocksOfResult B r (List.range r.N)


/-- Local successor blocks are ordered. -/
theorem lemma34_refinedBlocksFor_pairwise
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) :
    (lemma34_refinedBlocksFor P eps heps k B).Pairwise
      (fun I J => Le I.right J.left) := by
  dsimp [lemma34_refinedBlocksFor]
  exact lemma34_childBlocks_pairwise B
    (lemma34_blockRefinementResult P eps heps k B)


/-- Local successor multiplicities sum to the parent multiplicity. -/
theorem lemma34_refinedBlocksFor_total
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) :
    lemma34_totalMultiplicity (lemma34_refinedBlocksFor P eps heps k B) =
      B.mult := by
  dsimp [lemma34_refinedBlocksFor]
  exact lemma34_childBlocks_total B
    (lemma34_blockRefinementResult P eps heps k B)


/-- Every local successor block lies in its parent. -/
theorem lemma34_refinedBlocksFor_inside
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k)
    {C : Lemma34Block P eps (k + 1)}
    (hC : C ∈ lemma34_refinedBlocksFor P eps heps k B) :
    Le B.left C.left ∧ Le C.right B.right := by
  dsimp [lemma34_refinedBlocksFor] at hC
  exact lemma34_childBlocks_inside B
    (lemma34_blockRefinementResult P eps heps k B) hC


/-- Local repeated successor segments refine the repeated parent segment. -/
theorem lemma34_refinedBlocksFor_segmentsRefine
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) :
    Lemma34SegmentsRefine B.expand
      (lemma34_flattenBlocks (lemma34_refinedBlocksFor P eps heps k B)) := by
  dsimp [lemma34_refinedBlocksFor]
  exact lemma34_childSegments_refine B
    (lemma34_blockRefinementResult P eps heps k B)


/-- Concatenate the local successor block families of every previous block. -/
noncomputable def lemma34_refinedBlocks
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    List (Lemma34Block P eps (k + 1)) :=
  T.blocks.flatMap (fun B => lemma34_refinedBlocksFor P eps heps k B)


/-- The concatenated successor block family is ordered. -/
theorem lemma34_refinedBlocks_pairwise
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    (lemma34_refinedBlocks P n eps heps k T).Pairwise
      (fun I J => Le I.right J.left) := by
  unfold lemma34_refinedBlocks
  rw [List.pairwise_flatMap]
  constructor
  · intro B hB
    exact lemma34_refinedBlocksFor_pairwise P eps heps k B
  · refine T.blocks_ordered.imp ?_
    intro B C hBC D hD E hE
    have hDin := lemma34_refinedBlocksFor_inside P eps heps k B hD
    have hEin := lemma34_refinedBlocksFor_inside P eps heps k C hE
    exact le_trans hDin.2 (le_trans hBC hEin.1)


/-- Flat-mapping the local refinements preserves total multiplicity. -/
theorem lemma34_refinedBlocks_total_list
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (blocks : List (Lemma34Block P eps k)) :
    lemma34_totalMultiplicity
      (blocks.flatMap (fun B => lemma34_refinedBlocksFor P eps heps k B)) =
      lemma34_totalMultiplicity blocks := by
  induction blocks with
  | nil => simp [lemma34_totalMultiplicity]
  | cons B blocks ih =>
      rw [List.flatMap_cons, lemma34_totalMultiplicity_append,
        lemma34_refinedBlocksFor_total P eps heps k B, ih]
      simp [lemma34_totalMultiplicity]


/-- The global successor family still has total multiplicity `n`. -/
theorem lemma34_refinedBlocks_total
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    lemma34_totalMultiplicity (lemma34_refinedBlocks P n eps heps k T) = n := by
  unfold lemma34_refinedBlocks
  calc
    lemma34_totalMultiplicity
      (T.blocks.flatMap
        (fun B => lemma34_refinedBlocksFor P eps heps k B)) =
        lemma34_totalMultiplicity T.blocks :=
      lemma34_refinedBlocks_total_list P eps heps k T.blocks
    _ = n := T.total_mult


/-- Concatenating every local positionwise refinement gives a global
positionwise refinement of flattened block enumerations. -/
theorem lemma34_refinedSegments_refine_list
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (blocks : List (Lemma34Block P eps k)) :
    Lemma34SegmentsRefine
      (lemma34_flattenBlocks blocks)
      (lemma34_flattenBlocks
        (blocks.flatMap
          (fun B => lemma34_refinedBlocksFor P eps heps k B))) := by
  induction blocks with
  | nil =>
      simpa [lemma34_flattenBlocks] using
        (Lemma34SegmentsRefine.nil :
          Lemma34SegmentsRefine ([] : List (R × R)) [])
  | cons B blocks ih =>
      change Lemma34SegmentsRefine
        (B.expand ++ lemma34_flattenBlocks blocks)
        (lemma34_flattenBlocks
          (lemma34_refinedBlocksFor P eps heps k B ++
            blocks.flatMap
              (fun C => lemma34_refinedBlocksFor P eps heps k C)))
      rw [lemma34_flattenBlocks_append]
      exact lemma34_segmentsRefine_append
        (lemma34_refinedBlocksFor_segmentsRefine P eps heps k B) ih


/-- The actual previous tower segment list refines to the successor flattened list. -/
theorem lemma34_refinedSegments_refine
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    Lemma34SegmentsRefine T.segments
      (lemma34_flattenBlocks (lemma34_refinedBlocks P n eps heps k T)) := by
  simpa [T.flatten_segments, lemma34_refinedBlocks] using
    lemma34_refinedSegments_refine_list P eps heps k T.blocks


/-- All successor-level tower fields except `sigma` and `outside`. -/
structure Lemma34TowerStepAlpha
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat}
    (T : Lemma34Tower P n eps k) where
  blocks : List (Lemma34Block P eps (k + 1))
  blocks_ordered : blocks.Pairwise (fun I J => Le I.right J.left)
  total_mult : lemma34_totalMultiplicity blocks = n
  segments : List (R × R)
  flatten_segments : segments = lemma34_flattenBlocks blocks
  segments_length : segments.length = n
  segments_ordered : segments.Pairwise lemma34_segOrdered
  segment_proper : ∀ I, I ∈ segments →
    Le a I.1 ∧ COF.lt I.1 I.2 ∧ Le I.2 b
  segment_width : ∀ I, I ∈ segments →
    Le (I.2 - I.1) (lemma34_widthScale a b (k + 1))
  list_refines : Lemma34SegmentsRefine T.segments segments


/-- Positionwise access to a P2b-alpha successor segment. -/
def Lemma34TowerStepAlpha.segAt
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) (j : Fin n) : R × R :=
  A.segments.get ⟨j.1, by rw [A.segments_length]; exact j.2⟩


/-- Left endpoint at a P2b-alpha successor position. -/
def Lemma34TowerStepAlpha.segL
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) (j : Fin n) : R :=
  (A.segAt j).1


/-- Right endpoint at a P2b-alpha successor position. -/
def Lemma34TowerStepAlpha.segR
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) (j : Fin n) : R :=
  (A.segAt j).2


/-- The list-level refinement field gives the required positionwise nesting. -/
theorem lemma34_towerStepAlpha_nested
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) (j : Fin n) :
    Le (T.segL j) (A.segL j) ∧ Le (A.segR j) (T.segR j) := by
  have h := lemma34_segmentsRefine_get A.list_refines
    (i := j.1)
    (by simpa [T.segments_length] using j.2)
    (by simpa [A.segments_length] using j.2)
  simpa [lemma34_intervalNested,
    Lemma34Tower.segL, Lemma34Tower.segR, Lemma34Tower.segAt,
    Lemma34TowerStepAlpha.segL, Lemma34TowerStepAlpha.segR,
    Lemma34TowerStepAlpha.segAt] using h


/-- P2b-alpha: construct the successor blocks, repeated segments, all local
budgets and width bounds, and the positionwise nesting witness. -/
noncomputable def lemma34_tower_step_alpha
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    Lemma34TowerStepAlpha T := by
  let newBlocks := lemma34_refinedBlocks P n eps heps k T
  let newSegments := lemma34_flattenBlocks newBlocks
  have horder : newBlocks.Pairwise (fun I J => Le I.right J.left) := by
    dsimp [newBlocks]
    exact lemma34_refinedBlocks_pairwise P n eps heps k T
  have htotal : lemma34_totalMultiplicity newBlocks = n := by
    dsimp [newBlocks]
    exact lemma34_refinedBlocks_total P n eps heps k T
  have hlen : newSegments.length = n := by
    dsimp [newSegments]
    calc
      (lemma34_flattenBlocks newBlocks).length =
          lemma34_totalMultiplicity newBlocks :=
        lemma34_flattenBlocks_length newBlocks
      _ = n := htotal
  have hsegmentsOrder : newSegments.Pairwise lemma34_segOrdered := by
    dsimp [newSegments]
    exact lemma34_flattenBlocks_pairwise horder
  have hproper : ∀ I, I ∈ newSegments →
      Le a I.1 ∧ COF.lt I.1 I.2 ∧ Le I.2 b := by
    intro I hI
    dsimp [newSegments] at hI
    exact lemma34_flattenBlocks_proper hI
  have hwidth : ∀ I, I ∈ newSegments →
      Le (I.2 - I.1) (lemma34_widthScale a b (k + 1)) := by
    intro I hI
    dsimp [newSegments] at hI
    exact lemma34_flattenBlocks_width hI
  have hrefine : Lemma34SegmentsRefine T.segments newSegments := by
    dsimp [newSegments, newBlocks]
    exact lemma34_refinedSegments_refine P n eps heps k T
  exact {
    blocks := newBlocks
    blocks_ordered := horder
    total_mult := htotal
    segments := newSegments
    flatten_segments := rfl
    segments_length := hlen
    segments_ordered := hsegmentsOrder
    segment_proper := hproper
    segment_width := hwidth
    list_refines := hrefine
  }


/-- Exact remaining interface for P2b-beta.  Supplying this data upgrades the
P2b-alpha successor to a genuine `Lemma34Tower`. -/
structure Lemma34TowerStepOutside
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) where
  sigma : R
  sigma_pos : COF.lt 0 sigma
  outside : ∀ x, Le a x → Le x b →
    (∀ I, I ∈ A.segments → COF.lt I.2 x ∨ COF.lt x I.1) →
    P.p_lt (COF.max a (x - sigma)) (COF.min b (x + sigma)) eps



/- Technical proof note. -/


/-!
P2b-beta-sigma for Bishop--Cheng Lemma 3.4.

This file performs the finite-radius part of the successor `outside`
construction.  It records every discarded (`M = 0`) cell produced by the
same referentially transparent `lemma34_blockRefinementResult` used by
P2b-alpha, extracts its positive `p_lt` enlargement radius, and takes a
finite constructive minimum together with the parent radius `T.sigma`.

The resulting radius is positive and is at most half of every discarded-cell
radius and at most half of the parent radius.  The remaining P2b-beta-out
obligation is thereby reduced to the finite locatedness/cotransitivity split
for a point outside all successor segments.
-/

/-- Shrinking an interval preserves a `p_lt` witness. -/
def lemma33_p_lt_subset
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    {u v u' v' d : R}
    (h : P.p_lt u' v' d) (hu : Le u' u) (hv : Le v v') :
    P.p_lt u v d := by
  rcases h with ⟨f1, hf1, f2, hf2, hz, ho, hlt⟩
  refine ⟨f1, hf1, f2, hf2, ?_, ?_, hlt⟩
  · intro t hat htb htv
    exact hz t hat htb (le_trans htv hv)
  · intro t hat htb hut
    exact ho t hat htb (le_trans hu hut)


/-- Fprevious a finite list with constructive minimum, using `seed` for the empty
list.  The seed will be the previous tower radius. -/
def lemma34_foldMin (seed : R) : List R → R
  | [] => seed
  | x :: xs => COF.min x (lemma34_foldMin seed xs)


/-- A finite minimum of positive values with a positive seed is positive. -/
theorem lemma34_foldMin_pos (seed : R) (xs : List R)
    (hseed : COF.lt 0 seed)
    (hxs : ∀ x, x ∈ xs → COF.lt 0 x) :
    COF.lt 0 (lemma34_foldMin seed xs) := by
  induction xs with
  | nil => simpa [lemma34_foldMin] using hseed
  | cons x xs ih =>
      have hx : COF.lt 0 x := hxs x (by simp)
      have htail : ∀ y, y ∈ xs → COF.lt 0 y := by
        intro y hy
        exact hxs y (by simp [hy])
      simpa [lemma34_foldMin] using lemma34_min_pos hx (ih htail)


/-- The folded minimum is below its seed. -/
theorem lemma34_foldMin_le_seed (seed : R) (xs : List R) :
    Le (lemma34_foldMin seed xs) seed := by
  induction xs with
  | nil => simpa [lemma34_foldMin] using le_refl seed
  | cons x xs ih =>
      exact le_trans
        (by simpa [lemma34_foldMin] using
          (cof_min_le_right x (lemma34_foldMin seed xs)))
        ih


/-- The folded minimum is below every list member. -/
theorem lemma34_foldMin_le_mem (seed : R) (xs : List R) {x : R}
    (hx : x ∈ xs) : Le (lemma34_foldMin seed xs) x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [lemma34_foldMin] using
          (cof_min_le_left x (lemma34_foldMin seed ys))
      · exact le_trans
          (by simpa [lemma34_foldMin] using
            (cof_min_le_right y (lemma34_foldMin seed ys)))
          (ih hx)


/-- The constructive half is weakly below one. -/
theorem lemma34_half_le_one : Le (COF.half : R) 1 := by
  have h := lemma34_self_le_add (COF.half : R) COF.half
    (le_of_lt COFO.half_pos)
  rwa [COF.half_add_half] at h


/-- A discarded cell is an index at which the relative Lemma 3.3 charge is
zero.  Its result is definitionally the same chosen result used by P2b-alpha. -/
structure Lemma34ZeroCell
    {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (eps : R) (heps : COF.lt 0 eps) (k : Nat) where
  parent : Lemma34Block P eps k
  index : Nat
  index_lt :
    index < (lemma34_blockRefinementResult P eps heps k parent).N
  charge_zero :
    (lemma34_blockRefinementResult P eps heps k parent).M (index + 1) = 0


namespace Lemma34ZeroCell

/-- `p'_P < eps` on a zero-charge cell supplies the source proof's positive
radius `omega` and its enlarged `p_P < eps` estimate. -/
noncomputable def omega_exists
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {heps : COF.lt 0 eps} {k : Nat}
    (G : Lemma34ZeroCell P eps heps k) :
    P.p_prime_lt
        ((lemma34_blockRefinementResult P eps heps k G.parent).pts G.index)
        ((lemma34_blockRefinementResult P eps heps k G.parent).pts (G.index + 1))
        eps := by
  simpa [G.charge_zero] using
    (lemma34_blockRefinementResult P eps heps k G.parent).p_prime_cond
      G.index G.index_lt


/-- Chosen positive enlargement radius of a discarded cell. -/
noncomputable def omega
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {heps : COF.lt 0 eps} {k : Nat}
    (G : Lemma34ZeroCell P eps heps k) : R :=
  G.omega_exists.alpha


/-- The chosen discarded-cell radius is positive. -/
theorem omega_pos
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {heps : COF.lt 0 eps} {k : Nat}
    (G : Lemma34ZeroCell P eps heps k) : COF.lt 0 G.omega :=
  G.omega_exists.alpha_pos


/-- The chosen radius carries the required enlarged `p_lt` estimate. -/
noncomputable def omega_p_lt
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {heps : COF.lt 0 eps} {k : Nat}
    (G : Lemma34ZeroCell P eps heps k) :
    P.p_lt
      (COF.max a
        ((lemma34_blockRefinementResult P eps heps k G.parent).pts G.index - G.omega))
      (COF.min b
        ((lemma34_blockRefinementResult P eps heps k G.parent).pts (G.index + 1) + G.omega))
      eps :=
  G.omega_exists.inner


end Lemma34ZeroCell

/-- Canonical discarded-cell record at a specified zero-charge index. -/
def lemma34_zeroCellOf
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) (i : Nat)
    (hi : i < (lemma34_blockRefinementResult P eps heps k B).N)
    (hz : (lemma34_blockRefinementResult P eps heps k B).M (i + 1) = 0) :
    Lemma34ZeroCell P eps heps k :=
  { parent := B, index := i, index_lt := hi, charge_zero := hz }


/-- Filter an index list, retaining precisely the discarded (`M = 0`) cells. -/
noncomputable def lemma34_zeroCellsAux
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) :
    List Nat → List (Lemma34ZeroCell P eps heps k)
  | [] => []
  | i :: is =>
      if hi : i < (lemma34_blockRefinementResult P eps heps k B).N then
        if hz :
            (lemma34_blockRefinementResult P eps heps k B).M (i + 1) = 0 then
          lemma34_zeroCellOf P eps heps k B i hi hz ::
            lemma34_zeroCellsAux P eps heps k B is
        else
          lemma34_zeroCellsAux P eps heps k B is
      else
        lemma34_zeroCellsAux P eps heps k B is




/-- Conversely, every zero-charge index occurring in the input list is
retained by the filter. -/
theorem lemma34_zeroCellOf_mem_aux
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k)
    {xs : List Nat} {i : Nat}
    (hix : i ∈ xs)
    (hi : i < (lemma34_blockRefinementResult P eps heps k B).N)
    (hz : (lemma34_blockRefinementResult P eps heps k B).M (i + 1) = 0) :
    lemma34_zeroCellOf P eps heps k B i hi hz ∈
      lemma34_zeroCellsAux P eps heps k B xs := by
  induction xs with
  | nil => simp at hix
  | cons j xs ih =>
      simp only [List.mem_cons] at hix
      rcases hix with rfl | hix
      · simp [lemma34_zeroCellsAux, hi, hz]
      · by_cases hj : j < (lemma34_blockRefinementResult P eps heps k B).N
        · by_cases hjz :
            (lemma34_blockRefinementResult P eps heps k B).M (j + 1) = 0
          · simp [lemma34_zeroCellsAux, hj, hjz, ih hix]
          · simpa [lemma34_zeroCellsAux, hj, hjz] using ih hix
        · simpa [lemma34_zeroCellsAux, hj] using ih hix


/-- All discarded cells obtained from one parent block. -/
noncomputable def lemma34_zeroCellsFor
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) :
    List (Lemma34ZeroCell P eps heps k) :=
  lemma34_zeroCellsAux P eps heps k B
    (List.range (lemma34_blockRefinementResult P eps heps k B).N)




/-- The canonical record of any zero-charge source index occurs in the local
list of discarded cells. -/
theorem lemma34_zeroCellOf_mem_for
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) (i : Nat)
    (hi : i < (lemma34_blockRefinementResult P eps heps k B).N)
    (hz : (lemma34_blockRefinementResult P eps heps k B).M (i + 1) = 0) :
    lemma34_zeroCellOf P eps heps k B i hi hz ∈
      lemma34_zeroCellsFor P eps heps k B := by
  unfold lemma34_zeroCellsFor
  exact lemma34_zeroCellOf_mem_aux P eps heps k B
    (List.mem_range.mpr hi) hi hz


/-- Concatenate the discarded-cell lists of all previous tower blocks. -/
noncomputable def lemma34_zeroCells
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    List (Lemma34ZeroCell P eps heps k) :=
  T.blocks.flatMap (fun B => lemma34_zeroCellsFor P eps heps k B)




/-- A canonical zero-charge record is present globally whenever its parent
block is present in the previous tower. -/
theorem lemma34_zeroCellOf_mem
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    (B : Lemma34Block P eps k) (hB : B ∈ T.blocks) (i : Nat)
    (hi : i < (lemma34_blockRefinementResult P eps heps k B).N)
    (hz : (lemma34_blockRefinementResult P eps heps k B).M (i + 1) = 0) :
    lemma34_zeroCellOf P eps heps k B i hi hz ∈
      lemma34_zeroCells P n eps heps k T := by
  unfold lemma34_zeroCells
  rw [List.mem_flatMap]
  exact ⟨B, hB, lemma34_zeroCellOf_mem_for P eps heps k B i hi hz⟩


/-- Positive radii of all discarded cells. -/
noncomputable def lemma34_zeroOmegas
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) : List R :=
  (lemma34_zeroCells P n eps heps k T).map
    (fun G => G.omega)


/-- Every radius in the finite discarded-cell radius list is positive. -/
theorem lemma34_zeroOmegas_pos
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    {omega : R} (homega : omega ∈ lemma34_zeroOmegas P n eps heps k T) :
    COF.lt 0 omega := by
  unfold lemma34_zeroOmegas at homega
  rcases List.mem_map.mp homega with ⟨G, hG, rfl⟩
  exact G.omega_pos


/-- The chosen radius of any globally recorded discarded cell occurs in the
radius list. -/
theorem lemma34_zeroCell_omega_mem
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    {G : Lemma34ZeroCell P eps heps k}
    (hG : G ∈ lemma34_zeroCells P n eps heps k T) :
    G.omega ∈ lemma34_zeroOmegas P n eps heps k T := by
  unfold lemma34_zeroOmegas
  exact List.mem_map.mpr ⟨G, hG, rfl⟩


/-- Minimum of the parent radius and all discarded-cell radii. -/
noncomputable def lemma34_stepRadius
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) : R :=
  lemma34_foldMin T.sigma (lemma34_zeroOmegas P n eps heps k T)


/-- The finite common radius is positive. -/
theorem lemma34_stepRadius_pos
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    COF.lt 0 (lemma34_stepRadius P n eps heps k T) := by
  unfold lemma34_stepRadius
  exact lemma34_foldMin_pos T.sigma
    (lemma34_zeroOmegas P n eps heps k T)
    T.sigma_pos
    (fun omega _homega =>
      lemma34_zeroOmegas_pos P n eps heps k T _homega)


/-- The finite common radius is below the parent tower radius. -/
theorem lemma34_stepRadius_le_parent
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    Le (lemma34_stepRadius P n eps heps k T) T.sigma := by
  unfold lemma34_stepRadius
  exact lemma34_foldMin_le_seed T.sigma
    (lemma34_zeroOmegas P n eps heps k T)


/-- The finite common radius is below every discarded-cell radius. -/
theorem lemma34_stepRadius_le_zeroCell
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    {G : Lemma34ZeroCell P eps heps k}
    (hG : G ∈ lemma34_zeroCells P n eps heps k T) :
    Le (lemma34_stepRadius P n eps heps k T) G.omega := by
  unfold lemma34_stepRadius
  exact lemma34_foldMin_le_mem T.sigma
    (lemma34_zeroOmegas P n eps heps k T)
    (lemma34_zeroCell_omega_mem P n eps heps k T hG)


/-- Successor radius: one half of the finite common radius. -/
noncomputable def lemma34_stepSigma
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) : R :=
  COF.half * lemma34_stepRadius P n eps heps k T


/-- The successor radius is positive. -/
theorem lemma34_stepSigma_pos
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    COF.lt 0 (lemma34_stepSigma P n eps heps k T) := by
  unfold lemma34_stepSigma
  exact COFO.mul_pos COFO.half_pos
    (lemma34_stepRadius_pos P n eps heps k T)


/-- Twice the successor radius is exactly the finite common radius. -/
theorem lemma34_stepSigma_add_self
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    lemma34_stepSigma P n eps heps k T +
      lemma34_stepSigma P n eps heps k T =
      lemma34_stepRadius P n eps heps k T := by
  unfold lemma34_stepSigma
  calc
    COF.half * lemma34_stepRadius P n eps heps k T +
        COF.half * lemma34_stepRadius P n eps heps k T =
        (COF.half + COF.half) * lemma34_stepRadius P n eps heps k T := by
          ring
    _ = 1 * lemma34_stepRadius P n eps heps k T := by
          rw [COF.half_add_half]
    _ = lemma34_stepRadius P n eps heps k T := by ring


/-- The successor radius is below the finite common radius. -/
theorem lemma34_stepSigma_le_radius
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    Le (lemma34_stepSigma P n eps heps k T)
      (lemma34_stepRadius P n eps heps k T) := by
  have hr : Nonneg (lemma34_stepRadius P n eps heps k T) :=
    le_of_lt (lemma34_stepRadius_pos P n eps heps k T)
  have h := lemma33_mul_le_mul_right (lemma34_half_le_one (R := R)) hr
  simpa [lemma34_stepSigma] using h


/-- The successor radius is below the previous tower radius. -/
theorem lemma34_stepSigma_le_parent
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    Le (lemma34_stepSigma P n eps heps k T) T.sigma :=
  le_trans
    (lemma34_stepSigma_le_radius P n eps heps k T)
    (lemma34_stepRadius_le_parent P n eps heps k T)


/-- The successor radius is below every discarded-cell radius. -/
theorem lemma34_stepSigma_le_zeroCell
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    {G : Lemma34ZeroCell P eps heps k}
    (hG : G ∈ lemma34_zeroCells P n eps heps k T) :
    Le (lemma34_stepSigma P n eps heps k T) G.omega :=
  le_trans
    (lemma34_stepSigma_le_radius P n eps heps k T)
    (lemma34_stepRadius_le_zeroCell P n eps heps k T hG)


/-- The doubled successor radius is below the previous tower radius. -/
theorem lemma34_stepSigma_twice_le_parent
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) :
    Le (lemma34_stepSigma P n eps heps k T +
      lemma34_stepSigma P n eps heps k T) T.sigma := by
  rw [lemma34_stepSigma_add_self P n eps heps k T]
  exact lemma34_stepRadius_le_parent P n eps heps k T


/-- The doubled successor radius is below every discarded-cell radius. -/
theorem lemma34_stepSigma_twice_le_zeroCell
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    {G : Lemma34ZeroCell P eps heps k}
    (hG : G ∈ lemma34_zeroCells P n eps heps k T) :
    Le (lemma34_stepSigma P n eps heps k T +
      lemma34_stepSigma P n eps heps k T) G.omega := by
  rw [lemma34_stepSigma_add_self P n eps heps k T]
  exact lemma34_stepRadius_le_zeroCell P n eps heps k T hG


/-- P2b-beta-sigma package.  It is deliberately separate from
`Lemma34TowerStepOutside`: the next kernel-loop round only has to construct
the `outside` function using these quantitative bounds. -/
structure Lemma34TowerStepSigma
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} (heps : COF.lt 0 eps) {k : Nat}
    {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) where
  sigma : R
  sigma_pos : COF.lt 0 sigma
  sigma_le_parent : Le sigma T.sigma
  twice_sigma_le_parent : Le (sigma + sigma) T.sigma
  sigma_le_zeroCell : ∀ G : Lemma34ZeroCell P eps heps k,
    G ∈ lemma34_zeroCells P n eps heps k T → Le sigma G.omega
  twice_sigma_le_zeroCell : ∀ G : Lemma34ZeroCell P eps heps k,
    G ∈ lemma34_zeroCells P n eps heps k T → Le (sigma + sigma) G.omega


/-- Construct the positive common successor radius and all bounds required by
the forthcoming finite locatedness argument. -/
noncomputable def lemma34_tower_step_sigma
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    (A : Lemma34TowerStepAlpha T) :
    Lemma34TowerStepSigma heps A :=
  {
    sigma := lemma34_stepSigma P n eps heps k T
    sigma_pos := lemma34_stepSigma_pos P n eps heps k T
    sigma_le_parent := lemma34_stepSigma_le_parent P n eps heps k T
    twice_sigma_le_parent :=
      lemma34_stepSigma_twice_le_parent P n eps heps k T
    sigma_le_zeroCell := fun G hG =>
      lemma34_stepSigma_le_zeroCell P n eps heps k T hG
    twice_sigma_le_zeroCell := fun G hG =>
      lemma34_stepSigma_twice_le_zeroCell P n eps heps k T hG
  }


/-- Once P2b-beta-out supplies the pointwise `outside` proof at the sigma
chosen above, it packages directly into the established P2b-alpha interface. -/
def lemma34_stepOutside_of_sigma
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {heps : COF.lt 0 eps} {k : Nat}
    {T : Lemma34Tower P n eps k} {A : Lemma34TowerStepAlpha T}
    (Sg : Lemma34TowerStepSigma heps A)
    (hout : ∀ x, Le a x → Le x b →
      (∀ I, I ∈ A.segments → COF.lt I.2 x ∨ COF.lt x I.1) →
      P.p_lt (COF.max a (x - Sg.sigma))
        (COF.min b (x + Sg.sigma)) eps) :
    Lemma34TowerStepOutside A :=
  { sigma := Sg.sigma, sigma_pos := Sg.sigma_pos, outside := hout }


/-- Upgrade P2b-alpha and an `outside` package to a genuine successor tower. -/
def lemma34_tower_of_step
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) (O : Lemma34TowerStepOutside A) :
    Lemma34Tower P n eps (k + 1) :=
  {
    blocks := A.blocks
    blocks_ordered := A.blocks_ordered
    total_mult := A.total_mult
    segments := A.segments
    flatten_segments := A.flatten_segments
    segments_length := A.segments_length
    segments_ordered := A.segments_ordered
    segment_proper := A.segment_proper
    segment_width := A.segment_width
    sigma := O.sigma
    sigma_pos := O.sigma_pos
    outside := O.outside
  }


/-- The upgraded successor tower refines its parent positionwise. -/
theorem lemma34_tower_of_step_refines
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} {T : Lemma34Tower P n eps k}
    (A : Lemma34TowerStepAlpha T) (O : Lemma34TowerStepOutside A) :
    Lemma34Refines T (lemma34_tower_of_step A O) := by
  refine ⟨?_⟩
  intro j
  simpa [lemma34_tower_of_step,
    Lemma34Tower.segL, Lemma34Tower.segR, Lemma34Tower.segAt,
    Lemma34TowerStepAlpha.segL, Lemma34TowerStepAlpha.segR,
    Lemma34TowerStepAlpha.segAt] using
    (lemma34_towerStepAlpha_nested A j)



/- Technical proof note. -/


/-!
P2b-beta-out for Bishop--Cheng Lemma 3.4.

This file closes the remaining `outside` field for the *canonical* P2b-alpha
successor `lemma34_tower_step_alpha`.  The canonical specialization is
essential: an arbitrary value of `Lemma34TowerStepAlpha T` need not consist of
the positive-charge cells produced by `lemma34_blockRefinementResult`, whereas
the zero-cell list and its radii are defined from precisely that canonical
refinement.

The finite location step below uses finite search.  Its only logical
cost is `selector-style construction`, which is already in the campaign's admissible dependency
set.  Once a parent block and a subdivision cell containing `x` have been
selected, the hypothesis that `x` is strictly outside every retained successor
cell forces that cell's charge to be zero.  The radius package from
P2b-beta-sigma then shrinks either the parent `outside` estimate or the selected
zero-cell estimate to the common successor radius.
-/

/-- Monotonicity of `COF.max` in its second argument. -/
theorem lemma34_out_max_mono_right {c x y : R} (hxy : Le x y) :
    Le (COF.max c x) (COF.max c y) := by
  apply cof_max_le
  · exact lemma33_le_max_left c y
  · exact le_trans hxy (lemma33_le_max_right c y)


/-- Monotonicity of `COF.min` in its second argument. -/
theorem lemma34_out_min_mono_right {c x y : R} (hxy : Le x y) :
    Le (COF.min c x) (COF.min c y) := by
  exact lemma34_le_min
    (cof_min_le_left c x)
    (le_trans (cof_min_le_right c x) hxy)


/-- Shrink the previous tower's `outside` estimate from `T.sigma` to the successor
radius recorded in `Sg`. -/
def lemma34_out_shrink_parent
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {heps : COF.lt 0 eps} {k : Nat}
    {T : Lemma34Tower P n eps k} {A : Lemma34TowerStepAlpha T}
    (Sg : Lemma34TowerStepSigma heps A) (x : R)
    (hp : P.p_lt
      (COF.max a (x - T.sigma))
      (COF.min b (x + T.sigma)) eps) :
    P.p_lt
      (COF.max a (x - Sg.sigma))
      (COF.min b (x + Sg.sigma)) eps := by
  apply lemma33_p_lt_subset P hp
  · exact lemma34_out_max_mono_right
      (lemma33_sub_le_sub_left (c := x) Sg.sigma_le_parent)
  · exact lemma34_out_min_mono_right
      (lemma33_add_le_add_left (c := x) Sg.sigma_le_parent)


/-- A relative Lemma 3.3 output attached to a proper parent block has at least
one cell. -/
theorem lemma34_out_rel_N_pos
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1))) :
    0 < r.N := by
  by_contra hbad
  have hN : r.N = 0 := Nat.eq_zero_of_not_pos hbad
  have hEq : B.left = B.right := by
    calc
      B.left = r.pts 0 := r.pts_zero.symm
      _ = r.pts r.N := by rw [hN]
      _ = B.right := r.pts_N
  have hp := B.proper
  rw [← hEq] at hp
  exact COF.lt_irrefl B.left hp


/-- A positive source index is retained by `lemma34_childBlocksOfResult`. -/
theorem lemma34_out_childBlock_mem_aux
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {eps : R} {k : Nat} (B : Lemma34Block P eps k)
    (r : Lemma33RelResult P B.left B.right B.mult eps
      (lemma34_widthScale a b (k + 1)))
    {xs : List Nat} {i : Nat}
    (hix : i ∈ xs) (hi : i < r.N) (hm : 0 < r.M (i + 1)) :
    lemma34_childBlockOfResult B r i hi hm ∈
      lemma34_childBlocksOfResult B r xs := by
  induction xs with
  | nil => simp at hix
  | cons j js ih =>
      simp only [List.mem_cons] at hix
      rcases hix with rfl | hix
      · simp [lemma34_childBlocksOfResult, hi, hm]
      · by_cases hj : j < r.N
        · by_cases hjm : 0 < r.M (j + 1)
          · simp [lemma34_childBlocksOfResult, hj, hjm, ih hix]
          · simpa [lemma34_childBlocksOfResult, hj, hjm] using ih hix
        · simpa [lemma34_childBlocksOfResult, hj] using ih hix


/-- A positive source cell occurs in the local canonical successor block
family of its parent. -/
theorem lemma34_out_childBlock_mem_for
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (B : Lemma34Block P eps k) (i : Nat)
    (hi : i < (lemma34_blockRefinementResult P eps heps k B).N)
    (hm : 0 < (lemma34_blockRefinementResult P eps heps k B).M (i + 1)) :
    lemma34_childBlockOfResult B
        (lemma34_blockRefinementResult P eps heps k B) i hi hm ∈
      lemma34_refinedBlocksFor P eps heps k B := by
  dsimp [lemma34_refinedBlocksFor]
  exact lemma34_out_childBlock_mem_aux B
    (lemma34_blockRefinementResult P eps heps k B)
    (List.mem_range.mpr hi) hi hm


/-- A positive source cell occurs in the global canonical successor block
family whenever its parent occurs in the previous tower. -/
theorem lemma34_out_childBlock_mem
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    (B : Lemma34Block P eps k) (hB : B ∈ T.blocks) (i : Nat)
    (hi : i < (lemma34_blockRefinementResult P eps heps k B).N)
    (hm : 0 < (lemma34_blockRefinementResult P eps heps k B).M (i + 1)) :
    lemma34_childBlockOfResult B
        (lemma34_blockRefinementResult P eps heps k B) i hi hm ∈
      lemma34_refinedBlocks P n eps heps k T := by
  unfold lemma34_refinedBlocks
  rw [List.mem_flatMap]
  exact ⟨B, hB, lemma34_out_childBlock_mem_for P eps heps k B i hi hm⟩


/-- Every positive-charge source cell occurs as a repeated segment of the
canonical P2b-alpha successor. -/
theorem lemma34_out_positiveCell_mem_alpha
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    (B : Lemma34Block P eps k) (hB : B ∈ T.blocks) (i : Nat)
    (hi : i < (lemma34_blockRefinementResult P eps heps k B).N)
    (hm : 0 < (lemma34_blockRefinementResult P eps heps k B).M (i + 1)) :
    ((lemma34_blockRefinementResult P eps heps k B).pts i,
      (lemma34_blockRefinementResult P eps heps k B).pts (i + 1)) ∈
      (lemma34_tower_step_alpha P n eps heps k T).segments := by
  let r := lemma34_blockRefinementResult P eps heps k B
  let C := lemma34_childBlockOfResult B r i hi hm
  have hC : C ∈ lemma34_refinedBlocks P n eps heps k T := by
    dsimp [C, r]
    exact lemma34_out_childBlock_mem P n eps heps k T B hB i hi hm
  have hpairC : (r.pts i, r.pts (i + 1)) ∈ C.expand := by
    have hrep := lemma34_mem_replicate_self
      (r.pts i, r.pts (i + 1)) hm
    simpa [C, Lemma34Block.expand] using hrep
  have hflat : (r.pts i, r.pts (i + 1)) ∈
      lemma34_flattenBlocks (lemma34_refinedBlocks P n eps heps k T) := by
    unfold lemma34_flattenBlocks
    rw [List.mem_flatMap]
    exact ⟨C, hC, hpairC⟩
  let A := lemma34_tower_step_alpha P n eps heps k T
  have hblocks : A.blocks = lemma34_refinedBlocks P n eps heps k T := by
    rfl
  change (r.pts i, r.pts (i + 1)) ∈ A.segments
  rw [A.flatten_segments, hblocks]
  exact hflat




/-- A positive displacement moves a point strictly to the left. -/
theorem lemma34_h4_sub_lt_self {x d : R} (hd : COF.lt 0 d) :
    COF.lt (x - d) x := by
  have h := COF.lt_add_left (x - d) hd
  convert h using 1 <;> ring

/-- A positive displacement moves a point strictly to the right. -/
theorem lemma34_h4_lt_add_self {x d : R} (hd : COF.lt 0 d) :
    COF.lt x (x + d) := by
  have h := COF.lt_add_left x hd
  convert h using 1 <;> ring

/--
A data-valued certificate that `x` lies in the open `sigma`-collar of one
zero-charge refinement cell.  The global membership proof is stored so that
the common-radius bound in `Lemma34TowerStepSigma` can be projected without
any choice.
-/
structure Lemma34H4ZeroCollar
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k) (sigma x : R) where
  cell : Lemma34ZeroCell P eps heps k
  cell_mem : cell ∈ lemma34_zeroCells P n eps heps k T
  left : R
  right : R
  source :
    P.p_lt
      (COF.max a (left - cell.omega))
      (COF.min b (right + cell.omega)) eps
  left_near : COF.lt (left - sigma) x
  right_near : COF.lt x (right + sigma)

/- Technical proof note. -/

/--
Fprevious the first `N+1` consecutive cells.  A cell may return a witness `W`, or
strictly place `x` to the right/left of that cell.  At a shared endpoint the
two incompatible orientations contradict irreflexivity, so the fold itself
needs no order decision.
-/
def lemma34_h4_scanCellsSucc
    (pts : Nat → R) (x : R) {W : Type*} :
    (N : Nat) →
    (∀ i, i < Nat.succ N →
      PSum W
        (PSum
          (COF.lt (pts (i + 1)) x)
          (COF.lt x (pts i)))) →
    PSum W
      (PSum
        (COF.lt (pts (Nat.succ N)) x)
        (COF.lt x (pts 0)))
  | 0, hcell =>
      hcell 0 (Nat.zero_lt_succ 0)
  | Nat.succ N, hcell =>
      match lemma34_h4_scanCellsSucc (W := W) pts x N
          (fun i hi =>
            hcell i
              (Nat.lt_trans hi
                (Nat.lt_succ_self (Nat.succ N)))) with
      | .inl w =>
          .inl w
      | .inr (.inr hleft) =>
          .inr (.inr hleft)
      | .inr (.inl hright) =>
          match hcell (Nat.succ N)
              (Nat.lt_succ_self (Nat.succ N)) with
          | .inl w =>
              .inl w
          | .inr (.inl hright') =>
              .inr (.inl hright')
          | .inr (.inr hleft') =>
              False.elim
                (COF.lt_irrefl (pts (Nat.succ N))
                  (COFO.lt_trans hright hleft'))

/-- Nonempty-cell wrapper around `lemma34_h4_scanCellsSucc`. -/
def lemma34_h4_scanCells
    (pts : Nat → R) (x : R) {W : Type*}
    (N : Nat) (hN : 0 < N)
    (hcell : ∀ i, i < N →
      PSum W
        (PSum
          (COF.lt (pts (i + 1)) x)
          (COF.lt x (pts i)))) :
    PSum W
      (PSum
        (COF.lt (pts N) x)
        (COF.lt x (pts 0))) := by
  cases N with
  | zero =>
      exact False.elim ((Nat.not_lt_zero 0) hN)
  | succ N =>
      exact lemma34_h4_scanCellsSucc (W := W) pts x N hcell

/--
Finite-list fold: either one element supplies `W`, or every element satisfies
`Q`.  The branch datum comes solely from the supplied data-valued local
classifier.
-/
def lemma34_h4_scanList {α W : Type*} (Q : α → Prop) :
    (xs : List α) →
    (∀ y, y ∈ xs → PSum W (Q y)) →
    PSum W (∀ y, y ∈ xs → Q y)
  | [], _ =>
      .inr (by
        intro y hy
        have hfalse : False := by simpa using hy
        exact hfalse.elim)
  | y :: ys, hloc =>
      match hloc y (by simp) with
      | .inl w =>
          .inl w
      | .inr hy =>
          match lemma34_h4_scanList (W := W) Q ys
              (fun z hz => hloc z (List.mem_cons_of_mem y hz)) with
          | .inl w =>
              .inl w
          | .inr hys =>
              .inr (by
                intro z hz
                simp only [List.mem_cons] at hz
                rcases hz with rfl | hz
                · exact hy
                · exact hys z hz)

/--
Constructively classify one refinement cell.

* A zero-charge cell is tested against the two open `sigma` collars by two
  calls to `COF.lt_cotrans_data`.
* A positive-charge cell occurs in the successor segment family.  Its proper
  endpoint gap supplies the data branch; the Prop-valued `hnew` disjunction
  is eliminated only while proving the selected strict-order proposition.
-/
noncomputable def lemma34_h4_classifyCell
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    (sigma x : R) (hsigma : COF.lt 0 sigma)
    (hnew : ∀ I,
      I ∈ (lemma34_tower_step_alpha
        P n eps heps k T).segments →
        COF.lt I.2 x ∨ COF.lt x I.1)
    (B : Lemma34Block P eps k) (hB : B ∈ T.blocks)
    (i : Nat)
    (hi : i < (lemma34_blockRefinementResult
      P eps heps k B).N) :
    PSum
      (Lemma34H4ZeroCollar
        P n eps heps k T sigma x)
      (PSum
        (COF.lt
          ((lemma34_blockRefinementResult
            P eps heps k B).pts (i + 1)) x)
        (COF.lt x
          ((lemma34_blockRefinementResult
            P eps heps k B).pts i))) := by
  let r := lemma34_blockRefinementResult P eps heps k B
  change
    PSum
      (Lemma34H4ZeroCollar
        P n eps heps k T sigma x)
      (PSum
        (COF.lt (r.pts (i + 1)) x)
        (COF.lt x (r.pts i)))
  by_cases hz : r.M (i + 1) = 0
  · have hleftGap : COF.lt (r.pts i - sigma) (r.pts i) :=
      lemma34_h4_sub_lt_self hsigma
    match COF.lt_cotrans_data hleftGap x with
    | .inr hxleft =>
        exact .inr (.inr hxleft)
    | .inl hleftNear =>
        have hrightGap :
            COF.lt (r.pts (i + 1))
              (r.pts (i + 1) + sigma) :=
          lemma34_h4_lt_add_self hsigma
        match COF.lt_cotrans_data hrightGap x with
        | .inl hright =>
            exact .inr (.inl hright)
        | .inr hrightNear =>
            let G := lemma34_zeroCellOf
              P eps heps k B i hi hz
            have hG :
                G ∈ lemma34_zeroCells P n eps heps k T := by
              dsimp [G]
              exact lemma34_zeroCellOf_mem
                P n eps heps k T B hB i hi hz
            exact .inl
              { cell := G
                cell_mem := hG
                left := r.pts i
                right := r.pts (i + 1)
                /- Technical proof note. -/
                source := by
                  simpa [G, lemma34_zeroCellOf, r] using
                    G.omega_p_lt
                left_near := hleftNear
                right_near := hrightNear }
  · have hm : 0 < r.M (i + 1) := Nat.pos_of_ne_zero hz
    have hmem :
        (r.pts i, r.pts (i + 1)) ∈
          (lemma34_tower_step_alpha
            P n eps heps k T).segments := by
      simpa [r] using
        (lemma34_out_positiveCell_mem_alpha
          P n eps heps k T B hB i hi hm)
    have hout := hnew (r.pts i, r.pts (i + 1)) hmem
    have hproper : COF.lt (r.pts i) (r.pts (i + 1)) :=
      r.pts_mono i hi
    match COF.lt_cotrans_data hproper x with
    | .inl hlx =>
        have hrx : COF.lt (r.pts (i + 1)) x := by
          rcases hout with hrx | hxl
          · exact hrx
          · exact False.elim
              (COF.lt_irrefl x
                (COFO.lt_trans hxl hlx))
        exact .inr (.inl hrx)
    | .inr hxr =>
        have hxl : COF.lt x (r.pts i) := by
          rcases hout with hrx | hxl
          · exact False.elim
              (COF.lt_irrefl x
                (COFO.lt_trans hxr hrx))
          · exact hxl
        exact .inr (.inr hxl)

/--
Scan all cells of one parent block.  If no zero-cell collar is found, the
cell fold places `x` strictly outside one of the two parent endpoints.
-/
noncomputable def lemma34_h4_classifyBlock
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    (sigma x : R) (hsigma : COF.lt 0 sigma)
    (hnew : ∀ I,
      I ∈ (lemma34_tower_step_alpha
        P n eps heps k T).segments →
        COF.lt I.2 x ∨ COF.lt x I.1)
    (B : Lemma34Block P eps k) (hB : B ∈ T.blocks) :
    PSum
      (Lemma34H4ZeroCollar
        P n eps heps k T sigma x)
      (COF.lt B.right x ∨ COF.lt x B.left) := by
  let r := lemma34_blockRefinementResult P eps heps k B
  have hN : 0 < r.N := lemma34_out_rel_N_pos B r
  have hscan :
      PSum
        (Lemma34H4ZeroCollar
          P n eps heps k T sigma x)
        (PSum
          (COF.lt (r.pts r.N) x)
          (COF.lt x (r.pts 0))) :=
    lemma34_h4_scanCells
      (W := Lemma34H4ZeroCollar
        P n eps heps k T sigma x)
      r.pts x r.N hN
      (fun i hi =>
        lemma34_h4_classifyCell
          P n eps heps k T sigma x hsigma hnew B hB i hi)
  match hscan with
  | .inl W =>
      exact .inl W
  /- Technical proof note. -/
  | .inr (.inl hright) =>
      exact .inr (Or.inl (by
        rw [← r.pts_N]
        exact hright))
  | .inr (.inr hleft) =>
      exact .inr (Or.inr (by
        rw [← r.pts_zero]
        exact hleft))

/--
Shrink the `p_lt` witness of a zero-charge cell to the successor collar around
`x`.  The two strict collar inequalities consume one `sigma` each, while
`Sg.twice_sigma_le_zeroCell` supplies `2*sigma ≤ omega`.
-/
noncomputable def lemma34_h4_shrink_zeroCollar
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (T : Lemma34Tower P n eps k)
    {A : Lemma34TowerStepAlpha T}
    (Sg : Lemma34TowerStepSigma heps A)
    {x : R}
    (W : Lemma34H4ZeroCollar
      P n eps heps k T Sg.sigma x) :
    P.p_lt
      (COF.max a (x - Sg.sigma))
      (COF.min b (x + Sg.sigma)) eps := by
  have htwice :
      Le (Sg.sigma + Sg.sigma) W.cell.omega :=
    Sg.twice_sigma_le_zeroCell W.cell W.cell_mem
  have hleftWeak :
      Le
        (W.left - W.cell.omega)
        (W.left - (Sg.sigma + Sg.sigma)) :=
    lemma33_sub_le_sub (le_refl _) htwice
  have hleftStrict :
      COF.lt
        (W.left - (Sg.sigma + Sg.sigma))
        (x - Sg.sigma) := by
    have h := COF.lt_add_left (-Sg.sigma) W.left_near
    convert h using 1 <;> ring
  have hrightStrict :
      COF.lt
        (x + Sg.sigma)
        (W.right + (Sg.sigma + Sg.sigma)) := by
    have h := COF.lt_add_left Sg.sigma W.right_near
    convert h using 1 <;> ring
  have hrightWeak :
      Le
        (W.right + (Sg.sigma + Sg.sigma))
        (W.right + W.cell.omega) :=
    lemma33_add_le_add (le_refl _) htwice
  apply lemma33_p_lt_subset P W.source
  · exact lemma34_out_max_mono_right
      (le_trans hleftWeak (le_of_lt hleftStrict))
  · exact lemma34_out_min_mono_right
      (le_trans (le_of_lt hrightStrict) hrightWeak)

/--
Choice-free Phase-3 replacement for the successor `outside` proof.

The finite list fold returns either a concrete zero-cell collar, or strict
outside proofs for every previous parent block.  In the former branch the stored
zero-cell `p_lt` witness is shrunk using `2*sigma ≤ omega`; in the latter the
previous tower's `outside` witness is shrunk using `sigma ≤ T.sigma`.
-/
noncomputable def lemma34_step_outside_proof
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (_hn : 0 < n) (T : Lemma34Tower P n eps k) :
    ∀ x, Le a x → Le x b →
      (∀ I,
        I ∈ (lemma34_tower_step_alpha
          P n eps heps k T).segments →
          COF.lt I.2 x ∨ COF.lt x I.1) →
      P.p_lt
        (COF.max a
          (x - (lemma34_tower_step_sigma
            P n eps heps k T
            (lemma34_tower_step_alpha
              P n eps heps k T)).sigma))
        (COF.min b
          (x + (lemma34_tower_step_sigma
            P n eps heps k T
            (lemma34_tower_step_alpha
              P n eps heps k T)).sigma))
        eps := by
  intro x hax hxb hnew
  set A := lemma34_tower_step_alpha P n eps heps k T with hA
  set Sg := lemma34_tower_step_sigma P n eps heps k T A with hSg
  have hscan :
      PSum
        (Lemma34H4ZeroCollar
          P n eps heps k T Sg.sigma x)
        (∀ B, B ∈ T.blocks →
          COF.lt B.right x ∨ COF.lt x B.left) := by
    exact lemma34_h4_scanList
      (W := Lemma34H4ZeroCollar
        P n eps heps k T Sg.sigma x)
      (fun B : Lemma34Block P eps k =>
        COF.lt B.right x ∨ COF.lt x B.left)
      T.blocks
      (fun B hB =>
        lemma34_h4_classifyBlock
          P n eps heps k T Sg.sigma x
          Sg.sigma_pos hnew B hB)
  match hscan with
  | .inl W =>
      exact lemma34_h4_shrink_zeroCollar
        P n eps heps k T Sg W
  | .inr hprevious =>
      have hsegments : ∀ I, I ∈ T.segments →
          COF.lt I.2 x ∨ COF.lt x I.1 := by
        intro I hI
        have hIf :
            I ∈ lemma34_flattenBlocks T.blocks := by
          rw [← T.flatten_segments]
          exact hI
        rcases lemma34_mem_flattenBlocks hIf with
          ⟨B, hB, hEq⟩
        subst I
        exact hprevious B hB
      exact lemma34_out_shrink_parent Sg x
        (T.outside x hax hxb hsegments)


/-- Package the canonical successor radius together with the completed
`outside` proof. -/
noncomputable def lemma34_tower_step_outside
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (hn : 0 < n) (T : Lemma34Tower P n eps k) :
    Lemma34TowerStepOutside
      (lemma34_tower_step_alpha P n eps heps k T) := by
  let A := lemma34_tower_step_alpha P n eps heps k T
  let Sg := lemma34_tower_step_sigma P n eps heps k T A
  have hout : ∀ x, Le a x → Le x b →
      (∀ I, I ∈ A.segments → COF.lt I.2 x ∨ COF.lt x I.1) →
      P.p_lt (COF.max a (x - Sg.sigma))
        (COF.min b (x + Sg.sigma)) eps := by
    intro x hax hxb hx
    simpa [A, Sg] using
      (lemma34_step_outside_proof P n eps heps k hn T x hax hxb
        (by simpa [A] using hx))
  have O : Lemma34TowerStepOutside A :=
    lemma34_stepOutside_of_sigma Sg hout
  simpa [A] using O


/-- Complete P2b: one canonical tower successor together with its positionwise
refinement witness. -/
noncomputable def lemma34_tower_step
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (n : Nat) (eps : R) (heps : COF.lt 0 eps) (k : Nat)
    (hn : 0 < n) (T : Lemma34Tower P n eps k) :
    {T' : Lemma34Tower P n eps (k + 1) // Lemma34Refines T T'} := by
  let A := lemma34_tower_step_alpha P n eps heps k T
  have O : Lemma34TowerStepOutside A := by
    simpa [A] using lemma34_tower_step_outside P n eps heps k hn T
  exact ⟨lemma34_tower_of_step A O, lemma34_tower_of_step_refines A O⟩



/- Technical proof note. -/


/-!
P3-a for Bishop--Cheng Lemma 3.4.

The outer induction is now available as the verified constructor
`lemma34_tower_step`.  This file builds its canonical dependent tower sequence,
proves positionwise nesting at arbitrary levels, constructs an explicit Cauchy
modulus for every left-endpoint sequence, and extracts the points `t_j` by
`COFOC.complete`.

The Cauchy proof uses a direct nested-interval estimate rather than
`isCauchy_of_mono_bounded_gap`, whose fixed upper-bound parameter would be
circular here: for `M <= m,n`, both left endpoints lie in the level-`M`
interval, so their distance is bounded by that interval's dyadic width.
-/

/-- The canonical tower obtained by iterating the verified successor step. -/
noncomputable def lemma34_towerSeq
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) :
    (k : Nat) -> Lemma34Tower P n eps k
  | 0 => lemma34_tower_base P eps n hn h_cond
  | k + 1 =>
      (lemma34_tower_step P n eps heps k hn
        (lemma34_towerSeq P eps heps n hn h_cond k)).val


/-- Consecutive members of the canonical tower carry the refinement witness
returned by `lemma34_tower_step`. -/
theorem lemma34_towerSeq_refines
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (k : Nat) :
    Lemma34Refines
      (lemma34_towerSeq P eps heps n hn h_cond k)
      (lemma34_towerSeq P eps heps n hn h_cond (k + 1)) := by
  change Lemma34Refines
    (lemma34_towerSeq P eps heps n hn h_cond k)
    ((lemma34_tower_step P n eps heps k hn
      (lemma34_towerSeq P eps heps n hn h_cond k)).val)
  exact (lemma34_tower_step P n eps heps k hn
    (lemma34_towerSeq P eps heps n hn h_cond k)).property


/-- The interval selected at a position belongs to the stored segment list. -/
theorem Lemma34Tower.segAt_mem
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat} (T : Lemma34Tower P n eps k)
    (j : Fin n) : T.segAt j ∈ T.segments := by
  unfold Lemma34Tower.segAt
  exact List.get_mem _ _


/-- Bounds and properness of the interval occupying position `j`. -/
theorem lemma34_towerSeq_segment_proper
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (k : Nat) (j : Fin n) :
    Le a ((lemma34_towerSeq P eps heps n hn h_cond k).segL j) ∧
      COF.lt ((lemma34_towerSeq P eps heps n hn h_cond k).segL j)
        ((lemma34_towerSeq P eps heps n hn h_cond k).segR j) ∧
      Le ((lemma34_towerSeq P eps heps n hn h_cond k).segR j) b := by
  let T := lemma34_towerSeq P eps heps n hn h_cond k
  have h := T.segment_proper (T.segAt j) (T.segAt_mem j)
  simpa [T, Lemma34Tower.segL, Lemma34Tower.segR] using h


/-- Width estimate for the interval occupying position `j`. -/
theorem lemma34_towerSeq_segment_width
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (k : Nat) (j : Fin n) :
    Le
      ((lemma34_towerSeq P eps heps n hn h_cond k).segR j -
        (lemma34_towerSeq P eps heps n hn h_cond k).segL j)
      (lemma34_widthScale a b k) := by
  let T := lemma34_towerSeq P eps heps n hn h_cond k
  have h := T.segment_width (T.segAt j) (T.segAt_mem j)
  simpa [T, Lemma34Tower.segL, Lemma34Tower.segR] using h


/-- Positionwise inclusion between any two levels of the canonical tower. -/
theorem lemma34_towerSeq_nested
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps))
    {p q : Nat} (hpq : p ≤ q) (j : Fin n) :
    Le ((lemma34_towerSeq P eps heps n hn h_cond p).segL j)
        ((lemma34_towerSeq P eps heps n hn h_cond q).segL j) ∧
      Le ((lemma34_towerSeq P eps heps n hn h_cond q).segR j)
        ((lemma34_towerSeq P eps heps n hn h_cond p).segR j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  induction d with
  | zero =>
      simpa using And.intro
        (le_refl
          ((lemma34_towerSeq P eps heps n hn h_cond p).segL j))
        (le_refl
          ((lemma34_towerSeq P eps heps n hn h_cond p).segR j))
  | succ d ih =>
      have hs :=
        (lemma34_towerSeq_refines P eps heps n hn h_cond (p + d)).nested j
      have ihc := ih (Nat.le_add_right p d)
      constructor
      · have h := le_trans ihc.1 hs.1
        simpa [Nat.add_assoc] using h
      · have h := le_trans hs.2 ihc.2
        simpa [Nat.add_assoc] using h


/-- Left endpoint sequence at a fixed repeated position. -/
noncomputable def lemma34_leftSeq
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n) (k : Nat) : R :=
  (lemma34_towerSeq P eps heps n hn h_cond k).segL j


/-- Right endpoint sequence at a fixed repeated position. -/
noncomputable def lemma34_rightSeq
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n) (k : Nat) : R :=
  (lemma34_towerSeq P eps heps n hn h_cond k).segR j


/-- Left endpoints are weakly increasing with the tower level. -/
theorem lemma34_leftSeq_mono
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n)
    {p q : Nat} (hpq : p ≤ q) :
    Le (lemma34_leftSeq P eps heps n hn h_cond j p)
      (lemma34_leftSeq P eps heps n hn h_cond j q) := by
  simpa [lemma34_leftSeq] using
    (lemma34_towerSeq_nested P eps heps n hn h_cond hpq j).1


/-- Right endpoints are weakly decreasing with the tower level. -/
theorem lemma34_rightSeq_antitone
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n)
    {p q : Nat} (hpq : p ≤ q) :
    Le (lemma34_rightSeq P eps heps n hn h_cond j q)
      (lemma34_rightSeq P eps heps n hn h_cond j p) := by
  simpa [lemma34_rightSeq] using
    (lemma34_towerSeq_nested P eps heps n hn h_cond hpq j).2


/-- Once level `M` has been reached, any two left endpoints at the same
position are at distance at most the width of the level-`M` interval. -/
theorem lemma34_leftSeq_abs_le_width
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n)
    (M m q : Nat) (hMm : M ≤ m) (hMq : M ≤ q) :
    Le (COF.abs
        (lemma34_leftSeq P eps heps n hn h_cond j m -
          lemma34_leftSeq P eps heps n hn h_cond j q))
      (lemma34_widthScale a b M) := by
  by_cases hmq : m ≤ q
  · have hMmNest :=
      lemma34_towerSeq_nested P eps heps n hn h_cond hMm j
    have hmqNest :=
      lemma34_towerSeq_nested P eps heps n hn h_cond hmq j
    have hproperQ :=
      lemma34_towerSeq_segment_proper P eps heps n hn h_cond q j
    have hLqRq : Le
        (lemma34_leftSeq P eps heps n hn h_cond j q)
        (lemma34_rightSeq P eps heps n hn h_cond j q) := by
      exact le_of_lt hproperQ.2.1
    have hLqRM : Le
        (lemma34_leftSeq P eps heps n hn h_cond j q)
        (lemma34_rightSeq P eps heps n hn h_cond j M) := by
      exact le_trans hLqRq (le_trans
        (by simpa [lemma34_rightSeq] using hmqNest.2)
        (by simpa [lemma34_rightSeq] using hMmNest.2))
    have hLMLm : Le
        (lemma34_leftSeq P eps heps n hn h_cond j M)
        (lemma34_leftSeq P eps heps n hn h_cond j m) := by
      simpa [lemma34_leftSeq] using hMmNest.1
    have hdiff : Le
        (lemma34_leftSeq P eps heps n hn h_cond j q -
          lemma34_leftSeq P eps heps n hn h_cond j m)
        (lemma34_rightSeq P eps heps n hn h_cond j M -
          lemma34_leftSeq P eps heps n hn h_cond j M) :=
      lemma33_sub_le_sub hLqRM hLMLm
    have hLmLq : Le
        (lemma34_leftSeq P eps heps n hn h_cond j m)
        (lemma34_leftSeq P eps heps n hn h_cond j q) := by
      simpa [lemma34_leftSeq] using hmqNest.1
    have hnonneg : Nonneg
        (lemma34_leftSeq P eps heps n hn h_cond j q -
          lemma34_leftSeq P eps heps n hn h_cond j m) :=
      nonneg_sub_of_le hLmLq
    have habs : COF.abs
        (lemma34_leftSeq P eps heps n hn h_cond j m -
          lemma34_leftSeq P eps heps n hn h_cond j q) =
        lemma34_leftSeq P eps heps n hn h_cond j q -
          lemma34_leftSeq P eps heps n hn h_cond j m := by
      rw [show
          lemma34_leftSeq P eps heps n hn h_cond j m -
              lemma34_leftSeq P eps heps n hn h_cond j q =
            -(lemma34_leftSeq P eps heps n hn h_cond j q -
              lemma34_leftSeq P eps heps n hn h_cond j m) by ring,
        COFO.abs_neg, COFO.abs_of_nonneg hnonneg]
    rw [habs]
    exact le_trans hdiff
      (by simpa [lemma34_leftSeq, lemma34_rightSeq] using
        lemma34_towerSeq_segment_width P eps heps n hn h_cond M j)
  · have hqm : q ≤ m := by omega
    have hMqNest :=
      lemma34_towerSeq_nested P eps heps n hn h_cond hMq j
    have hqmNest :=
      lemma34_towerSeq_nested P eps heps n hn h_cond hqm j
    have hproperM :=
      lemma34_towerSeq_segment_proper P eps heps n hn h_cond m j
    have hLmRm : Le
        (lemma34_leftSeq P eps heps n hn h_cond j m)
        (lemma34_rightSeq P eps heps n hn h_cond j m) := by
      exact le_of_lt hproperM.2.1
    have hLmRM : Le
        (lemma34_leftSeq P eps heps n hn h_cond j m)
        (lemma34_rightSeq P eps heps n hn h_cond j M) := by
      exact le_trans hLmRm (le_trans
        (by simpa [lemma34_rightSeq] using hqmNest.2)
        (by simpa [lemma34_rightSeq] using hMqNest.2))
    have hLMLq : Le
        (lemma34_leftSeq P eps heps n hn h_cond j M)
        (lemma34_leftSeq P eps heps n hn h_cond j q) := by
      simpa [lemma34_leftSeq] using hMqNest.1
    have hdiff : Le
        (lemma34_leftSeq P eps heps n hn h_cond j m -
          lemma34_leftSeq P eps heps n hn h_cond j q)
        (lemma34_rightSeq P eps heps n hn h_cond j M -
          lemma34_leftSeq P eps heps n hn h_cond j M) :=
      lemma33_sub_le_sub hLmRM hLMLq
    have hLqLm : Le
        (lemma34_leftSeq P eps heps n hn h_cond j q)
        (lemma34_leftSeq P eps heps n hn h_cond j m) := by
      simpa [lemma34_leftSeq] using hqmNest.1
    have hnonneg : Nonneg
        (lemma34_leftSeq P eps heps n hn h_cond j m -
          lemma34_leftSeq P eps heps n hn h_cond j q) :=
      nonneg_sub_of_le hLqLm
    rw [COFO.abs_of_nonneg hnonneg]
    exact le_trans hdiff
      (by simpa [lemma34_leftSeq, lemma34_rightSeq] using
        lemma34_towerSeq_segment_width P eps heps n hn h_cond M j)


/-- Explicit dyadic Cauchy modulus for the left endpoints at position `j`. -/
noncomputable def lemma34_leftSeq_isCauchy
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n) :
    IsCauchy (lemma34_leftSeq P eps heps n hn h_cond j) := by
  refine {
    cmod := fun k =>
      (lemma34_widthScale_eventually_lt a b (COF.halfPow k)
        (halfPow_pos k)).val
    ccond := ?_
  }
  intro k m q hm hq
  have habs := lemma34_leftSeq_abs_le_width P eps heps n hn h_cond j
    ((lemma34_widthScale_eventually_lt a b (COF.halfPow k)
      (halfPow_pos k)).val) m q hm hq
  exact lt_of_le_of_lt habs
    (lemma34_widthScale_eventually_lt a b (COF.halfPow k)
      (halfPow_pos k)).property


/-- Completeness supplies the point determined by the nested intervals at
position `j`. -/
noncomputable def lemma34_leftLimit
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n) :
    HasLim (lemma34_leftSeq P eps heps n hn h_cond j) :=
  COFOC.complete (lemma34_leftSeq_isCauchy P eps heps n hn h_cond j)


/-- Every left endpoint lies weakly below the extracted limit point. -/
theorem lemma34_leftSeq_le_limit
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n) (k : Nat) :
    Le (lemma34_leftSeq P eps heps n hn h_cond j k)
      (lemma34_leftLimit P eps heps n hn h_cond j).val := by
  let L : Nat -> R := lemma34_leftSeq P eps heps n hn h_cond j
  let H : HasLim L := lemma34_leftLimit P eps heps n hn h_cond j
  change Le (L k) H.val
  intro hbad
  have hgap : COF.lt 0 (L k - H.val) := lemma33_sub_pos_of_lt hbad
  let w := COFO.archimedean_pos (L k - H.val) hgap
  let m : Nat := Nat.max k (H.tends.mod w.val)
  have hkm : k ≤ m := Nat.le_max_left _ _
  have hmod : H.tends.mod w.val ≤ m := Nat.le_max_right _ _
  have hmono : Le (L k) (L m) := by
    dsimp [L]
    exact lemma34_leftSeq_mono P eps heps n hn h_cond j hkm
  have htLm : Le H.val (L m) := le_trans (le_of_lt hbad) hmono
  have hclose : COF.lt (COF.abs (L m - H.val)) (COF.halfPow w.val) :=
    H.tends.close w.val m hmod
  have hnonneg : Nonneg (L m - H.val) := nonneg_sub_of_le htLm
  rw [COFO.abs_of_nonneg hnonneg] at hclose
  have hsub : Le (L k - H.val) (L m - H.val) :=
    lemma33_sub_le_sub_right hmono
  have hloop : COF.lt (COF.halfPow w.val) (COF.halfPow w.val) :=
    COFO.lt_trans (lt_of_lt_of_le w.property hsub) hclose
  exact COF.lt_irrefl _ hloop


/-- The extracted point lies weakly below every right endpoint. -/
theorem lemma34_limit_le_rightSeq
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n) (k : Nat) :
    Le (lemma34_leftLimit P eps heps n hn h_cond j).val
      (lemma34_rightSeq P eps heps n hn h_cond j k) := by
  let L : Nat -> R := lemma34_leftSeq P eps heps n hn h_cond j
  let Rr : Nat -> R := lemma34_rightSeq P eps heps n hn h_cond j
  let H : HasLim L := lemma34_leftLimit P eps heps n hn h_cond j
  change Le H.val (Rr k)
  intro hbad
  have hgap : COF.lt 0 (H.val - Rr k) := lemma33_sub_pos_of_lt hbad
  let w := COFO.archimedean_pos (H.val - Rr k) hgap
  let m : Nat := Nat.max k (H.tends.mod w.val)
  have hkm : k ≤ m := Nat.le_max_left _ _
  have hmod : H.tends.mod w.val ≤ m := Nat.le_max_right _ _
  have hRmk : Le (Rr m) (Rr k) := by
    dsimp [Rr]
    exact lemma34_rightSeq_antitone P eps heps n hn h_cond j hkm
  have hproperM :=
    lemma34_towerSeq_segment_proper P eps heps n hn h_cond m j
  have hLmRm : Le (L m) (Rr m) := by
    exact le_of_lt hproperM.2.1
  have hLmRk : Le (L m) (Rr k) := le_trans hLmRm hRmk
  have hLmt : Le (L m) H.val := le_trans hLmRk (le_of_lt hbad)
  have hclose : COF.lt (COF.abs (L m - H.val)) (COF.halfPow w.val) :=
    H.tends.close w.val m hmod
  have hnonneg : Nonneg (H.val - L m) := nonneg_sub_of_le hLmt
  rw [show L m - H.val = -(H.val - L m) by ring,
    COFO.abs_neg, COFO.abs_of_nonneg hnonneg] at hclose
  have hsub : Le (H.val - Rr k) (H.val - L m) :=
    lemma33_sub_le_sub_left hLmRk
  have hloop : COF.lt (COF.halfPow w.val) (COF.halfPow w.val) :=
    COFO.lt_trans (lt_of_lt_of_le w.property hsub) hclose
  exact COF.lt_irrefl _ hloop


/-- The extracted point belongs to `[a,b]`. -/
theorem lemma34_leftLimit_bounds
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) (j : Fin n) :
    Le a (lemma34_leftLimit P eps heps n hn h_cond j).val ∧
      Le (lemma34_leftLimit P eps heps n hn h_cond j).val b := by
  have hproper0 :=
    lemma34_towerSeq_segment_proper P eps heps n hn h_cond 0 j
  exact ⟨
    le_trans hproper0.1
      (by simpa [lemma34_leftSeq] using
        lemma34_leftSeq_le_limit P eps heps n hn h_cond j 0),
    le_trans
      (by simpa [lemma34_rightSeq] using
        lemma34_limit_le_rightSeq P eps heps n hn h_cond j 0)
      hproper0.2.2
  ⟩


/-- P3-a output package: the `n` extracted points, their convergence
certificates, their global bounds, and membership in every nested segment. -/
structure Lemma34LimitData
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) where
  t : Fin n -> R
  tends : ∀ j : Fin n,
    RSeq.TendstoHalf
      (lemma34_leftSeq P eps heps n hn h_cond j) (t j)
  bounds : ∀ j : Fin n, Le a (t j) ∧ Le (t j) b
  in_segment : ∀ (k : Nat) (j : Fin n),
    Le (lemma34_leftSeq P eps heps n hn h_cond j k) (t j) ∧
      Le (t j) (lemma34_rightSeq P eps heps n hn h_cond j k)
  width : ∀ (k : Nat) (j : Fin n),
    Le
      (lemma34_rightSeq P eps heps n hn h_cond j k -
        lemma34_leftSeq P eps heps n hn h_cond j k)
      (lemma34_widthScale a b k)


/-- Canonical P3-a data obtained from the completed left endpoint sequences. -/
noncomputable def lemma34_limitData
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat) (hn : 0 < n)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) :
    Lemma34LimitData P eps heps n hn h_cond := by
  refine {
    t := fun j => (lemma34_leftLimit P eps heps n hn h_cond j).val
    tends := ?_
    bounds := ?_
    in_segment := ?_
    width := ?_
  }
  · intro j
    exact (lemma34_leftLimit P eps heps n hn h_cond j).tends
  · intro j
    exact lemma34_leftLimit_bounds P eps heps n hn h_cond j
  · intro k j
    exact ⟨
      lemma34_leftSeq_le_limit P eps heps n hn h_cond j k,
      lemma34_limit_le_rightSeq P eps heps n hn h_cond j k
    ⟩
  · intro k j
    simpa [lemma34_leftSeq, lemma34_rightSeq] using
      lemma34_towerSeq_segment_width P eps heps n hn h_cond k j





/- Technical proof note. -/


/-!
P3-b for Bishop--Cheng Lemma 3.4.

P3-a has already constructed the canonical tower and the limiting points.  The
remaining argument chooses a level whose segment width is smaller than `beta`,
shows that every point more than `beta` from all limiting points is strictly
outside every segment at that level, and invokes the tower's `outside` field.

This splice version uses the final declaration name `lemma_3_4`.  Insert the
helper declarations and replace the scaffold declaration of `lemma_3_4` with
the theorem below.
-/

/-- Every member of a tower's segment list occurs at a `Fin n` position. -/
theorem lemma34_segments_mem_index
    {a b : R} {hab : COF.lt a b} {P : Profile a b hab}
    {n : Nat} {eps : R} {k : Nat}
    (T : Lemma34Tower P n eps k) {I : R × R}
    (hI : I ∈ T.segments) :
    ∃ j : Fin n, I.1 = T.segL j ∧ I.2 = T.segR j := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hI
  have hin : i < n := by
    rw [← T.segments_length]
    exact hi
  let j : Fin n := ⟨i, hin⟩
  have hAt : T.segAt j = I := by
    simpa [Lemma34Tower.segAt, j] using hget
  refine ⟨j, ?_, ?_⟩
  · simpa [Lemma34Tower.segL] using
      congrArg (fun J : R × R => J.1) hAt.symm
  · simpa [Lemma34Tower.segR] using
      congrArg (fun J : R × R => J.2) hAt.symm


/-- A positive number below `|c|` lies below `c` or below `-c`.
This is the constructive sign split supplied by apartness. -/
theorem lemma34_lt_abs_cases {beta c : R}
    (hbeta : COF.lt 0 beta)
    (hfar : COF.lt beta (COF.abs c)) :
    COF.lt beta c ∨ COF.lt c (-beta) := by
  have habs_pos : COF.lt 0 (COF.abs c) := COFO.lt_trans hbeta hfar
  rcases COFO.lt_or_lt_of_abs_pos habs_pos with hcpos | hcneg
  · have hc_nonneg : Nonneg c := le_of_lt hcpos
    rw [COFO.abs_of_nonneg hc_nonneg] at hfar
    exact Or.inl hfar
  · have hneg_pos : COF.lt 0 (-c) := by
      have h := lemma33_add_lt_add_left (c := -c) hcneg
      convert h using 1 <;> ring
    have hneg_nonneg : Nonneg (-c) := le_of_lt hneg_pos
    rw [show c = -(-c) by ring, COFO.abs_neg,
      COFO.abs_of_nonneg hneg_nonneg] at hfar
    have hsum : COF.lt (c + beta) 0 := by
      have h := lemma33_add_lt_add_left (c := c) hfar
      convert h using 1 <;> ring
    have hshift := lemma33_add_lt_add_right (c := -beta) hsum
    exact Or.inr (by convert hshift using 1 <;> ring)


/-- If `t ∈ [L,R]`, the interval width is below `beta`, and `x` is farther
than `beta` from `t`, then `x` is strictly outside `[L,R]`. -/
theorem lemma34_far_outside_interval
    {L Rr t x beta : R}
    (hbeta : COF.lt 0 beta)
    (hLt : Le L t) (htR : Le t Rr)
    (hwidth : COF.lt (Rr - L) beta)
    (hfar : COF.lt beta (COF.abs (x - t))) :
    COF.lt Rr x ∨ COF.lt x L := by
  rcases lemma34_lt_abs_cases hbeta hfar with hright | hleft
  · left
    have hRt : Le (Rr - t) (Rr - L) :=
      lemma33_sub_le_sub_left (c := Rr) hLt
    have hRt_beta : COF.lt (Rr - t) beta :=
      BishopC.lt_of_le_of_lt hRt hwidth
    have hdiff : COF.lt (Rr - t) (x - t) :=
      COFO.lt_trans hRt_beta hright
    have hadd := lemma33_add_lt_add_right (c := t) hdiff
    convert hadd using 1 <;> ring
  · right
    have htL : Le (t - L) (Rr - L) :=
      lemma33_sub_le_sub_right (c := L) htR
    have htL_beta : COF.lt (t - L) beta :=
      BishopC.lt_of_le_of_lt htL hwidth
    have hneg_beta : COF.lt (-beta) (L - t) := by
      have h := lemma33_add_lt_add_right
        (c := L - t - beta) htL_beta
      convert h using 1 <;> ring
    have hdiff : COF.lt (x - t) (L - t) :=
      COFO.lt_trans hleft hneg_beta
    have hadd := lemma33_add_lt_add_right (c := t) hdiff
    convert hadd using 1 <;> ring


/-- (A) Data-valued form of Bishop--Cheng Lemma 3.4. -/
noncomputable def lemma_3_4
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (eps : R) (heps : COF.lt 0 eps) (n : Nat)
    (h_cond : COF.lt
      (P.lambda P.oneCode - P.lambda P.zeroCode)
      (((n + 1 : Nat) : R) * eps)) :
    Σ' t : Fin n → R,
      (∀ i, Le a (t i) ∧ Le (t i) b) ×'
      (∀ beta : R, COF.lt 0 beta →
        Σ' gamma : R,
          COF.lt 0 gamma ×'
          (∀ t_pt : R, Le a t_pt → Le t_pt b →
            (∀ i, COF.lt beta (COF.abs (t_pt - t i))) →
            P.p_lt
              (COF.max a (t_pt - gamma))
              (COF.min b (t_pt + gamma)) eps)) := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨(fun i => Fin.elim0 i), ?_,
      (fun beta hbeta => ?_)⟩
    · intro i
      exact Fin.elim0 i
    · refine ⟨1, COFO.one_pos,
        (fun t_pt hat htb hfar => ?_)⟩
      exact
        { f1 := P.zeroCode
          f1_mem := P.has_zero
          f2 := P.oneCode
          f2_mem := P.has_one
          cond1 := by
            intro s _ _ _
            exact P.zeroCode_apply s
          cond2 := by
            intro s _ _ _
            exact P.oneCode_apply s
          gap := by
            simpa using h_cond }
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let D := lemma34_limitData P eps heps n hn h_cond
    refine ⟨D.t, D.bounds, (fun beta hbeta => ?_)⟩
    let K := lemma34_widthScale_eventually_lt a b beta hbeta
    let k : Nat := K.val
    have hk : COF.lt (lemma34_widthScale a b k) beta := by
      simpa [k] using K.property
    let T : Lemma34Tower P n eps k :=
      lemma34_towerSeq P eps heps n hn h_cond k
    refine ⟨T.sigma, T.sigma_pos,
      (fun t_pt hat htb hfar => ?_)⟩
    refine T.outside t_pt hat htb ?_
    intro I hI
    obtain ⟨j, hIleft, hIright⟩ :=
      lemma34_segments_mem_index T hI
    /- Technical proof note. -/
    have hs :
        Le (T.segL j) (D.t j) ∧
        Le (D.t j) (T.segR j) ∧
        Le (T.segR j - T.segL j)
          (lemma34_widthScale a b k) := by
      exact ⟨
        by
          simpa [T, lemma34_leftSeq] using
            (D.in_segment k j).1,
        by
          simpa [T, lemma34_rightSeq] using
            (D.in_segment k j).2,
        by
          simpa [T, lemma34_leftSeq, lemma34_rightSeq] using
            D.width k j
      ⟩
    have hwidth : COF.lt (T.segR j - T.segL j) beta :=
      BishopC.lt_of_le_of_lt hs.2.2 hk
    rw [hIleft, hIright]
    exact lemma34_far_outside_interval
      (L := T.segL j) (Rr := T.segR j) (t := D.t j)
      (x := t_pt) (beta := beta)
      hbeta hs.1 hs.2.1 hwidth (hfar j)



/-- Technical lemma used in the public import closure. -/
-- Technical note.
def Profile.IsSmoothAt {a b : R} {hab : COF.lt a b} (P : Profile a b hab) (t : R) : Prop :=
  ∃ lambda_bar : R,
    ∀ eps : R, COF.lt 0 eps →
      ∃ delta : R, COF.lt 0 delta ∧
        ∀ f ∈ P.F, (∀ x, Le (t + delta) x → f x = 1) →
                   (∀ x, Le x (t - delta) → f x = 0) →
                   COF.lt (COF.abs (P.lambda f - lambda_bar)) eps

-- Technical note.
-- Technical note.
-- Technical note.
/- Technical proof note. -/


variable {R : Type*} [COFOC R]

/-!
T-a/T-b for Bishop--Cheng Theorem 3.5.

* T-a chooses a finite exceptional family at every dyadic accuracy
  `COF.halfPow k` and flattens all families into one sequence `Nat → R`.
* T-b, at a point apart from that sequence, takes a positive finite minimum
  of the distances to the level-`k` exceptional points, invokes `lemma_3_4`,
  and records the resulting lower/upper profile witnesses.

The Cauchy/common-limit construction and the final epsilon--delta squeeze are
left to T-c/T-d.  No new dependency is introduced here.
-/

/-- The total variation of a profile between its constant endpoints is
constructively nonnegative. -/
theorem lemma35_gap_nonneg
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab) :
    Nonneg (P.lambda P.oneCode - P.lambda P.zeroCode) := by
  apply nonneg_sub_of_le
  exact P.mono P.zeroCode P.oneCode P.has_zero P.has_one
    (fun x _ _ => by simpa using le_of_lt COFO.one_pos)


/-- A single Archimedean exponent dominating the profile's endpoint gap. -/
noncomputable def lemma35_archExponent
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab) : Nat :=
  (COFO.mul_archimedean
    (P.lambda P.oneCode - P.lambda P.zeroCode)).1


/-- The endpoint gap is weakly bounded by the dyadic integer selected above. -/
theorem lemma35_gap_le_twoPow
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab) :
    Le (P.lambda P.oneCode - P.lambda P.zeroCode)
      (twoPow (lemma35_archExponent P)) := by
  let D : R := P.lambda P.oneCode - P.lambda P.zeroCode
  let m : Nat := (COFO.mul_archimedean D).1
  have hD : Nonneg D := by
    simpa [D] using lemma35_gap_nonneg P
  have hm : Le (D * COF.halfPow m) 1 := by
    have harch : Le (COF.abs D * COF.halfPow m) 1 :=
      (COFO.mul_archimedean D).2
    rw [COFO.abs_of_nonneg hD] at harch
    exact harch
  have htwo : Nonneg (twoPow (R := R) m) := by
    rw [← lemma33_natCast_twoPow m]
    exact lemma33_natCast_nonneg (2 ^ m)
  have hmul := lemma33_mul_le_mul_right hm htwo
  have hleft : (D * COF.halfPow m) * twoPow m = D := by
    calc
      (D * COF.halfPow m) * twoPow m =
          D * (COF.halfPow m * twoPow m) := by ring
      _ = D * 1 := by rw [halfPow_mul_twoPow]
      _ = D := by ring
  have hright : (1 : R) * twoPow m = twoPow m := by ring
  rw [hleft, hright] at hmul
  simpa [D, m, lemma35_archExponent] using hmul


/-- Number of exceptional points used at accuracy `halfPow k`.

The factor `2^k` exactly compensates `halfPow k`; the extra `+1` occurring in
Lemma 3.4 then turns the weak Archimedean bound into a strict budget. -/
noncomputable def lemma35_count
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (k : Nat) : Nat :=
  2 ^ lemma35_archExponent P * 2 ^ k




/-- The main part of `(n(k)+1) * halfPow k` is exactly the fixed dyadic
Archimedean bound. -/
theorem lemma35_count_mul_halfPow
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (k : Nat) :
    ((lemma35_count P k : Nat) : R) * COF.halfPow k =
      twoPow (lemma35_archExponent P) := by
  unfold lemma35_count
  rw [Nat.cast_mul, lemma33_natCast_twoPow, lemma33_natCast_twoPow]
  calc
    ((twoPow (R := R) (lemma35_archExponent P)) * twoPow k) * COF.halfPow k =
        twoPow (lemma35_archExponent P) *
          (COF.halfPow k * twoPow k) := by ring
    _ = twoPow (lemma35_archExponent P) * 1 := by
      rw [halfPow_mul_twoPow]
    _ = twoPow (lemma35_archExponent P) := by ring


/-- Budget required to apply `lemma_3_4` at every dyadic level. -/
theorem lemma35_budget
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (k : Nat) :
    COF.lt (P.lambda P.oneCode - P.lambda P.zeroCode)
      ((((lemma35_count P k + 1 : Nat) : R)) * COF.halfPow k) := by
  have hbase := lemma35_gap_le_twoPow P
  have hcast :
      COF.lt ((lemma35_count P k : Nat) : R)
        (((lemma35_count P k + 1 : Nat) : R)) :=
    lemma33_natCast_lt (by omega)
  have hscaled :
      COF.lt (((lemma35_count P k : Nat) : R) * COF.halfPow k)
        ((((lemma35_count P k + 1 : Nat) : R)) * COF.halfPow k) :=
    lemma33_mul_lt_mul_right hcast (halfPow_pos k)
  rw [lemma35_count_mul_halfPow P k] at hscaled
  exact BishopC.lt_of_le_of_lt hbase hscaled


/-- (C) All data supplied by Lemma 3.4 at one dyadic level. -/
structure Lemma35LevelData
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (k : Nat) where
  points : Fin (lemma35_count P k) → R
  bounds : ∀ i, Le a (points i) ∧ Le (points i) b
  local_small :
    ∀ beta : R, COF.lt 0 beta →
      Σ' gamma : R,
        COF.lt 0 gamma ×'
        (∀ t : R, Le a t → Le t b →
          (∀ i, COF.lt beta (COF.abs (t - points i))) →
          P.p_lt
            (COF.max a (t - gamma))
            (COF.min b (t + gamma))
            (COF.halfPow k))




/-- Canonically chosen level data. -/
noncomputable def lemma35_levelData
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (k : Nat) : Lemma35LevelData P k :=
  let D := lemma_3_4 P (COF.halfPow k) (halfPow_pos k)
    (lemma35_count P k) (lemma35_budget P k)
  { points := D.1
    bounds := D.2.1
    local_small := D.2.2 }


/-- Triangular block size: total slots in Cantor diagonals `d0 .. d0+m-1`. -/
def lemma35_blockSum : Nat → Nat → Nat
  | _, 0 => 0
  | d0, (m + 1) => (d0 + 1) + lemma35_blockSum (d0 + 1) m

theorem lemma35_blockSum_ge (m : Nat) :
    ∀ d0, m ≤ lemma35_blockSum d0 m := by
  induction m with
  | zero => intro d0; exact Nat.zero_le _
  | succ m ih =>
      intro d0
      have h := ih (d0 + 1)
      simp only [lemma35_blockSum]
      omega

/-- Choice-free diagonal decode (fuel-driven, structural) used in place of
`Nat.unpair`, whose `Nat.sqrt` lemma API is `selector-style construction`-risky here. -/
def lemma35_diagDecode : Nat → Nat → Nat → Nat × Nat
  | 0, _, d => (d, 0)
  | (fuel + 1), n, d =>
      if n ≤ d then (d - n, n)
      else lemma35_diagDecode fuel (n - (d + 1)) (d + 1)

theorem lemma35_diagDecode_blockSum (m : Nat) :
    ∀ (fuel d0 r : Nat), r ≤ d0 + m → m < fuel →
      lemma35_diagDecode fuel (lemma35_blockSum d0 m + r) d0 = (d0 + m - r, r) := by
  induction m with
  | zero =>
      intro fuel d0 r hr hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [lemma35_blockSum, lemma35_diagDecode]
      rw [if_pos (show (0 : Nat) + r ≤ d0 by omega)]
      congr 1 <;> omega
  | succ m ih =>
      intro fuel d0 r hr hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [lemma35_blockSum, lemma35_diagDecode]
      rw [if_neg (show ¬ (d0 + 1 + lemma35_blockSum (d0 + 1) m + r ≤ d0) by omega)]
      have hkey :
          d0 + 1 + lemma35_blockSum (d0 + 1) m + r - (d0 + 1)
            = lemma35_blockSum (d0 + 1) m + r := by omega
      rw [hkey, ih f (d0 + 1) r (by omega) (by omega)]
      congr 1 <;> omega

/-- Choice-free Cantor encode. -/
def lemma35_encode (k j : Nat) : Nat := lemma35_blockSum 0 (k + j) + j

/-- Choice-free Cantor decode. -/
def lemma35_unpairCF (q : Nat) : Nat × Nat := lemma35_diagDecode (q + 1) q 0

theorem lemma35_unpairCF_encode (k j : Nat) :
    lemma35_unpairCF (lemma35_encode k j) = (k, j) := by
  unfold lemma35_unpairCF lemma35_encode
  have hge : k + j ≤ lemma35_blockSum 0 (k + j) := lemma35_blockSum_ge (k + j) 0
  rw [lemma35_diagDecode_blockSum (k + j)
      (lemma35_blockSum 0 (k + j) + j + 1) 0 j (by omega) (by omega)]
  congr 1 <;> omega


/-- Flatten all finite exceptional families into a single sequence by the
standard natural pairing function.  Invalid second coordinates are sent to
`a`; every genuine exceptional point has an exact paired index. -/
noncomputable def lemma35_exceptionSeq
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab) :
    Nat → R := fun q =>
  let ij := lemma35_unpairCF q
  if h : ij.2 < lemma35_count P ij.1 then
    (lemma35_levelData P ij.1).points ⟨ij.2, h⟩
  else
    a


/-- Every level point occurs in the flattened exceptional sequence. -/
theorem lemma35_exceptionSeq_pair
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (k : Nat) (j : Fin (lemma35_count P k)) :
    lemma35_exceptionSeq P (lemma35_encode k j.1) =
      (lemma35_levelData P k).points j := by
  unfold lemma35_exceptionSeq
  rw [lemma35_unpairCF_encode, dif_pos j.2]


/-- Finite list of distances from `t` to the level-`k` exceptional points. -/
noncomputable def lemma35_distanceList
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (k : Nat) : List R :=
  List.ofFn (fun j : Fin (lemma35_count P k) =>
    COF.abs (t - (lemma35_levelData P k).points j))


/-- Apartness from the flattened sequence makes every distance in the finite
level list strictly positive. -/
theorem lemma35_distanceList_pos
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) :
    ∀ x, x ∈ lemma35_distanceList P t k → COF.lt 0 x := by
  intro x hx
  have hx' :
      ∃ j : Fin (lemma35_count P k),
        COF.abs (t - (lemma35_levelData P k).points j) = x := by
    unfold lemma35_distanceList at hx
    exact List.mem_ofFn.mp hx
  rcases hx' with ⟨j, rfl⟩
  have h := hT (lemma35_encode k j.1)
  rw [lemma35_exceptionSeq_pair P k j] at h
  exact h


/-- Positive finite minimum of the level distances, with `1` as harmless seed. -/
noncomputable def lemma35_minDistance
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (k : Nat) : R :=
  lemma34_foldMin 1 (lemma35_distanceList P t k)


/-- The finite minimum is positive away from the exceptional sequence. -/
theorem lemma35_minDistance_pos
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) : COF.lt 0 (lemma35_minDistance P t k) := by
  unfold lemma35_minDistance
  exact lemma34_foldMin_pos 1 (lemma35_distanceList P t k)
    COFO.one_pos (lemma35_distanceList_pos P t hT k)


/-- One half of a positive number is strictly smaller than that number. -/
theorem lemma35_half_mul_lt_self {x : R} (hx : COF.lt 0 x) :
    COF.lt (COF.half * x) x := by
  have hhalf : COF.lt 0 (COF.half * x) :=
    COFO.mul_pos COFO.half_pos hx
  have h := lemma33_lt_add_of_pos_right
    (a := COF.half * x) hhalf
  have hsum : COF.half * x + COF.half * x = x := by
    calc
      COF.half * x + COF.half * x =
          (COF.half + COF.half) * x := by ring
      _ = 1 * x := by rw [COF.half_add_half]
      _ = x := by ring
  rwa [hsum] at h


/-- Radius used when applying Lemma 3.4 at one level. -/
noncomputable def lemma35_beta
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (k : Nat) : R :=
  COF.half * lemma35_minDistance P t k


/-- The selected level radius is positive. -/
theorem lemma35_beta_pos
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) : COF.lt 0 (lemma35_beta P t k) := by
  unfold lemma35_beta
  exact COFO.mul_pos COFO.half_pos
    (lemma35_minDistance_pos P t hT k)


/-- The selected radius is strictly below every level distance. -/
theorem lemma35_beta_lt_point
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) (j : Fin (lemma35_count P k)) :
    COF.lt (lemma35_beta P t k)
      (COF.abs (t - (lemma35_levelData P k).points j)) := by
  have hhalf :
      COF.lt (lemma35_beta P t k) (lemma35_minDistance P t k) := by
    unfold lemma35_beta
    exact lemma35_half_mul_lt_self
      (lemma35_minDistance_pos P t hT k)
  have hmem :
      COF.abs (t - (lemma35_levelData P k).points j) ∈
        lemma35_distanceList P t k := by
    apply List.mem_ofFn.mpr
    exact ⟨j, rfl⟩
  have hmin :
      Le (lemma35_minDistance P t k)
        (COF.abs (t - (lemma35_levelData P k).points j)) := by
    unfold lemma35_minDistance
    exact lemma34_foldMin_le_mem 1
      (lemma35_distanceList P t k) hmem
  exact BishopC.lt_of_lt_of_le hhalf hmin


/-- T-b output: the two profile functions witnessing a small jump around `t`
at level `k`.  The collar statements are normalized to the unclipped points
`t + gamma` and `t - gamma`, which is the form needed in the final squeeze. -/
structure Lemma35LocalWitness
    {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab) (t : R) (k : Nat) where
  beta : R
  beta_pos : COF.lt 0 beta
  beta_far : ∀ j : Fin (lemma35_count P k),
    COF.lt beta (COF.abs (t - (lemma35_levelData P k).points j))
  gamma : R
  gamma_pos : COF.lt 0 gamma
  lower : P.Code
  lower_mem : lower ∈ P.F
  upper : P.Code
  upper_mem : upper ∈ P.F
  lower_zero : ∀ x : R, Le a x → Le x b → Le x (t + gamma) →
    lower x = 0
  upper_one : ∀ x : R, Le a x → Le x b → Le (t - gamma) x →
    upper x = 1
  gap_lt : COF.lt (P.lambda upper - P.lambda lower) (COF.halfPow k)




/-- Canonically chosen T-b witness.  The same data can be referenced
transparently by the subsequent T-c/T-d construction. -/
noncomputable def lemma35_localWitness
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) : Lemma35LocalWitness P t k := by
  let beta : R := lemma35_beta P t k
  have hbeta : COF.lt 0 beta := lemma35_beta_pos P t hT k
  have hfar : ∀ j : Fin (lemma35_count P k),
      COF.lt beta
        (COF.abs (t - (lemma35_levelData P k).points j)) :=
    lemma35_beta_lt_point P t hT k
  obtain ⟨gamma, hgamma, hlocal⟩ :=
    (lemma35_levelData P k).local_small beta hbeta
  have hp :
      P.p_lt (COF.max a (t - gamma))
        (COF.min b (t + gamma)) (COF.halfPow k) :=
    hlocal t hat htb hfar
  rcases hp with
    ⟨lower, hlower, upper, hupper, hzero, hone, hgap⟩
  refine {
    beta := beta
    beta_pos := hbeta
    beta_far := hfar
    gamma := gamma
    gamma_pos := hgamma
    lower := lower
    lower_mem := hlower
    upper := upper
    upper_mem := hupper
    lower_zero := ?_
    upper_one := ?_
    gap_lt := hgap
  }
  · intro x hax hxb hxt
    exact hzero x hax hxb (lemma34_le_min hxb hxt)
  · intro x hax hxb htx
    exact hone x hax hxb (cof_max_le hax htx)


/- Technical proof note. -/


/-!
T-c for Bishop--Cheng Theorem 3.5.

T-a/T-b have already produced, at every dyadic level `k`, a profile bracket
`lower_k ≤ upper_k` around the fixed point `t`, with

  `lambda upper_k - lambda lower_k < halfPow k`.

This file proves the cross-level bracket

  `lambda lower_k ≤ lambda upper_m`,

uses it to give an explicit Cauchy modulus for the lower lambda-values, takes
their limit by `COFOC.complete`, and proves that this common limit lies in every
level bracket.  The final epsilon--delta squeeze is deliberately left to T-d.
-/



/-- `halfPow` is weakly antitone in its natural-number exponent. -/
theorem lemma35_halfPow_antitone {k m : Nat} (hkm : k ≤ m) :
    Le (COF.halfPow (R := R) m) (COF.halfPow (R := R) k) :=
  halfPow_antitone hkm


/-- Every element is weakly below its absolute value. -/
theorem lemma35_le_abs_self (x : R) : Le x (COF.abs x) := by
  intro hbad
  rcases COF.lt_cotrans hbad 0 with habsneg | hxpos
  · exact (abs_nonneg x) habsneg
  · have hxnonneg : Nonneg x := le_of_lt hxpos
    rw [COFO.abs_of_nonneg hxnonneg] at hbad
    exact COF.lt_irrefl _ hbad


/-- The negative of every element is weakly below its absolute value. -/
theorem lemma35_neg_le_abs (x : R) : Le (-x) (COF.abs x) := by
  intro hbad
  rcases COF.lt_cotrans hbad 0 with habsneg | hnegpos
  · exact (abs_nonneg x) habsneg
  · have hneg_nonneg : Nonneg (-x) := le_of_lt hnegpos
    have habs : COF.abs x = -x := by
      rw [← COFO.abs_neg x, COFO.abs_of_nonneg hneg_nonneg]
    rw [habs] at hbad
    exact COF.lt_irrefl _ hbad


/-- Two strict one-sided difference bounds give a strict absolute-value bound.
The proof uses only cotransitivity and the constructive sign split for `abs`. -/
theorem lemma35_abs_sub_lt_of_two_sided {x y eps : R}
    (heps : COF.lt 0 eps)
    (hxy : COF.lt (x - y) eps)
    (hyx : COF.lt (y - x) eps) :
    COF.lt (COF.abs (x - y)) eps := by
  rcases COF.lt_cotrans heps (COF.abs (x - y)) with habspos | habslt
  · rcases COFO.lt_or_lt_of_abs_pos habspos with hpos | hneg
    · rw [COFO.abs_of_nonneg (le_of_lt hpos)]
      exact hxy
    · have hrevpos : COF.lt 0 (y - x) := by
        have h := BishopC.neg_pos_of_neg hneg
        convert h using 1 <;> ring
      rw [show x - y = -(y - x) by ring, COFO.abs_neg,
        COFO.abs_of_nonneg (le_of_lt hrevpos)]
      exact hyx
  · exact habslt


/-- Transparent abbreviation for the canonically chosen T-b witnesses. -/
noncomputable def lemma35_witnessSeq
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) : Lemma35LocalWitness P t k :=
  lemma35_localWitness P t hat htb hT k


/-- Lower lambda-value at dyadic level `k`. -/
noncomputable def lemma35_lowerLambda
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) : R :=
  P.lambda (lemma35_witnessSeq P t hat htb hT k).lower


/-- Upper lambda-value at dyadic level `k`. -/
noncomputable def lemma35_upperLambda
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) : R :=
  P.lambda (lemma35_witnessSeq P t hat htb hT k).upper


/-- Cross-level bracket: every lower witness lies below every upper witness
under `lambda`.  The overlap between the two collars is supplied by the
strict positivity of both radii and cotransitivity. -/
theorem lemma35_cross_bracket
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k m : Nat) :
    Le (lemma35_lowerLambda P t hat htb hT k)
      (lemma35_upperLambda P t hat htb hT m) := by
  let Wk : Lemma35LocalWitness P t k :=
    lemma35_witnessSeq P t hat htb hT k
  let Wm : Lemma35LocalWitness P t m :=
    lemma35_witnessSeq P t hat htb hT m
  change Le (P.lambda Wk.lower) (P.lambda Wm.upper)
  apply P.mono Wk.lower Wm.upper Wk.lower_mem Wm.upper_mem
  intro x hax hxb
  have hsum : COF.lt 0 (Wm.gamma + Wk.gamma) := by
    simpa using lemma33_add_lt_add Wm.gamma_pos Wk.gamma_pos
  have hspan : COF.lt (t - Wm.gamma) (t + Wk.gamma) := by
    have h := lemma33_add_lt_add_left (c := t - Wm.gamma) hsum
    convert h using 1 <;> ring
  rcases COF.lt_cotrans hspan x with hleft | hright
  · have hu : Wm.upper x = 1 :=
      Wm.upper_one x hax hxb (le_of_lt hleft)
    rw [hu]
    exact (P.bound Wk.lower Wk.lower_mem x hax hxb).2
  · have hl : Wk.lower x = 0 :=
      Wk.lower_zero x hax hxb (le_of_lt hright)
    rw [hl]
    exact (P.bound Wm.upper Wm.upper_mem x hax hxb).1


/-- A lower lambda-value at level `m` exceeds that at level `n` by less
than the level-`n` bracket width. -/
theorem lemma35_lower_sub_lt_halfPow_right
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (m n : Nat) :
    COF.lt
      (lemma35_lowerLambda P t hat htb hT m -
        lemma35_lowerLambda P t hat htb hT n)
      (COF.halfPow n) := by
  have hcross := lemma35_cross_bracket P t hat htb hT m n
  have hsub :
      Le
        (lemma35_lowerLambda P t hat htb hT m -
          lemma35_lowerLambda P t hat htb hT n)
        (lemma35_upperLambda P t hat htb hT n -
          lemma35_lowerLambda P t hat htb hT n) :=
    lemma33_sub_le_sub_right hcross
  have hgap :
      COF.lt
        (lemma35_upperLambda P t hat htb hT n -
          lemma35_lowerLambda P t hat htb hT n)
        (COF.halfPow n) := by
    simpa [lemma35_lowerLambda, lemma35_upperLambda,
      lemma35_witnessSeq] using
      (lemma35_witnessSeq P t hat htb hT n).gap_lt
  exact BishopC.lt_of_le_of_lt hsub hgap


/-- The lower lambda-values form a Cauchy sequence with the identity modulus. -/
noncomputable def lemma35_lowerLambda_isCauchy
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q))) :
    IsCauchy (lemma35_lowerLambda P t hat htb hT) := by
  refine {
    cmod := fun k => k
    ccond := ?_
  }
  intro k m n hkm hkn
  have hmn :
      COF.lt
        (lemma35_lowerLambda P t hat htb hT m -
          lemma35_lowerLambda P t hat htb hT n)
        (COF.halfPow k) :=
    BishopC.lt_of_lt_of_le
      (lemma35_lower_sub_lt_halfPow_right P t hat htb hT m n)
      (lemma35_halfPow_antitone hkn)
  have hnm :
      COF.lt
        (lemma35_lowerLambda P t hat htb hT n -
          lemma35_lowerLambda P t hat htb hT m)
        (COF.halfPow k) :=
    BishopC.lt_of_lt_of_le
      (lemma35_lower_sub_lt_halfPow_right P t hat htb hT n m)
      (lemma35_halfPow_antitone hkm)
  exact lemma35_abs_sub_lt_of_two_sided (halfPow_pos k) hmn hnm


/-- Completeness supplies the candidate `lambdaBar(t)`. -/
noncomputable def lemma35_lowerLimit
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q))) :
    HasLim (lemma35_lowerLambda P t hat htb hT) :=
  COFOC.complete (lemma35_lowerLambda_isCauchy P t hat htb hT)


/-- The common limiting value used in Theorem 3.5. -/
noncomputable def lemma35_lambdaBar
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q))) : R :=
  (lemma35_lowerLimit P t hat htb hT).val


/-- Every lower lambda-value lies weakly below the completed limit. -/
theorem lemma35_lowerLambda_le_lambdaBar
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) :
    Le (lemma35_lowerLambda P t hat htb hT k)
      (lemma35_lambdaBar P t hat htb hT) := by
  let L : Nat → R := lemma35_lowerLambda P t hat htb hT
  let U : Nat → R := lemma35_upperLambda P t hat htb hT
  let H : HasLim (lemma35_lowerLambda P t hat htb hT) :=
    lemma35_lowerLimit P t hat htb hT
  change Le (L k) H.val
  intro hbad
  have hd : COF.lt 0 (L k - H.val) :=
    lemma33_sub_pos_of_lt hbad
  have hhalfD : COF.lt 0 (COF.half * (L k - H.val)) :=
    COFO.mul_pos COFO.half_pos hd
  let w := COFO.archimedean_pos (COF.half * (L k - H.val)) hhalfD
  let m : Nat := Nat.max w.val (H.tends.mod w.val)
  have hwm : w.val ≤ m := Nat.le_max_left _ _
  have hmod : H.tends.mod w.val ≤ m := Nat.le_max_right _ _
  have hclose :
      COF.lt (COF.abs (L m - H.val)) (COF.halfPow w.val) :=
    H.tends.close w.val m hmod
  have hLmbar : COF.lt (L m - H.val) (COF.halfPow w.val) :=
    BishopC.lt_of_le_of_lt (lemma35_le_abs_self (L m - H.val)) hclose
  have hkU : Le (L k) (U m) := by
    dsimp [L, U]
    exact lemma35_cross_bracket P t hat htb hT k m
  have hgapm : COF.lt (U m - L m) (COF.halfPow m) := by
    dsimp [L, U]
    simpa [lemma35_lowerLambda, lemma35_upperLambda,
      lemma35_witnessSeq] using
      (lemma35_witnessSeq P t hat htb hT m).gap_lt
  have hgapw : COF.lt (U m - L m) (COF.halfPow w.val) :=
    BishopC.lt_of_lt_of_le hgapm (lemma35_halfPow_antitone hwm)
  have hadd := lemma33_add_lt_add hgapw hLmbar
  have hUmb :
      COF.lt (U m - H.val)
        (COF.halfPow w.val + COF.halfPow w.val) := by
    convert hadd using 1 <;> ring
  have hsub : Le (L k - H.val) (U m - H.val) :=
    lemma33_sub_le_sub_right hkU
  have hbound :
      COF.lt (L k - H.val)
        (COF.halfPow w.val + COF.halfPow w.val) :=
    BishopC.lt_of_le_of_lt hsub hUmb
  have htwoRaw := lemma33_add_lt_add w.property w.property
  have hhalf :
      COF.half * (L k - H.val) + COF.half * (L k - H.val) =
        L k - H.val := by
    calc
      COF.half * (L k - H.val) + COF.half * (L k - H.val) =
          (COF.half + COF.half) * (L k - H.val) := by ring
      _ = 1 * (L k - H.val) := by rw [COF.half_add_half]
      _ = L k - H.val := by ring
  rw [hhalf] at htwoRaw
  have hloop :
      COF.lt
        (COF.halfPow w.val + COF.halfPow w.val)
        (COF.halfPow w.val + COF.halfPow w.val) :=
    COFO.lt_trans htwoRaw hbound
  exact COF.lt_irrefl _ hloop


/-- The completed limit lies weakly below every upper lambda-value. -/
theorem lemma35_lambdaBar_le_upperLambda
    {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ q : Nat,
      COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P q)))
    (k : Nat) :
    Le (lemma35_lambdaBar P t hat htb hT)
      (lemma35_upperLambda P t hat htb hT k) := by
  let L : Nat → R := lemma35_lowerLambda P t hat htb hT
  let U : Nat → R := lemma35_upperLambda P t hat htb hT
  let H : HasLim (lemma35_lowerLambda P t hat htb hT) :=
    lemma35_lowerLimit P t hat htb hT
  change Le H.val (U k)
  intro hbad
  have hd : COF.lt 0 (H.val - U k) :=
    lemma33_sub_pos_of_lt hbad
  let w := COFO.archimedean_pos (H.val - U k) hd
  let m : Nat := H.tends.mod w.val
  have hclose :
      COF.lt (COF.abs (L m - H.val)) (COF.halfPow w.val) :=
    H.tends.close w.val m (Nat.le_refl m)
  have hbarLmLe : Le (H.val - L m) (COF.abs (L m - H.val)) := by
    have h := lemma35_neg_le_abs (L m - H.val)
    convert h using 1 <;> ring
  have hbarLm : COF.lt (H.val - L m) (COF.halfPow w.val) :=
    BishopC.lt_of_le_of_lt hbarLmLe hclose
  have hmU : Le (L m) (U k) := by
    dsimp [L, U]
    exact lemma35_cross_bracket P t hat htb hT m k
  have hsub : Le (H.val - U k) (H.val - L m) :=
    lemma33_sub_le_sub_left hmU
  have hbound : COF.lt (H.val - U k) (COF.halfPow w.val) :=
    BishopC.lt_of_le_of_lt hsub hbarLm
  have hloop : COF.lt (COF.halfPow w.val) (COF.halfPow w.val) :=
    COFO.lt_trans w.property hbound
  exact COF.lt_irrefl _ hloop








/-- Technical lemma used in the public import closure. -/
noncomputable def thm_3_5_smooth_at_seq_spec {a b : R} {hab : COF.lt a b}
    (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ n, COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P n))) :
    ∀ eps : R, COF.lt 0 eps →
      Σ' delta : R, COF.lt 0 delta ×'
        (∀ f ∈ P.F, (∀ x, Le (t + delta) x → f x = 1) →
                   (∀ x, Le x (t - delta) → f x = 0) →
                   COF.lt (COF.abs (P.lambda f -
                     lemma35_lambdaBar P t hat htb hT)) eps) := by
  intro eps heps
  obtain ⟨k, hk⟩ := COFO.archimedean_pos eps heps
  let W : Lemma35LocalWitness P t k := lemma35_witnessSeq P t hat htb hT k
  have hLL : lemma35_lowerLambda P t hat htb hT k = P.lambda W.lower := rfl
  have hUL : lemma35_upperLambda P t hat htb hT k = P.lambda W.upper := rfl
  have hδpos : COF.lt 0 (COF.half * W.gamma) :=
    COFO.mul_pos COFO.half_pos W.gamma_pos
  refine ⟨COF.half * W.gamma, hδpos, ?_⟩
  intro f hf hf1 hf0
  have hδγ : COF.lt (COF.half * W.gamma) W.gamma :=
    lemma35_half_mul_lt_self W.gamma_pos
  have htpδ : COF.lt (t + COF.half * W.gamma) (t + W.gamma) :=
    COF.lt_add_left t hδγ
  have htmγδ : COF.lt (t - W.gamma) (t - COF.half * W.gamma) := by
    have h := COF.lt_add_left (t - W.gamma - COF.half * W.gamma) hδγ
    convert h using 1 <;> ring
  have hlower_le_f : Le (P.lambda W.lower) (P.lambda f) := by
    apply P.mono W.lower f W.lower_mem hf
    intro x hax hxb
    rcases COF.lt_cotrans htpδ x with hxr | hxl
    · have hf1x : f x = 1 := hf1 x (le_of_lt hxr)
      rw [hf1x]
      exact (P.bound W.lower W.lower_mem x hax hxb).2
    · have hl0 : W.lower x = 0 := W.lower_zero x hax hxb (le_of_lt hxl)
      rw [hl0]
      exact (P.bound f hf x hax hxb).1
  have hf_le_upper : Le (P.lambda f) (P.lambda W.upper) := by
    apply P.mono f W.upper hf W.upper_mem
    intro x hax hxb
    rcases COF.lt_cotrans htmγδ x with hxr | hxl
    · have hu1 : W.upper x = 1 := W.upper_one x hax hxb (le_of_lt hxr)
      rw [hu1]
      exact (P.bound f hf x hax hxb).2
    · have hf0x : f x = 0 := hf0 x (le_of_lt hxl)
      rw [hf0x]
      exact (P.bound W.upper W.upper_mem x hax hxb).1
  have hlower_le_bar :
      Le (P.lambda W.lower) (lemma35_lambdaBar P t hat htb hT) :=
    hLL ▸ lemma35_lowerLambda_le_lambdaBar P t hat htb hT k
  have hbar_le_upper :
      Le (lemma35_lambdaBar P t hat htb hT) (P.lambda W.upper) :=
    hUL ▸ lemma35_lambdaBar_le_upperLambda P t hat htb hT k
  have hgapε : COF.lt (P.lambda W.upper - P.lambda W.lower) eps :=
    COFO.lt_trans W.gap_lt hk
  have hxy : COF.lt (P.lambda f - lemma35_lambdaBar P t hat htb hT) eps :=
    lt_of_le_of_lt (lemma33_sub_le_sub hf_le_upper hlower_le_bar) hgapε
  have hyx : COF.lt (lemma35_lambdaBar P t hat htb hT - P.lambda f) eps :=
    lt_of_le_of_lt (lemma33_sub_le_sub hbar_le_upper hlower_le_f) hgapε
  exact lemma35_abs_sub_lt_of_two_sided heps hxy hyx

theorem thm_3_5_smooth_at_seq {a b : R} {hab : COF.lt a b} (P : Profile a b hab)
    (t : R) (hat : Le a t) (htb : Le t b)
    (hT : ∀ n, COF.lt 0 (COF.abs (t - lemma35_exceptionSeq P n))) :
    P.IsSmoothAt t :=
  ⟨lemma35_lambdaBar P t hat htb hT,
    fun eps heps =>
      let d := thm_3_5_smooth_at_seq_spec P t hat htb hT eps heps
      ⟨d.1, d.2.1, d.2.2⟩⟩


/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
noncomputable def thm_3_6_ramp_comp {S : IntSpaceRC X R} (h : IntegrableRep S)
    (u v : R) (hu : ¬ COF.lt u 0) (_huv : COF.lt u v) : IntegrableRep S :=
  -- min{ (v−u)⁻¹ · (h − min{h,u}) , 1 }
  (IntegrableRep.smul (COFO.inv (v - u)) (h.sub (h.cutConstVal u hu))).cutConstVal 1
    (fun h1 => COF.lt_irrefl (0 : R) (COFO.lt_trans COFO.one_pos h1))


/-- Technical lemma used in the public import closure. -/
noncomputable def thm_3_6_rampFn (u v : R) : R → R :=
  fun y => COF.max (COF.min ((COFO.inv (v - u)) * (y - u)) 1) 0

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_sub_pos_of_lt {u v : R} (huv : COF.lt u v) :
    COF.lt 0 (v - u) := by
  have h := COF.lt_add_left (-u) huv
  convert h using 1 <;> ring

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_sub_le_sub_right {x y u : R} (hxy : Le x y) :
    Le (x - u) (y - u) := by
  intro hbad
  apply hxy
  have h := COF.lt_add_left u hbad
  convert h using 1 <;> ring

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_sub_nonpos_of_le {x u : R} (hxu : Le x u) :
    Le (x - u) 0 := by
  intro hpos
  apply hxu
  have h := COF.lt_add_left u hpos
  convert h using 1 <;> ring

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_mul_max_zero (c z : R) (hc : Nonneg c) :
    c * COF.max z 0 = COF.max (c * z) 0 := by
  rw [COF.max_halfsum, COF.max_halfsum, sub_zero, sub_zero,
      COFO.abs_mul, COFO.abs_of_nonneg hc]
  ring

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_clamp_swap (z : R) :
    COF.min (COF.max z 0) 1 = COF.max (COF.min z 1) 0 := by
  rcases COF.lt_cotrans_data COFO.one_pos z with hz | hz1
  · -- Technical note.
    have hmaxz : COF.max z 0 = z := cof_max_eq_left_of_le (le_of_lt hz)
    have hmin_nn : Le 0 (COF.min z 1) :=
      lemma34_le_min (le_of_lt hz) (le_of_lt COFO.one_pos)
    rw [hmaxz, cof_max_eq_left_of_le hmin_nn]
  · -- Technical note.
    have hminz : COF.min z 1 = z := cof_min_eq_left_of_le (le_of_lt hz1)
    have hmax_le1 : Le (COF.max z 0) 1 :=
      cof_max_le (le_of_lt hz1) (le_of_lt COFO.one_pos)
    rw [hminz, cof_min_eq_left_of_le hmax_le1]

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_value_formula (u v y : R) (huv : COF.lt u v) :
    COF.min
        ((COFO.inv (v - u)) * (y - COF.min y u)) 1 =
      thm_3_6_rampFn u v y := by
  have hvu : COF.lt 0 (v - u) := thm36A1_sub_pos_of_lt huv
  have hinv : Nonneg (COFO.inv (v - u)) :=
    le_of_lt (COFO.inv_pos hvu)
  unfold thm_3_6_rampFn
  rw [sub_min_eq_max_sub]
  rw [thm36A1_mul_max_zero (COFO.inv (v - u)) (y - u) hinv]
  exact thm36A1_clamp_swap _


/-- Domain transport through the representative implementing the ramp. -/
theorem thm36A1_ramp_comp_memAt {S : IntSpaceRC X R}
    (h : IntegrableRep S) (u v : R) (hu : Nonneg u) (huv : COF.lt u v)
    {x : X} (hdom : h.MemAt x) :
    (thm_3_6_ramp_comp h u v hu huv).MemAt x := by
  have hone : Nonneg (1 : R) := le_of_lt COFO.one_pos
  let hcutDom : (h.cutConstVal u hu).MemAt x :=
    h.mem_cutConstVal_dom u hu hdom
  let hsubDom : (h.sub (h.cutConstVal u hu)).MemAt x :=
    IntegrableRep.add_memAt hdom (IntegrableRep.neg_memAt hcutDom)
  let hsmulDom :
      (IntegrableRep.smul (COFO.inv (v - u))
        (h.sub (h.cutConstVal u hu))).MemAt x :=
    IntegrableRep.smul_memAt hsubDom
  simpa [thm_3_6_ramp_comp] using
    ((IntegrableRep.smul (COFO.inv (v - u))
      (h.sub (h.cutConstVal u hu))).mem_cutConstVal_dom 1 hone hsmulDom)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A1_ramp_comp_value_witness {S : IntSpaceRC X R}
    (h : IntegrableRep S) (u v : R) (hu : Nonneg u) (huv : COF.lt u v)
    (x : X) (hdom : h.MemAt x)
    (hx : RSeq.SeriesSum (fun n => h.valueAt x hdom n)) :
    { hr : RSeq.SeriesSum
        (fun n => (thm_3_6_ramp_comp h u v hu huv).valueAt x
          (thm36A1_ramp_comp_memAt h u v hu huv hdom) n) //
      hr.sum = thm_3_6_rampFn u v hx.sum } := by
  let hcutDom : (h.cutConstVal u hu).MemAt x :=
    h.mem_cutConstVal_dom u hu hdom
  let hcut := IntegrableRep.cutConstVal_signed_value h u hu x hdom hx
  let hnegDom : (h.cutConstVal u hu).neg.MemAt x :=
    IntegrableRep.neg_memAt hcutDom
  let hneg : RSeq.SeriesSum
      (fun n => (h.cutConstVal u hu).neg.valueAt x hnegDom n) :=
    neg_seriesSum_value hcutDom hcut.val
  let hsubDom : (h.sub (h.cutConstVal u hu)).MemAt x :=
    IntegrableRep.add_memAt hdom hnegDom
  let hsub : RSeq.SeriesSum
      (fun n => (h.sub (h.cutConstVal u hu)).valueAt x hsubDom n) :=
    add_seriesSum_value hdom hnegDom hx hneg
  have hsub_sum : hsub.sum = hx.sum - COF.min hx.sum u := by
    change hx.sum + (-hcut.val.sum) = hx.sum - COF.min hx.sum u
    rw [hcut.property]; ring
  let hsmulDom :
      (IntegrableRep.smul (COFO.inv (v - u))
        (h.sub (h.cutConstVal u hu))).MemAt x :=
    IntegrableRep.smul_memAt hsubDom
  let hsmul : RSeq.SeriesSum
      (fun n =>
        (IntegrableRep.smul (COFO.inv (v - u))
          (h.sub (h.cutConstVal u hu))).valueAt x hsmulDom n) :=
    smul_seriesSum_value (COFO.inv (v - u)) hsubDom hsub
  have hsmul_sum :
      hsmul.sum = (COFO.inv (v - u)) * (hx.sum - COF.min hx.sum u) := by
    change (COFO.inv (v - u)) * hsub.sum = _
    rw [hsub_sum]
  have hone : Nonneg (1 : R) := le_of_lt COFO.one_pos
  let hout := IntegrableRep.cutConstVal_signed_value
    (IntegrableRep.smul (COFO.inv (v - u))
      (h.sub (h.cutConstVal u hu))) 1 hone x hsmulDom hsmul
  let hrout : RSeq.SeriesSum
      (fun n => (thm_3_6_ramp_comp h u v hu huv).valueAt x
        (thm36A1_ramp_comp_memAt h u v hu huv hdom) n) := by
    simpa [thm_3_6_ramp_comp] using hout.val
  refine ⟨hrout, ?_⟩
  calc
    hrout.sum = hout.val.sum := by rfl
    _ = COF.min hsmul.sum 1 := hout.property
    _ = COF.min
        ((COFO.inv (v - u)) * (hx.sum - COF.min hx.sum u)) 1 := by
          rw [hsmul_sum]
    _ = thm_3_6_rampFn u v hx.sum :=
      thm36A1_ramp_value_formula u v hx.sum huv

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_comp_value {S : IntSpaceRC X R}
    (h : IntegrableRep S) (u v : R) (hu : Nonneg u) (huv : COF.lt u v)
    (x : X) (hdom : h.MemAt x)
    (hx : RSeq.SeriesSum (fun n => h.valueAt x hdom n))
    (hrdom : (thm_3_6_ramp_comp h u v hu huv).MemAt x)
    (hr : RSeq.SeriesSum
      (fun n => (thm_3_6_ramp_comp h u v hu huv).valueAt x hrdom n)) :
    hr.sum = thm_3_6_rampFn u v hx.sum := by
  let hw := thm36A1_ramp_comp_value_witness h u v hu huv x hdom hx
  calc
    hr.sum = hw.val.sum := seriesSum_unique hr hw.val
    _ = thm_3_6_rampFn u v hx.sum := hw.property

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_bound (u v y : R) :
    Nonneg (thm_3_6_rampFn u v y) ∧
      Le (thm_3_6_rampFn u v y) 1 := by
  constructor
  · exact COFO.max_zero_nonneg _
  · exact cof_max_le (cof_min_le_right _ 1) (le_of_lt COFO.one_pos)

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_zero (u v y : R) (huv : COF.lt u v)
    (hyu : Le y u) : thm_3_6_rampFn u v y = 0 := by
  let c : R := COFO.inv (v - u)
  have hvu : COF.lt 0 (v - u) := thm36A1_sub_pos_of_lt huv
  have hc : Nonneg c := le_of_lt (COFO.inv_pos hvu)
  have hyu0 : Le (y - u) 0 := thm36A1_sub_nonpos_of_le hyu
  have hraw0 : Le (c * (y - u)) 0 := by
    have h := mul_le_mul_left hyu0 hc
    simpa using h
  have hraw1 : Le (c * (y - u)) 1 := by
    intro h1raw
    have hraw1lt : COF.lt (c * (y - u)) 1 :=
      BishopC.lt_of_le_of_lt hraw0 COFO.one_pos
    exact COF.lt_irrefl (1 : R) (COFO.lt_trans h1raw hraw1lt)
  change COF.max (COF.min (c * (y - u)) 1) 0 = 0
  rw [cof_min_eq_left_of_le hraw1, cof_max_eq_right_of_le hraw0]

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_one (u v y : R) (huv : COF.lt u v)
    (hvy : Le v y) : thm_3_6_rampFn u v y = 1 := by
  let c : R := COFO.inv (v - u)
  have hvu : COF.lt 0 (v - u) := thm36A1_sub_pos_of_lt huv
  have hc : Nonneg c := le_of_lt (COFO.inv_pos hvu)
  have hsub : Le (v - u) (y - u) := thm36A1_sub_le_sub_right hvy
  have hmul : Le (c * (v - u)) (c * (y - u)) :=
    mul_le_mul_left hsub hc
  have hcancel : c * (v - u) = 1 := by
    dsimp [c]
    calc
      (COFO.inv (v - u)) * (v - u) =
          (v - u) * COFO.inv (v - u) := by ring
      _ = 1 := COFO.mul_inv_cancel hvu
  rw [hcancel] at hmul
  change COF.max (COF.min (c * (y - u)) 1) 0 = 1
  rw [cof_min_eq_right_of_le hmul,
      cof_max_eq_left_of_le (le_of_lt COFO.one_pos)]

/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem cof_mul_lt_mul_left {a b c : R} (hab : COF.lt a b) (hc : COF.lt 0 c) :
    COF.lt (c * a) (c * b) := by
  have hba : COF.lt 0 (b - a) := lemma33_sub_pos_of_lt hab
  have hpos : COF.lt 0 (c * (b - a)) := COFO.mul_pos hc hba
  have h := COF.lt_add_left (c * a) hpos
  have e1 : c * a + 0 = c * a := by ring
  have e2 : c * a + c * (b - a) = c * b := by ring
  rw [e1, e2] at h
  exact h

/-- Technical lemma used in the public import closure. -/
theorem cof_min_one_lt_one_imp {W : R} (h : COF.lt (COF.min W 1) 1) :
    COF.lt W 1 := by
  rcases COF.lt_cotrans h W with hl | hr
  · have h1W : Le 1 W := by
      intro hW1
      have hmW : COF.min W 1 = W := cof_min_eq_left_of_le (le_of_lt hW1)
      rw [hmW] at hl
      exact COF.lt_irrefl W hl
    have hmin1 : COF.min W 1 = 1 := cof_min_eq_right_of_le h1W
    rw [hmin1] at h
    exact (COF.lt_irrefl 1 h).elim
  · exact hr

/-- Technical lemma used in the public import closure. -/
theorem cof_le_max_left (A : R) : Le A (COF.max A 0) := by
  intro h
  have hself := COF.max_add_min_eq_self A
  have hlt : COF.lt (COF.max A 0) (COF.max A 0 + COF.min A 0) := by
    rw [hself]; exact h
  have h2 := COF.lt_add_left (-(COF.max A 0)) hlt
  have e1 : -(COF.max A 0) + COF.max A 0 = 0 := by ring
  have e2 : -(COF.max A 0) + (COF.max A 0 + COF.min A 0) = COF.min A 0 := by ring
  rw [e1, e2] at h2
  exact cof_min_le_right A 0 h2

/-- `max A 0 < c → A < c`(strict max)。 -/
theorem cof_lt_of_max_zero_lt {A c : R} (h : COF.lt (COF.max A 0) c) :
    COF.lt A c :=
  lt_of_le_of_lt (cof_le_max_left A) h

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_lt_one_imp (u v y : R) (huv : COF.lt u v)
    (h : COF.lt (thm_3_6_rampFn u v y) 1) : COF.lt y v := by
  have hvu : COF.lt 0 (v - u) := thm36A1_sub_pos_of_lt huv
  unfold thm_3_6_rampFn at h
  have hA : COF.lt (COF.min (COFO.inv (v - u) * (y - u)) 1) 1 :=
    cof_lt_of_max_zero_lt h
  have hZ : COF.lt (COFO.inv (v - u) * (y - u)) 1 :=
    cof_min_one_lt_one_imp hA
  have hmul : COF.lt ((v - u) * (COFO.inv (v - u) * (y - u))) ((v - u) * 1) :=
    cof_mul_lt_mul_left hZ hvu
  have hcancel : (v - u) * (COFO.inv (v - u) * (y - u)) = y - u := by
    rw [← mul_assoc, COFO.mul_inv_cancel hvu, one_mul]
  have hrhs : (v - u) * 1 = v - u := mul_one _
  rw [hcancel, hrhs] at hmul
  have hadd := COF.lt_add_left u hmul
  have e1 : u + (y - u) = y := by ring
  have e2 : u + (v - u) = v := by ring
  rw [e1, e2] at hadd
  exact hadd


/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_pos_nonneg {x : R} (hx : COF.lt 0 x) : Nonneg x :=
  le_of_lt hx

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_u_nonneg {a u : R} (ha : COF.lt 0 a) (hau : Le a u) :
    Nonneg u :=
  le_trans (le_of_lt ha) hau

/-- Technical lemma used in the public import closure. -/
structure Thm36A2Endpoints (a b : R) where
  alpha : R
  beta : R
  gamma : R
  delta : R
  zero_lt_alpha : COF.lt 0 alpha
  alpha_lt_beta : COF.lt alpha beta
  beta_lt_a : COF.lt beta a
  b_lt_gamma : COF.lt b gamma
  gamma_lt_delta : COF.lt gamma delta

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_gamma_nonneg {a b : R} (hab : COF.lt a b)
    (ha : COF.lt 0 a) (E : Thm36A2Endpoints a b) : Nonneg E.gamma := by
  exact le_trans (le_of_lt ha)
    (le_trans (le_of_lt hab) (le_of_lt E.b_lt_gamma))

/-- Technical lemma used in the public import closure. -/
def thm36A2_endpoints (a b : R) (_hab : COF.lt a b) (ha : COF.lt 0 a) :
    Thm36A2Endpoints a b := by
  let alpha : R := (a * COF.half) * COF.half
  let beta : R := a * COF.half
  let gamma : R := b + 1
  let delta : R := (b + 1) + 1

  have hbeta_pos : COF.lt 0 beta := by
    dsimp [beta]
    exact COFO.mul_pos ha COFO.half_pos

  have halpha_pos : COF.lt 0 alpha := by
    dsimp [alpha]
    exact COFO.mul_pos (COFO.mul_pos ha COFO.half_pos) COFO.half_pos

  have halpha_double : alpha + alpha = beta := by
    dsimp [alpha, beta]
    calc
      (a * COF.half) * COF.half + (a * COF.half) * COF.half
          = (a * COF.half) * (COF.half + COF.half) := by ring
      _ = (a * COF.half) * 1 := by rw [COF.half_add_half]
      _ = a * COF.half := by ring

  have hbeta_double : beta + beta = a := by
    dsimp [beta]
    calc
      a * COF.half + a * COF.half = a * (COF.half + COF.half) := by ring
      _ = a * 1 := by rw [COF.half_add_half]
      _ = a := by ring

  have halpha_beta : COF.lt alpha beta := by
    have h := COF.lt_add_left alpha halpha_pos
    have h' : COF.lt alpha (alpha + alpha) := by simpa using h
    rw [halpha_double] at h'
    exact h'

  have hbeta_a : COF.lt beta a := by
    have h := COF.lt_add_left beta hbeta_pos
    have h' : COF.lt beta (beta + beta) := by simpa using h
    rw [hbeta_double] at h'
    exact h'

  have hb_gamma : COF.lt b gamma := by
    dsimp [gamma]
    simpa using (COF.lt_add_left b COFO.one_pos)

  have hgamma_delta : COF.lt gamma delta := by
    dsimp [gamma, delta]
    simpa using (COF.lt_add_left (b + 1) COFO.one_pos)

  exact
    { alpha := alpha
      beta := beta
      gamma := gamma
      delta := delta
      zero_lt_alpha := halpha_pos
      alpha_lt_beta := halpha_beta
      beta_lt_a := hbeta_a
      b_lt_gamma := hb_gamma
      gamma_lt_delta := hgamma_delta }

/-- Technical lemma used in the public import closure. -/
inductive Thm36A2Code (a b : R) where
  | one
  | zero
  | ramp (u v : R) (hau : Le a u) (huv : COF.lt u v) (hvb : Le v b)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeFn {a b : R} : Thm36A2Code a b → (R → R)
  | .one => fun _ => 1
  | .zero => fun _ => 0
  | .ramp u v _ _ _ => thm_3_6_rampFn u v

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeU {a b : R} (E : Thm36A2Endpoints a b) :
    Thm36A2Code a b → R
  | .one => E.alpha
  | .zero => E.gamma
  | .ramp u _ _ _ _ => u

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeV {a b : R} (E : Thm36A2Endpoints a b) :
    Thm36A2Code a b → R
  | .one => E.beta
  | .zero => E.delta
  | .ramp _ v _ _ _ => v

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_codeU_nonneg {a b : R} (hab : COF.lt a b)
    (ha : COF.lt 0 a) (E : Thm36A2Endpoints a b) :
    ∀ c : Thm36A2Code a b, Nonneg (thm36A2_codeU E c)
  | .one => thm36A2_pos_nonneg E.zero_lt_alpha
  | .zero => thm36A2_gamma_nonneg hab ha E
  | .ramp u _ hau _ _ => thm36A2_u_nonneg ha hau

/-- Technical lemma used in the public import closure. -/
theorem thm36A2_codeUV_lt {a b : R} (E : Thm36A2Endpoints a b) :
    ∀ c : Thm36A2Code a b,
      COF.lt (thm36A2_codeU E c) (thm36A2_codeV E c)
  | .one => E.alpha_lt_beta
  | .zero => E.gamma_lt_delta
  | .ramp _ _ _ huv _ => huv

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeRepFn {a b : R} (E : Thm36A2Endpoints a b)
    (c : Thm36A2Code a b) : R → R :=
  thm_3_6_rampFn (thm36A2_codeU E c) (thm36A2_codeV E c)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36A2_codeRep {S : IntSpaceRC X R} (h : IntegrableRep S)
    {a b : R} (hab : COF.lt a b) (ha : COF.lt 0 a)
    (E : Thm36A2Endpoints a b) (c : Thm36A2Code a b) : IntegrableRep S :=
  thm_3_6_ramp_comp h (thm36A2_codeU E c) (thm36A2_codeV E c)
    (thm36A2_codeU_nonneg hab ha E c) (thm36A2_codeUV_lt E c)





/-- Technical lemma used in the public import closure. -/
theorem cof_pos_of_max_zero_pos {A : R} (h : COF.lt 0 (COF.max A 0)) :
    COF.lt 0 A := by
  have habs : COF.lt 0 (COF.abs A) :=
    lt_of_lt_of_le h (COFO.max_le_abs A)
  rcases COFO.lt_or_lt_of_abs_pos habs with hpos | hneg
  · exact hpos
  · have hmax0 : COF.max A 0 = 0 := cof_max_eq_right_of_le (le_of_lt hneg)
    rw [hmax0] at h
    exact (COF.lt_irrefl 0 h).elim

/-- Technical lemma used in the public import closure. -/
theorem thm36A1_ramp_pos_imp (u v y : R) (huv : COF.lt u v)
    (hpos : COF.lt 0 (thm_3_6_rampFn u v y)) : COF.lt u y := by
  have hvu : COF.lt 0 (v - u) := thm36A1_sub_pos_of_lt huv
  unfold thm_3_6_rampFn at hpos
  have hA : COF.lt 0 (COF.min (COFO.inv (v - u) * (y - u)) 1) :=
    cof_pos_of_max_zero_pos hpos
  have hZ : COF.lt 0 (COFO.inv (v - u) * (y - u)) :=
    lt_of_lt_of_le hA (cof_min_le_left _ _)
  have hmul : COF.lt ((v - u) * 0)
      ((v - u) * (COFO.inv (v - u) * (y - u))) :=
    cof_mul_lt_mul_left hZ hvu
  have hcancel : (v - u) * (COFO.inv (v - u) * (y - u)) = y - u := by
    rw [← mul_assoc, COFO.mul_inv_cancel hvu, one_mul]
  have hzero : (v - u) * (0 : R) = 0 := by ring
  rw [hcancel, hzero] at hmul
  have hadd := COF.lt_add_left u hmul
  have e1 : u + 0 = u := by ring
  have e2 : u + (y - u) = y := by ring
  rw [e1, e2] at hadd
  exact hadd


/-- If the right ramp reaches `1` no later than the left ramp can become
positive, the two ramps are globally ordered. -/
theorem thm36A2_ramp_le_global_of_right_le_left
    {u v p q : R}
    (huv : COF.lt u v) (hpq : COF.lt p q) (hqu : Le q u) :
    ∀ y : R,
      Le (thm_3_6_rampFn u v y) (thm_3_6_rampFn p q y) := by
  intro y hbad
  have hpos : COF.lt 0 (thm_3_6_rampFn u v y) :=
    BishopC.lt_of_le_of_lt (thm36A1_ramp_bound p q y).1 hbad
  have hlt_one : COF.lt (thm_3_6_rampFn p q y) 1 :=
    BishopC.lt_of_lt_of_le hbad (thm36A1_ramp_bound u v y).2
  have huy : COF.lt u y := thm36A1_ramp_pos_imp u v y huv hpos
  have hyq : COF.lt y q :=
    thm36A1_ramp_lt_one_imp p q y hpq hlt_one
  exact hqu (COFO.lt_trans huy hyq)


/-! Technical auxiliary material for the public import closure. -/


/-- `[a,b]`-order of internal ramps extends globally without deciding the
location of `y`. -/
theorem thm36A2_ramp_le_global_of_interval {a b u v p q : R}
    (hau : Le a u) (huv : COF.lt u v) (_hvb : Le v b)
    (_hap : Le a p) (hpq : COF.lt p q) (hqb : Le q b)
    (hfg : ∀ x : R, Le a x → Le x b →
      Le (thm_3_6_rampFn u v x) (thm_3_6_rampFn p q x)) :
    ∀ y : R,
      Le (thm_3_6_rampFn u v y) (thm_3_6_rampFn p q y) := by
  intro y hbad
  have hpos : COF.lt 0 (thm_3_6_rampFn u v y) :=
    BishopC.lt_of_le_of_lt (thm36A1_ramp_bound p q y).1 hbad
  have hlt_one : COF.lt (thm_3_6_rampFn p q y) 1 :=
    BishopC.lt_of_lt_of_le hbad (thm36A1_ramp_bound u v y).2
  have huy : COF.lt u y := thm36A1_ramp_pos_imp u v y huv hpos
  have hyq : COF.lt y q :=
    thm36A1_ramp_lt_one_imp p q y hpq hlt_one
  have hax : Le a y := le_trans hau (le_of_lt huy)
  have hyb : Le y b := le_trans (le_of_lt hyq) hqb
  exact (hfg y hax hyb) hbad


/-- `codeFn` order on `[a,b]` implies global order of the representative
ramps.  All code pairs are treated without a decidable split on a real comparison. -/
theorem thm36A2_codeRepFn_le_global {a b : R} (hab : COF.lt a b)
    (E : Thm36A2Endpoints a b) (c d : Thm36A2Code a b)
    (hcd : ∀ x : R, Le a x → Le x b →
      Le (thm36A2_codeFn c x) (thm36A2_codeFn d x)) :
    ∀ y : R,
      Le (thm36A2_codeRepFn E c y) (thm36A2_codeRepFn E d y) := by
  intro y
  cases c with
  | one =>
      cases d with
      | one =>
          exact le_refl _
      | zero =>
          have h10 : Le (1 : R) 0 := by
            simpa [thm36A2_codeFn] using
              hcd a (le_refl a) (le_of_lt hab)
          exact False.elim (h10 COFO.one_pos)
      | ramp p q hap hpq hqb =>
          have hpb : Le p b := le_trans (le_of_lt hpq) hqb
          have h10 : Le (1 : R) (thm_3_6_rampFn p q p) := by
            simpa [thm36A2_codeFn] using hcd p hap hpb
          rw [thm36A1_ramp_zero p q p hpq (le_refl p)] at h10
          exact False.elim (h10 COFO.one_pos)
  | zero =>
      cases d with
      | one =>
          change Le (thm_3_6_rampFn E.gamma E.delta y)
            (thm_3_6_rampFn E.alpha E.beta y)
          apply thm36A2_ramp_le_global_of_right_le_left
            E.gamma_lt_delta E.alpha_lt_beta
          exact le_trans (le_of_lt E.beta_lt_a)
            (le_trans (le_of_lt hab) (le_of_lt E.b_lt_gamma))
      | zero =>
          exact le_refl _
      | ramp p q _hap hpq hqb =>
          change Le (thm_3_6_rampFn E.gamma E.delta y)
            (thm_3_6_rampFn p q y)
          apply thm36A2_ramp_le_global_of_right_le_left
            E.gamma_lt_delta hpq
          exact le_trans hqb (le_of_lt E.b_lt_gamma)
  | ramp u v hau huv hvb =>
      cases d with
      | one =>
          change Le (thm_3_6_rampFn u v y)
            (thm_3_6_rampFn E.alpha E.beta y)
          apply thm36A2_ramp_le_global_of_right_le_left
            huv E.alpha_lt_beta
          exact le_trans (le_of_lt E.beta_lt_a) hau
      | zero =>
          have hav : Le a v := le_trans hau (le_of_lt huv)
          have h10 : Le (thm_3_6_rampFn u v v) 0 := by
            simpa [thm36A2_codeFn] using hcd v hav hvb
          rw [thm36A1_ramp_one u v v huv (le_refl v)] at h10
          exact False.elim (h10 COFO.one_pos)
      | ramp p q hap hpq hqb =>
          apply thm36A2_ramp_le_global_of_interval
            hau huv hvb hap hpq hqb
          intro x hax hxb
          simpa [thm36A2_codeFn] using hcd x hax hxb


/-- Code order implies integral order.  The absolute-sum witness inside
`h.domain` is eliminated only while proving a proposition. -/
theorem thm36A2_codeRep_integral_mono {S : IntSpaceRC X R}
    (h : IntegrableRep S) {a b : R} (hab : COF.lt a b)
    (ha : COF.lt 0 a) (E : Thm36A2Endpoints a b)
    (c d : Thm36A2Code a b)
    (hcd : ∀ x : R, Le a x → Le x b →
      Le (thm36A2_codeFn c x) (thm36A2_codeFn d x)) :
    Le (thm36A2_codeRep h hab ha E c).integral
       (thm36A2_codeRep h hab ha E d).integral := by
  refine prop_1_11 (IntegrableRep.domain_isFull h)
    (thm36A2_codeRep h hab ha E c)
    (thm36A2_codeRep h hab ha E d) ?_
  intro x hx hrcDom hrdDom hr hd
  obtain ⟨hdom, ⟨hxabs⟩⟩ := hx
  let hxsum : RSeq.SeriesSum (fun n => h.valueAt x hdom n) :=
    seriesSum_of_abs hxabs
  have hcval : hr.sum = thm36A2_codeRepFn E c hxsum.sum := by
    simpa [thm36A2_codeRep, thm36A2_codeRepFn] using
      (thm36A1_ramp_comp_value h
        (thm36A2_codeU E c) (thm36A2_codeV E c)
        (thm36A2_codeU_nonneg hab ha E c)
        (thm36A2_codeUV_lt E c) x hdom hxsum hrcDom hr)
  have hdval : hd.sum = thm36A2_codeRepFn E d hxsum.sum := by
    simpa [thm36A2_codeRep, thm36A2_codeRepFn] using
      (thm36A1_ramp_comp_value h
        (thm36A2_codeU E d) (thm36A2_codeV E d)
        (thm36A2_codeU_nonneg hab ha E d)
        (thm36A2_codeUV_lt E d) x hdom hxsum hrdDom hd)
  rw [hcval, hdval]
  exact thm36A2_codeRepFn_le_global hab E c d hcd hxsum.sum


/-- The admissible family is now a set of tags; all generated codes are
admissible. -/
def thm36A2_profileF {a b : R} : Set (Thm36A2Code a b) := Set.univ


/-- Constant-zero tag belongs to the coded family. -/
theorem thm36A2_zero_mem {a b : R} :
    (Thm36A2Code.zero : Thm36A2Code a b) ∈
      thm36A2_profileF (a := a) (b := b) := by
  exact Set.mem_univ _


/-- Constant-one tag belongs to the coded family. -/
theorem thm36A2_one_mem {a b : R} :
    (Thm36A2Code.one : Thm36A2Code a b) ∈
      thm36A2_profileF (a := a) (b := b) := by
  exact Set.mem_univ _


/-- Every internal-ramp tag belongs to the coded family. -/
theorem thm36A2_ramp_mem {a b u v : R} (hau : Le a u)
    (huv : COF.lt u v) (hvb : Le v b) :
    Thm36A2Code.ramp u v hau huv hvb ∈
      thm36A2_profileF (a := a) (b := b) := by
  exact Set.mem_univ _


/-- The functional is evaluated directly on a tag. -/
noncomputable def thm36A2_profileLambda {S : IntSpaceRC X R}
    (h : IntegrableRep S) {a b : R} (hab : COF.lt a b)
    (ha : COF.lt 0 a) (E : Thm36A2Endpoints a b)
    (c : Thm36A2Code a b) : R :=
  (thm36A2_codeRep h hab ha E c).integral


/-- Monotonicity of the coded functional. -/
theorem thm36A2_profileLambda_mono {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (E : Thm36A2Endpoints a b)
    (c d : Thm36A2Code a b)
    (_hc : c ∈ thm36A2_profileF (a := a) (b := b))
    (_hd : d ∈ thm36A2_profileF (a := a) (b := b))
    (hcd : ∀ x : R, Le a x → Le x b →
      Le (thm36A2_codeFn c x) (thm36A2_codeFn d x)) :
    Le (thm36A2_profileLambda h hab ha E c)
       (thm36A2_profileLambda h hab ha E d) := by
  exact thm36A2_codeRep_integral_mono h hab ha E c d hcd


/-- T36-A2, coded and free of representative selection. -/
noncomputable def thm36A2_profile {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) : Profile a b hab := by
  let E : Thm36A2Endpoints a b := thm36A2_endpoints a b hab ha
  refine
    { Code := Thm36A2Code a b
      embed := thm36A2_codeFn
      F := thm36A2_profileF
      bound := ?_
      zeroCode := .zero
      has_zero := thm36A2_zero_mem
      embed_zero := rfl
      oneCode := .one
      has_one := thm36A2_one_mem
      embed_one := rfl
      separating := ?_
      lambda := thm36A2_profileLambda h hab ha E
      mono := ?_ }
  · intro c _hc x _hax _hxb
    cases c with
    | one =>
        exact ⟨le_of_lt COFO.one_pos, le_refl (1 : R)⟩
    | zero =>
        exact ⟨le_refl (0 : R), le_of_lt COFO.one_pos⟩
    | ramp u v _ _ _ =>
        exact thm36A1_ramp_bound u v x
  · intro u v hau huv hvb
    refine ⟨.ramp u v hau huv hvb, thm36A2_ramp_mem hau huv hvb, ?_, ?_⟩
    · intro t _hat htu
      exact thm36A1_ramp_zero u v t huv htu
    · intro t hvt _htb
      exact thm36A1_ramp_one u v t huv hvt
  · intro c d hc hd hcd
    exact thm36A2_profileLambda_mono h a b hab ha E c d hc hd hcd


/-! Technical auxiliary material for the public import closure. -/

/-- One quarter of an element, expressed using only the constructive half. -/
def thm36B1_quarter (x : R) : R :=
  COF.half * (COF.half * x)

/-- A quarter of a positive element is positive. -/
theorem thm36B1_quarter_pos {x : R} (hx : COF.lt 0 x) :
    COF.lt 0 (thm36B1_quarter x) := by
  unfold thm36B1_quarter
  exact COFO.mul_pos COFO.half_pos (COFO.mul_pos COFO.half_pos hx)

/-- Two quarters make one half. -/
theorem thm36B1_quarter_add_self (x : R) :
    thm36B1_quarter x + thm36B1_quarter x = COF.half * x := by
  unfold thm36B1_quarter
  calc
    COF.half * (COF.half * x) + COF.half * (COF.half * x) =
        (COF.half + COF.half) * (COF.half * x) := by ring
    _ = 1 * (COF.half * x) := by rw [COF.half_add_half]
    _ = COF.half * x := by ring

/-- Four quarters recover the original element. -/
theorem thm36B1_four_quarters (x : R) :
    (thm36B1_quarter x + thm36B1_quarter x) +
        (thm36B1_quarter x + thm36B1_quarter x) = x := by
  rw [thm36B1_quarter_add_self]
  calc
    COF.half * x + COF.half * x = (COF.half + COF.half) * x := by ring
    _ = 1 * x := by rw [COF.half_add_half]
    _ = x := by ring

/-- Two quarters of a positive element are positive. -/
theorem thm36B1_two_quarters_pos {x : R} (hx : COF.lt 0 x) :
    COF.lt 0 (thm36B1_quarter x + thm36B1_quarter x) := by
  have hq := thm36B1_quarter_pos hx
  have h := lemma33_add_lt_add hq hq
  simpa using h

/-- A quarter is weakly below a half for a positive input. -/
theorem thm36B1_quarter_le_half {x : R} (hx : COF.lt 0 x) :
    Le (thm36B1_quarter x) (COF.half * x) := by
  have hhalfX : Nonneg (COF.half * x) :=
    COFO.mul_nonneg (le_of_lt COFO.half_pos) (le_of_lt hx)
  have h := lemma33_mul_le_mul_right
    (lemma34_half_le_one (R := R)) hhalfX
  simpa [thm36B1_quarter] using h

/-- The left quarter-cut of `[l,r]`. -/
def thm36B1_leftCut (l r : R) : R :=
  l + thm36B1_quarter (r - l)

/-- The right quarter-cut of `[l,r]`. -/
def thm36B1_rightCut (l r : R) : R :=
  r - thm36B1_quarter (r - l)

/-- The left quarter-cut is strictly inside a proper interval. -/
theorem thm36B1_left_lt_leftCut {l r : R} (hlr : COF.lt l r) :
    COF.lt l (thm36B1_leftCut l r) := by
  unfold thm36B1_leftCut
  exact lemma33_lt_add_of_pos_right
    (thm36B1_quarter_pos (lemma33_sub_pos_of_lt hlr))

/-- The right quarter-cut is strictly inside a proper interval. -/
theorem thm36B1_rightCut_lt_right {l r : R} (hlr : COF.lt l r) :
    COF.lt (thm36B1_rightCut l r) r := by
  let q : R := thm36B1_quarter (r - l)
  have hq : COF.lt 0 q := by
    dsimp [q]
    exact thm36B1_quarter_pos (lemma33_sub_pos_of_lt hlr)
  have h := lemma33_lt_add_of_pos_right (a := r - q) hq
  unfold thm36B1_rightCut
  dsimp [q] at h
  convert h using 1 <;> ring

/-- The two quarter-cuts leave a nonempty middle gap. -/
theorem thm36B1_leftCut_lt_rightCut {l r : R} (hlr : COF.lt l r) :
    COF.lt (thm36B1_leftCut l r) (thm36B1_rightCut l r) := by
  let q : R := thm36B1_quarter (r - l)
  have htwo : COF.lt 0 (q + q) := by
    dsimp [q]
    exact thm36B1_two_quarters_pos (lemma33_sub_pos_of_lt hlr)
  have h := lemma33_lt_add_of_pos_right
    (a := thm36B1_leftCut l r) htwo
  have hfour : (q + q) + (q + q) = r - l := by
    dsimp [q]
    exact thm36B1_four_quarters (r - l)
  have heq : thm36B1_leftCut l r + (q + q) =
      thm36B1_rightCut l r := by
    dsimp [thm36B1_leftCut, thm36B1_rightCut]
    change l + q + (q + q) = r - q
    calc
      l + q + (q + q) = l + ((q + q) + (q + q)) - q := by ring
      _ = l + (r - l) - q := by rw [hfour]
      _ = r - q := by ring
  rw [heq] at h
  exact h

/-- Width of the left retained quarter. -/
theorem thm36B1_leftCut_sub_left (l r : R) :
    thm36B1_leftCut l r - l = thm36B1_quarter (r - l) := by
  unfold thm36B1_leftCut
  ring

/-- Width of the right retained quarter. -/
theorem thm36B1_right_sub_rightCut (l r : R) :
    r - thm36B1_rightCut l r = thm36B1_quarter (r - l) := by
  unfold thm36B1_rightCut
  ring

/-- Width of the initial middle interval. -/
theorem thm36B1_rightCut_sub_leftCut (l r : R) :
    thm36B1_rightCut l r - thm36B1_leftCut l r =
      thm36B1_quarter (r - l) + thm36B1_quarter (r - l) := by
  let q : R := thm36B1_quarter (r - l)
  have hfour : (q + q) + (q + q) = r - l := by
    dsimp [q]
    exact thm36B1_four_quarters (r - l)
  unfold thm36B1_leftCut thm36B1_rightCut
  change (r - q) - (l + q) = q + q
  calc
    (r - q) - (l + q) = (r - l) - (q + q) := by ring
    _ = ((q + q) + (q + q)) - (q + q) := by rw [hfour]
    _ = q + q := by ring

/-- Multiplying the level-`n` width scale by one half gives the successor
scale.  This is derived from `halfPow_succ_add`, without unfolding `halfPow`. -/
theorem thm36B1_half_widthScale_eq_succ (a b : R) (n : Nat) :
    COF.half * lemma34_widthScale a b n =
      lemma34_widthScale a b (n + 1) := by
  unfold lemma34_widthScale
  have hsum :
      COF.halfPow (n + 1) * COF.max 1 (b - a) +
          COF.halfPow (n + 1) * COF.max 1 (b - a) =
        COF.halfPow n * COF.max 1 (b - a) := by
    calc
      COF.halfPow (n + 1) * COF.max 1 (b - a) +
          COF.halfPow (n + 1) * COF.max 1 (b - a) =
          (COF.halfPow (n + 1) + COF.halfPow (n + 1)) *
            COF.max 1 (b - a) := by ring
      _ = COF.halfPow n * COF.max 1 (b - a) := by
        rw [halfPow_succ_add]
  calc
    COF.half * (COF.halfPow n * COF.max 1 (b - a)) =
        COF.half *
          (COF.halfPow (n + 1) * COF.max 1 (b - a) +
            COF.halfPow (n + 1) * COF.max 1 (b - a)) := by
              rw [hsum]
    _ = (COF.half + COF.half) *
          (COF.halfPow (n + 1) * COF.max 1 (b - a)) := by ring
    _ = 1 * (COF.halfPow (n + 1) * COF.max 1 (b - a)) := by
          rw [COF.half_add_half]
    _ = COF.halfPow (n + 1) * COF.max 1 (b - a) := by ring

/-- A quarter of a proper interval whose width is bounded at level `n` is
bounded by the level-`n+1` dyadic scale. -/
theorem thm36B1_quarter_le_next_widthScale
    {a b l r : R} {n : Nat} (hlr : COF.lt l r)
    (hwidth : Le (r - l) (lemma34_widthScale a b n)) :
    Le (thm36B1_quarter (r - l))
      (lemma34_widthScale a b (n + 1)) := by
  have hqhalf :
      Le (thm36B1_quarter (r - l)) (COF.half * (r - l)) :=
    thm36B1_quarter_le_half (lemma33_sub_pos_of_lt hlr)
  have hhalf :
      Le (COF.half * (r - l))
        (COF.half * lemma34_widthScale a b n) :=
    mul_le_mul_left hwidth (le_of_lt COFO.half_pos)
  rw [thm36B1_half_widthScale_eq_succ] at hhalf
  exact le_trans hqhalf hhalf

/-- State of the nested interval construction after avoiding `s 0,...,s(n-1)`. -/
structure Thm36B1Interval (s : Nat → R) (a b : R) (n : Nat) where
  left : R
  right : R
  proper : COF.lt left right
  a_lt_left : COF.lt a left
  right_lt_b : COF.lt right b
  width : Le (right - left) (lemma34_widthScale a b n)
  avoided : ∀ j : Nat, j < n →
    COF.lt (s j) left ∨ COF.lt right (s j)

/-- The initial interval is the middle half of `(a,b)`, hence is strictly
inside the ambient interval and has the level-zero width bound. -/
noncomputable def thm36B1_interval_base
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    Thm36B1Interval s a b 0 := by
  have hd : COF.lt 0 (b - a) := lemma33_sub_pos_of_lt hab
  have hdnn : Nonneg (b - a) := le_of_lt hd
  have hhalfLe : Le (COF.half * (b - a)) (b - a) := by
    have h := lemma33_mul_le_mul_right
      (lemma34_half_le_one (R := R)) hdnn
    rw [one_mul] at h
    exact h
  have hwidth :
      Le (thm36B1_rightCut a b - thm36B1_leftCut a b)
        (lemma34_widthScale a b 0) := by
    rw [thm36B1_rightCut_sub_leftCut,
      thm36B1_quarter_add_self]
    have hmax : Le (b - a) (COF.max 1 (b - a)) :=
      lemma33_le_max_right (1 : R) (b - a)
    have h := le_trans hhalfLe hmax
    have hws0 : lemma34_widthScale a b 0 = COF.max 1 (b - a) := by
      unfold lemma34_widthScale
      rw [show (COF.halfPow (0 : Nat) : R) = 1 from rfl]; ring
    rw [hws0]; exact h
  exact {
    left := thm36B1_leftCut a b
    right := thm36B1_rightCut a b
    proper := thm36B1_leftCut_lt_rightCut hab
    a_lt_left := thm36B1_left_lt_leftCut hab
    right_lt_b := thm36B1_rightCut_lt_right hab
    width := hwidth
    avoided := by
      intro j hj
      exact absurd hj (Nat.not_lt_zero j)
  }

/-- Previously avoided points remain avoided after passing to a nested
subinterval. -/
theorem thm36B1_preserve_avoided
    {s : Nat → R} {a b : R} {n : Nat}
    (I : Thm36B1Interval s a b n) {l r : R}
    (hl : Le I.left l) (hr : Le r I.right)
    {j : Nat} (hj : j < n) :
    COF.lt (s j) l ∨ COF.lt r (s j) := by
  rcases I.avoided j hj with hleft | hright
  · exact Or.inl (lt_of_lt_of_le hleft hl)
  · exact Or.inr (lt_of_le_of_lt hr hright)

/-- One diagonal step.  The returned subtype records positionwise nesting. -/
noncomputable def thm36B1_interval_step
    (s : Nat → R) {a b : R} (n : Nat)
    (I : Thm36B1Interval s a b n) :
    {J : Thm36B1Interval s a b (n + 1) //
      Le I.left J.left ∧ Le J.right I.right} := by
  let ql : R := thm36B1_leftCut I.left I.right
  let qr : R := thm36B1_rightCut I.left I.right
  have hLql : COF.lt I.left ql := by
    dsimp [ql]
    exact thm36B1_left_lt_leftCut I.proper
  have hqlqr : COF.lt ql qr := by
    dsimp [ql, qr]
    exact thm36B1_leftCut_lt_rightCut I.proper
  have hqrR : COF.lt qr I.right := by
    dsimp [qr]
    exact thm36B1_rightCut_lt_right I.proper
  have hLqr : COF.lt I.left qr := COFO.lt_trans hLql hqlqr
  have hqBound :
      Le (thm36B1_quarter (I.right - I.left))
        (lemma34_widthScale a b (n + 1)) :=
    thm36B1_quarter_le_next_widthScale I.proper I.width
  have hwidthLeft :
      Le (ql - I.left) (lemma34_widthScale a b (n + 1)) := by
    dsimp [ql]
    rw [thm36B1_leftCut_sub_left]
    exact hqBound
  have hwidthRight :
      Le (I.right - qr) (lemma34_widthScale a b (n + 1)) := by
    dsimp [qr]
    rw [thm36B1_right_sub_rightCut]
    exact hqBound
  rcases COF.lt_cotrans_data hqlqr (s n) with hleft | hright
  · let J : Thm36B1Interval s a b (n + 1) := {
      left := I.left
      right := ql
      proper := hLql
      a_lt_left := I.a_lt_left
      right_lt_b := COFO.lt_trans hqlqr (COFO.lt_trans hqrR I.right_lt_b)
      width := hwidthLeft
      avoided := by
        intro j hj
        by_cases hjn : j < n
        · exact thm36B1_preserve_avoided I
            (le_refl I.left) (le_of_lt (COFO.lt_trans hqlqr hqrR)) hjn
        · have hjeq : j = n := by omega
          subst j
          exact Or.inr hleft
    }
    refine ⟨J, ?_⟩
    exact ⟨le_refl I.left, le_of_lt (COFO.lt_trans hqlqr hqrR)⟩
  · let J : Thm36B1Interval s a b (n + 1) := {
      left := qr
      right := I.right
      proper := hqrR
      a_lt_left := COFO.lt_trans I.a_lt_left hLqr
      right_lt_b := I.right_lt_b
      width := hwidthRight
      avoided := by
        intro j hj
        by_cases hjn : j < n
        · exact thm36B1_preserve_avoided I
            (le_of_lt hLqr) (le_refl I.right) hjn
        · have hjeq : j = n := by omega
          subst j
          exact Or.inl hright
    }
    refine ⟨J, ?_⟩
    exact ⟨le_of_lt hLqr, le_refl I.right⟩

/-- Canonical nested interval sequence. -/
noncomputable def thm36B1_intervalSeq
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    (n : Nat) → Thm36B1Interval s a b n
  | 0 => thm36B1_interval_base s hab
  | n + 1 =>
      (thm36B1_interval_step s n
        (thm36B1_intervalSeq s hab n)).val

/-- Consecutive canonical intervals are nested. -/
theorem thm36B1_intervalSeq_step_nested
    (s : Nat → R) {a b : R} (hab : COF.lt a b) (n : Nat) :
    Le (thm36B1_intervalSeq s hab n).left
        (thm36B1_intervalSeq s hab (n + 1)).left ∧
      Le (thm36B1_intervalSeq s hab (n + 1)).right
        (thm36B1_intervalSeq s hab n).right := by
  change
    Le (thm36B1_intervalSeq s hab n).left
        ((thm36B1_interval_step s n
          (thm36B1_intervalSeq s hab n)).val).left ∧
      Le ((thm36B1_interval_step s n
          (thm36B1_intervalSeq s hab n)).val).right
        (thm36B1_intervalSeq s hab n).right
  exact (thm36B1_interval_step s n
    (thm36B1_intervalSeq s hab n)).property

/-- Nesting between arbitrary levels. -/
theorem thm36B1_intervalSeq_nested
    (s : Nat → R) {a b : R} (hab : COF.lt a b)
    {p q : Nat} (hpq : p ≤ q) :
    Le (thm36B1_intervalSeq s hab p).left
        (thm36B1_intervalSeq s hab q).left ∧
      Le (thm36B1_intervalSeq s hab q).right
        (thm36B1_intervalSeq s hab p).right := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  clear hpq
  induction d with
  | zero =>
      exact ⟨le_refl _, le_refl _⟩
  | succ d ih =>
      have hs := thm36B1_intervalSeq_step_nested s hab (p + d)
      constructor
      · have h := le_trans ih.1 hs.1
        simpa [Nat.add_assoc] using h
      · have h := le_trans hs.2 ih.2
        simpa [Nat.add_assoc] using h

/-- Left endpoint sequence. -/
noncomputable def thm36B1_leftSeq
    (s : Nat → R) {a b : R} (hab : COF.lt a b) (n : Nat) : R :=
  (thm36B1_intervalSeq s hab n).left

/-- Right endpoint sequence. -/
noncomputable def thm36B1_rightSeq
    (s : Nat → R) {a b : R} (hab : COF.lt a b) (n : Nat) : R :=
  (thm36B1_intervalSeq s hab n).right

/-- Left endpoints increase. -/
theorem thm36B1_leftSeq_mono
    (s : Nat → R) {a b : R} (hab : COF.lt a b)
    {p q : Nat} (hpq : p ≤ q) :
    Le (thm36B1_leftSeq s hab p) (thm36B1_leftSeq s hab q) := by
  simpa [thm36B1_leftSeq] using
    (thm36B1_intervalSeq_nested s hab hpq).1

/-- Right endpoints decrease. -/
theorem thm36B1_rightSeq_antitone
    (s : Nat → R) {a b : R} (hab : COF.lt a b)
    {p q : Nat} (hpq : p ≤ q) :
    Le (thm36B1_rightSeq s hab q) (thm36B1_rightSeq s hab p) := by
  simpa [thm36B1_rightSeq] using
    (thm36B1_intervalSeq_nested s hab hpq).2

/-- The two left endpoints at levels beyond `M` are at distance at most the
width of the level-`M` interval. -/
theorem thm36B1_leftSeq_abs_le_width
    (s : Nat → R) {a b : R} (hab : COF.lt a b)
    (M m q : Nat) (hMm : M ≤ m) (hMq : M ≤ q) :
    Le (COF.abs
        (thm36B1_leftSeq s hab m - thm36B1_leftSeq s hab q))
      (lemma34_widthScale a b M) := by
  by_cases hmq : m ≤ q
  · have hMmNest := thm36B1_intervalSeq_nested s hab hMm
    have hmqNest := thm36B1_intervalSeq_nested s hab hmq
    have hproperQ := (thm36B1_intervalSeq s hab q).proper
    have hLqRq : Le (thm36B1_leftSeq s hab q)
        (thm36B1_rightSeq s hab q) := by
      exact le_of_lt hproperQ
    have hLqRM : Le (thm36B1_leftSeq s hab q)
        (thm36B1_rightSeq s hab M) := by
      exact le_trans hLqRq (le_trans
        (by simpa [thm36B1_rightSeq] using hmqNest.2)
        (by simpa [thm36B1_rightSeq] using hMmNest.2))
    have hLMLm : Le (thm36B1_leftSeq s hab M)
        (thm36B1_leftSeq s hab m) := by
      simpa [thm36B1_leftSeq] using hMmNest.1
    have hdiff : Le
        (thm36B1_leftSeq s hab q - thm36B1_leftSeq s hab m)
        (thm36B1_rightSeq s hab M - thm36B1_leftSeq s hab M) :=
      lemma33_sub_le_sub hLqRM hLMLm
    have hLmLq : Le (thm36B1_leftSeq s hab m)
        (thm36B1_leftSeq s hab q) := by
      simpa [thm36B1_leftSeq] using hmqNest.1
    have hnonneg : Nonneg
        (thm36B1_leftSeq s hab q - thm36B1_leftSeq s hab m) :=
      nonneg_sub_of_le hLmLq
    have habs : COF.abs
        (thm36B1_leftSeq s hab m - thm36B1_leftSeq s hab q) =
        thm36B1_leftSeq s hab q - thm36B1_leftSeq s hab m := by
      rw [show thm36B1_leftSeq s hab m - thm36B1_leftSeq s hab q =
          -(thm36B1_leftSeq s hab q - thm36B1_leftSeq s hab m) by ring,
        COFO.abs_neg, COFO.abs_of_nonneg hnonneg]
    rw [habs]
    exact le_trans hdiff (by
      simpa [thm36B1_leftSeq, thm36B1_rightSeq] using
        (thm36B1_intervalSeq s hab M).width)
  · have hqm : q ≤ m := by omega
    have hMqNest := thm36B1_intervalSeq_nested s hab hMq
    have hqmNest := thm36B1_intervalSeq_nested s hab hqm
    have hproperM := (thm36B1_intervalSeq s hab m).proper
    have hLmRm : Le (thm36B1_leftSeq s hab m)
        (thm36B1_rightSeq s hab m) := by
      exact le_of_lt hproperM
    have hLmRM : Le (thm36B1_leftSeq s hab m)
        (thm36B1_rightSeq s hab M) := by
      exact le_trans hLmRm (le_trans
        (by simpa [thm36B1_rightSeq] using hqmNest.2)
        (by simpa [thm36B1_rightSeq] using hMqNest.2))
    have hLMLq : Le (thm36B1_leftSeq s hab M)
        (thm36B1_leftSeq s hab q) := by
      simpa [thm36B1_leftSeq] using hMqNest.1
    have hdiff : Le
        (thm36B1_leftSeq s hab m - thm36B1_leftSeq s hab q)
        (thm36B1_rightSeq s hab M - thm36B1_leftSeq s hab M) :=
      lemma33_sub_le_sub hLmRM hLMLq
    have hLqLm : Le (thm36B1_leftSeq s hab q)
        (thm36B1_leftSeq s hab m) := by
      simpa [thm36B1_leftSeq] using hqmNest.1
    have hnonneg : Nonneg
        (thm36B1_leftSeq s hab m - thm36B1_leftSeq s hab q) :=
      nonneg_sub_of_le hLqLm
    rw [COFO.abs_of_nonneg hnonneg]
    exact le_trans hdiff (by
      simpa [thm36B1_leftSeq, thm36B1_rightSeq] using
        (thm36B1_intervalSeq s hab M).width)

/-- Explicit Cauchy modulus for the left endpoints. -/
noncomputable def thm36B1_leftSeq_isCauchy
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    IsCauchy (thm36B1_leftSeq s hab) := by
  refine {
    cmod := fun k =>
      (lemma34_widthScale_eventually_lt a b (COF.halfPow k)
        (halfPow_pos k)).val
    ccond := ?_
  }
  intro k m q hm hq
  have habs := thm36B1_leftSeq_abs_le_width s hab
    ((lemma34_widthScale_eventually_lt a b (COF.halfPow k)
      (halfPow_pos k)).val) m q hm hq
  exact BishopC.lt_of_le_of_lt habs
    (lemma34_widthScale_eventually_lt a b (COF.halfPow k)
      (halfPow_pos k)).property

/-- Limit of the canonical left endpoint sequence. -/
noncomputable def thm36B1_leftLimit
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    HasLim (thm36B1_leftSeq s hab) :=
  COFOC.complete (thm36B1_leftSeq_isCauchy s hab)

/-- Every left endpoint lies weakly below the limit. -/
theorem thm36B1_leftSeq_le_limit
    (s : Nat → R) {a b : R} (hab : COF.lt a b) (k : Nat) :
    Le (thm36B1_leftSeq s hab k) (thm36B1_leftLimit s hab).val := by
  let L : Nat → R := thm36B1_leftSeq s hab
  let H : HasLim L := thm36B1_leftLimit s hab
  change Le (L k) H.val
  intro hbad
  have hgap : COF.lt 0 (L k - H.val) := lemma33_sub_pos_of_lt hbad
  let w := COFO.archimedean_pos (L k - H.val) hgap
  let m : Nat := Nat.max k (H.tends.mod w.val)
  have hkm : k ≤ m := Nat.le_max_left _ _
  have hmod : H.tends.mod w.val ≤ m := Nat.le_max_right _ _
  have hmono : Le (L k) (L m) := by
    dsimp [L]
    exact thm36B1_leftSeq_mono s hab hkm
  have htLm : Le H.val (L m) := le_trans (le_of_lt hbad) hmono
  have hclose : COF.lt (COF.abs (L m - H.val)) (COF.halfPow w.val) :=
    H.tends.close w.val m hmod
  have hnonneg : Nonneg (L m - H.val) := nonneg_sub_of_le htLm
  rw [COFO.abs_of_nonneg hnonneg] at hclose
  have hsub : Le (L k - H.val) (L m - H.val) :=
    lemma33_sub_le_sub_right hmono
  have hloop : COF.lt (COF.halfPow w.val) (COF.halfPow w.val) :=
    COFO.lt_trans (BishopC.lt_of_lt_of_le w.property hsub) hclose
  exact COF.lt_irrefl _ hloop

/-- The limit lies weakly below every right endpoint. -/
theorem thm36B1_limit_le_rightSeq
    (s : Nat → R) {a b : R} (hab : COF.lt a b) (k : Nat) :
    Le (thm36B1_leftLimit s hab).val (thm36B1_rightSeq s hab k) := by
  let L : Nat → R := thm36B1_leftSeq s hab
  let Rr : Nat → R := thm36B1_rightSeq s hab
  let H : HasLim L := thm36B1_leftLimit s hab
  change Le H.val (Rr k)
  intro hbad
  have hgap : COF.lt 0 (H.val - Rr k) := lemma33_sub_pos_of_lt hbad
  let w := COFO.archimedean_pos (H.val - Rr k) hgap
  let m : Nat := Nat.max k (H.tends.mod w.val)
  have hkm : k ≤ m := Nat.le_max_left _ _
  have hmod : H.tends.mod w.val ≤ m := Nat.le_max_right _ _
  have hRmk : Le (Rr m) (Rr k) := by
    dsimp [Rr]
    exact thm36B1_rightSeq_antitone s hab hkm
  have hproperM := (thm36B1_intervalSeq s hab m).proper
  have hLmRm : Le (L m) (Rr m) := by
    exact le_of_lt hproperM
  have hLmRk : Le (L m) (Rr k) := le_trans hLmRm hRmk
  have hLmt : Le (L m) H.val := le_trans hLmRk (le_of_lt hbad)
  have hclose : COF.lt (COF.abs (L m - H.val)) (COF.halfPow w.val) :=
    H.tends.close w.val m hmod
  have hnonneg : Nonneg (H.val - L m) := nonneg_sub_of_le hLmt
  rw [show L m - H.val = -(H.val - L m) by ring,
    COFO.abs_neg, COFO.abs_of_nonneg hnonneg] at hclose
  have hsub : Le (H.val - Rr k) (H.val - L m) :=
    lemma33_sub_le_sub_left hLmRk
  have hloop : COF.lt (COF.halfPow w.val) (COF.halfPow w.val) :=
    COFO.lt_trans (BishopC.lt_of_lt_of_le w.property hsub) hclose
  exact COF.lt_irrefl _ hloop

/-- The completed point remains in every nested interval. -/
theorem thm36B1_limit_in_interval
    (s : Nat → R) {a b : R} (hab : COF.lt a b) (k : Nat) :
    Le (thm36B1_leftSeq s hab k) (thm36B1_leftLimit s hab).val ∧
      Le (thm36B1_leftLimit s hab).val (thm36B1_rightSeq s hab k) :=
  ⟨thm36B1_leftSeq_le_limit s hab k,
    thm36B1_limit_le_rightSeq s hab k⟩

/-- The completed point lies strictly inside the original interval. -/
theorem thm36B1_limit_strict_bounds
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    COF.lt a (thm36B1_leftLimit s hab).val ∧
      COF.lt (thm36B1_leftLimit s hab).val b := by
  have hin := thm36B1_limit_in_interval s hab 0
  constructor
  · exact lt_of_lt_of_le (thm36B1_intervalSeq s hab 0).a_lt_left
      (by simpa [thm36B1_leftSeq] using hin.1)
  · exact lt_of_le_of_lt
      (by simpa [thm36B1_rightSeq] using hin.2)
      (thm36B1_intervalSeq s hab 0).right_lt_b

/-- The completed point is apart from the `n`-th forbidden value. -/
theorem thm36B1_limit_apart
    (s : Nat → R) {a b : R} (hab : COF.lt a b) (n : Nat) :
    COF.lt 0 (COF.abs ((thm36B1_leftLimit s hab).val - s n)) := by
  have hav := (thm36B1_intervalSeq s hab (n + 1)).avoided n
    (Nat.lt_succ_self n)
  have hin := thm36B1_limit_in_interval s hab (n + 1)
  rcases hav with hleft | hright
  · have hst : COF.lt (s n) (thm36B1_leftLimit s hab).val :=
      lt_of_lt_of_le hleft
        (by simpa [thm36B1_leftSeq] using hin.1)
    have hdiff : COF.lt 0 ((thm36B1_leftLimit s hab).val - s n) :=
      lemma33_sub_pos_of_lt hst
    rw [COFO.abs_of_nonneg (le_of_lt hdiff)]
    exact hdiff
  · have hts : COF.lt (thm36B1_leftLimit s hab).val (s n) :=
      lt_of_le_of_lt
        (by simpa [thm36B1_rightSeq] using hin.2) hright
    have hdiff : COF.lt 0 (s n - (thm36B1_leftLimit s hab).val) :=
      lemma33_sub_pos_of_lt hts
    rw [show (thm36B1_leftLimit s hab).val - s n =
        -(s n - (thm36B1_leftLimit s hab).val) by ring,
      COFO.abs_neg, COFO.abs_of_nonneg (le_of_lt hdiff)]
    exact hdiff

/-- Constructive countable avoidance in every nondegenerate interval. -/
theorem thm36B1_exists_apart_in_interval
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    ∃ t : R, COF.lt a t ∧ COF.lt t b ∧
      ∀ n : Nat, COF.lt 0 (COF.abs (t - s n)) := by
  refine ⟨(thm36B1_leftLimit s hab).val,
    (thm36B1_limit_strict_bounds s hab).1,
    (thm36B1_limit_strict_bounds s hab).2, ?_⟩
  intro n
  exact thm36B1_limit_apart s hab n

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36B1_apart_data
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    Σ' t : R, COF.lt a t ×' COF.lt t b ×'
      (∀ n : Nat, COF.lt 0 (COF.abs (t - s n))) :=
  ⟨(thm36B1_leftLimit s hab).val,
   (thm36B1_limit_strict_bounds s hab).1,
   (thm36B1_limit_strict_bounds s hab).2,
   fun n => thm36B1_limit_apart s hab n⟩

/-- Data form of the canonical apart point. -/
structure Thm36B1ApartPointData
    (s : Nat → R) (a b : R) (hab : COF.lt a b) where
  t : R
  a_lt : COF.lt a t
  lt_b : COF.lt t b
  apart : ∀ n : Nat, COF.lt 0 (COF.abs (t - s n))

/-- Canonical apart point obtained from the nested interval construction. -/
noncomputable def thm36B1_apartPointData
    (s : Nat → R) {a b : R} (hab : COF.lt a b) :
    Thm36B1ApartPointData s a b hab := {
  t := (thm36B1_leftLimit s hab).val
  a_lt := (thm36B1_limit_strict_bounds s hab).1
  lt_b := (thm36B1_limit_strict_bounds s hab).2
  apart := thm36B1_limit_apart s hab
}


/-- Data package used by T36-C and T36-D. -/
structure Thm36BSmoothPointData
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) where
  t : R
  a_lt : COF.lt a t
  lt_b : COF.lt t b
  smooth : (thm36A2_profile h a b hab ha).IsSmoothAt t
  /-- Technical lemma used in the public import closure. -/
  lambdaBar : R
  /-- Technical lemma used in the public import closure. -/
  lambdaBar_spec :
    ∀ eps : R, COF.lt 0 eps →
      Σ' delta : R, COF.lt 0 delta ×'
        (∀ f ∈ (thm36A2_profile h a b hab ha).F,
          (∀ x, Le (t + delta) x → f x = 1) →
          (∀ x, Le x (t - delta) → f x = 0) →
          COF.lt (COF.abs ((thm36A2_profile h a b hab ha).lambda f - lambdaBar))
            eps)


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36B_smoothPointData_of_apart {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (t : R) (hat : COF.lt a t) (htb : COF.lt t b)
    (hT : ∀ n, COF.lt 0 (COF.abs (t - lemma35_exceptionSeq (thm36A2_profile h a b hab ha) n))) :
    Thm36BSmoothPointData h a b hab ha :=
  let P : Profile a b hab := thm36A2_profile h a b hab ha
  { t := t
    a_lt := hat
    lt_b := htb
    smooth := thm_3_5_smooth_at_seq P t (le_of_lt hat) (le_of_lt htb) hT
    lambdaBar := lemma35_lambdaBar P t (le_of_lt hat) (le_of_lt htb) hT
    lambdaBar_spec := thm_3_5_smooth_at_seq_spec P t (le_of_lt hat) (le_of_lt htb) hT }

/-! Technical auxiliary material for the public import closure. -/


/-- Strict subtraction is antitone in the subtracted argument. -/
theorem thm36C_sub_lt_sub_left {x y z : R} (hxy : COF.lt x y) :
    COF.lt (z - y) (z - x) := by
  have hneg : COF.lt (-y) (-x) := by
    have h := lemma33_add_lt_add_left (c := -(x + y)) hxy
    convert h using 1 <;> ring
  have h := lemma33_add_lt_add_left (c := z) hneg
  convert h using 1 <;> ring

/-- One dyadic step is strictly smaller than the preceding dyadic scale. -/
theorem thm36C_halfPow_succ_lt (n : Nat) :
    COF.lt (COF.halfPow (R := R) (n + 1)) (COF.halfPow (R := R) n) :=
  halfPow_lt_succ n

/-- Canonical smooth point selected in T36-B. -/
noncomputable def thm36C_t {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) : R :=
  (spD).t

/-- The selected point lies strictly above `a`. -/
theorem thm36C_a_lt_t {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    COF.lt a (thm36C_t h a b hab ha spD) := by
  simpa [thm36C_t] using (spD).a_lt

/-- The selected point lies strictly below `b`. -/
theorem thm36C_t_lt_b {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    COF.lt (thm36C_t h a b hab ha spD) b := by
  simpa [thm36C_t] using (spD).lt_b


/-- Fixed positive radius used in the dyadic approach to `t`. -/
noncomputable def thm36C_radius {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) : R :=
  (thm36C_t h a b hab ha spD - a) * COF.half

/-- The fixed radius is positive. -/
theorem thm36C_radius_pos {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    COF.lt 0 (thm36C_radius h a b hab ha spD) := by
  unfold thm36C_radius
  exact COFO.mul_pos (lemma33_sub_pos_of_lt (thm36C_a_lt_t h a b hab ha spD))
    COFO.half_pos

/-- Two copies of the fixed radius equal the full distance `t-a`. -/
theorem thm36C_radius_add_self {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    thm36C_radius h a b hab ha spD + thm36C_radius h a b hab ha spD =
      thm36C_t h a b hab ha spD - a := by
  unfold thm36C_radius
  calc
    (thm36C_t h a b hab ha spD - a) * COF.half +
        (thm36C_t h a b hab ha spD - a) * COF.half =
        (thm36C_t h a b hab ha spD - a) * (COF.half + COF.half) := by ring
    _ = (thm36C_t h a b hab ha spD - a) * 1 := by rw [COF.half_add_half]
    _ = thm36C_t h a b hab ha spD - a := by ring

/-- The fixed radius is strictly smaller than `t-a`. -/
theorem thm36C_radius_lt_span {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    COF.lt (thm36C_radius h a b hab ha spD)
      (thm36C_t h a b hab ha spD - a) := by
  have hr := thm36C_radius_pos h a b hab ha spD
  have hlt := lemma33_lt_add_of_pos_right
    (a := thm36C_radius h a b hab ha spD) hr
  rw [thm36C_radius_add_self h a b hab ha spD] at hlt
  exact hlt

/-- Dyadic distance from the `n`-th lower endpoint to `t`. -/
noncomputable def thm36C_gap {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) : R :=
  COF.halfPow n * thm36C_radius h a b hab ha spD

/-- Every dyadic gap is positive. -/
theorem thm36C_gap_pos {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    COF.lt 0 (thm36C_gap h a b hab ha spD n) := by
  unfold thm36C_gap
  exact COFO.mul_pos (halfPow_pos n) (thm36C_radius_pos h a b hab ha spD)

/-- Every dyadic gap is at most the fixed radius. -/
theorem thm36C_gap_le_radius {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    Le (thm36C_gap h a b hab ha spD n) (thm36C_radius h a b hab ha spD) := by
  have hpow : Le (COF.halfPow n) (1 : R) := by
    have hh := lemma35_halfPow_antitone (R := R) (k := 0) (m := n) (Nat.zero_le n)
    simpa using hh
  have hr : Nonneg (thm36C_radius h a b hab ha spD) :=
    le_of_lt (thm36C_radius_pos h a b hab ha spD)
  have hm := lemma33_mul_le_mul_right hpow hr
  simpa [thm36C_gap] using hm

/-- Every dyadic gap is strictly smaller than `t-a`. -/
theorem thm36C_gap_lt_span {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    COF.lt (thm36C_gap h a b hab ha spD n)
      (thm36C_t h a b hab ha spD - a) :=
  BishopC.lt_of_le_of_lt (thm36C_gap_le_radius h a b hab ha spD n)
    (thm36C_radius_lt_span h a b hab ha spD)

/-- The dyadic gaps are weakly antitone. -/
theorem thm36C_gap_antitone {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    {m n : Nat} (hmn : m ≤ n) :
    Le (thm36C_gap h a b hab ha spD n) (thm36C_gap h a b hab ha spD m) := by
  have hp := lemma35_halfPow_antitone (R := R) hmn
  have hr : Nonneg (thm36C_radius h a b hab ha spD) :=
    le_of_lt (thm36C_radius_pos h a b hab ha spD)
  simpa [thm36C_gap] using lemma33_mul_le_mul_right hp hr

/-- Consecutive dyadic gaps strictly decrease. -/
theorem thm36C_gap_succ_lt {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    COF.lt (thm36C_gap h a b hab ha spD (n + 1))
      (thm36C_gap h a b hab ha spD n) := by
  unfold thm36C_gap
  exact lemma33_mul_lt_mul_right (thm36C_halfPow_succ_lt n)
    (thm36C_radius_pos h a b hab ha spD)

/-- The lower endpoint `u_n = t-gap_n`. -/
noncomputable def thm36C_level {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) : R :=
  thm36C_t h a b hab ha spD - thm36C_gap h a b hab ha spD n

/-- The `n`-th lower endpoint lies strictly below `t`. -/
theorem thm36C_level_lt_t {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    COF.lt (thm36C_level h a b hab ha spD n) (thm36C_t h a b hab ha spD) := by
  have hp := thm36C_gap_pos h a b hab ha spD n
  have hlt := lemma33_lt_add_of_pos_right
    (a := thm36C_t h a b hab ha spD - thm36C_gap h a b hab ha spD n) hp
  convert hlt using 1 <;> ring

/-- The `n`-th lower endpoint remains strictly above `a`. -/
theorem thm36C_a_lt_level {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    COF.lt a (thm36C_level h a b hab ha spD n) := by
  have hgap := thm36C_gap_lt_span h a b hab ha spD n
  have hpos : COF.lt 0
      ((thm36C_t h a b hab ha spD - a) - thm36C_gap h a b hab ha spD n) :=
    lemma33_sub_pos_of_lt hgap
  have hadd := lemma33_add_lt_add_left (c := a) hpos
  unfold thm36C_level
  convert hadd using 1 <;> ring

/-- The lower endpoint is nonnegative, as required by `ramp_comp`. -/
theorem thm36C_level_nonneg {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    Nonneg (thm36C_level h a b hab ha spD n) :=
  le_trans (le_of_lt ha) (le_of_lt (thm36C_a_lt_level h a b hab ha spD n))

/-- The dyadic lower endpoints strictly increase to `t`. -/
theorem thm36C_level_lt_succ {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    COF.lt (thm36C_level h a b hab ha spD n)
      (thm36C_level h a b hab ha spD (n + 1)) := by
  exact thm36C_sub_lt_sub_left (z := thm36C_t h a b hab ha spD)
    (thm36C_gap_succ_lt h a b hab ha spD n)

/-- Some dyadic gap is below every positive tolerance. -/
noncomputable def thm36C_gap_eventually_lt {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (eps : R) (heps : COF.lt 0 eps) :
    {n : Nat // COF.lt (thm36C_gap h a b hab ha spD n) eps} := by
  let r : R := thm36C_radius h a b hab ha spD
  have hr : COF.lt 0 r := by
    dsimp [r]
    exact thm36C_radius_pos h a b hab ha spD
  let q : R := eps * COFO.inv r
  have hq : COF.lt 0 q := by
    dsimp [q]
    exact COFO.mul_pos heps (COFO.inv_pos hr)
  let n : Nat := (COFO.archimedean_pos q hq).1
  have hn : COF.lt (COF.halfPow n) q :=
    (COFO.archimedean_pos q hq).2
  have hmul : COF.lt (COF.halfPow n * r) (q * r) :=
    lemma33_mul_lt_mul_right hn hr
  have hinv : COFO.inv r * r = (1 : R) := by
    calc
      COFO.inv r * r = r * COFO.inv r := by ring
      _ = 1 := COFO.mul_inv_cancel hr
  have hqr : q * r = eps := by
    dsimp [q]
    calc
      (eps * COFO.inv r) * r = eps * (COFO.inv r * r) := by ring
      _ = eps * 1 := by rw [hinv]
      _ = eps := by ring
  refine ⟨n, ?_⟩
  change COF.lt (COF.halfPow n * r) eps
  rwa [hqr] at hmul

/-- Explicit modulus for `u_n → t`. -/
noncomputable def thm36C_levelMod {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (k : Nat) : Nat :=
  (thm36C_gap_eventually_lt h a b hab ha spD
    (COF.halfPow k) (halfPow_pos k)).1

/-- The modulus chosen above has the required gap estimate. -/
theorem thm36C_levelMod_spec {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (k : Nat) :
    COF.lt
      (thm36C_gap h a b hab ha spD (thm36C_levelMod h a b hab ha spD k))
      (COF.halfPow k) :=
  (thm36C_gap_eventually_lt h a b hab ha spD
    (COF.halfPow k) (halfPow_pos k)).2

/-- The dyadic lower endpoints converge to `t`. -/
noncomputable def thm36C_level_tends {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    RSeq.TendstoHalf (thm36C_level h a b hab ha spD)
      (thm36C_t h a b hab ha spD) := by
  refine {
    mod := thm36C_levelMod h a b hab ha spD
    close := ?_
  }
  intro k n hkn
  have hle : Le (thm36C_gap h a b hab ha spD n)
      (thm36C_gap h a b hab ha spD (thm36C_levelMod h a b hab ha spD k)) :=
    thm36C_gap_antitone h a b hab ha spD hkn
  have hgap : COF.lt (thm36C_gap h a b hab ha spD n) (COF.halfPow k) :=
    BishopC.lt_of_le_of_lt hle (thm36C_levelMod_spec h a b hab ha spD k)
  change COF.lt
    (COF.abs (thm36C_level h a b hab ha spD n - thm36C_t h a b hab ha spD))
    (COF.halfPow k)
  rw [show thm36C_level h a b hab ha spD n - thm36C_t h a b hab ha spD =
      -(thm36C_gap h a b hab ha spD n) by
        simp only [thm36C_level]; ring,
    COFO.abs_neg,
    COFO.abs_of_nonneg (le_of_lt (thm36C_gap_pos h a b hab ha spD n))]
  exact hgap


/-- The integrable composition corresponding to the `n`-th profile ramp. -/
noncomputable def thm36C_ramp {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) : IntegrableRep S :=
  thm_3_6_ramp_comp h (thm36C_level h a b hab ha spD n)
    (thm36C_t h a b hab ha spD)
    (thm36C_level_nonneg h a b hab ha spD n)
    (thm36C_level_lt_t h a b hab ha spD n)

/-- Tag of the `n`-th dyadic ramp(coded ABI). -/
noncomputable def thm36C_rampCode {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) : Thm36A2Code a b :=
  .ramp
    (thm36C_level h a b hab ha spD n)
    (thm36C_t h a b hab ha spD)
    (le_of_lt (thm36C_a_lt_level h a b hab ha spD n))
    (thm36C_level_lt_t h a b hab ha spD n)
    (le_of_lt (thm36C_t_lt_b h a b hab ha spD))

theorem thm36C_rampCode_mem {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    thm36C_rampCode h a b hab ha spD n ∈
      (thm36A2_profile h a b hab ha).F := by
  change thm36C_rampCode h a b hab ha spD n ∈
    thm36A2_profileF (a := a) (b := b)
  exact thm36A2_ramp_mem
    (le_of_lt (thm36C_a_lt_level h a b hab ha spD n))
    (thm36C_level_lt_t h a b hab ha spD n)
    (le_of_lt (thm36C_t_lt_b h a b hab ha spD))


/-- Technical lemma used in the public import closure. -/
theorem thm36C_profileLambda_ramp_eq_integral_raw
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (u v : R) (hau : Le a u) (huv : COF.lt u v) (hvb : Le v b) :
    thm36A2_profileLambda h hab ha (thm36A2_endpoints a b hab ha)
        (.ramp u v hau huv hvb) =
      (thm_3_6_ramp_comp h u v (thm36A2_u_nonneg ha hau) huv).integral := by
  rfl

/-- Profile-field version of the preceding equality. -/
theorem thm36C_profileLambda_ramp_eq_integral
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (u v : R) (hau : Le a u) (huv : COF.lt u v) (hvb : Le v b) :
    (thm36A2_profile h a b hab ha).lambda (.ramp u v hau huv hvb) =
      (thm_3_6_ramp_comp h u v (thm36A2_u_nonneg ha hau) huv).integral := by
  simpa [thm36A2_profile] using
    thm36C_profileLambda_ramp_eq_integral_raw h a b hab ha u v hau huv hvb

/-- Smooth limiting lambda value selected from T36-B. -/
noncomputable def thm36C_lambdaBar {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) : R :=
  (spD).lambdaBar

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36C_lambdaBar_spec {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    ∀ eps : R, COF.lt 0 eps →
      Σ' delta : R, COF.lt 0 delta ×'
        (∀ f ∈ (thm36A2_profile h a b hab ha).F,
          (∀ x : R, Le (thm36C_t h a b hab ha spD + delta) x → f x = 1) →
          (∀ x : R, Le x (thm36C_t h a b hab ha spD - delta) → f x = 0) →
          COF.lt
            (COF.abs ((thm36A2_profile h a b hab ha).lambda f -
              thm36C_lambdaBar h a b hab ha spD)) eps) :=
  (spD).lambdaBar_spec

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36C_rampLambda_mod_exists {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (k : Nat) :
    Σ' N : Nat, ∀ n : Nat, N ≤ n →
      COF.lt
        (COF.abs
          ((thm36A2_profile h a b hab ha).lambda
              (thm36C_rampCode h a b hab ha spD n) -
            thm36C_lambdaBar h a b hab ha spD))
        (COF.halfPow k) := by
  let s := thm36C_lambdaBar_spec h a b hab ha spD
      (COF.halfPow k) (halfPow_pos k)
  let delta : R := s.1
  have hdelta : COF.lt 0 delta := s.2.1
  have hsmooth := s.2.2
  let W := thm36C_gap_eventually_lt h a b hab ha spD delta hdelta
  refine ⟨W.1, ?_⟩
  intro n hWn
  have hgapLe : Le (thm36C_gap h a b hab ha spD n)
      (thm36C_gap h a b hab ha spD W.1) :=
    thm36C_gap_antitone h a b hab ha spD hWn
  have hgap : COF.lt (thm36C_gap h a b hab ha spD n) delta :=
    BishopC.lt_of_le_of_lt hgapLe W.2
  apply hsmooth (thm36C_rampCode h a b hab ha spD n)
    (thm36C_rampCode_mem h a b hab ha spD n)
  · intro x htx
    change thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD) x = 1
    apply thm36A1_ramp_one
      (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD) x
      (thm36C_level_lt_t h a b hab ha spD n)
    exact le_trans
      (lemma34_self_le_add (thm36C_t h a b hab ha spD) delta
        (le_of_lt hdelta)) htx
  · intro x hxt
    change thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD) x = 0
    apply thm36A1_ramp_zero
      (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD) x
      (thm36C_level_lt_t h a b hab ha spD n)
    have hgapLeDelta : Le (thm36C_gap h a b hab ha spD n) delta :=
      le_of_lt hgap
    have hleft : Le
        (thm36C_t h a b hab ha spD - delta)
        (thm36C_t h a b hab ha spD - thm36C_gap h a b hab ha spD n) :=
      lemma33_sub_le_sub_left hgapLeDelta
    exact le_trans hxt (by simpa [thm36C_level] using hleft)

/-- The profile lambda-values of the dyadic ramps converge to `lambdaBar`. -/
noncomputable def thm36C_rampLambda_tends {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    RSeq.TendstoHalf
      (fun n => (thm36A2_profile h a b hab ha).lambda
        (thm36C_rampCode h a b hab ha spD n))
      (thm36C_lambdaBar h a b hab ha spD) := by
  refine {
    mod := fun k => (thm36C_rampLambda_mod_exists h a b hab ha spD k).1
    close := ?_
  }
  intro k n hkn
  exact (thm36C_rampLambda_mod_exists h a b hab ha spD k).2 n hkn

/-- At level `n`, the profile lambda is the integral of `thm36C_ramp n`. -/
theorem thm36C_levelLambda_eq_rampIntegral {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (n : Nat) :
    (thm36A2_profile h a b hab ha).lambda
        (thm36C_rampCode h a b hab ha spD n) =
      (thm36C_ramp h a b hab ha spD n).integral := by
  simpa [thm36C_rampCode, thm36C_ramp] using
    thm36C_profileLambda_ramp_eq_integral h a b hab ha
      (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD)
      (le_of_lt (thm36C_a_lt_level h a b hab ha spD n))
      (thm36C_level_lt_t h a b hab ha spD n)
      (le_of_lt (thm36C_t_lt_b h a b hab ha spD))

/-- The actual ramp integrals converge to the smooth limiting value. -/
noncomputable def thm36C_rampIntegral_tends {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    RSeq.TendstoHalf
      (fun n => (thm36C_ramp h a b hab ha spD n).integral)
      (thm36C_lambdaBar h a b hab ha spD) := by
  let H := thm36C_rampLambda_tends h a b hab ha spD
  refine {
    mod := H.mod
    close := ?_
  }
  intro k n hkn
  have hc := H.close k n hkn
  rw [thm36C_levelLambda_eq_rampIntegral h a b hab ha spD n] at hc
  exact hc

/-! Technical auxiliary material for the public import closure. -/





























/-! Technical auxiliary material for the public import closure. -/

theorem IntegrableRep.collapseFirst_integral {S : IntSpaceRC X R}
    (r : IntegrableRep S) (N : Nat) :
    (r.collapseFirst N).integral = r.integral := by
  have hgg : (fun k => S.I ((r.collapseFirst N).fn k))
           = (fun k => if k = 0 then RSeq.partialSum (fun n => S.I (r.fn n)) N
                       else S.I (r.fn (N + k))) := by
    funext k
    show S.I (if k = 0 then BFunR.seqSum r.fn N else r.fn (N + k))
       = if k = 0 then RSeq.partialSum (fun n => S.I (r.fn n)) N else S.I (r.fn (N + k))
    by_cases h : k = 0
    · rw [if_pos h, if_pos h]; exact S.toIntSpaceR.I_seqSum r.mem N
    · rw [if_neg h, if_neg h]
  let W := seriesSum_collapse r.seriesSum_I N
  let hWg' : RSeq.SeriesSum
      (fun k => if k = 0 then RSeq.partialSum (fun n => S.I (r.fn n)) N
                else S.I (r.fn (N + k))) :=
    seriesSum_congr (fun k => congrFun hgg k) (r.collapseFirst N).seriesSum_I
  show (r.collapseFirst N).seriesSum_I.sum = r.seriesSum_I.sum
  calc (r.collapseFirst N).seriesSum_I.sum
      = hWg'.sum := rfl
    _ = W.val.sum := seriesSum_unique hWg' W.val
    _ = r.seriesSum_I.sum := W.property


/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_rampFn_between
    {u v y : R} (huv : COF.lt u v) (huy : Le u y) (hyv : Le y v) :
    thm_3_6_rampFn u v y = COFO.inv (v - u) * (y - u) := by
  let c : R := COFO.inv (v - u)
  have hvu : COF.lt 0 (v - u) := thm36A1_sub_pos_of_lt huv
  have hc : Nonneg c := le_of_lt (COFO.inv_pos hvu)
  have hyu : Nonneg (y - u) := nonneg_sub_of_le huy
  have hraw0 : Nonneg (c * (y - u)) := COFO.mul_nonneg hc hyu
  have hsub : Le (y - u) (v - u) := thm36A1_sub_le_sub_right hyv
  have hraw1 : Le (c * (y - u)) 1 := by
    have hm := mul_le_mul_left hsub hc
    have hcancel : c * (v - u) = (1 : R) := by
      dsimp [c]
      calc
        COFO.inv (v - u) * (v - u) =
            (v - u) * COFO.inv (v - u) := by ring
        _ = 1 := COFO.mul_inv_cancel hvu
    rwa [hcancel] at hm
  unfold thm_3_6_rampFn
  change COF.max (COF.min (c * (y - u)) 1) 0 = c * (y - u)
  rw [cof_min_eq_left_of_le hraw1, cof_max_eq_left_of_le hraw0]


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_cross_ratio
    {u p y t : R} (hup : Le u p) (hyt : Le y t) :
    Le ((y - p) * (t - u)) ((y - u) * (t - p)) := by
  apply le_of_nonneg_sub
  have hpu : Nonneg (p - u) := nonneg_sub_of_le hup
  have hty : Nonneg (t - y) := nonneg_sub_of_le hyt
  have hprod : Nonneg ((p - u) * (t - y)) := COFO.mul_nonneg hpu hty
  convert hprod using 1 <;> ring


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_ratio_antitone_left
    {u p y t : R} (hup : Le u p)
    (hut : COF.lt u t) (hpt : COF.lt p t)
    (hpy : Le p y) (hyt : Le y t) :
    Le (COFO.inv (t - p) * (y - p))
      (COFO.inv (t - u) * (y - u)) := by
  have hB : COF.lt 0 (t - p) := thm36A1_sub_pos_of_lt hpt
  have hD : COF.lt 0 (t - u) := thm36A1_sub_pos_of_lt hut
  apply lemma33_mul_le_cancel_left hB
  have hBinv : (t - p) * COFO.inv (t - p) = (1 : R) :=
    COFO.mul_inv_cancel hB
  rw [show (t - p) * (COFO.inv (t - p) * (y - p)) = y - p by
    calc
      (t - p) * (COFO.inv (t - p) * (y - p)) =
          ((t - p) * COFO.inv (t - p)) * (y - p) := by ring
      _ = 1 * (y - p) := by rw [hBinv]
      _ = y - p := by ring]
  apply lemma33_mul_le_cancel_left hD
  have hDinv : (t - u) * COFO.inv (t - u) = (1 : R) :=
    COFO.mul_inv_cancel hD
  have hcross := thm36Cb_cross_ratio (R := R) hup hyt
  convert hcross using 1
  · ring
  · calc
      (t - u) * ((t - p) * (COFO.inv (t - u) * (y - u))) =
          ((t - u) * COFO.inv (t - u)) * ((y - u) * (t - p)) := by ring
      _ = 1 * ((y - u) * (t - p)) := by rw [hDinv]
      _ = (y - u) * (t - p) := by ring


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_rampFn_antitone_left
    {u p t : R} (hup : Le u p)
    (hut : COF.lt u t) (hpt : COF.lt p t) :
    ∀ y : R, Le (thm_3_6_rampFn p t y) (thm_3_6_rampFn u t y) := by
  -- Technical note.
  -- Technical note.
  intro y h
  -- h : COF.lt (rampFn u t y) (rampFn p t y)
  have hpos : COF.lt 0 (thm_3_6_rampFn p t y) :=
    lt_of_le_of_lt (thm36A1_ramp_bound u t y).1 h
  have hpy : COF.lt p y := thm36A1_ramp_pos_imp p t y hpt hpos
  have hu_lt_1 : COF.lt (thm_3_6_rampFn u t y) 1 :=
    lt_of_lt_of_le h (thm36A1_ramp_bound p t y).2
  have hyt : COF.lt y t := thm36A1_ramp_lt_one_imp u t y hut hu_lt_1
  rw [thm36Cb_rampFn_between hpt (le_of_lt hpy) (le_of_lt hyt),
      thm36Cb_rampFn_between hut
        (le_trans hup (le_of_lt hpy)) (le_of_lt hyt)] at h
  exact thm36Cb_ratio_antitone_left hup hut hpt
    (le_of_lt hpy) (le_of_lt hyt) h


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_rampFn_succ_le
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) (y : R) :
    Le
      (thm_3_6_rampFn (thm36C_level h a b hab ha spD (n + 1))
        (thm36C_t h a b hab ha spD) y)
      (thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
        (thm36C_t h a b hab ha spD) y) := by
  exact thm36Cb_rampFn_antitone_left
    (le_of_lt (thm36C_level_lt_succ h a b hab ha spD n))
    (thm36C_level_lt_t h a b hab ha spD n)
    (thm36C_level_lt_t h a b hab ha spD (n + 1)) y


/-- Domain transport from the source representative to a profile ramp. -/
theorem thm36Cb_ramp_memAt
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) {x : X} (hdom : h.MemAt x) :
    (thm36C_ramp h a b hab ha spD n).MemAt x := by
  simpa [thm36C_ramp] using
    (thm36A1_ramp_comp_memAt h
      (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD)
      (thm36C_level_nonneg h a b hab ha spD n)
      (thm36C_level_lt_t h a b hab ha spD n) hdom)

/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_ramp_value_witness
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) (x : X) (hdom : h.MemAt x)
    (hx : RSeq.SeriesSum (fun m => h.valueAt x hdom m)) :
    {hr : RSeq.SeriesSum
      (fun m => (thm36C_ramp h a b hab ha spD n).valueAt x
        (thm36Cb_ramp_memAt h a b hab ha spD n hdom) m) //
      hr.sum =
        thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
          (thm36C_t h a b hab ha spD) hx.sum} := by
  simpa [thm36C_ramp] using
    (thm36A1_ramp_comp_value_witness h
      (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD)
      (thm36C_level_nonneg h a b hab ha spD n)
      (thm36C_level_lt_t h a b hab ha spD n) x hdom hx)


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_decrement
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) : IntegrableRep S :=
  (thm36C_ramp h a b hab ha spD n).sub
    (thm36C_ramp h a b hab ha spD (n + 1))




/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_decrement_nonneg_on_domain
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) (x : X) (hxdom : x ∈ h.domain)
    (hdDom : (thm36Cb_decrement h a b hab ha spD n).MemAt x)
    (hd : RSeq.SeriesSum
      (fun m => (thm36Cb_decrement h a b hab ha spD n).valueAt x hdDom m)) :
    Nonneg hd.sum := by
  obtain ⟨hdom, ⟨hxabs⟩⟩ := hxdom
  let hx := seriesSum_of_abs hxabs
  let Wn := thm36Cb_ramp_value_witness h a b hab ha spD n x hdom hx
  let Ws := thm36Cb_ramp_value_witness h a b hab ha spD (n + 1) x hdom hx
  let WnDom := thm36Cb_ramp_memAt h a b hab ha spD n hdom
  let WsDom := thm36Cb_ramp_memAt h a b hab ha spD (n + 1) hdom
  let hnegDom := IntegrableRep.neg_memAt WsDom
  let hneg : RSeq.SeriesSum
      (fun m => (thm36C_ramp h a b hab ha spD (n + 1)).neg.valueAt x
        hnegDom m) :=
    neg_seriesSum_value WsDom Ws.val
  let hcanDom := IntegrableRep.add_memAt WnDom hnegDom
  let hcan : RSeq.SeriesSum
      (fun m => (thm36Cb_decrement h a b hab ha spD n).valueAt x hcanDom m) := by
    exact add_seriesSum_value WnDom hnegDom Wn.val hneg
  have hsum : hd.sum = Wn.val.sum - Ws.val.sum := by
    calc
      hd.sum = hcan.sum := seriesSum_unique hd hcan
      _ = Wn.val.sum + (-Ws.val.sum) := by rfl
      _ = Wn.val.sum - Ws.val.sum := by ring
  rw [hsum, Wn.property, Ws.property]
  exact nonneg_sub_of_le
    (thm36Cb_rampFn_succ_le h a b hab ha spD n hx.sum)


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_ramp_nonneg_on_domain
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) (x : X) (hxdom : x ∈ h.domain)
    (hrDom : (thm36C_ramp h a b hab ha spD n).MemAt x)
    (hr : RSeq.SeriesSum
      (fun m => (thm36C_ramp h a b hab ha spD n).valueAt x hrDom m)) :
    Nonneg hr.sum := by
  obtain ⟨hdom, ⟨hxabs⟩⟩ := hxdom
  let hx := seriesSum_of_abs hxabs
  have hval : hr.sum =
      thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
        (thm36C_t h a b hab ha spD) hx.sum := by
    simpa [thm36C_ramp] using
      (thm36A1_ramp_comp_value h
        (thm36C_level h a b hab ha spD n)
        (thm36C_t h a b hab ha spD)
        (thm36C_level_nonneg h a b hab ha spD n)
        (thm36C_level_lt_t h a b hab ha spD n) x hdom hx hrDom hr)
  rw [hval]
  exact (thm36A1_ramp_bound
    (thm36C_level h a b hab ha spD n)
    (thm36C_t h a b hab ha spD) hx.sum).1


/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_normL1_eq_integral_on_full
    {S : IntSpaceRC X R} {r : IntegrableRep S} {A : Set X}
    (hA : IsFull S A)
    (hnn : ∀ x ∈ A,
      ∀ (hrDom : r.MemAt x)
        (hr : RSeq.SeriesSum (fun m => r.valueAt x hrDom m)),
        Nonneg hr.sum) :
    r.normL1 = r.integral := by
  show r.absVal.integral = r.integral
  refine cor_1_12 hA r.absVal r ?_
  intro x hxA habsDom hrDom habs hr
  let W := r.absVal_pointSum x hrDom hr
  calc
    habs.sum = W.1.sum := seriesSum_unique habs W.1
    _ = COF.abs hr.sum := W.2
    _ = hr.sum := COFO.abs_of_nonneg (hnn x hxA hrDom hr)


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_ramp_normL1
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) :
    (thm36C_ramp h a b hab ha spD n).normL1 =
      (thm36C_ramp h a b hab ha spD n).integral :=
  thm36Cb_normL1_eq_integral_on_full
    (IntegrableRep.domain_isFull h)
    (thm36Cb_ramp_nonneg_on_domain h a b hab ha spD n)


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_signedDiff_normL1
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) :
    ((thm36C_ramp h a b hab ha spD (n + 1)).sub (thm36C_ramp h a b hab ha spD n)).normL1 =
      (thm36Cb_decrement h a b hab ha spD n).integral := by
  let s : IntegrableRep S :=
    (thm36C_ramp h a b hab ha spD (n + 1)).sub (thm36C_ramp h a b hab ha spD n)
  let d : IntegrableRep S := thm36Cb_decrement h a b hab ha spD n
  show s.absVal.integral = d.integral
  refine cor_1_12 (IntegrableRep.domain_isFull h) s.absVal d ?_
  intro x hxdom habsDom hdDom habs hd
  obtain ⟨hdom, ⟨hxabs⟩⟩ := hxdom
  let hx := seriesSum_of_abs hxabs
  let Wn := thm36Cb_ramp_value_witness h a b hab ha spD n x hdom hx
  let Ws := thm36Cb_ramp_value_witness h a b hab ha spD (n + 1) x hdom hx
  let WnDom := thm36Cb_ramp_memAt h a b hab ha spD n hdom
  let WsDom := thm36Cb_ramp_memAt h a b hab ha spD (n + 1) hdom
  let hnegNDom := IntegrableRep.neg_memAt WnDom
  let hnegN : RSeq.SeriesSum
      (fun m => (thm36C_ramp h a b hab ha spD n).neg.valueAt x hnegNDom m) :=
    neg_seriesSum_value WnDom Wn.val
  let hsDom : s.MemAt x := IntegrableRep.add_memAt WsDom hnegNDom
  let hs : RSeq.SeriesSum (fun m => s.valueAt x hsDom m) := by
    dsimp [s, IntegrableRep.sub]
    exact add_seriesSum_value WsDom hnegNDom Ws.val hnegN
  let hnegSDom := IntegrableRep.neg_memAt WsDom
  let hnegS : RSeq.SeriesSum
      (fun m => (thm36C_ramp h a b hab ha spD (n + 1)).neg.valueAt x hnegSDom m) :=
    neg_seriesSum_value WsDom Ws.val
  let hd0Dom : d.MemAt x := IntegrableRep.add_memAt WnDom hnegSDom
  let hd0 : RSeq.SeriesSum (fun m => d.valueAt x hd0Dom m) := by
    dsimp [d, thm36Cb_decrement, IntegrableRep.sub]
    exact add_seriesSum_value WnDom hnegSDom Wn.val hnegS
  let Wa := s.absVal_pointSum x hsDom hs
  have hs_sum : hs.sum = Ws.val.sum - Wn.val.sum := by
    calc
      hs.sum = Ws.val.sum + (-Wn.val.sum) := by rfl
      _ = Ws.val.sum - Wn.val.sum := by ring
  have hd_sum : hd0.sum = Wn.val.sum - Ws.val.sum := by
    calc
      hd0.sum = Wn.val.sum + (-Ws.val.sum) := by rfl
      _ = Wn.val.sum - Ws.val.sum := by ring
  have hnn : Nonneg hd0.sum :=
    thm36Cb_decrement_nonneg_on_domain h a b hab ha spD n x
      ⟨hdom, ⟨hxabs⟩⟩ hd0Dom hd0
  calc
    habs.sum = Wa.1.sum := seriesSum_unique habs Wa.1
    _ = COF.abs hs.sum := Wa.2
    _ = COF.abs (Ws.val.sum - Wn.val.sum) := by rw [hs_sum]
    _ = COF.abs (-(Wn.val.sum - Ws.val.sum)) := by congr 1; ring
    _ = COF.abs (Wn.val.sum - Ws.val.sum) := COFO.abs_neg _
    _ = COF.abs hd0.sum := by rw [hd_sum]
    _ = hd0.sum := COFO.abs_of_nonneg hnn
    _ = hd.sum := seriesSum_unique hd0 hd


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_decrement_integral
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) :
    (thm36Cb_decrement h a b hab ha spD n).integral =
      (thm36C_ramp h a b hab ha spD n).integral -
        (thm36C_ramp h a b hab ha spD (n + 1)).integral := by
  unfold thm36Cb_decrement
  exact IntegrableRep.integral_sub _ _


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_signedTerm
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    Nat → IntegrableRep S
  | 0 => thm36C_ramp h a b hab ha spD 0
  | n + 1 =>
      (thm36C_ramp h a b hab ha spD (n + 1)).sub (thm36C_ramp h a b hab ha spD n)


theorem thm36Cb_signedTerm_memAt
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) {x : X} (hdom : h.MemAt x) :
    (thm36Cb_signedTerm h a b hab ha spD n).MemAt x := by
  cases n with
  | zero => exact thm36Cb_ramp_memAt h a b hab ha spD 0 hdom
  | succ n =>
      exact IntegrableRep.add_memAt
        (thm36Cb_ramp_memAt h a b hab ha spD (n + 1) hdom)
        (IntegrableRep.neg_memAt
          (thm36Cb_ramp_memAt h a b hab ha spD n hdom))


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_term
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (m : Nat) : IntegrableRep S :=
  (thm36Cb_signedTerm h a b hab ha spD m).collapseFirst
    ((thm36Cb_signedTerm h a b hab ha spD m).contNf m)


theorem thm36Cb_term_memAt
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) {x : X} (hdom : h.MemAt x) :
    (thm36Cb_term h a b hab ha spD n).MemAt x :=
  (thm36Cb_signedTerm h a b hab ha spD n).collapseFirst_memAt
    ((thm36Cb_signedTerm h a b hab ha spD n).contNf n)
    (thm36Cb_signedTerm_memAt h a b hab ha spD n hdom)


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_normL1Value
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    Nat → R
  | 0 => (thm36C_ramp h a b hab ha spD 0).integral
  | n + 1 => (thm36Cb_decrement h a b hab ha spD n).integral


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_signedTerm_normL1
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (m : Nat) :
    (thm36Cb_signedTerm h a b hab ha spD m).normL1 =
      thm36Cb_normL1Value h a b hab ha spD m := by
  cases m with
  | zero =>
      show (thm36C_ramp h a b hab ha spD 0).normL1 = (thm36C_ramp h a b hab ha spD 0).integral
      exact thm36Cb_ramp_normL1 h a b hab ha spD 0
  | succ n =>
      show ((thm36C_ramp h a b hab ha spD (n + 1)).sub (thm36C_ramp h a b hab ha spD n)).normL1
          = (thm36Cb_decrement h a b hab ha spD n).integral
      exact thm36Cb_signedDiff_normL1 h a b hab ha spD n


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_term_integral
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (m : Nat) :
    (thm36Cb_term h a b hab ha spD m).integral =
      (thm36Cb_signedTerm h a b hab ha spD m).integral := by
  unfold thm36Cb_term
  exact IntegrableRep.collapseFirst_integral _ _


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_term_absConv_lt
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (m : Nat) :
    COF.lt
      ((thm36Cb_term h a b hab ha spD m).absConv.sum)
      (thm36Cb_normL1Value h a b hab ha spD m + COF.halfPow m) := by
  have hd := (thm36Cb_signedTerm h a b hab ha spD m).collapseFirst_dense m
  have hnorm := thm36Cb_signedTerm_normL1 h a b hab ha spD m
  show COF.lt ((thm36Cb_signedTerm h a b hab ha spD m).collapseFirst
      ((thm36Cb_signedTerm h a b hab ha spD m).contNf m)).absConv.sum _
  rw [← hnorm]
  exact hd


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_partialSum_normL1Value
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    ∀ n : Nat,
      RSeq.partialSum (thm36Cb_normL1Value h a b hab ha spD) n =
        (thm36C_ramp h a b hab ha spD 0).integral +
          (thm36C_ramp h a b hab ha spD 0).integral -
          (thm36C_ramp h a b hab ha spD n).integral
  | 0 => by
      show thm36Cb_normL1Value h a b hab ha spD 0 = _
      show (thm36C_ramp h a b hab ha spD 0).integral = _
      ring
  | n + 1 => by
      rw [RSeq.partialSum,
        thm36Cb_partialSum_normL1Value h a b hab ha spD n]
      show _ + thm36Cb_normL1Value h a b hab ha spD (n + 1) = _
      rw [show thm36Cb_normL1Value h a b hab ha spD (n + 1)
            = (thm36Cb_decrement h a b hab ha spD n).integral from rfl,
        thm36Cb_decrement_integral h a b hab ha spD n]
      ring


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_normSeries
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    RSeq.SeriesSum (thm36Cb_normL1Value h a b hab ha spD) := by
  let H := thm36C_rampIntegral_tends h a b hab ha spD
  refine {
    sum :=
      (thm36C_ramp h a b hab ha spD 0).integral +
        (thm36C_ramp h a b hab ha spD 0).integral -
        thm36C_lambdaBar h a b hab ha spD
    tends := { mod := H.mod, close := ?_ } }
  intro k n hkn
  rw [thm36Cb_partialSum_normL1Value h a b hab ha spD n]
  have hc := H.close k n hkn
  change COF.lt
    (COF.abs ((thm36C_ramp h a b hab ha spD n).integral - thm36C_lambdaBar h a b hab ha spD))
    (COF.halfPow k) at hc
  show COF.lt
    (COF.abs
      (((thm36C_ramp h a b hab ha spD 0).integral +
          (thm36C_ramp h a b hab ha spD 0).integral -
          (thm36C_ramp h a b hab ha spD n).integral) -
        ((thm36C_ramp h a b hab ha spD 0).integral +
          (thm36C_ramp h a b hab ha spD 0).integral -
          thm36C_lambdaBar h a b hab ha spD)))
    (COF.halfPow k)
  rw [show
      ((thm36C_ramp h a b hab ha spD 0).integral +
          (thm36C_ramp h a b hab ha spD 0).integral -
          (thm36C_ramp h a b hab ha spD n).integral) -
        ((thm36C_ramp h a b hab ha spD 0).integral +
          (thm36C_ramp h a b hab ha spD 0).integral -
          thm36C_lambdaBar h a b hab ha spD) =
        -((thm36C_ramp h a b hab ha spD n).integral -
          thm36C_lambdaBar h a b hab ha spD) from by ring,
    COFO.abs_neg]
  exact hc


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_majorantSeries
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    RSeq.SeriesSum
      (fun m => thm36Cb_normL1Value h a b hab ha spD m + COF.halfPow m) :=
  seriesSum_add (thm36Cb_normSeries h a b hab ha spD) seriesSum_halfPow


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_termAbsSeries
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    RSeq.SeriesSum
      (fun m => (thm36Cb_term h a b hab ha spD m).absConv.sum) :=
  seriesSum_comparison
    (fun m => (thm36Cb_term h a b hab ha spD m).absSum_nonneg)
    (fun m => le_of_lt (thm36Cb_term_absConv_lt h a b hab ha spD m))
    (thm36Cb_majorantSeries h a b hab ha spD)


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_f
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    IntegrableRep S :=
  seriesIntegrable (thm36Cb_term h a b hab ha spD)
    (thm36Cb_termAbsSeries h a b hab ha spD)


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_partialSum_term_integral
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    ∀ n : Nat,
      RSeq.partialSum
        (fun m => (thm36Cb_term h a b hab ha spD m).integral) n =
      (thm36C_ramp h a b hab ha spD n).integral
  | 0 => by
      show (thm36Cb_term h a b hab ha spD 0).integral = _
      rw [thm36Cb_term_integral h a b hab ha spD 0]
      rfl
  | n + 1 => by
      rw [RSeq.partialSum,
        thm36Cb_partialSum_term_integral h a b hab ha spD n,
        thm36Cb_term_integral h a b hab ha spD (n + 1)]
      show _ + ((thm36C_ramp h a b hab ha spD (n + 1)).sub
            (thm36C_ramp h a b hab ha spD n)).integral = _
      rw [IntegrableRep.integral_sub]
      ring


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_termIntegralSeries
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    RSeq.SeriesSum
      (fun m => (thm36Cb_term h a b hab ha spD m).integral) := by
  let H := thm36C_rampIntegral_tends h a b hab ha spD
  refine { sum := thm36C_lambdaBar h a b hab ha spD
           tends := { mod := H.mod, close := ?_ } }
  intro k n hkn
  rw [thm36Cb_partialSum_term_integral h a b hab ha spD n]
  exact H.close k n hkn


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_f_integral
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    (thm36Cb_f h a b hab ha spD).integral =
      thm36C_lambdaBar h a b hab ha spD := by
  let W := seriesIntegrable_integral
    (thm36Cb_term h a b hab ha spD)
    (thm36Cb_termAbsSeries h a b hab ha spD)
  calc
    (thm36Cb_f h a b hab ha spD).integral = W.val.sum := by
      simpa [thm36Cb_f] using W.property
    _ = (thm36Cb_termIntegralSeries h a b hab ha spD).sum :=
      seriesSum_unique W.val (thm36Cb_termIntegralSeries h a b hab ha spD)
    _ = thm36C_lambdaBar h a b hab ha spD := rfl


/-! Technical auxiliary material for the public import closure. -/





























/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_pointTerm
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (z : R) : Nat → R
  | 0 =>
      thm_3_6_rampFn (thm36C_level h a b hab ha spD 0)
        (thm36C_t h a b hab ha spD) z
  | n + 1 =>
      thm_3_6_rampFn (thm36C_level h a b hab ha spD (n + 1))
          (thm36C_t h a b hab ha spD) z -
        thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
          (thm36C_t h a b hab ha spD) z


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_signedTerm_value_witness
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) (x : X) (hdom : h.MemAt x)
    (hx : RSeq.SeriesSum (fun m => h.valueAt x hdom m)) :
    {hv : RSeq.SeriesSum
      (fun m => (thm36Cb_signedTerm h a b hab ha spD n).valueAt x
        (thm36Cb_signedTerm_memAt h a b hab ha spD n hdom) m) //
      hv.sum = thm36Cb_pointTerm h a b hab ha spD hx.sum n} := by
  cases n with
  | zero =>
      let W := thm36Cb_ramp_value_witness h a b hab ha spD 0 x hdom hx
      refine ⟨W.val, ?_⟩
      simpa [thm36Cb_signedTerm, thm36Cb_pointTerm] using W.property
  | succ n =>
      let Wn := thm36Cb_ramp_value_witness h a b hab ha spD n x hdom hx
      let Ws := thm36Cb_ramp_value_witness h a b hab ha spD (n + 1) x hdom hx
      let WnDom := thm36Cb_ramp_memAt h a b hab ha spD n hdom
      let WsDom := thm36Cb_ramp_memAt h a b hab ha spD (n + 1) hdom
      let hnegDom := IntegrableRep.neg_memAt WnDom
      let hneg : RSeq.SeriesSum
          (fun m => (thm36C_ramp h a b hab ha spD n).neg.valueAt x hnegDom m) :=
        neg_seriesSum_value WnDom Wn.val
      let hsubDom := IntegrableRep.add_memAt WsDom hnegDom
      let hsub : RSeq.SeriesSum
          (fun m => (thm36Cb_signedTerm h a b hab ha spD (n + 1)).valueAt x
            hsubDom m) := by
        dsimp [thm36Cb_signedTerm, IntegrableRep.sub]
        exact add_seriesSum_value WsDom hnegDom Ws.val hneg
      refine ⟨hsub, ?_⟩
      change Ws.val.sum + (-Wn.val.sum) = _
      rw [Ws.property, Wn.property]
      simp only [thm36Cb_pointTerm]
      ring


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36Cb_term_value_witness
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (n : Nat) (x : X) (hdom : h.MemAt x)
    (hx : RSeq.SeriesSum (fun m => h.valueAt x hdom m)) :
    {hv : RSeq.SeriesSum
      (fun m => (thm36Cb_term h a b hab ha spD n).valueAt x
        (thm36Cb_term_memAt h a b hab ha spD n hdom) m) //
      hv.sum = thm36Cb_pointTerm h a b hab ha spD hx.sum n} := by
  let hsigDom := thm36Cb_signedTerm_memAt h a b hab ha spD n hdom
  let Wsig := thm36Cb_signedTerm_value_witness h a b hab ha spD n x hdom hx
  let Wc := (thm36Cb_signedTerm h a b hab ha spD n).collapseFirst_toFun_seriesSum
    ((thm36Cb_signedTerm h a b hab ha spD n).contNf n) x hsigDom Wsig.val
  exact ⟨Wc.val, by rw [Wc.property]; exact Wsig.property⟩


/-- scalar pointwise partial sums telescope to the `n`-th ramp value。 -/
theorem thm36Cb_partialSum_pointTerm
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (z : R) :
    ∀ n : Nat,
      RSeq.partialSum (thm36Cb_pointTerm h a b hab ha spD z) n =
        thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
          (thm36C_t h a b hab ha spD) z
  | 0 => by rfl
  | n + 1 => by
      rw [RSeq.partialSum,
        thm36Cb_partialSum_pointTerm h a b hab ha spD z n]
      simp only [thm36Cb_pointTerm]
      ring


/-- Technical lemma used in the public import closure. -/
theorem thm36Cb_partialSum_term_values
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (x : X) (hdom : h.MemAt x)
    (hx : RSeq.SeriesSum (fun m => h.valueAt x hdom m))
    (n : Nat) :
    RSeq.partialSum
        (fun j => (thm36Cb_term_value_witness
          h a b hab ha spD j x hdom hx).val.sum) n =
      thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
        (thm36C_t h a b hab ha spD) hx.sum := by
  have hterms :
      (fun j => (thm36Cb_term_value_witness
        h a b hab ha spD j x hdom hx).val.sum) =
      thm36Cb_pointTerm h a b hab ha spD hx.sum := by
    funext j
    exact (thm36Cb_term_value_witness h a b hab ha spD j x hdom hx).property
  rw [hterms]
  exact thm36Cb_partialSum_pointTerm h a b hab ha spD hx.sum n


/-- Technical lemma used in the public import closure. -/
structure Thm36CIntegrableData
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) where
  f : IntegrableRep S
  f_eq : f = thm36Cb_f h a b hab ha spD
  integral_eq : f.integral = thm36C_lambdaBar h a b hab ha spD
  point_partial_sum :
    ∀ x : X, ∀ (hdom : h.MemAt x)
      (hx : RSeq.SeriesSum (fun m => h.valueAt x hdom m)), ∀ n : Nat,
      RSeq.partialSum
          (fun j => (thm36Cb_term_value_witness
            h a b hab ha spD j x hdom hx).val.sum) n =
        thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
          (thm36C_t h a b hab ha spD) hx.sum


/-- canonical T36-Cβ data。 -/
noncomputable def thm36C_integrableData
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    Thm36CIntegrableData h a b hab ha spD := {
  f := thm36Cb_f h a b hab ha spD
  f_eq := rfl
  integral_eq := thm36Cb_f_integral h a b hab ha spD
  point_partial_sum := thm36Cb_partialSum_term_values h a b hab ha spD
}


/-! Technical auxiliary material for the public import closure. -/

/-- Technical lemma used in the public import closure. -/
def thm36D_upperSet {S : IntSpaceRC X R} (h : IntegrableRep S) (t : R) : Set X :=
  {x | ∃ (hdom : h.MemAt x) (_habs : RSeq.SeriesSum
      (fun n => COF.abs (h.valueAt x hdom n)))
      (hx : RSeq.SeriesSum (fun n => h.valueAt x hdom n)),
      Le t hx.sum}


/-- Technical lemma used in the public import closure. -/
def thm36D_lowerSet {S : IntSpaceRC X R} (h : IntegrableRep S) (t : R) : Set X :=
  {x | ∃ (hdom : h.MemAt x) (_habs : RSeq.SeriesSum
      (fun n => COF.abs (h.valueAt x hdom n)))
      (hx : RSeq.SeriesSum (fun n => h.valueAt x hdom n)),
      COF.lt hx.sum t}


/-- Technical lemma used in the public import closure. -/
theorem thm36D_levelSets_disjoint {S : IntSpaceRC X R}
    (h : IntegrableRep S) (t : R) :
    ∀ x ∈ thm36D_upperSet h t, ∀ y ∈ thm36D_lowerSet h t, x ≠ y := by
  intro x hx y hy hxy
  subst y
  rcases hx with ⟨_hdomx, _habsx, hxsum, hle⟩
  rcases hy with ⟨_hdomy, _habsy, hysum, hlt⟩
  have hsum : hxsum.sum = hysum.sum := seriesSum_unique hxsum hysum
  rw [hsum] at hle
  exact hle hlt


/-- Technical lemma used in the public import closure. -/
def thm36D_levelBSet {S : IntSpaceRC X R}
    (h : IntegrableRep S) (t : R) : BSet X := {
  S1 := thm36D_upperSet h t
  S2 := thm36D_lowerSet h t
  disj := thm36D_levelSets_disjoint h t
}






/-- Technical lemma used in the public import closure. -/
theorem thm36D_tendsto_eventually_const
    {u : Nat → R} {z c : R} (H : RSeq.TendstoHalf u z)
    (N : Nat) (hu : ∀ n : Nat, N ≤ n → u n = c) : z = c := by
  apply COFO.eq_of_small
  intro k hbad
  let n : Nat := max N (H.mod k)
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hnmod : H.mod k ≤ n := Nat.le_max_right _ _
  have hclose := H.close k n hnmod
  rw [hu n hnN] at hclose
  have hbad' : COF.lt (COF.halfPow k) (COF.abs (c - z)) := by
    rw [show z - c = -(c - z) by ring, COFO.abs_neg] at hbad
    exact hbad
  exact COF.lt_irrefl _ (COFO.lt_trans hbad' hclose)


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36D_lt_limit_eventually
    {u : Nat → R} {y z : R} (H : RSeq.TendstoHalf u z)
    (hyz : COF.lt y z) : {N : Nat // COF.lt y (u N)} := by
  have hgap : COF.lt 0 (z - y) := lemma33_sub_pos_of_lt hyz
  let W := COFO.archimedean_pos (z - y) hgap
  let N : Nat := H.mod W.val
  have hclose : COF.lt (COF.abs (u N - z)) (COF.halfPow W.val) :=
    H.close W.val N (Nat.le_refl N)
  have hzu_le : Le (z - u N) (COF.abs (u N - z)) := by
    have h := lemma35_neg_le_abs (u N - z)
    convert h using 1 <;> ring
  have hzu_hp : COF.lt (z - u N) (COF.halfPow W.val) :=
    BishopC.lt_of_le_of_lt hzu_le hclose
  have hzu_zy : COF.lt (z - u N) (z - y) :=
    COFO.lt_trans hzu_hp W.property
  have hadd := lemma33_add_lt_add_left (c := u N + y - z) hzu_zy
  refine ⟨N, ?_⟩
  convert hadd using 1 <;> ring


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36D_limit_lt_eventually
    {u : Nat → R} {z c : R} (H : RSeq.TendstoHalf u z)
    (hzc : COF.lt z c) : {N : Nat // COF.lt (u N) c} := by
  have hgap : COF.lt 0 (c - z) := lemma33_sub_pos_of_lt hzc
  let W := COFO.archimedean_pos (c - z) hgap
  let N : Nat := H.mod W.val
  have hclose : COF.lt (COF.abs (u N - z)) (COF.halfPow W.val) :=
    H.close W.val N (Nat.le_refl N)
  have huz_le : Le (u N - z) (COF.abs (u N - z)) :=
    lemma35_le_abs_self (u N - z)
  have huz_hp : COF.lt (u N - z) (COF.halfPow W.val) :=
    BishopC.lt_of_le_of_lt huz_le hclose
  have huz_zc : COF.lt (u N - z) (c - z) :=
    COFO.lt_trans huz_hp W.property
  have hadd := lemma33_add_lt_add_left (c := z) huz_zc
  refine ⟨N, ?_⟩
  convert hadd using 1 <;> ring

/-- Technical lemma used in the public import closure. -/
theorem thm36D_level_mono {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) {m n : Nat} (hmn : m ≤ n) :
    Le (thm36C_level h a b hab ha spD m)
      (thm36C_level h a b hab ha spD n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero =>
      simpa using le_refl (thm36C_level h a b hab ha spD m)
  | succ d ih =>
      have hs : Le
          (thm36C_level h a b hab ha spD (m + d))
          (thm36C_level h a b hab ha spD ((m + d) + 1)) :=
        le_of_lt (thm36C_level_lt_succ h a b hab ha spD (m + d))
      have htrans := le_trans ih hs
      simpa [Nat.add_assoc, Nat.succ_eq_add_one] using htrans


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36D_ramp_eventually_zero {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (y : R)
    (hyt : COF.lt y (thm36C_t h a b hab ha spD)) :
    {N : Nat // ∀ n : Nat, N ≤ n →
      thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
        (thm36C_t h a b hab ha spD) y = 0} := by
  let W := thm36D_lt_limit_eventually
    (thm36C_level_tends h a b hab ha spD) hyt
  refine ⟨W.val, ?_⟩
  intro n hWn
  have hyun : Le y (thm36C_level h a b hab ha spD n) :=
    le_trans (le_of_lt W.property)
      (thm36D_level_mono h a b hab ha spD hWn)
  exact thm36A1_ramp_zero
    (thm36C_level h a b hab ha spD n)
    (thm36C_t h a b hab ha spD) y
    (thm36C_level_lt_t h a b hab ha spD n) hyun


/-- Technical lemma used in the public import closure. -/
theorem thm36D_ramp_always_one {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (y : R)
    (hty : Le (thm36C_t h a b hab ha spD) y) (n : Nat) :
    thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD) y = 1 :=
  thm36A1_ramp_one
    (thm36C_level h a b hab ha spD n)
    (thm36C_t h a b hab ha spD) y
    (thm36C_level_lt_t h a b hab ha spD n) hty


/-- Technical lemma used in the public import closure. -/
structure Thm36DPointData {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (x : X) where
  hDom : h.MemAt x
  hAbs : RSeq.SeriesSum (fun n => COF.abs (h.valueAt x hDom n))
  hSum : RSeq.SeriesSum (fun n => h.valueAt x hDom n)
  fDom : (thm36Cb_f h a b hab ha spD).MemAt x
  fSum : RSeq.SeriesSum
    (fun n => (thm36Cb_f h a b hab ha spD).valueAt x fDom n)
  ramp_tends : RSeq.TendstoHalf
    (fun n => thm_3_6_rampFn (thm36C_level h a b hab ha spD n)
      (thm36C_t h a b hab ha spD) hSum.sum)
    fSum.sum


/-- Technical lemma used in the public import closure. -/
structure Thm36DPointBridge {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) : Prop where
  point : ∀ x : X,
    ∀ fDom : (thm36Cb_f h a b hab ha spD).MemAt x,
    RSeq.SeriesSum
      (fun n => COF.abs
        ((thm36Cb_f h a b hab ha spD).valueAt x fDom n)) →
    Nonempty (Thm36DPointData h a b hab ha spD x)


/-- Technical lemma used in the public import closure. -/
theorem thm36D_point_classify {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (x : X)
    (D : Thm36DPointData h a b hab ha spD x) :
    (Le (thm36C_t h a b hab ha spD) D.hSum.sum ∧ D.fSum.sum = 1) ∨
    (COF.lt D.hSum.sum (thm36C_t h a b hab ha spD) ∧ D.fSum.sum = 0) := by
  rcases COF.lt_cotrans COFO.one_pos D.fSum.sum with hpos | hltOne
  · left
    have hty : Le (thm36C_t h a b hab ha spD) D.hSum.sum := by
      intro hyt
      let W := thm36D_ramp_eventually_zero
        h a b hab ha spD D.hSum.sum hyt
      have hz0 : D.fSum.sum = 0 :=
        thm36D_tendsto_eventually_const D.ramp_tends W.val W.property
      rw [hz0] at hpos
      exact COF.lt_irrefl _ hpos
    have hz1 : D.fSum.sum = 1 :=
      thm36D_tendsto_eventually_const D.ramp_tends 0
        (fun n _ => thm36D_ramp_always_one
          h a b hab ha spD D.hSum.sum hty n)
    exact ⟨hty, hz1⟩
  · right
    have hyt : COF.lt D.hSum.sum (thm36C_t h a b hab ha spD) := by
      let WN := thm36D_limit_lt_eventually D.ramp_tends hltOne
      exact thm36A1_ramp_lt_one_imp
        (thm36C_level h a b hab ha spD WN.val)
        (thm36C_t h a b hab ha spD)
        D.hSum.sum
        (thm36C_level_lt_t h a b hab ha spD WN.val)
        WN.property
    let W := thm36D_ramp_eventually_zero
      h a b hab ha spD D.hSum.sum hyt
    have hz0 : D.fSum.sum = 0 :=
      thm36D_tendsto_eventually_const D.ramp_tends W.val W.property
    exact ⟨hyt, hz0⟩


/-- Technical lemma used in the public import closure. -/
theorem thm36D_point_mem_union {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (x : X)
    (D : Thm36DPointData h a b hab ha spD x) :
    x ∈ thm36D_upperSet h (thm36C_t h a b hab ha spD) ∪
      thm36D_lowerSet h (thm36C_t h a b hab ha spD) := by
  rcases thm36D_point_classify h a b hab ha spD x D with hup | hlo
  · exact Or.inl ⟨D.hDom, D.hAbs, D.hSum, hup.1⟩
  · exact Or.inr ⟨D.hDom, D.hAbs, D.hSum, hlo.1⟩


/-- Technical lemma used in the public import closure. -/
theorem thm36D_upper_value {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (x : X)
    (D : Thm36DPointData h a b hab ha spD x)
    (hx : x ∈ thm36D_upperSet h (thm36C_t h a b hab ha spD))
    (hfDom : (thm36Cb_f h a b hab ha spD).MemAt x)
    (hf : RSeq.SeriesSum
      (fun n => (thm36Cb_f h a b hab ha spD).valueAt x hfDom n)) :
    hf.sum = 1 := by
  rcases hx with ⟨_hdom, _habs, hxsum, hle⟩
  have hsame : hxsum.sum = D.hSum.sum := seriesSum_unique hxsum D.hSum
  have hleD : Le (thm36C_t h a b hab ha spD) D.hSum.sum := by
    simpa [hsame] using hle
  have hz1 : D.fSum.sum = 1 :=
    thm36D_tendsto_eventually_const D.ramp_tends 0
      (fun n _ => thm36D_ramp_always_one
        h a b hab ha spD D.hSum.sum hleD n)
  calc
    hf.sum = D.fSum.sum := seriesSum_unique hf D.fSum
    _ = 1 := hz1


/-- Technical lemma used in the public import closure. -/
theorem thm36D_lower_value {S : IntSpaceRC X R}
    (h : IntegrableRep S) (a b : R) (hab : COF.lt a b)
    (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) (x : X)
    (D : Thm36DPointData h a b hab ha spD x)
    (hx : x ∈ thm36D_lowerSet h (thm36C_t h a b hab ha spD))
    (hfDom : (thm36Cb_f h a b hab ha spD).MemAt x)
    (hf : RSeq.SeriesSum
      (fun n => (thm36Cb_f h a b hab ha spD).valueAt x hfDom n)) :
    hf.sum = 0 := by
  rcases hx with ⟨_hdom, _habs, hxsum, hlt⟩
  have hsame : hxsum.sum = D.hSum.sum := seriesSum_unique hxsum D.hSum
  have hltD : COF.lt D.hSum.sum (thm36C_t h a b hab ha spD) := by
    simpa [hsame] using hlt
  let W := thm36D_ramp_eventually_zero
    h a b hab ha spD D.hSum.sum hltD
  have hz0 : D.fSum.sum = 0 :=
    thm36D_tendsto_eventually_const D.ramp_tends W.val W.property
  calc
    hf.sum = D.fSum.sum := seriesSum_unique hf D.fSum
    _ = 0 := hz0


/-- Technical lemma used in the public import closure. -/
theorem thm36D_isFull_mono {S : IntSpaceRC X R} {A B : Set X}
    (hA : IsFull S A) (hAB : A ⊆ B) : IsFull S B := by
  rcases hA with ⟨F, hF⟩
  exact ⟨F, fun x hx => hAB (hF hx)⟩


/-- Technical lemma used in the public import closure. -/
noncomputable def thm36D_integrableSet_of_bridge
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (B : Thm36DPointBridge h a b hab ha spD) :
    IntegrableSet1 S
      (thm36D_levelBSet h (thm36C_t h a b hab ha spD)) := by
  let f : IntegrableRep S := thm36Cb_f h a b hab ha spD
  have hsub : f.domain ⊆
      (thm36D_upperSet h (thm36C_t h a b hab ha spD) ∪
       thm36D_lowerSet h (thm36C_t h a b hab ha spD)) := by
    intro x hxdom
    obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxdom
    obtain ⟨D⟩ := B.point x (by simpa [f] using hfDom)
      (by simpa [f] using hfabs)
    exact thm36D_point_mem_union h a b hab ha spD x D
  refine {
    full := thm36D_isFull_mono (IntegrableRep.domain_isFull f) hsub
    rep := f
    valid := ?_
  }
  intro x hfDom hfabs
  obtain ⟨D⟩ := B.point x (by simpa [f] using hfDom)
    (by simpa [f] using hfabs)
  change
    (x ∈ thm36D_upperSet h (thm36C_t h a b hab ha spD) ∪
      thm36D_lowerSet h (thm36C_t h a b hab ha spD)) ∧
    (x ∈ thm36D_upperSet h (thm36C_t h a b hab ha spD) →
      ∀ hf : RSeq.SeriesSum (fun n => f.valueAt x hfDom n), hf.sum = 1) ∧
    (x ∈ thm36D_lowerSet h (thm36C_t h a b hab ha spD) →
      ∀ hf : RSeq.SeriesSum (fun n => f.valueAt x hfDom n), hf.sum = 0)
  refine ⟨thm36D_point_mem_union h a b hab ha spD x D, ?_, ?_⟩
  · intro hx hf
    exact thm36D_upper_value h a b hab ha spD x D hx
      (by simpa [f] using hfDom) (by simpa [f] using hf)
  · intro hx hf
    exact thm36D_lower_value h a b hab ha spD x D hx
      (by simpa [f] using hfDom) (by simpa [f] using hf)




/-! Technical auxiliary material for the public import closure. -/

theorem cellAt_rowsum_sum_eq {A : Nat → Nat → R} (hA : ∀ i j, Nonneg (A i j))
    (hflat : RSeq.SeriesSum (fun m => A (cellAt m).1 (cellAt m).2)) :
    (cellAt_rowsum hA hflat).sum = hflat.sum := by
  refine le_antisymm (cellAt_rowsum_le hA hflat) ?_
  refine le_of_tendsto_le hflat _ (fun N => ?_)
  have hNle : N ≤ N * N + 2 * N := by
    calc N ≤ N + (N * N + N) := Nat.le_add_right _ _
      _ = N * N + 2 * N := by ring
  have hmono : Le (RSeq.partialSum (fun m => A (cellAt m).1 (cellAt m).2) N)
      (RSeq.partialSum (fun m => A (cellAt m).1 (cellAt m).2) (N * N + 2 * N)) :=
    partialSum_mono (fun m => hA (cellAt m).1 (cellAt m).2) hNle
  rw [partialSum_cellAt_eq_gridSum A N] at hmono
  exact le_trans hmono
    (gridSum_le_T hA (fun i => row_seriesSum hA hflat i) (cellAt_rowsum hA hflat) N)



/-- Positive part used only in the signed-Fubini reduction. -/
def thm36D_pos (z : R) : R := COF.max z 0


/-- The positive part is non-negative. -/
theorem thm36D_pos_nonneg (z : R) : Nonneg (thm36D_pos z) := by
  exact COFO.max_zero_nonneg z


/-- The positive part is bounded by the absolute value. -/
theorem thm36D_pos_le_abs (z : R) : Le (thm36D_pos z) (COF.abs z) := by
  exact COFO.max_le_abs z


/-- The positive part of `-z` is also bounded by `|z|`. -/
theorem thm36D_negPos_le_abs (z : R) :
    Le (thm36D_pos (-z)) (COF.abs z) := by
  have h := COFO.max_le_abs (-z)
  simpa [thm36D_pos, COFO.abs_neg] using h


/-- Constructive Jordan decomposition at the scalar level. -/
theorem thm36D_pos_sub_negPos (z : R) :
    thm36D_pos z - thm36D_pos (-z) = z := by
  unfold thm36D_pos
  rw [COF.max_halfsum, COF.max_halfsum]
  simp only [add_zero, sub_zero, COFO.abs_neg]
  calc
    COF.half * (z + COF.abs z) -
        COF.half * (-z + COF.abs z) =
        (COF.half + COF.half) * z := by ring
    _ = 1 * z := by rw [COF.half_add_half]
    _ = z := by ring


/--
Canonical data supplied by signed Fubini.

`flatSigned` is the signed sum of the flattened sequence; `rowSigned i` is the
signed sum of row `i`; `rowsSigned` is the sum of those row sums; and
`rows_sum_eq` states that the two signed totals agree.
-/
structure Thm36DSignedFubiniData (A : Nat → Nat → R) where
  flatSigned : RSeq.SeriesSum
    (fun k => A (cellAt k).1 (cellAt k).2)
  rowAbs : ∀ i : Nat, RSeq.SeriesSum (fun j => COF.abs (A i j))
  rowSigned : ∀ i : Nat, RSeq.SeriesSum (A i)
  rowsSigned : RSeq.SeriesSum (fun i => (rowSigned i).sum)
  rows_sum_eq : rowsSigned.sum = flatSigned.sum


/--
Signed Fubini for the explicit shell enumeration `cellAt`.

The only hypothesis is absolute convergence of the flattened double sequence.
The non-negative theorem `cellAt_rowsum` is applied to `max(A,0)` and
`max(-A,0)`. Row and flattened signed sums are reconstructed by subtraction.
Finally uniqueness identifies the decomposed sums with the canonical sums from
absolute convergence.
-/
noncomputable def thm36D_signedFubini
    (A : Nat → Nat → R)
    (habs : RSeq.SeriesSum
      (fun k => COF.abs (A (cellAt k).1 (cellAt k).2))) :
    Thm36DSignedFubiniData A := by
  let flatPos : RSeq.SeriesSum
      (fun k => thm36D_pos (A (cellAt k).1 (cellAt k).2)) :=
    seriesSum_comparison
      (fun k => thm36D_pos_nonneg (A (cellAt k).1 (cellAt k).2))
      (fun k => thm36D_pos_le_abs (A (cellAt k).1 (cellAt k).2))
      habs

  let flatNeg : RSeq.SeriesSum
      (fun k => thm36D_pos (-(A (cellAt k).1 (cellAt k).2))) :=
    seriesSum_comparison
      (fun k => thm36D_pos_nonneg (-(A (cellAt k).1 (cellAt k).2)))
      (fun k => thm36D_negPos_le_abs (A (cellAt k).1 (cellAt k).2))
      habs

  let rowAbs : ∀ i : Nat,
      RSeq.SeriesSum (fun j => COF.abs (A i j)) :=
    fun i => row_seriesSum
      (fun p q => abs_nonneg (A p q)) habs i

  let rowSigned : ∀ i : Nat, RSeq.SeriesSum (A i) :=
    fun i => seriesSum_of_abs (rowAbs i)

  let rowsAbsMajorant : RSeq.SeriesSum
      (fun i => (rowAbs i).sum) :=
    cellAt_rowsum (fun p q => abs_nonneg (A p q)) habs

  let rowsAbsOfSignedSums : RSeq.SeriesSum
      (fun i => COF.abs (rowSigned i).sum) :=
    seriesSum_comparison
      (fun i => abs_nonneg (rowSigned i).sum)
      (fun i => seriesSum_abs_le (rowSigned i) (rowAbs i))
      rowsAbsMajorant

  let rowsSigned : RSeq.SeriesSum
      (fun i => (rowSigned i).sum) :=
    seriesSum_of_abs rowsAbsOfSignedSums

  let flatSigned : RSeq.SeriesSum
      (fun k => A (cellAt k).1 (cellAt k).2) :=
    seriesSum_of_abs habs

  let rowPos : ∀ i : Nat,
      RSeq.SeriesSum (fun j => thm36D_pos (A i j)) :=
    fun i => row_seriesSum
      (fun p q => thm36D_pos_nonneg (A p q)) flatPos i

  let rowNeg : ∀ i : Nat,
      RSeq.SeriesSum (fun j => thm36D_pos (-(A i j))) :=
    fun i => row_seriesSum
      (fun p q => thm36D_pos_nonneg (-(A p q))) flatNeg i

  let rowsPos : RSeq.SeriesSum (fun i => (rowPos i).sum) :=
    cellAt_rowsum
      (fun p q => thm36D_pos_nonneg (A p q)) flatPos

  let rowsNeg : RSeq.SeriesSum (fun i => (rowNeg i).sum) :=
    cellAt_rowsum
      (fun p q => thm36D_pos_nonneg (-(A p q))) flatNeg

  let rowDecomp : ∀ i : Nat, RSeq.SeriesSum (A i) := fun i =>
    seriesSum_congr
      (fun j => by
        calc
          thm36D_pos (A i j) + (-1 : R) * thm36D_pos (-(A i j)) =
              thm36D_pos (A i j) - thm36D_pos (-(A i j)) := by ring
          _ = A i j := thm36D_pos_sub_negPos (A i j))
      (seriesSum_add (rowPos i) (seriesSum_smul (-1) (rowNeg i)))

  let rowsDecomp0 : RSeq.SeriesSum
      (fun i => (rowPos i).sum + (-1 : R) * (rowNeg i).sum) :=
    seriesSum_add rowsPos (seriesSum_smul (-1) rowsNeg)

  let rowsDecomp : RSeq.SeriesSum (fun i => (rowDecomp i).sum) :=
    seriesSum_congr (fun i => by rfl) rowsDecomp0

  let rowsCanonical : RSeq.SeriesSum
      (fun i => (rowSigned i).sum) :=
    seriesSum_congr
      (fun i => seriesSum_unique (rowDecomp i) (rowSigned i))
      rowsDecomp

  let flatDecomp : RSeq.SeriesSum
      (fun k => A (cellAt k).1 (cellAt k).2) :=
    seriesSum_congr
      (fun k => by
        calc
          thm36D_pos (A (cellAt k).1 (cellAt k).2) +
              (-1 : R) * thm36D_pos (-(A (cellAt k).1 (cellAt k).2)) =
              thm36D_pos (A (cellAt k).1 (cellAt k).2) -
                thm36D_pos (-(A (cellAt k).1 (cellAt k).2)) := by ring
          _ = A (cellAt k).1 (cellAt k).2 :=
            thm36D_pos_sub_negPos (A (cellAt k).1 (cellAt k).2))
      (seriesSum_add flatPos (seriesSum_smul (-1) flatNeg))

  have hPos : rowsPos.sum = flatPos.sum :=
    cellAt_rowsum_sum_eq (fun p q => thm36D_pos_nonneg (A p q)) flatPos
  have hNeg : rowsNeg.sum = flatNeg.sum :=
    cellAt_rowsum_sum_eq (fun p q => thm36D_pos_nonneg (-(A p q))) flatNeg
  have hrows_decomp_flat : rowsDecomp.sum = flatDecomp.sum := by
    show rowsPos.sum + (-1 : R) * rowsNeg.sum
        = flatPos.sum + (-1 : R) * flatNeg.sum
    rw [hPos, hNeg]

  have hrows : rowsSigned.sum = rowsCanonical.sum :=
    seriesSum_unique rowsSigned rowsCanonical

  have hcanonical : rowsCanonical.sum = rowsDecomp.sum := by
    rfl

  have hflat : flatDecomp.sum = flatSigned.sum :=
    seriesSum_unique flatDecomp flatSigned

  exact {
    flatSigned := flatSigned
    rowAbs := rowAbs
    rowSigned := rowSigned
    rowsSigned := rowsSigned
    rows_sum_eq := hrows.trans (hcanonical.trans
      (hrows_decomp_flat.trans hflat))
  }


/-! ## 2. Backward extraction through the Cβ-v2 representation -/

/-- Recover every original component domain from a collapsed representative. -/
theorem thm36D_collapseFirst_dom {S : IntSpaceRC X R}
    {r : IntegrableRep S} {x : X}
    (N : Nat) (hd : (r.collapseFirst N).MemAt x) : r.MemAt x := by
  intro m
  by_cases hm : m ≤ N
  · have hzero := hd 0
    have hsum : x ∈ (BFunR.seqSum r.fn N).dom := by
      simpa [IntegrableRep.collapseFirst] using hzero
    exact mem_seqSum_dom_le hsum m hm
  · have hkpos : m - N ≠ 0 := by omega
    have hk := hd (m - N)
    have hindex : N + (m - N) = m := by omega
    simpa [IntegrableRep.collapseFirst, hkpos, hindex] using hk

/-- Cancel a positive scalar from an absolutely convergent scaled series. -/
noncomputable def thm36D_absSeries_of_pos_smul
    (c : R) (hc : COF.lt 0 c) (u : Nat → R)
    (hscaled : RSeq.SeriesSum (fun n => COF.abs (c * u n))) :
    RSeq.SeriesSum (fun n => COF.abs (u n)) := by
  let hc_nonneg : Nonneg c := le_of_lt hc
  let hmul : RSeq.SeriesSum (fun n => c * COF.abs (u n)) :=
    seriesSum_congr
      (fun n => by
        rw [COFO.abs_mul, COFO.abs_of_nonneg hc_nonneg])
      hscaled
  let hinv := seriesSum_smul (COFO.inv c) hmul
  exact seriesSum_congr
    (fun n => by
      calc
        COFO.inv c * (c * COF.abs (u n)) =
            (c * COFO.inv c) * COF.abs (u n) := by ring
        _ = 1 * COF.abs (u n) := by rw [COFO.mul_inv_cancel hc]
        _ = COF.abs (u n) := by ring)
    hinv


/--
Recover absolute convergence of `h` from absolute convergence of the zeroth
ramp. `cutConstVal_absSeries` exposes the pre-cut middle lane; positive-scalar
cancellation exposes `h.sub (...)`; the even interleave lane is `h`.
-/
theorem thm36D_hDom_of_ramp0Dom
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (spD : Thm36BSmoothPointData h a b hab ha)
    {x : X}
    (hrampDom : (thm36C_ramp h a b hab ha spD 0).MemAt x) :
    h.MemAt x := by
  let u : R := thm36C_level h a b hab ha spD 0
  let t : R := thm36C_t h a b hab ha spD
  let hu : Nonneg u := thm36C_level_nonneg h a b hab ha spD 0
  let c : R := COFO.inv (t - u)
  let r : IntegrableRep S := h.sub (h.cutConstVal u hu)
  let q : IntegrableRep S := IntegrableRep.smul c r
  let hOne : Nonneg (1 : R) := le_of_lt COFO.one_pos
  let hcutDom : (q.cutConstVal 1 hOne).MemAt x := by
    simpa [thm36C_ramp, thm_3_6_ramp_comp, u, t, hu, c, r, q]
      using hrampDom
  let hqDom : q.MemAt x := q.cutConstVal_base_memAt 1 hOne hcutDom
  let hrDom : r.MemAt x := smul_dom hqDom
  exact add_dom_left hrDom

noncomputable def thm36D_hAbs_of_ramp0Abs
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (x : X)
    (hrampDom : (thm36C_ramp h a b hab ha spD 0).MemAt x)
    (hramp : RSeq.SeriesSum
      (fun n => COF.abs
        ((thm36C_ramp h a b hab ha spD 0).valueAt x hrampDom n))) :
    RSeq.SeriesSum (fun n => COF.abs
      (h.valueAt x (thm36D_hDom_of_ramp0Dom h a b hab ha spD hrampDom) n)) := by
  let u : R := thm36C_level h a b hab ha spD 0
  let t : R := thm36C_t h a b hab ha spD
  let hu : Nonneg u := thm36C_level_nonneg h a b hab ha spD 0
  let hut : COF.lt u t := thm36C_level_lt_t h a b hab ha spD 0
  let c : R := COFO.inv (t - u)
  let r : IntegrableRep S := h.sub (h.cutConstVal u hu)
  let q : IntegrableRep S := IntegrableRep.smul c r
  let hOne : Nonneg (1 : R) :=
    fun h10 => COF.lt_irrefl (0 : R) (COFO.lt_trans COFO.one_pos h10)

  let hcutDom : (q.cutConstVal 1 hOne).MemAt x := by
    simpa [thm36C_ramp, thm_3_6_ramp_comp, u, t, hu, c, r, q]
      using hrampDom
  let hcut : RSeq.SeriesSum
      (fun n => COF.abs ((q.cutConstVal 1 hOne).valueAt x hcutDom n)) := by
    simpa [thm36C_ramp, thm_3_6_ramp_comp, u, t, c, r, q]
      using hramp

  let hqDom : q.MemAt x := q.cutConstVal_base_memAt 1 hOne hcutDom
  let hq : RSeq.SeriesSum
      (fun n => COF.abs (q.valueAt x hqDom n)) :=
    cutConstVal_absSeriesSum_mid 1 hOne hcutDom hcut

  let hrDom : r.MemAt x := smul_dom hqDom
  let hscaled : RSeq.SeriesSum
      (fun n => COF.abs (c * r.valueAt x hrDom n)) :=
    seriesSum_congr (fun n => by rfl) hq

  have htu : COF.lt 0 (t - u) := thm36A1_sub_pos_of_lt hut
  have hc : COF.lt 0 c := COFO.inv_pos htu

  let hr : RSeq.SeriesSum
      (fun n => COF.abs (r.valueAt x hrDom n)) :=
    thm36D_absSeries_of_pos_smul c hc
      (fun n => r.valueAt x hrDom n) hscaled

  exact add_absSeriesSum_left hrDom hr


/-- Undo the zeroth `collapseFirst` and recover the original ramp abs-series. -/
theorem thm36D_ramp0Dom_of_term0Dom
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (spD : Thm36BSmoothPointData h a b hab ha)
    {x : X} (htermDom : (thm36Cb_term h a b hab ha spD 0).MemAt x) :
    (thm36C_ramp h a b hab ha spD 0).MemAt x := by
  let s0 : IntegrableRep S := thm36Cb_signedTerm h a b hab ha spD 0
  let N : Nat := s0.contNf 0
  have hs0Dom : s0.MemAt x := by
    apply thm36D_collapseFirst_dom N
    simpa [thm36Cb_term, s0, N] using htermDom
  simpa [s0, thm36Cb_signedTerm] using hs0Dom

noncomputable def thm36D_ramp0Abs_of_term0Abs
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (x : X)
    (htermDom : (thm36Cb_term h a b hab ha spD 0).MemAt x)
    (hterm : RSeq.SeriesSum
      (fun n => COF.abs
        ((thm36Cb_term h a b hab ha spD 0).valueAt x htermDom n))) :
    RSeq.SeriesSum
      (fun n => COF.abs ((thm36C_ramp h a b hab ha spD 0).valueAt x
        (thm36D_ramp0Dom_of_term0Dom h a b hab ha spD htermDom) n)) := by
  let s0 : IntegrableRep S := thm36Cb_signedTerm h a b hab ha spD 0
  let N : Nat := s0.contNf 0
  let hs0Dom : s0.MemAt x := by
    apply thm36D_collapseFirst_dom N
    simpa [thm36Cb_term, s0, N] using htermDom
  let hrampDom : (thm36C_ramp h a b hab ha spD 0).MemAt x := by
    simpa [s0, thm36Cb_signedTerm] using hs0Dom
  let htail0 := seriesSum_tail hterm 0
  let htailRamp : RSeq.SeriesSum
      (fun k => COF.abs
        ((thm36C_ramp h a b hab ha spD 0).valueAt x hrampDom (N + 1 + k))) :=
    seriesSum_congr
      (fun k => by
        simp [IntegrableRep.valueAt, thm36Cb_term, thm36Cb_signedTerm,
          IntegrableRep.collapseFirst, s0, N, Nat.add_assoc])
      htail0
  exact seriesSum_of_tail N htailRamp


/-- Normalize `thm36Cb_f` abs convergence to its explicit `cellAt` flattening. -/
theorem thm36D_f_row_memAt
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (spD : Thm36BSmoothPointData h a b hab ha)
    {x : X} (hfDom : (thm36Cb_f h a b hab ha spD).MemAt x)
    (i : Nat) : (thm36Cb_term h a b hab ha spD i).MemAt x := by
  simpa [thm36Cb_f] using
    (seriesIntegrable_row_memAt
      (thm36Cb_term h a b hab ha spD)
      (thm36Cb_termAbsSeries h a b hab ha spD) hfDom i)

noncomputable def thm36D_fAbs_flat
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (x : X) (hfDom : (thm36Cb_f h a b hab ha spD).MemAt x)
    (hfabs : RSeq.SeriesSum
      (fun k => COF.abs
        ((thm36Cb_f h a b hab ha spD).valueAt x hfDom k))) :
    RSeq.SeriesSum
      (fun k => COF.abs
        ((thm36Cb_term h a b hab ha spD (cellAt k).1).valueAt x
          (thm36D_f_row_memAt h a b hab ha spD hfDom (cellAt k).1)
          (cellAt k).2)) := by
  simpa [thm36Cb_f, seriesIntegrable, IntegrableRep.valueAt] using hfabs


/-- Normalize the signed value series of `thm36Cb_f` to the same flattening. -/
noncomputable def thm36D_fSigned_flat
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha)
    (x : X) (hfDom : (thm36Cb_f h a b hab ha spD).MemAt x)
    (hf : RSeq.SeriesSum
      (fun k => (thm36Cb_f h a b hab ha spD).valueAt x hfDom k)) :
    RSeq.SeriesSum
      (fun k => (thm36Cb_term h a b hab ha spD (cellAt k).1).valueAt x
        (thm36D_f_row_memAt h a b hab ha spD hfDom (cellAt k).1)
        (cellAt k).2) := by
  simpa [thm36Cb_f, seriesIntegrable, IntegrableRep.valueAt] using hf


/-! ## 3. Final bridge -/

/--
The Cβ-v2 point bridge. Generic signed Fubini identifies the flattened signed
value with the outer sum of signed rows; the existing Cβ telescope then gives
the required ramp limit.
-/
noncomputable def thm36D_pointBridge
    {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a) (spD : Thm36BSmoothPointData h a b hab ha) :
    Thm36DPointBridge h a b hab ha spD := {
  point := by
    intro x hfDom hfabs

    let hflatAbs := thm36D_fAbs_flat h a b hab ha spD x hfDom hfabs

    let F := thm36D_signedFubini
      (fun i j => (thm36Cb_term h a b hab ha spD i).valueAt x
        (thm36D_f_row_memAt h a b hab ha spD hfDom i) j)
      hflatAbs

    let hterm0Dom := thm36D_f_row_memAt h a b hab ha spD hfDom 0
    let hramp0Abs := thm36D_ramp0Abs_of_term0Abs
      h a b hab ha spD x hterm0Dom (F.rowAbs 0)

    let hramp0Dom := thm36D_ramp0Dom_of_term0Dom
      h a b hab ha spD hterm0Dom
    let hAbs := thm36D_hAbs_of_ramp0Abs
      h a b hab ha spD x hramp0Dom hramp0Abs

    let hDom := thm36D_hDom_of_ramp0Dom h a b hab ha spD hramp0Dom
    let hSum := seriesSum_of_abs hAbs
    let fSum := seriesSum_of_abs hfabs
    let fSumFlat := thm36D_fSigned_flat h a b hab ha spD x hfDom fSum

    let rowValue : ∀ n : Nat,
        RSeq.SeriesSum
          (fun j => (thm36Cb_term h a b hab ha spD n).valueAt x
            (thm36D_f_row_memAt h a b hab ha spD hfDom n) j) :=
      fun n => (thm36Cb_term_value_witness
        h a b hab ha spD n x hDom hSum).val

    let rowTotals : RSeq.SeriesSum
        (fun n => (rowValue n).sum) :=
      seriesSum_congr
        (fun n => seriesSum_unique (F.rowSigned n) (rowValue n))
        F.rowsSigned

    have hrowTotal : rowTotals.sum = fSum.sum := by
      calc
        rowTotals.sum = F.rowsSigned.sum := by rfl
        _ = F.flatSigned.sum := F.rows_sum_eq
        _ = fSumFlat.sum := seriesSum_unique F.flatSigned fSumFlat
        _ = fSum.sum := by rfl

    let rampTends : RSeq.TendstoHalf
        (fun n => thm_3_6_rampFn
          (thm36C_level h a b hab ha spD n)
          (thm36C_t h a b hab ha spD) hSum.sum)
        fSum.sum := {
      mod := rowTotals.tends.mod
      close := by
        intro k n hn
        have hc := rowTotals.tends.close k n hn
        rw [(thm36C_integrableData h a b hab ha spD).point_partial_sum
              x hDom hSum n,
            hrowTotal] at hc
        exact hc
    }

    exact ⟨{
      hDom := hDom
      hAbs := hAbs
      hSum := hSum
      fDom := hfDom
      fSum := fSum
      ramp_tends := rampTends
    }⟩
}


/-! Technical auxiliary material for the public import closure. -/
















/-! Technical auxiliary material for the public import closure. -/














/-- Technical lemma used in the public import closure. -/
noncomputable def thm_3_6_forall_apart_measure {S : IntSpaceRC X R} (h : IntegrableRep S)
    (a b : R) (hab : COF.lt a b) (ha : COF.lt 0 a)
    (t : R) (hat : COF.lt a t) (htb : COF.lt t b)
    (hT : ∀ n, COF.lt 0
      (COF.abs (t - lemma35_exceptionSeq (thm36A2_profile h a b hab ha) n))) :
    Σ' (hA : IntegrableSet1 S (thm36D_levelBSet h t)),
      measure1 S hA = thm36C_lambdaBar h a b hab ha
        (thm36B_smoothPointData_of_apart h a b hab ha t hat htb hT) :=
  let spd := thm36B_smoothPointData_of_apart h a b hab ha t hat htb hT
  let hA : IntegrableSet1 S (thm36D_levelBSet h t) :=
    thm36D_integrableSet_of_bridge h a b hab ha spd (thm36D_pointBridge h a b hab ha spd)
  ⟨hA, thm36Cb_f_integral h a b hab ha spd⟩


/-! Technical auxiliary material for the public import closure. -/












/-! Technical auxiliary material for the public import closure. -/






















end BishopC
