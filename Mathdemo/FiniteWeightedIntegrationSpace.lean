import Mathdemo.DiracIntegrationSpace

/-!
# Finitely many points as an integration space

`Mathdemo.DiracIntegrationSpace` gives the normalized model with a single point.
This file gives the finite generalization: a list of points `pts 0, …, pts N`
(repetition allowed) with

* `L`  = the partial functions defined at every listed point, and
* `I f = Σ_{i ≤ N} f (pts i)`.

Repetition realizes integer multiplicities: listing a point `k` times gives it
multiplicity `k`.  Clause (3) asks only that *some* `p ∈ L` satisfy `I p = 1`;
it does not rescale `I`.  That clause is discharged here by the constant
function with value `m⁻¹`, where `m = N + 1` is the number of slots, since the
`m` copies of `m⁻¹` sum to `1`.  The functional itself stays the unscaled sum,
so the integral of a characteristic function counts the listed points the set
contains: an integer between `0` and `m`, and not a weight of the form `k/m`.
The instance provided in the middle of the file (`twoPointDef11`) is the
two-slot case with the constant `1/2 = eps 1`, for which the normalization
identity `eps 1 + eps 1 = eps 0 = 1` is already in the development.

On a general `X` nothing forces the two slots of `twoPointDef11 x₀ x₁` to be
distinct — this interface carries no apartness structure on `X` — so if
`x₀ = x₁` the functional is twice the evaluation at `x₀`.  The `Bool` section at
the end of the file removes that possibility and is what certifies that the
axioms admit a model which is not a point mass.

The mathematical content beyond the Dirac model is clause (2).  For a single
point the continuity clause is the identity; for several points it requires
*choosing* a point at which the series stays below the function, given only
that the *sums* compare.  Constructively this is the cotransitivity of the
strict order, applied along the finite sum, together with the comparison test
for series with nonnegative terms — both available in the development
(`regularSeqLtData_cotrans`, upgraded from the `Prop`-valued hypothesis by
`BishopSec3P.regularSeqLtData_of_ltPropC`, and `repSeriesSum_comparison`).
No choice is used anywhere; the point is *computed* from the strict
inequality's positivity witness.

Both limits of clause (4) reduce to the finite sum of the single-point limits
proved for the Dirac model, combined by `repSeriesTendsto_finSumC`.
-/

namespace BishopCheng

open BishopCReal BishopSec1P

universe u

variable {X : Type u}

/-! ## Representative-layer helpers

Small lemmas about `addSeq` and `regularSeqFinSum` that the model needs and
that the development states either for all indices or not at all.  The
`_upto` variants matter because membership hypotheses are only available at
the listed points `i ≤ N`. -/

/-- Rearrangement `(p+q)+(r+s) ≈ (p+r)+(q+s)` over the implementation setoid. -/
theorem addSeq_add_add_swap_eventually (p q r s : CReal) :
    relEventually (addSeq (addSeq p q) (addSeq r s))
      (addSeq (addSeq p r) (addSeq q s)) := by
  have h1 := addSeq_assoc_eventually p q (addSeq r s)
  have h2a : relEventually (addSeq q (addSeq r s)) (addSeq (addSeq q r) s) :=
    relEventually_symm _ _ (addSeq_assoc_eventually q r s)
  have h2b : relEventually (addSeq (addSeq q r) s) (addSeq (addSeq r q) s) :=
    addSeq_respects_eventually _ _ _ _
      (addSeq_comm_eventually q r) (relEventually_refl s)
  have h2c := addSeq_assoc_eventually r q s
  have h2 : relEventually (addSeq q (addSeq r s)) (addSeq r (addSeq q s)) :=
    relEventually_trans _ _ _ h2a (relEventually_trans _ _ _ h2b h2c)
  have h3 : relEventually (addSeq p (addSeq q (addSeq r s)))
      (addSeq p (addSeq r (addSeq q s))) :=
    addSeq_respects_eventually _ _ _ _ (relEventually_refl p) h2
  have h4 : relEventually (addSeq p (addSeq r (addSeq q s)))
      (addSeq (addSeq p r) (addSeq q s)) :=
    relEventually_symm _ _ (addSeq_assoc_eventually p r (addSeq q s))
  exact relEventually_trans _ _ _ h1 (relEventually_trans _ _ _ h3 h4)

/-- Termwise congruence of finite sums, from congruence at the used indices. -/
theorem regularSeqFinSum_congr_eventually_upto {u v : Nat → CReal} :
    ∀ N : Nat, (∀ j, j ≤ N → relEventually (u j) (v j)) →
      relEventually (regularSeqFinSum u N) (regularSeqFinSum v N)
  | 0, h => h 0 (Nat.le_refl 0)
  | N + 1, h =>
      addSeq_respects_eventually _ _ _ _
        (regularSeqFinSum_congr_eventually_upto N
          (fun j hj => h j (Nat.le_succ_of_le hj)))
        (h (N + 1) (Nat.le_refl _))

/-- A finite sum of termwise sums is the sum of the finite sums. -/
theorem regularSeqFinSum_add_termwise (u v : Nat → CReal) :
    ∀ N : Nat,
      relEventually (regularSeqFinSum (fun i => addSeq (u i) (v i)) N)
        (addSeq (regularSeqFinSum u N) (regularSeqFinSum v N))
  | 0 => relEventually_refl _
  | N + 1 =>
      relEventually_trans _ _ _
        (addSeq_respects_eventually _ _ _ _
          (regularSeqFinSum_add_termwise u v N)
          (relEventually_refl (addSeq (u (N + 1)) (v (N + 1)))))
        (addSeq_add_add_swap_eventually
          (regularSeqFinSum u N) (regularSeqFinSum v N) (u (N + 1)) (v (N + 1)))

/-- Nonnegativity of a finite sum, from nonnegativity at the used indices. -/
theorem regularSeqFinSum_nonneg_upto {u : Nat → CReal} :
    ∀ N : Nat, (∀ j, j ≤ N → RegularSeqNonneg (u j)) →
      RegularSeqNonneg (regularSeqFinSum u N)
  | 0, hu => hu 0 (Nat.le_refl 0)
  | N + 1, hu =>
      regularSeqNonneg_add
        (regularSeqFinSum_nonneg_upto N (fun j hj => hu j (Nat.le_succ_of_le hj)))
        (hu (N + 1) (Nat.le_refl _))

/-- Each term of a finite sum of nonnegative terms is at most the sum. -/
theorem le_regularSeqFinSum_of_nonneg_upto {u : Nat → CReal} :
    ∀ N : Nat, (∀ j, j ≤ N → RegularSeqNonneg (u j)) →
      ∀ i : Nat, i ≤ N → RegularSeqLe (u i) (regularSeqFinSum u N)
  | 0, _, i, hi => by
      have h0 : i = 0 := Nat.le_zero.mp hi
      subst h0
      exact regularSeqLe_refl (u 0)
  | N + 1, hu, i, hi => by
      have hnnN : RegularSeqNonneg (regularSeqFinSum u N) :=
        regularSeqFinSum_nonneg_upto N (fun j hj => hu j (Nat.le_succ_of_le hj))
      rcases Nat.eq_or_lt_of_le hi with heq | hlt
      · subst heq
        refine regularSeqLe_of_left_eventual
          (relEventually_symm _ _ (addSeq_zero_left_eventually (u (N + 1)))) ?_
        exact regularSeqLe_add (regularSeqLe_zero_of_nonneg hnnN)
          (regularSeqLe_refl (u (N + 1)))
      · have hiN : i ≤ N := Nat.lt_succ_iff.mp hlt
        refine regularSeqLe_trans
          (le_regularSeqFinSum_of_nonneg_upto N
            (fun j hj => hu j (Nat.le_succ_of_le hj)) i hiN) ?_
        refine regularSeqLe_of_left_eventual
          (relEventually_symm _ _ (CReal.add_zero (regularSeqFinSum u N))) ?_
        exact regularSeqLe_add (regularSeqLe_refl (regularSeqFinSum u N))
          (regularSeqLe_zero_of_nonneg (hu (N + 1) (Nat.le_refl _)))

/-! ## Strict order: data, cancellation, and the descent along a finite sum -/

/-- Forgetting the witness of a data-valued strict inequality. -/
theorem regularSeqLtProp_of_ltData {x y : CReal}
    (h : regularSeqLtData x y) : regularSeqLtProp x y :=
  h.toProp

/-- Strict cancellation of a common right summand: `a+c < b+c → a < b`. -/
theorem regularSeqLtProp_add_cancel_right {a b c : CReal}
    (h : regularSeqLtProp (addSeq a c) (addSeq b c)) :
    regularSeqLtProp a b := by
  have hsub : ∀ x : CReal,
      relEventually (CReal.sub x (CReal.neg c)) (addSeq x c) := fun x =>
    relEventually_trans _ _ _
      (subSeq_eq_add_neg_eventually x (CReal.neg c))
      (addSeq_respects_eventually _ _ _ _ (relEventually_refl x)
        (negSeq_negSeq_eventually c))
  refine BishopSec3P.regularSeqLtProp_add_sub_cancel_rightC (z := CReal.neg c) ?_
  exact regularSeqLtProp_of_left_eventual (hsub a)
    (regularSeqLtProp_of_right_eventual
      (relEventually_symm _ _ (hsub b)) h)

/-- Strict cancellation of a common left summand: `c+a < c+b → a < b`. -/
theorem regularSeqLtProp_add_cancel_left {a b c : CReal}
    (h : regularSeqLtProp (addSeq c a) (addSeq c b)) :
    regularSeqLtProp a b :=
  regularSeqLtProp_add_cancel_right
    (regularSeqLtProp_of_left_eventual (addSeq_comm_eventually a c)
      (regularSeqLtProp_of_right_eventual (addSeq_comm_eventually c b) h))

/-- **The descent.**  From a strict inequality between two finite sums, compute
an index at which the terms compare strictly.  The choice of index is made by
the data-valued cotransitivity of the strict order; the `Prop`-valued
hypothesis produced by each cancellation step is upgraded back to data by the
choice-free strong-gauge extraction of the development. -/
def regularSeqFinSum_lt_pick {u v : Nat → CReal} :
    ∀ N : Nat,
      regularSeqLtData (regularSeqFinSum u N) (regularSeqFinSum v N) →
      Σ' i : Nat, i ≤ N ∧ regularSeqLtProp (u i) (v i)
  | 0, h => ⟨0, Nat.le_refl 0, regularSeqLtProp_of_ltData h⟩
  | N + 1, h =>
      match regularSeqLtData_cotrans _ _
          (addSeq (regularSeqFinSum u N) (v (N + 1))) h with
      | PSum.inl hl =>
          ⟨N + 1, Nat.le_refl _,
            regularSeqLtProp_add_cancel_left (regularSeqLtProp_of_ltData hl)⟩
      | PSum.inr hr =>
          match regularSeqFinSum_lt_pick N
              (BishopSec3P.regularSeqLtData_of_ltPropC
                (regularSeqLtProp_add_cancel_right
                  (regularSeqLtProp_of_ltData hr))) with
          | ⟨i, hiN, hlt⟩ => ⟨i, Nat.le_succ_of_le hiN, hlt⟩

/-! ## Series: the finite sum of pointwise series -/

/-- A finite sum of convergent series, as a convergent series. -/
def repSeriesSum_finSum {a : Nat → Nat → CReal}
    (S : ∀ i : Nat, RepSeriesSum (fun n => a i n)) :
    ∀ N : Nat, RepSeriesSum (fun n => regularSeqFinSum (fun i => a i n) N)
  | 0 => S 0
  | N + 1 => repSeriesSum_add (repSeriesSum_finSum S N) (S (N + 1))

/-- The sum of the combined series is the finite sum of the sums. -/
theorem repSeriesSum_finSum_sum_eq {a : Nat → Nat → CReal}
    (S : ∀ i : Nat, RepSeriesSum (fun n => a i n)) :
    ∀ N : Nat,
      (repSeriesSum_finSum S N).sum
        = regularSeqFinSum (fun i => (S i).sum) N
  | 0 => rfl
  | N + 1 => by
      show (repSeriesSum_add (repSeriesSum_finSum S N) (S (N + 1))).sum = _
      show addSeq (repSeriesSum_finSum S N).sum ((S (N + 1)).sum) = _
      rw [repSeriesSum_finSum_sum_eq S N]
      rfl

/-! ## The model -/

/-- The partial functions defined at every listed point. -/
def finPtsL (pts : Nat → X) (N : Nat) : Set (BFunC X) :=
  {f | ∀ i, i ≤ N → pts i ∈ f.dom}

/-- The value of `f` at the `i`-th listed point.  The membership witness is
available only for `i ≤ N`, so the index is clamped with `min i N`; this is
harmless because `regularSeqFinSum u N` reads `u i` only for `i ≤ N`, where
`min i N = i`. -/
def finPtsEval (pts : Nat → X) (N : Nat) {f : BFunC X}
    (hf : f ∈ finPtsL pts N) (i : Nat) : CReal :=
  f.toFun (pts (min i N)) (hf (min i N) (Nat.min_le_right i N))

/-- `finPtsEval` already clamps its index, so clamping again changes nothing.
This is what lets a bound proved for `i ≤ N` be used at an arbitrary `i`. -/
theorem finPtsEval_min (pts : Nat → X) (N : Nat) {f : BFunC X}
    (hf : f ∈ finPtsL pts N) (i : Nat) :
    finPtsEval pts N hf (min i N) = finPtsEval pts N hf i := by
  have h : min (min i N) N = min i N := by omega
  simp only [finPtsEval, h]

/-- The sum of the values at the listed points.  A point listed `k` times
contributes with weight `k`. -/
def finPtsI (pts : Nat → X) (N : Nat) (f : BFunC X)
    (hf : f ∈ finPtsL pts N) : CReal :=
  regularSeqFinSum (finPtsEval pts N hf) N

set_option maxHeartbeats 1000000 in
/-- **Finitely many points are an integration space in the sense of
Definition 1.1**, given the normalizing constant: a `c` whose `N + 1`-fold sum
is `1`. -/
noncomputable def finPtsDef11 (pts : Nat → X) (N : Nat) (c : CReal)
    (hnorm : relEventually
      (regularSeqFinSum (fun _ : Nat => c) N) oneSeq) :
    IntegrationSpaceDef11 X where
  inhabited := pts 0
  L := finPtsL pts N
  I := finPtsI pts N
  L_resp := by
    intro f g hf hfg i hi
    show pts i ∈ g.dom
    rw [← hfg.1]
    exact hf i hi
  I_resp := by
    intro f g hf hfg
    refine regularSeqFinSum_congr_eventually_upto N (fun j hj => ?_)
    show relEventually (finPtsEval pts N hf j) (finPtsEval pts N (_ : g ∈ finPtsL pts N) j)
    simpa [finPtsEval, Nat.min_eq_left hj] using hfg.2 (pts j) (hf j hj)
  lin_mem := by
    intro α β f g hf hg i hi
    exact ⟨hf i hi, hg i hi⟩
  abs_mem := by
    intro f hf
    exact hf
  cutOne_mem := by
    intro f hf
    exact hf
  I_lin := by
    intro α β f g _hf _hg
    have h1 := regularSeqFinSum_add_termwise
      (fun i => CReal.mul α (finPtsEval pts N _hf i))
      (fun i => CReal.mul β (finPtsEval pts N _hg i)) N
    have h2 := addSeq_respects_eventually _ _ _ _
      (BishopRegularSeqSeriesSum.regularSeqFinSum_mulSeq α
        (finPtsEval pts N _hf) N)
      (BishopRegularSeqSeriesSum.regularSeqFinSum_mulSeq β
        (finPtsEval pts N _hg) N)
    exact relEventually_trans _ _ _ h1 h2
  continuity := by
    intro f fs hf hfs hnn hI hlt
    have hmem : ∀ (n i : Nat), pts (min i N) ∈ (fs n).dom :=
      fun n i => hfs n (min i N) (Nat.min_le_right i N)
    have hnnq : ∀ (i n : Nat),
        RegularSeqNonneg (finPtsEval pts N (hfs n) i) :=
      fun i n => regularSeqNonneg_of_zero_le (hnn n (pts (min i N)) (hmem n i))
    have hbound : ∀ (i n : Nat),
        RegularSeqLe (finPtsEval pts N (hfs n) i) (finPtsI pts N (fs n) (hfs n)) := by
      intro i n
      rw [← finPtsEval_min pts N (hfs n) i]
      refine le_regularSeqFinSum_of_nonneg_upto (u := finPtsEval pts N (hfs n)) N
        (fun j hj => ?_) (min i N) (Nat.min_le_right i N)
      show RegularSeqNonneg (finPtsEval pts N (hfs n) j)
      simpa [finPtsEval, Nat.min_eq_left hj] using
        regularSeqNonneg_of_zero_le (hnn n (pts j) (hfs n j hj))
    have S : ∀ i : Nat, RepSeriesSum (fun n => finPtsEval pts N (hfs n) i) :=
      fun i => repSeriesSum_comparison (fun n => hnnq i n) (fun n => hbound i n) hI
    have hcongrEq : ∀ n : Nat,
        relEventually (finPtsI pts N (fs n) (hfs n))
          (regularSeqFinSum (fun i => finPtsEval pts N (hfs n) i) N) :=
      fun n => relEventually_refl _
    have hlt1 : regularSeqLtProp (repSeriesSum_finSum S N).sum
        (finPtsI pts N f hf) :=
      regularSeqLtProp_of_left_eventual
        (repSeriesSum_unique
          (repSeriesSum_congr (repSeriesSum_finSum S N) hcongrEq) hI) hlt
    rw [repSeriesSum_finSum_sum_eq S N] at hlt1
    obtain ⟨i, _hiN, hlt2⟩ := regularSeqFinSum_lt_pick N
      (BishopSec3P.regularSeqLtData_of_ltPropC hlt1)
    exact ⟨pts (min i N), hf (min i N) (Nat.min_le_right i N),
      fun n => hmem n i, S i, hlt2⟩
  p := ⟨Set.univ, fun _ _ => c⟩
  p_mem := by
    intro i _hi
    trivial
  I_p := hnorm
  cutNat_tendsto := by
    intro f hf _hcut
    exact repSeriesTendsto_finSumC
      (fun i => cutNat_tendsto_point (finPtsEval pts N hf i)) N
  cutSmallSrc_tendsto := by
    intro f hf _hcut
    exact repSeriesTendsto_limit_congr
      (repSeriesTendsto_finSumC
        (fun i => cutSmallSrc_tendsto_point (finPtsEval pts N hf i)) N)
      (regularSeqFinSum_const_eventually_zero CReal.zero
        (relEventually_refl CReal.zero) N)

/-- Truncation at an arbitrary constant does not change a domain, so it keeps
membership in `L`; the single extra argument of the adapter holds here for the
same reason it holds for the Dirac model. -/
theorem finPtsCutConst (pts : Nat → X) (N : Nat) (a : CReal) {f : BFunC X}
    (hf : f ∈ finPtsL pts N) : BFunC.minC f a ∈ finPtsL pts N := hf

/-- The interface of Definition 2.1 for finitely many points, through the
adapter. -/
noncomputable def finPtsIntSpaceC (pts : Nat → X) (N : Nat) (c : CReal)
    (hnorm : relEventually
      (regularSeqFinSum (fun _ : Nat => c) N) oneSeq) :
    IntSpaceC X :=
  (finPtsDef11 pts N c hnorm).toIntSpaceC

/-! ## The two-point instance -/

/-- `1/2 + 1/2 = 1`, in the form the normalization clause asks for. -/
theorem twoPoint_norm :
    relEventually
      (regularSeqFinSum (fun _ : Nat => (constSeq (eps 1) : CReal)) 1)
      oneSeq := by
  show relEventually (addSeq (constSeq (eps 1)) (constSeq (eps 1))) oneSeq
  have h : eps 1 + eps 1 = eps 0 := eps_succ_add_self 0
  change relEventually (constSeq (eps 1 + eps 1)) oneSeq
  rw [h]
  exact relEventually_refl oneSeq

/-- **Two points, equal weights.**  A normalized integration space supported on
two (not necessarily distinct) points, with no remaining hypotheses. -/
noncomputable def twoPointDef11 (x₀ x₁ : X) : IntegrationSpaceDef11 X :=
  finPtsDef11 (fun i => match i with | 0 => x₀ | _ => x₁) 1
    (constSeq (eps 1)) twoPoint_norm

/-- The Definition 2.1 interface for the two-point space. -/
noncomputable def twoPointIntSpaceC (x₀ x₁ : X) : IntSpaceC X :=
  finPtsIntSpaceC (fun i => match i with | 0 => x₀ | _ => x₁) 1
    (constSeq (eps 1)) twoPoint_norm

/-! ## A closed two-point instance on `Bool`

`twoPointDef11` is unconditional but takes its two points as parameters, and on
a general `X` they may coincide.  Specializing to `Bool` settles the question:
`false` and `true` are distinct, and because equality on `Bool` is decidable the
characteristic function of each is definable without any appeal to choice.  The
two theorems below show that both singletons carry positive measure, and hence
that the functional is the evaluation at neither point. -/

/-- The two slots `false` and `true`. -/
def boolPts : Nat → Bool
  | 0 => false
  | _ => true

/-- **A two-point integration space on `Bool`.**  The instance of
`twoPointDef11` at the two distinct booleans; it has no parameters left. -/
noncomputable def boolTwoPointDef11 : IntegrationSpaceDef11 Bool :=
  twoPointDef11 false true

/-- The Definition 2.1 interface for that space. -/
noncomputable def boolTwoPointIntSpaceC : IntSpaceC Bool :=
  twoPointIntSpaceC false true

/-- The characteristic function of `{b}`, total on `Bool`. -/
def boolIndicator (b : Bool) : BFunC Bool where
  dom := Set.univ
  toFun := fun x _ => if x = b then CReal.one else CReal.zero

theorem boolIndicator_mem (b : Bool) : boolIndicator b ∈ finPtsL boolPts 1 :=
  fun _ _ => Set.mem_univ _

/-- The carrier of `boolTwoPointDef11` is the one the theorems below use. -/
theorem boolTwoPointDef11_L : boolTwoPointDef11.L = finPtsL boolPts 1 := rfl

/-- `0 < 1` on the representative layer. -/
theorem zero_lt_oneC : regularSeqLtProp CReal.zero CReal.one :=
  regularSeqLtProp_of_right_eventual halfPow_zero (regularSeqLtProp_zero_halfPow 0)

/-- Each singleton has integral `1`: the sum has one term `1` and one term `0`. -/
theorem boolIndicator_integral (b : Bool) :
    relEventually
      (finPtsI boolPts 1 (boolIndicator b) (boolIndicator_mem b)) CReal.one := by
  cases b
  · exact addSeq_zero_right_eventually CReal.one
  · exact addSeq_zero_left_eventually CReal.one

/-- **Both singletons carry positive measure.**  Since `false` and `true` are
distinct, the measure of `boolTwoPointDef11` is not carried by one point. -/
theorem boolIndicator_integral_pos (b : Bool) :
    regularSeqLtProp CReal.zero
      (finPtsI boolPts 1 (boolIndicator b) (boolIndicator_mem b)) :=
  regularSeqLtProp_of_right_eventual
    (relEventually_symm _ _ (boolIndicator_integral b)) zero_lt_oneC

/-- **The functional is the evaluation at neither point.**  For each `x : Bool`
an element of `L` is exhibited whose integral is strictly greater than its value
at `x`; the witness is the characteristic function of the other boolean. -/
theorem boolTwoPoint_not_concentrated (x : Bool) :
    ∃ (f : BFunC Bool) (hf : f ∈ finPtsL boolPts 1) (hx : x ∈ f.dom),
      regularSeqLtProp (f.toFun x hx) (finPtsI boolPts 1 f hf) := by
  cases x
  · exact ⟨boolIndicator true, boolIndicator_mem true, Set.mem_univ _,
      boolIndicator_integral_pos true⟩
  · exact ⟨boolIndicator false, boolIndicator_mem false, Set.mem_univ _,
      boolIndicator_integral_pos false⟩

#print axioms BishopCheng.addSeq_add_add_swap_eventually
#print axioms BishopCheng.regularSeqFinSum_add_termwise
#print axioms BishopCheng.le_regularSeqFinSum_of_nonneg_upto
#print axioms BishopCheng.regularSeqLtProp_add_cancel_right
#print axioms BishopCheng.regularSeqFinSum_lt_pick
#print axioms BishopCheng.repSeriesSum_finSum
#print axioms BishopCheng.finPtsDef11
#print axioms BishopCheng.finPtsIntSpaceC
#print axioms BishopCheng.twoPointDef11
#print axioms BishopCheng.twoPointIntSpaceC
#print axioms BishopCheng.boolTwoPointDef11
#print axioms BishopCheng.boolTwoPointIntSpaceC
#print axioms BishopCheng.boolIndicator_integral
#print axioms BishopCheng.boolIndicator_integral_pos
#print axioms BishopCheng.boolTwoPoint_not_concentrated

end BishopCheng
