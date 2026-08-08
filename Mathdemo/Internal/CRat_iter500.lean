-- CRat_iter500: pointwise scalar-scale primitive (clean low-import ring context)
import Mathdemo.Internal.CRat_iter31

namespace BishopCReal
open BishopC BishopCRat

/-- Pointwise scalar scaling by a bounded constant `|c|≤1` (clean ring context). -/
def scaleC (c : Scalar) (hc : Le (COF.abs c) 1) (x : RegularSeq) : RegularSeq where
  val := fun n => c * x.val n
  regular := by
    intro m n
    have hstep : c * x.val m - c * x.val n = c * (x.val m - x.val n) := by ring
    rw [hstep, scalar_abs_mul]
    have hnn : Le 0 (COF.abs (x.val m - x.val n)) := scalar_abs_nonneg _
    have h1 : Le (COF.abs c * COF.abs (x.val m - x.val n))
                 (1 * COF.abs (x.val m - x.val n)) := scalar_mul_le_mul_right hc hnn
    have h2 : (1 : Scalar) * COF.abs (x.val m - x.val n) = COF.abs (x.val m - x.val n) := by ring
    rw [h2] at h1
    exact BishopC.le_trans h1 (x.regular m n)

theorem scaleC_val (c : Scalar) (hc : Le (COF.abs c) 1) (x : RegularSeq) (n : Nat) :
    (scaleC c hc x).val n = c * x.val n := rfl

/-- `|½| = ½` for the scalar half (pure-term reduction; the `rw` tactic form is
not used by audited public declarations at this import level, so we use a term-mode rewrite). -/
theorem abs_half_redC : COF.abs (COF.half : Scalar) = COF.half :=
  scalarCOFOSeed.abs_of_nonneg (scalar_nonneg_of_pos scalarCOFOSeed.half_pos)

/-- `|½| ≤ 1` for the scalar half (clean via pure-term `▸`). -/
theorem abs_half_le_oneC : Le (COF.abs COF.half) (1 : Scalar) :=
  abs_half_redC ▸ scalar_le_of_lt scalar_half_lt_one

/-- Pointwise σ = ¼·d via double `scaleC ½` (pointwise, no mul-bound index shift). -/
def sigmaScaleC (d : RegularSeq) : RegularSeq :=
  scaleC COF.half abs_half_le_oneC (scaleC COF.half abs_half_le_oneC d)

theorem sigmaScaleC_val (d : RegularSeq) (n : Nat) :
    (sigmaScaleC d).val n = COF.half * (COF.half * d.val n) := rfl

/-- `½+½ = 1` on the scalar (pure-term via the seed field; clean at this import
level — the higher-import `rw`/nested-`ring` contamination does not reach here). -/
theorem scalar_half_add_half : (COF.half : Scalar) + (COF.half : Scalar) = 1 :=
  COF.half_add_half

/-- Opaque symbolic right-distributivity `h·a + h·a = (h+h)·a` (variables only ⇒
`ring` stays symbolic and clean, as in `scaleC`'s `c·(a-b)` step). -/
theorem scalar_add_self_mul_gen (h a : Scalar) : h * a + h * a = (h + h) * a := by ring

/-- Scalar half-doubling `½·a + ½·a = a` — the nested-constant collapse built
clean by composing opaque distributivity, pure-term `½+½=1`, and symbolic `1·a=a`
(direct `by ring` on this identity evaluates the `½` constant and is contaminated). -/
theorem scalar_half_add_self_mul (a : Scalar) : COF.half * a + COF.half * a = a := by
  have h1 : (COF.half + COF.half) * a = (1 : Scalar) * a :=
    congrArg (· * a) scalar_half_add_half
  have ho : (1 : Scalar) * a = a := by ring
  exact (scalar_add_self_mul_gen COF.half a).trans (h1.trans ho)

/-- Pointwise value of `2σ = σ+σ = ½·d` (collapsed clean). Note the `addIndex n`
shift from `addSeq`; the two `σ` copies land at the *same* index so they collapse. -/
theorem two_sigmaScaleC_val (d : RegularSeq) (n : Nat) :
    (addSeq (sigmaScaleC d) (sigmaScaleC d)).val n = COF.half * d.val (addIndex n) :=
  scalar_half_add_self_mul (COF.half * d.val (addIndex n))

/-- Pointwise `½·d`. -/
def halfScaleC (d : RegularSeq) : RegularSeq := scaleC COF.half abs_half_le_oneC d

theorem halfScaleC_val (d : RegularSeq) (n : Nat) :
    (halfScaleC d).val n = COF.half * d.val n := rfl

/-- Opaque symbolic `c·a − c·b = c·(a−b)` (variables ⇒ `ring` stays symbolic/clean). -/
theorem scalar_mul_sub_gen (c a b : Scalar) : c * a - c * b = c * (a - b) := by ring

/-- Raw-rel `2σ ≈ ½d`: both pointwise `½·d`, differing only by the `addIndex` shift
on `d`, bounded by ½·regularity ≤ regularity ≤ tol. This is the exact identity that
makes `d − 2σ = ½d` a *raw* `rel` (hence DATA-transportable via `…_relT`). -/
theorem two_sigma_rel_halfScale (d : RegularSeq) :
    rel (addSeq (sigmaScaleC d) (sigmaScaleC d)) (halfScaleC d) := by
  intro n
  have hA : (addSeq (sigmaScaleC d) (sigmaScaleC d)).val n = COF.half * d.val (n + 1) :=
    two_sigmaScaleC_val d n
  have hB : (halfScaleC d).val n = COF.half * d.val n := halfScaleC_val d n
  have hfac : COF.half * d.val (n + 1) - COF.half * d.val n
            = COF.half * (d.val (n + 1) - d.val n) :=
    scalar_mul_sub_gen COF.half (d.val (n + 1)) (d.val n)
  have habs : COF.abs (COF.half * (d.val (n + 1) - d.val n))
            = COF.half * COF.abs (d.val (n + 1) - d.val n) :=
    (scalar_abs_mul COF.half (d.val (n + 1) - d.val n)).trans
      (congrArg (· * COF.abs (d.val (n + 1) - d.val n)) abs_half_redC)
  have hnn : Le 0 (COF.abs (d.val (n + 1) - d.val n)) := scalar_abs_nonneg _
  have hhalf_le : Le (COF.half * COF.abs (d.val (n + 1) - d.val n))
                     ((1 : Scalar) * COF.abs (d.val (n + 1) - d.val n)) :=
    scalar_mul_le_mul_right (scalar_le_of_lt scalar_half_lt_one) hnn
  have hone : (1 : Scalar) * COF.abs (d.val (n + 1) - d.val n)
            = COF.abs (d.val (n + 1) - d.val n) := by ring
  have hYtol : Le (COF.abs (d.val (n + 1) - d.val n)) (tol n) :=
    BishopC.le_trans (d.regular (n + 1) n) (eps_succ_add_le_tol n)
  have h1Ytol : Le ((1 : Scalar) * COF.abs (d.val (n + 1) - d.val n)) (tol n) := hone.symm ▸ hYtol
  have hfinal : Le (COF.half * COF.abs (d.val (n + 1) - d.val n)) (tol n) :=
    BishopC.le_trans hhalf_le h1Ytol
  show Le (COF.abs ((addSeq (sigmaScaleC d) (sigmaScaleC d)).val n - (halfScaleC d).val n)) (tol n)
  rw [hA, hB, hfac, habs]
  exact hfinal

/-- Opaque symbolic left-distributivity `c·(a+b)=c·a+c·b` (variables ⇒ clean ring). -/
theorem scalar_mul_add_gen (c a b : Scalar) : c * (a + b) = c * a + c * b := by ring

/-- Scalar half-halving of `eps`: `½·eps k = eps(k+1)`. Built clean from
`eps(k+1)+eps(k+1)=eps k` via opaque distributivity + half-doubling collapse (a
direct `by ring` would evaluate the `½` constant and be contaminated). Reusable
for every pointwise-half positivity transport (`½·(pos) > eps(k+1)`). -/
theorem half_eps_succ_eq (k : Nat) : COF.half * eps k = eps (k + 1) := by
  have hd : eps (k + 1) + eps (k + 1) = eps k := eps_succ_add_self k
  have s1 : COF.half * eps k = COF.half * (eps (k + 1) + eps (k + 1)) :=
    congrArg (COF.half * ·) hd.symm
  have s2 : COF.half * (eps (k + 1) + eps (k + 1))
          = COF.half * eps (k + 1) + COF.half * eps (k + 1) :=
    scalar_mul_add_gen COF.half (eps (k + 1)) (eps (k + 1))
  have s3 : COF.half * eps (k + 1) + COF.half * eps (k + 1) = eps (k + 1) :=
    scalar_half_add_self_mul (eps (k + 1))
  exact s1.trans (s2.trans s3)

/-- Opaque-gen scalar identity `h·a − (a − h·b) = h·(b−a)` under `h+h=1`
(variables only ⇒ symbolic ring stays clean; the `½` constant enters only via the
`h+h=1` hypothesis, never evaluated). This is exactly the value-level shape of the
`d − 2σ = ½d` bridge diff (`h:=½, a:=d(n+1), b:=d(n+2)`). -/
theorem sub_sub_gen (h a b : Scalar) (hh : h + h = 1) :
    h * a - (a - h * b) = h * (b - a) := by
  have e : (h + h) * a = a := by rw [hh]; ring
  calc h * a - (a - h * b)
      = (h + h) * a - a + h * b - h * a := by ring
    _ = a - a + h * b - h * a := by rw [e]
    _ = h * (b - a) := by ring

/-- Raw-rel bridge `½d ≈ d − 2σ` in the *subSeq-with-any-zero* shape: for any `z`
with `z.val(n+1)=0`, `subSeq (½d) z` (pointwise `½·d(n+1) − 0`) relates to
`subSeq d (2σ)` (pointwise `d(n+1) − ½·d(n+2)`); diff `= ½·(d(n+2) − d(n+1))` (via
`sub_sub_gen`, `h:=½`), `|·| = ½|d(n+2)−d(n+1)| ≤ |d(n+2)−d(n+1)| ≤ eps(n+2)+eps(n+1)
≤ tol n`. Being a *raw* `rel` it transports `data ½d>0` (`half_scale_pos_dataC`) to
`data d−2σ>0` via `…_relT`; the `z` parameter lets the BSP layer instantiate the
concrete `CReal.zero` (unavailable at this import level). -/
theorem two_sigma_sub_bridge (d z : RegularSeq) (hz : ∀ n, z.val (n + 1) = 0) :
    rel (subSeq (halfScaleC d) z)
        (subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d))) := by
  intro n
  have hL : (subSeq (halfScaleC d) z).val n
          = COF.half * d.val (n + 1) - z.val (n + 1) := rfl
  have hR : (subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d))).val n
          = d.val (n + 1) - COF.half * d.val (n + 2) :=
    congrArg (d.val (n + 1) - ·) (two_sigmaScaleC_val d (n + 1))
  have hfac : (COF.half * d.val (n + 1) - z.val (n + 1))
            - (d.val (n + 1) - COF.half * d.val (n + 2))
            = COF.half * (d.val (n + 2) - d.val (n + 1)) := by
    have hz0 : COF.half * d.val (n + 1) - z.val (n + 1) = COF.half * d.val (n + 1) := by
      rw [hz n]; ring
    rw [hz0]
    exact sub_sub_gen COF.half (d.val (n + 1)) (d.val (n + 2)) scalar_half_add_half
  have habs : COF.abs (COF.half * (d.val (n + 2) - d.val (n + 1)))
            = COF.half * COF.abs (d.val (n + 2) - d.val (n + 1)) :=
    (scalar_abs_mul COF.half (d.val (n + 2) - d.val (n + 1))).trans
      (congrArg (· * COF.abs (d.val (n + 2) - d.val (n + 1))) abs_half_redC)
  have hnn : Le 0 (COF.abs (d.val (n + 2) - d.val (n + 1))) := scalar_abs_nonneg _
  have hhalf_le : Le (COF.half * COF.abs (d.val (n + 2) - d.val (n + 1)))
                     ((1 : Scalar) * COF.abs (d.val (n + 2) - d.val (n + 1))) :=
    scalar_mul_le_mul_right (scalar_le_of_lt scalar_half_lt_one) hnn
  have hone : (1 : Scalar) * COF.abs (d.val (n + 2) - d.val (n + 1))
            = COF.abs (d.val (n + 2) - d.val (n + 1)) := by ring
  have hreg : Le (COF.abs (d.val (n + 2) - d.val (n + 1))) (eps (n + 2) + eps (n + 1)) :=
    d.regular (n + 2) (n + 1)
  have heps : Le (eps (n + 2) + eps (n + 1)) (tol n) := by
    have h2 : Le (eps (n + 2)) (eps n) := eps_le_of_le (by omega)
    have h1 : Le (eps (n + 1)) (eps n) := eps_le_of_le (by omega)
    exact BishopC.le_add h2 h1
  have h1tol : Le ((1 : Scalar) * COF.abs (d.val (n + 2) - d.val (n + 1))) (tol n) :=
    hone.symm ▸ BishopC.le_trans hreg heps
  have hfinal : Le (COF.half * COF.abs (d.val (n + 2) - d.val (n + 1))) (tol n) :=
    BishopC.le_trans hhalf_le h1tol
  show Le (COF.abs ((subSeq (halfScaleC d) z).val n
                  - (subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d))).val n)) (tol n)
  rw [hL, hR, hfac, habs]
  exact hfinal

/-- Technical lemma used in the public import closure. -/
def bptRC (a d : RegularSeq) : Nat → RegularSeq
  | 0 => a
  | (i + 1) => addSeq (bptRC a d i) d

/-- Technical lemma used in the public import closure. -/
theorem two_sigma_sub_bridge_grid (a d : RegularSeq) (j : Nat) :
    rel (subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d)))
        (subSeq (subSeq (bptRC a d (j + 1)) (sigmaScaleC d))
                (addSeq (bptRC a d j) (sigmaScaleC d))) := by
  intro n
  have hdiff :
      (subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d))).val n
        - (subSeq (subSeq (bptRC a d (j + 1)) (sigmaScaleC d))
                  (addSeq (bptRC a d j) (sigmaScaleC d))).val n
      = (d.val (n + 1) - d.val (n + 3))
        + ((bptRC a d j).val (n + 2) - (bptRC a d j).val (n + 3)) := by
    show (d.val (n + 1) - ((sigmaScaleC d).val (n + 2) + (sigmaScaleC d).val (n + 2)))
       - ((((bptRC a d j).val (n + 3) + d.val (n + 3)) - (sigmaScaleC d).val (n + 2))
          - ((bptRC a d j).val (n + 2) + (sigmaScaleC d).val (n + 2)))
       = (d.val (n + 1) - d.val (n + 3))
         + ((bptRC a d j).val (n + 2) - (bptRC a d j).val (n + 3))
    ring
  show Le (COF.abs ((subSeq d (addSeq (sigmaScaleC d) (sigmaScaleC d))).val n
        - (subSeq (subSeq (bptRC a d (j + 1)) (sigmaScaleC d))
                  (addSeq (bptRC a d j) (sigmaScaleC d))).val n)) (tol n)
  rw [hdiff]
  refine BishopC.le_trans (scalar_abs_add_le _ _) ?_
  have hP : Le (COF.abs (d.val (n + 1) - d.val (n + 3))) (eps (n + 1) + eps (n + 3)) :=
    d.regular (n + 1) (n + 3)
  have hR : Le (COF.abs ((bptRC a d j).val (n + 2) - (bptRC a d j).val (n + 3)))
               (eps (n + 2) + eps (n + 3)) :=
    (bptRC a d j).regular (n + 2) (n + 3)
  refine BishopC.le_trans (BishopC.le_add hP hR) ?_
  have e1 : Le (eps (n + 3)) (eps (n + 1)) := eps_le_of_le (by omega)
  have e2 : Le (eps (n + 2)) (eps (n + 1)) := eps_le_of_le (by omega)
  have erefl : Le (eps (n + 1)) (eps (n + 1)) := eps_le_of_le (Nat.le_refl _)
  have h1 : Le (eps (n + 1) + eps (n + 3)) (eps (n + 1) + eps (n + 1)) :=
    BishopC.le_add erefl e1
  have h2 : Le (eps (n + 2) + eps (n + 3)) (eps (n + 1) + eps (n + 1)) :=
    BishopC.le_add e2 e1
  have hcomb := BishopC.le_add h1 h2
  rw [eps_succ_add_self n] at hcomb
  exact hcomb

end BishopCReal

