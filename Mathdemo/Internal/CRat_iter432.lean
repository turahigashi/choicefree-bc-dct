import Mathdemo.Internal.CRat_iter431

set_option linter.style.longLine false

/-!
# Stage A12: data-carried measurability frontier for 4.6/4.7

This additive node keeps the previous `PFunR`/`IsMeasurable` stub out of the route.
It records Bishop 4.6 measurability as Type-carried cutoff representatives over
`DataPFunR`.

The full bound-only 4.6 statement is still a frontier in the current library:
`thm_4_13_monotone_convergence_faithful` requires a `TendstoHalf` witness for
the cutoff integrals, while the 4.6 hypothesis supplies only an upper bound.
This file therefore exposes the exact MCT kernel and the extra data still
needed to turn the bound-only statement into the final theorem.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

def DataPFunR.mul (p q : DataPFunR X R) : DataPFunR X R where
  domData := fun x => Prod (p.domData x) (q.domData x)
  toFun := fun x hx => p.toFun x hx.1 * q.toFun x hx.2

def DataPFunR.cutConst (p : DataPFunR X R) (a : R) : DataPFunR X R where
  domData := p.domData
  toFun := fun x hx => COF.min (p.toFun x hx) a

def DataPFunR.cutNat (p : DataPFunR X R) (n : Nat) : DataPFunR X R :=
  p.cutConst (n : R)

def DataPFunR.chiOfIntegrableSet {A : BSet X} (hA : IntegrableSet1 S A) :
    DataPFunR X R :=
  hA.rep.toDataPFunRSeries

def DataPFunR.chiMul {A : BSet X} (hA : IntegrableSet1 S A)
    (f : DataPFunR X R) : DataPFunR X R :=
  (DataPFunR.chiOfIntegrableSet (S := S) hA).mul f

def DataPFunR.chiMulAbs {A : BSet X} (hA : IntegrableSet1 S A)
    (f : DataPFunR X R) : DataPFunR X R :=
  (DataPFunR.chiOfIntegrableSet (S := S) hA).mul f.absVal

abbrev CutoffRepresentsData (f : DataPFunR X R) (A : BSet X)
    (hA : IntegrableSet1 S A) (n : Nat) (r : IntegrableRep S) : Type _ :=
  Lemma414RepresentsDataPFunR (S := S) r
    ((DataPFunR.chiMulAbs (S := S) hA f).cutNat n)

/-- Bishop measurable data: each integrable set and level returns an actual
cutoff representative, plus the monotonicity data needed by MCT. -/
structure IsMeasurableData (S : IntSpaceRC X R) (f : DataPFunR X R) : Type _ where
  cutoff : forall (A : BSet X), IntegrableSet1 S A -> Nat -> IntegrableRep S
  represents : forall (A : BSet X) (hA : IntegrableSet1 S A) (n : Nat),
    CutoffRepresentsData (S := S) f A hA n (cutoff A hA n)
  cutoff_nonneg : forall (A : BSet X) (hA : IntegrableSet1 S A) (n : Nat),
    RepNonneg (cutoff A hA n)
  cutoff_mono : forall (A : BSet X) (hA : IntegrableSet1 S A) (n : Nat),
    RepNonneg ((cutoff A hA (n + 1)).sub (cutoff A hA n))

def thm46CutoffSeq {f : DataPFunR X R} (hm : IsMeasurableData S f)
    (A : BSet X) (hA : IntegrableSet1 S A) : Nat -> IntegrableRep S :=
  fun n => hm.cutoff A hA n

def thm46CutoffSeq_mono {f : DataPFunR X R} (hm : IsMeasurableData S f)
    (A : BSet X) (hA : IntegrableSet1 S A) :
    forall n, RepNonneg (thm_4_13_lambda (thm46CutoffSeq hm A hA) n) :=
  fun n => hm.cutoff_mono A hA n

abbrev thm46CutoffIntegralBound {f : DataPFunR X R}
    (hm : IsMeasurableData S f) (A : BSet X) (hA : IntegrableSet1 S A)
    (c : R) : Prop :=
  forall n, Le ((thm46CutoffSeq hm A hA n).integral) c

noncomputable def thm46MCTRep {f : DataPFunR X R}
    (hm : IsMeasurableData S f) (A : BSet X) (hA : IntegrableSet1 S A)
    (c : R)
    (hlim : RSeq.TendstoHalf
      (fun n => (thm46CutoffSeq hm A hA n).integral) c) :
    IntegrableRep S :=
  thm_4_13_monotone_convergence_faithful
    (thm46CutoffSeq hm A hA)
    (thm46CutoffSeq_mono hm A hA) c hlim

/-- Extra data currently missing from the bound-only 4.6 statement:
an actual integral limit and faithfulness of the MCT representative. -/
structure Thm46MCTFrontierData (f : DataPFunR X R)
    (hm : IsMeasurableData S f) (A : BSet X) (hA : IntegrableSet1 S A)
    (c : R) : Type _ where
  upper_bound : thm46CutoffIntegralBound hm A hA c
  integral_limit : RSeq.TendstoHalf
    (fun n => (thm46CutoffSeq hm A hA n).integral) c
  represents_limit : forall hlim : RSeq.TendstoHalf
      (fun n => (thm46CutoffSeq hm A hA n).integral) c,
    Lemma414RepresentsDataPFunR (S := S) (thm46MCTRep hm A hA c hlim) f

/-- The honest MCT kernel for Bishop 4.6.  It uses the faithful MCT exactly,
but it does not claim that an upper bound alone supplies the required limit. -/
noncomputable def thm_4_6_measurable_integrable_data
    (f : DataPFunR X R) (hm : IsMeasurableData S f)
    (A : BSet X) (hA : IntegrableSet1 S A) (c : R)
    (D : Thm46MCTFrontierData (S := S) f hm A hA c) :
    Sigma (fun rep : IntegrableRep S =>
      Lemma414RepresentsDataPFunR (S := S) rep f) :=
  ⟨thm46MCTRep hm A hA c D.integral_limit,
    D.represents_limit D.integral_limit⟩

/-- Frontier package for 4.7: domination gives the desired integral bound, but
the current library still needs the 4.6 MCT frontier data above. -/
structure Cor47DominatedFrontierData (f : DataPFunR X R)
    (hm : IsMeasurableData S f) (g : IntegrableRep S)
    (A : BSet X) (hA : IntegrableSet1 S A) : Type _ where
  g_nonneg : RepNonneg g
  dominates_cutoffs : forall n, Le ((thm46CutoffSeq hm A hA n).integral) g.integral
  mct_data : Thm46MCTFrontierData (S := S) f hm A hA g.integral

/-- The 4.7 wrapper closes once domination has been upgraded to the 4.6 MCT
frontier data.  The upgrade itself is not manufactured here. -/
noncomputable def cor_4_7_dominated_data
    (f : DataPFunR X R) (hm : IsMeasurableData S f) (g : IntegrableRep S)
    (A : BSet X) (hA : IntegrableSet1 S A)
    (D : Cor47DominatedFrontierData (S := S) f hm g A hA) :
    Sigma (fun rep : IntegrableRep S =>
      Lemma414RepresentsDataPFunR (S := S) rep f) :=
  thm_4_6_measurable_integrable_data
    (S := S) f hm A hA g.integral D.mct_data

structure StageA12Audit : Type where
  isMeasurableData_defined : Nat
  old_isMeasurable_stub_used : Nat
  mct_kernel_uses_faithful_mct : Nat
  bound_only_to_integral_limit_closed : Nat
  mct_limit_represents_closed_from_existing_mct : Nat
  dominated_to_bound_closed_here : Nat

def stageA12Audit : StageA12Audit where
  isMeasurableData_defined := 1
  old_isMeasurable_stub_used := 0
  mct_kernel_uses_faithful_mct := 1
  bound_only_to_integral_limit_closed := 0
  mct_limit_represents_closed_from_existing_mct := 0
  dominated_to_bound_closed_here := 0


end BishopC
