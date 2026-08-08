import Mathdemo.BishopSec3PresentedEnhancementsC
import Mathdemo.BishopChengTheorem415Prop
import Mathdemo.BishopChengTheorem415FullSetData

/-!
# Public theorem aliases for the choice-free Bishop--Cheng DCT artifact

These are paper-facing names for implementation declarations in
`Mathdemo.BishopSec3Presented` or in the audited enhancement modules.  Each
declaration is a thin wrapper around the corresponding implementation theorem
and has the same mathematical content.
-/

namespace ChoiceFreeMeasureDCT

universe u

noncomputable def profile_partition_dataC
    {a b eps : BishopCReal.CReal}
    {hab : BishopCReal.regularSeqLtProp a b}
    (P : BishopSec3P.ProfileC a b hab)
    (heps : BishopCReal.regularSeqLtProp BishopCReal.zeroSeq eps)
    (n : Nat) (hn : 0 < n)
    (h_cond :
      BishopCReal.regularSeqLtProp
        ((P.lambda P.oneCode).sub (P.lambda P.zeroCode))
        (BishopCReal.CReal.mul (BishopCReal.constSeq (n + 1)) eps)) :=
  BishopSec3P.lemma_3_4DataC P heps n hn h_cond

noncomputable def profile_level_sets_integrable_apartC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (h : BishopSec1P.IntegrableRepC3 S)
    {a b : BishopCReal.CReal}
    (hab : BishopCReal.regularSeqLtProp a b)
    (ha : BishopCReal.PosEventuallyData a)
    (t : BishopCReal.CReal)
    (hat : BishopCReal.regularSeqLtProp a t)
    (htb : BishopCReal.regularSeqLtProp t b)
    (hT : forall n : Nat,
      BishopCReal.regularSeqLtProp BishopCReal.CReal.zero
        (t.sub (BishopSec3P.thm36ExceptionSeqC h hab ha n)).abs) :=
  BishopSec3P.thm_3_6_forall_apart_measureC h hab ha t hat htb hT

noncomputable def uniform_complement_from_profile_levelsC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (hnn : forall n : Nat, BishopSec1P.RepNonnegC (fn n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (D : BishopSec3P.Lemma43LevelSetSeqDataC g)
    (hdom : forall (n : Nat) (x : X)
      (fv : BishopSec1P.RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe fv.sum gv.sum)
    (eps : BishopCReal.CReal)
    (heps : BishopCReal.regularSeqLtProp BishopCReal.CReal.zero eps) :=
  BishopSec3P.lemma43UniformComplementData_of_majorantC
    fn hnn g hgnn D hdom eps heps

noncomputable def l1_error_convergence_from_majorant_measure_convergenceC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  BishopSec3P.lemma414_l1_error_tendsto_zero_from_majorant_smooth_measure_convergeC
    fn f herr_nn g hgnn Dsmooth hdom hconv

noncomputable def integral_convergence_from_majorant_measure_convergenceC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  BishopSec3P.thm_4_15_integral_convergence_from_majorant_smooth_measure_convergeC
    fn f herr_nn g hgnn Dsmooth hdom hconv

noncomputable def dominated_convergence_from_error_majorant_profileC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  BishopSec3P.goalB_dominated_convergence_dataC
    fn f g hgnn Dsmooth hdom hconv

noncomputable def dominated_convergence_from_pointwise_majorant_profileC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC (g.add f.absVal))
    (hfn_bound : forall (n : Nat) (x : X)
      (hfnv : BishopSec1P.RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (hgv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe hfnv.sum.abs hgv.sum)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureDataC fn f) :=
  BishopSec3P.goalB_classical_dominated_convergence_dataC
    fn f g hgnn Dsmooth hfn_bound hconv

noncomputable def dominated_convergence_from_pointwise_majorant_good_set_profileC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC (g.add f.absVal))
    (hfn_bound : forall (n : Nat) (x : X)
      (hfnv : BishopSec1P.RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (hgv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe hfnv.sum.abs hgv.sum)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureGoodSetDataC fn f) :=
  BishopSec3P.goalB_pointwise_majorant_goodSet_convergence_dataC
    fn f g hgnn Dsmooth hfn_bound hconv

noncomputable def l1_error_convergence_from_majorant_measure_convergence_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  l1_error_convergence_from_majorant_measure_convergenceC
    fn f herr_nn g hgnn (BishopSec3P.lemma43DyadicSmoothDataC_construct g)
    hdom hconv

noncomputable def integral_convergence_from_majorant_measure_convergence_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  integral_convergence_from_majorant_measure_convergenceC
    fn f herr_nn g hgnn (BishopSec3P.lemma43DyadicSmoothDataC_construct g)
    hdom hconv

noncomputable def dominated_convergence_from_error_majorant_profile_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (hdom : forall (n : Nat) (x : X)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        ((BishopSec1P.thm_4_15_abs_errorC fn f n).fn k).toFun x)
      (gv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  dominated_convergence_from_error_majorant_profileC
    fn f g hgnn (BishopSec3P.lemma43DyadicSmoothDataC_construct g) hdom hconv

noncomputable def dominated_convergence_from_pointwise_majorant_profile_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (hfn_bound : forall (n : Nat) (x : X)
      (hfnv : BishopSec1P.RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (hgv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe hfnv.sum.abs hgv.sum)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureDataC fn f) :=
  dominated_convergence_from_pointwise_majorant_profileC
    fn f g hgnn
    (BishopSec3P.lemma43DyadicSmoothDataC_construct (g.add f.absVal))
    hfn_bound hconv

noncomputable def dominated_convergence_from_pointwise_majorant_good_set_profile_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (hfn_bound : forall (n : Nat) (x : X)
      (hfnv : BishopSec1P.RepSeriesSum fun k => ((fn n).fn k).toFun x)
      (hgv : BishopSec1P.RepSeriesSum fun k => (g.fn k).toFun x),
        BishopCReal.RegularSeqLe hfnv.sum.abs hgv.sum)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureGoodSetDataC fn f) :=
  dominated_convergence_from_pointwise_majorant_good_set_profileC
    fn f g hgnn
    (BishopSec3P.lemma43DyadicSmoothDataC_construct (g.add f.absVal))
    hfn_bound hconv

/-- Type-valued L1-error convergence with an explicit full-set selector for
the error-majorant bound. -/
noncomputable def l1_error_convergence_from_majorant_on_full_dataC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f H : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (hHnn : BishopSec1P.RepNonnegC H)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC H)
    (hdom : forall n : Nat,
      BishopSec1P.RepLeOnFullDataC
        (BishopSec1P.thm_4_15_abs_errorC fn f n) H)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  BishopSec3P.l1ErrorConvergence_from_errorMajorantOnFullDataC
    fn f H herr_nn hHnn Dsmooth hdom hconv

/-- Type-valued integral convergence with an explicit full-set selector for
the error-majorant bound. -/
noncomputable def integral_convergence_from_majorant_on_full_dataC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f H : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (hHnn : BishopSec1P.RepNonnegC H)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC H)
    (hdom : forall n : Nat,
      BishopSec1P.RepLeOnFullDataC
        (BishopSec1P.thm_4_15_abs_errorC fn f n) H)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :=
  BishopSec3P.integralConvergence_from_errorMajorantOnFullDataC
    fn f H herr_nn hHnn Dsmooth hdom hconv

/-- Fully data-carrying DCT with a single majorant and an explicit full-set
selector for every sequence index. -/
noncomputable def dominated_convergence_from_pointwise_majorant_on_full_dataC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC (g.absVal.add f.absVal))
    (hdom : BishopSec1P.DominatedOnFullDataC fn g)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureDataC fn f) :=
  BishopSec3P.dominatedConvergence_from_pointwiseMajorantOnFullDataC
    fn f g Dsmooth hdom hconv

/-- Automatic smooth-level wrapper for the explicit full-set Type-valued DCT. -/
noncomputable def dominated_convergence_from_pointwise_majorant_on_full_data_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hdom : BishopSec1P.DominatedOnFullDataC fn g)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureDataC fn f) :=
  BishopSec3P.dominatedConvergence_from_pointwiseMajorantOnFullData_autoC
    fn f g hdom hconv

/-- Automatic smooth-level DCT combining explicit domination full sets with
explicit convergence good sets.  The two set families remain separate. -/
noncomputable def dominated_convergence_from_pointwise_majorant_on_full_good_set_data_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hdom : BishopSec1P.DominatedOnFullDataC fn g)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureGoodSetDataC fn f) :=
  BishopSec3P.dominatedConvergence_from_pointwiseMajorantOnFullGoodSetData_autoC
    fn f g hdom hconv

noncomputable def bishop_cheng_dominated_convergence_propC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (hconv : BishopSec1P.ConvergeInMeasureC S
      (fun n => (fn n).toDataPFunRC) f.toDataPFunRC)
    (hdom : exists g : BishopSec1P.IntegrableRepC3 S,
      BishopSec1P.DominatedOnFullC fn g) :=
  BishopSec3P.bishop_cheng_thm_4_15_propC S fn f hconv hdom

end ChoiceFreeMeasureDCT

#check ChoiceFreeMeasureDCT.profile_partition_dataC
#check ChoiceFreeMeasureDCT.profile_level_sets_integrable_apartC
#check ChoiceFreeMeasureDCT.uniform_complement_from_profile_levelsC
#check ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergenceC
#check ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergenceC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profileC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profileC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profileC
#check ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergence_autoC
#check ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergence_autoC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profile_autoC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profile_autoC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profile_autoC
#check ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_on_full_dataC
#check ChoiceFreeMeasureDCT.integral_convergence_from_majorant_on_full_dataC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_dataC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_data_autoC
#check ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_good_set_data_autoC
#check ChoiceFreeMeasureDCT.bishop_cheng_dominated_convergence_propC

#print axioms ChoiceFreeMeasureDCT.profile_partition_dataC
#print axioms ChoiceFreeMeasureDCT.profile_level_sets_integrable_apartC
#print axioms ChoiceFreeMeasureDCT.uniform_complement_from_profile_levelsC
#print axioms ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergenceC
#print axioms ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergenceC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profileC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profileC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profileC
#print axioms ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_measure_convergence_autoC
#print axioms ChoiceFreeMeasureDCT.integral_convergence_from_majorant_measure_convergence_autoC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_error_majorant_profile_autoC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_profile_autoC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_good_set_profile_autoC
#print axioms ChoiceFreeMeasureDCT.l1_error_convergence_from_majorant_on_full_dataC
#print axioms ChoiceFreeMeasureDCT.integral_convergence_from_majorant_on_full_dataC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_dataC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_data_autoC
#print axioms ChoiceFreeMeasureDCT.dominated_convergence_from_pointwise_majorant_on_full_good_set_data_autoC
#print axioms ChoiceFreeMeasureDCT.bishop_cheng_dominated_convergence_propC
