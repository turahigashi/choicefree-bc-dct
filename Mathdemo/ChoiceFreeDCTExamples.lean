import ChoiceFreeMeasureDCTPublic

/-!
# Application examples for the public Bishop--Cheng DCT API

This module contains small, parameterized uses of the public theorem aliases.
The examples are intentionally abstract: their purpose is to exercise the public
interfaces as callable theorems, not to construct a concrete integration space.
-/

namespace ChoiceFreeMeasureDCT

universe u

/-- Abstract smoke test for the corrected good-set convergence wrapper. -/
noncomputable def abstract_good_set_dct_applicationC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC (g.add f.absVal))
    (hfn_bound : forall (n : Nat) (x : X)
      (hfndom : (fn n).MemAt x) (hgdom : g.MemAt x)
      (hfnv : BishopSec1P.RepSeriesSum
        (fun k => (fn n).valueAt x hfndom k))
      (hgv : BishopSec1P.RepSeriesSum
        (fun k => g.valueAt x hgdom k)),
        BishopCReal.RegularSeqLe hfnv.sum.abs hgv.sum)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureGoodSetDataC fn f) :
    BishopSec1P.RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  dominated_convergence_from_pointwise_majorant_good_set_profileC
    fn f g hgnn Dsmooth hfn_bound hconv

/-- Abstract smoke test for the separated L1 endpoint. -/
noncomputable def abstract_l1_error_endpoint_applicationC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (Dsmooth : BishopSec3P.Lemma43DyadicSmoothDataC g)
    (hdom : forall (n : Nat) (x : X)
      (herrdom : (BishopSec1P.thm_4_15_abs_errorC fn f n).MemAt x)
      (hgdom : g.MemAt x)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        (BishopSec1P.thm_4_15_abs_errorC fn f n).valueAt x herrdom k)
      (gv : BishopSec1P.RepSeriesSum fun k => g.valueAt x hgdom k),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :
    BishopSec1P.RepSeriesTendsto
      (fun n => (BishopSec1P.thm_4_15_abs_errorC fn f n).integral)
      BishopCReal.CReal.zero :=
  l1_error_convergence_from_majorant_measure_convergenceC
    fn f herr_nn g hgnn Dsmooth hdom hconv

/-- Abstract smoke test for the automatic good-set convergence wrapper. -/
noncomputable def abstract_good_set_dct_application_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (hfn_bound : forall (n : Nat) (x : X)
      (hfndom : (fn n).MemAt x) (hgdom : g.MemAt x)
      (hfnv : BishopSec1P.RepSeriesSum
        (fun k => (fn n).valueAt x hfndom k))
      (hgv : BishopSec1P.RepSeriesSum
        (fun k => g.valueAt x hgdom k)),
        BishopCReal.RegularSeqLe hfnv.sum.abs hgv.sum)
    (hconv : BishopSec3P.Lemma415ConvergeInMeasureGoodSetDataC fn f) :
    BishopSec1P.RepSeriesTendsto (fun n => (fn n).integral) f.integral :=
  dominated_convergence_from_pointwise_majorant_good_set_profile_autoC
    fn f g hgnn hfn_bound hconv

/-- Abstract smoke test for the automatic separated L1 endpoint. -/
noncomputable def abstract_l1_error_endpoint_application_autoC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (herr_nn : forall n : Nat,
      BishopSec1P.RepNonnegC (BishopSec1P.thm_4_15_abs_errorC fn f n))
    (g : BishopSec1P.IntegrableRepC3 S)
    (hgnn : BishopSec1P.RepNonnegC g)
    (hdom : forall (n : Nat) (x : X)
      (herrdom : (BishopSec1P.thm_4_15_abs_errorC fn f n).MemAt x)
      (hgdom : g.MemAt x)
      (ev : BishopSec1P.RepSeriesSum fun k =>
        (BishopSec1P.thm_4_15_abs_errorC fn f n).valueAt x herrdom k)
      (gv : BishopSec1P.RepSeriesSum fun k => g.valueAt x hgdom k),
        BishopCReal.RegularSeqLe ev.sum gv.sum)
    (hconv : BishopSec1P.Lemma414ConvergeInMeasureToZeroDataC
      (BishopSec1P.thm_4_15_abs_errorC fn f)) :
    BishopSec1P.RepSeriesTendsto
      (fun n => (BishopSec1P.thm_4_15_abs_errorC fn f n).integral)
      BishopCReal.CReal.zero :=
  l1_error_convergence_from_majorant_measure_convergence_autoC
    fn f herr_nn g hgnn hdom hconv

/-- Abstract smoke test for the Prop-facing Bishop--Cheng theorem 4.15
wrapper. -/
noncomputable def abstract_bishop_cheng_prop_applicationC
    {X : Type u} {S : BishopSec1P.IntSpaceC X}
    (fn : Nat -> BishopSec1P.IntegrableRepC3 S)
    (f : BishopSec1P.IntegrableRepC3 S)
    (hconv : BishopSec1P.ConvergeInMeasureC S
      (fun n => (fn n).toDataPFunRC) f.toDataPFunRC)
    (hdom : exists g : BishopSec1P.IntegrableRepC3 S,
      BishopSec1P.DominatedOnFullC fn g) :
    BishopSec1P.RepSeriesTendstoEpsPropC
      (fun n => (fn n).integral) f.integral :=
  bishop_cheng_dominated_convergence_propC fn f hconv hdom

end ChoiceFreeMeasureDCT
