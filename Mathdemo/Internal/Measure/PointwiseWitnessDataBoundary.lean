import Mathdemo.Internal.Measure.ImportCompatibilityNode

set_option linter.style.longLine false

/-!
# Stage A9: pointwise witness data boundary

This additive node records the hard boundary found after `ImportCompatibilityNode`.
An `IntegrableRep` carries `absConv`, the integral-side absolute convergence
of `S.I (BFunR.absf (fn n))`.  The pointwise absolute convergence witness at a
fixed `x` is not a field of `IntegrableRep`; in the existing plain domain it is
only stored behind `Nonempty` in `Prop`.

The definitions below show the positive data statement: if the pointwise
SeriesSum witness is supplied as Type-data, the signed point value is obtained
directly.  They deliberately do not manufacture that witness from `absConv`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R] {S : IntSpaceRC X R}

/-- Full-domain data with the pointwise absolute SeriesSum witness exposed. -/
structure IntegrableRep.PointwiseDomainData (r : IntegrableRep S) (x : X) where
  mem : r.MemAt x
  absWitness : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x mem n))

/-- The requested pointwise witness is just a projection once it is carried as data. -/
def IntegrableRep.pointwiseWitnessData (r : IntegrableRep S) :
    forall (x : X) (hx : r.PointwiseDomainData x),
      RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hx.mem n)) :=
  fun _x hx => hx.absWitness

/-- The data package implies membership in the existing plain domain. -/
theorem IntegrableRep.pointwiseDomainData_mem (r : IntegrableRep S) {x : X}
    (hx : r.PointwiseDomainData x) : x ∈ r.domain :=
  ⟨hx.mem, ⟨hx.absWitness⟩⟩

/-- Signed convergence at a point, obtained from the exposed absolute witness. -/
def IntegrableRep.signedWitnessData (r : IntegrableRep S) (x : X)
    (hx : r.PointwiseDomainData x) :
    RSeq.SeriesSum (fun n => r.valueAt x hx.mem n) :=
  seriesSum_of_abs (r.pointwiseWitnessData x hx)

/-- A data-carrying partial function whose domain argument keeps Type-data. -/
structure DataPFunR (X R : Type*) where
  domData : X -> Type*
  toFun : forall x : X, domData x -> R

/-- Series-valued projection succeeds without any selector when the domain carries data. -/
def IntegrableRep.toDataPFunRSeries (r : IntegrableRep S) : DataPFunR X R where
  domData := r.PointwiseDomainData
  toFun := fun x hx => (r.signedWitnessData x hx).sum

/-- Any supplied absolute witness gives the same signed value as the data projection. -/
theorem IntegrableRep.toDataPFunRSeries_represents (r : IntegrableRep S)
    (x : X) (hx : (r.toDataPFunRSeries).domData x)
    (hrabs : RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hx.mem n))) :
    (seriesSum_of_abs hrabs).sum = (r.toDataPFunRSeries).toFun x hx := by
  unfold IntegrableRep.toDataPFunRSeries IntegrableRep.signedWitnessData
    IntegrableRep.pointwiseWitnessData
  exact seriesSum_unique _ _

end BishopC
