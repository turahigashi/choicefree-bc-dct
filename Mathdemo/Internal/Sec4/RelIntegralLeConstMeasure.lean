import Mathdemo.Internal.BishopSec4_Convergence

/-! Technical auxiliary material for the public import closure. -/

namespace BishopC

variable {X R : Type*} [COFOC R]

/-- Technical lemma used in the public import closure. -/
theorem relIntegral_le_const_measure {S : IntSpaceRC X R} (C : BSet X) (hC : IntegrableSet1 S C)
    (f : IntegrableRep S) (hnn : RepNonneg f) (c : R)
    (hbound : ∀ (x : X)
      (hfDom : f.MemAt x) (hχDom : hC.rep.MemAt x)
      (hfabs : RSeq.SeriesSum (fun n => COF.abs (f.valueAt x hfDom n)))
      (hχabs : RSeq.SeriesSum (fun n => COF.abs (hC.rep.valueAt x hχDom n))),
      (seriesSum_of_abs hχabs).sum = 1 → Le (seriesSum_of_abs hfabs).sum c) :
    Le (relIntegral C hC f hnn) (c * measure1 S hC) := by
  show Le (prop_4_2_chi_f_rep C hC f hnn).integral (c * hC.rep.integral)
  rw [← IntegrableRep.integral_smul c hC.rep]
  refine prop_1_11 (isFull_inter (isFull_inter
      (prop_4_2_chi_f_rep C hC f hnn).domain_isFull f.domain_isFull) hC.rep.domain_isFull)
    (prop_4_2_chi_f_rep C hC f hnn) (hC.rep.smul c) ?_
  intro x hx hrDom hr'Dom hr hr'
  obtain ⟨⟨hxrep, hxf⟩, hxχ⟩ := hx
  obtain ⟨hflatDom, ⟨hflatabs⟩⟩ := hxrep
  obtain ⟨hfDom, ⟨hfabs⟩⟩ := hxf
  obtain ⟨hχDom, ⟨hχabs⟩⟩ := hxχ
  have hval := prop_4_2_chi_f_rep_value C hC f hnn
    hflatDom hχDom hfDom hflatabs hχabs hfabs
  rw [seriesSum_unique hr (seriesSum_of_abs hflatabs), hval,
      seriesSum_unique hr'
        (smul_seriesSum_value c hχDom (seriesSum_of_abs hχabs))]
  -- goal: Le (χ_C.sum * f.sum) ((smul_seriesSum_value c χ).sum)
  -- Technical note.
  show Le ((seriesSum_of_abs hχabs).sum * (seriesSum_of_abs hfabs).sum)
        (c * (seriesSum_of_abs hχabs).sum)
  have hfnn : Nonneg (seriesSum_of_abs hfabs).sum :=
    hnn x hfDom hfabs (seriesSum_of_abs hfabs)
  have hχ01 : (seriesSum_of_abs hχabs).sum = 0 ∨ (seriesSum_of_abs hχabs).sum = 1 := by
    rcases (hC.valid x hχDom hχabs).1 with hS1 | hS2
    · exact Or.inr ((hC.valid x hχDom hχabs).2.1 hS1 (seriesSum_of_abs hχabs))
    · exact Or.inl ((hC.valid x hχDom hχabs).2.2 hS2 (seriesSum_of_abs hχabs))
  rcases hχ01 with h0 | h1
  · rw [h0, zero_mul, mul_zero]; exact le_refl _
  · rw [h1, one_mul, mul_one]; exact hbound x hfDom hχDom hfabs hχabs h1


end BishopC
