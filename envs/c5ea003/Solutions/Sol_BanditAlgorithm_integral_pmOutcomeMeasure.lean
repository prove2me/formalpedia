-- Prove2me | solution 1 for BanditAlgorithm.integral_pmOutcomeMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:27:59.546542+00:00
-- url     : https://prove2.me/submissions/7c8190d9-3922-4e82-8a92-a3bfa2cd3538

import Definitions.Def_PartialMonitoringStochastic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

theorem _root_.solution
    {d : ℕ} (p : Fin d → ℝ) (hp : p ∈ stdSimplex ℝ (Fin d))
    (g : Fin d → ℝ) :
    ∫ i, g i ∂pmOutcomeMeasure p = ∑ i, p i * g i := by
  classical
  letI : IsProbabilityMeasure (pmOutcomeMeasure p) :=
    pmOutcomeMeasure_isProbabilityMeasure p hp
  have hint : Integrable g (pmOutcomeMeasure p) := by
    obtain ⟨C, hC⟩ := Finite.exists_le (fun i : Fin d => ‖g i‖)
    exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  rw [pmOutcomeMeasure] at hint ⊢
  rw [MeasureTheory.integral_sum_measure hint]
  simp only [tsum_fintype, MeasureTheory.integral_smul_measure, integral_dirac,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.toReal_ofReal (hp.1 i)]

end BanditAlgorithm
