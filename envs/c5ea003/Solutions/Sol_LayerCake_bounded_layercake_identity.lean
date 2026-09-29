-- Prove2me | solution 1 for LayerCake.bounded_layercake_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:59:30.607343+00:00
-- url     : https://prove2.me/submissions/12f16b8e-dc63-4c00-9649-ef16ddfd89fd

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped Topology ENNReal

theorem solution (u M : ℝ) (h : |u| ≤ M) :
    u + M = ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio u) 1 t := by
  have hlo : -M ≤ u := by
    have := neg_le_of_abs_le h
    linarith
  have hhi : u ≤ M := le_of_abs_le h
  have hset : Set.Icc (-M) M ∩ Set.Iio u = Set.Ico (-M) u := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2.le hhi⟩, h2⟩
  have hint : ∫ t in Set.Icc (-M) M, Set.indicator (Set.Iio u) 1 t
      = ∫ _ in Set.Ico (-M) u, (1 : ℝ) := by
    rw [setIntegral_indicator (measurableSet_Iio (a := u)), hset]
    rfl
  rw [hint]
  have hvol : ((volume.restrict (Set.Ico (-M) u)) Set.univ).toReal = u + M := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ u - -M)]
    ring
  have hint2 : (∫ _ in Set.Ico (-M) u, (1 : ℝ))
      = ((volume.restrict (Set.Ico (-M) u)) Set.univ).toReal := by
    simp [integral_const, smul_eq_mul, Measure.real_def]
  rw [hint2, hvol]
