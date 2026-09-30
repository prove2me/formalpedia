-- Prove2me | solution 1 for lean_workbook_plus_47604
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:20.267463+00:00
-- url     : https://prove2.me/submissions/7a1d7f8b-dd3a-4d51-9e5c-4655f51d2cf1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ,
    x ∈ Set.Ioo 1 δ → |(x ^ 3 - 1) / (x - 1) - 3| < ε := by
  intro ε hε
  have hc : ContinuousAt (fun x : ℝ => x ^ 2 + x + 1) 1 := by fun_prop
  obtain ⟨d, hd, hdist⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨1 + d, by linarith, ?_⟩
  intro x hx
  have hnear : dist x 1 < d := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hx.1)]
    linarith [hx.2]
  have he : (x ^ 3 - 1) / (x - 1) = x ^ 2 + x + 1 := by
    field_simp [sub_ne_zero.mpr (ne_of_gt hx.1)]
    ring
  rw [he]
  simpa only [Real.dist_eq, show (1 : ℝ) ^ 2 + 1 + 1 = 3 by ring] using hdist hnear

#print axioms solution
