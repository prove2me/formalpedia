-- Prove2me | solution 1 for lean_workbook_plus_49542
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:35.125182+00:00
-- url     : https://prove2.me/submissions/0a9bfac7-9c64-4d98-9f15-1256fce6be99

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ,
    x ∈ Set.Ioo 1 δ → |(x + 3) / (x ^ 2 + x + 4) - 2 / 3| < ε := by
  intro ε hε
  have hc : ContinuousAt (fun x : ℝ => (x + 3) / (x ^ 2 + x + 4)) 1 :=
    (continuousAt_id.add continuousAt_const).div
      ((continuousAt_id.pow 2 |>.add continuousAt_id).add continuousAt_const) (by norm_num)
  obtain ⟨d, hd, hdist⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨1 + d, by linarith, ?_⟩
  intro x hx
  have hnear : dist x 1 < d := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hx.1)]
    linarith [hx.2]
  simpa only [Real.dist_eq, show ((1 : ℝ) + 3) / (1 ^ 2 + 1 + 4) = 2 / 3 by norm_num]
    using hdist hnear

#print axioms solution
