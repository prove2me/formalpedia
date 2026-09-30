-- Prove2me | solution 1 for lean_workbook_plus_79560
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:03:44.186503+00:00
-- url     : https://prove2.me/submissions/66288cfe-b34c-41ff-a24f-1a29a8a891ac

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∃ f : ℝ → ℝ, ContinuousOn f (Set.Ioi 0) ∧
    ∀ x > 0, f (f x) = x ∧ f (x + 1) = f x / (f x + 1) := by
  refine ⟨fun x => x⁻¹, continuousOn_id.inv₀ (fun x hx => ne_of_gt hx), ?_⟩
  intro x hx
  constructor
  · exact inv_inv x
  · have hx0 : x ≠ 0 := ne_of_gt hx
    have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith)
    dsimp
    field_simp
    ring

#print axioms solution
