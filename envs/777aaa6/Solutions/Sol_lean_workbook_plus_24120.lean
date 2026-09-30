-- Prove2me | solution 1 for lean_workbook_plus_24120
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:19:41.045586+00:00
-- url     : https://prove2.me/submissions/aa067d61-bbcd-4fa0-8c25-4eb0bacb35c9

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f = fun (y:ℝ) ↦ y + f 0) : ∃ (α : ℝ), ∀ (y : ℝ), f y = α + y := by
  refine ⟨f 0, fun y => ?_⟩
  have h := congrFun hf y
  simp only [] at h
  rw [h, add_comm]
