-- Prove2me | solution 1 for lean_workbook_plus_15622
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:25:01.492085+00:00
-- url     : https://prove2.me/submissions/32365326-3e75-4acb-847b-e8e5b3da98dc

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (u v p q : Fin n → ℝ) (h₁ : u > v) (h₂ : p > q) : u + p > v + q := by
  rw [gt_iff_lt, Pi.lt_def] at h₁ h₂ ⊢
  obtain ⟨hle1, i, hi⟩ := h₁
  obtain ⟨hle2, j, hj⟩ := h₂
  refine ⟨fun k => add_le_add (hle1 k) (hle2 k), i, ?_⟩
  simp only [Pi.add_apply]
  exact add_lt_add_of_lt_of_le hi (hle2 i)
