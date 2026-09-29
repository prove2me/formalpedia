-- Prove2me | Theorems.Thm_lean_workbook_plus_76519
-- name    : lean_workbook_plus_76519
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f19d33bd-7660-4fbd-b56e-d24ce3ed0b01
-- statement:
--   Prove $ \lim_{x\to0}\frac{\sin x}{x}=1$ using the geometric definition of $ \sin$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76519 (x : ℝ) (hx : x ≠ 0) :
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo (-δ) δ → |sin x / x - 1| < ε   :=  by sorry
