-- Prove2me | Theorems.Thm_lean_workbook_plus_35485
-- name    : lean_workbook_plus_35485
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a50710b9-1837-47a4-b1dc-e5df4dfa51d8
-- statement:
--   Determine the range of $y$ where $y = 2\sin p$ and $-\frac{\pi}{2} \leq p \leq \frac{\pi}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35485 (p y : ℝ) (h₁ : y = 2 * Real.sin p) (h₂ : -Real.pi / 2 ≤ p ∧ p ≤ Real.pi / 2) : -2 ≤ y ∧ y ≤ 2   :=  by sorry
