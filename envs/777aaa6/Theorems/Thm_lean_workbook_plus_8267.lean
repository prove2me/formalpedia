-- Prove2me | Theorems.Thm_lean_workbook_plus_8267
-- name    : lean_workbook_plus_8267
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4af93475-a0d0-4144-9160-0c2ee7c041a6
-- statement:
--   Let $a=\alpha\cdot\pi$ so that $\cos a=\frac 1{\sqrt 3}$ and $\cos^2 a=\frac 13$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8267 (a : ℝ) (h : a = π / 3) : cos a = 1 / Real.sqrt 3 ∧ cos a ^ 2 = 1 / 3   :=  by sorry
