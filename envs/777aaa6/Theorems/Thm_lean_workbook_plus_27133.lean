-- Prove2me | Theorems.Thm_lean_workbook_plus_27133
-- name    : lean_workbook_plus_27133
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/955af5ba-fa99-4d55-84dd-1c9b2170447a
-- statement:
--   prove that $\frac{1}{2n}<\{n\sqrt{7}\}<1-\frac{1}{6n}$ for all $n\in \mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27133 (n : ℕ) : (1 / (2 * n) : ℝ) < (n * Real.sqrt 7 % 1) ∧ (n * Real.sqrt 7 % 1) < 1 - 1 / (6 * n)   :=  by sorry
