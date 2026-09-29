-- Prove2me | Theorems.Thm_lean_workbook_plus_33830
-- name    : lean_workbook_plus_33830
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9afb00b0-7495-448a-bda9-d1ba1b15b9d6
-- statement:
--   prove that $\frac{1}{2n}<\{n\sqrt{7}\}<1-\frac{1}{6n}$ for all $n\in \mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33830 (n : ℕ) : 1 / (2 * n) < (n * Real.sqrt 7 % 1) ∧ (n * Real.sqrt 7 % 1) < 1 - 1 / (6 * n)   :=  by sorry
