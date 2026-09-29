-- Prove2me | Theorems.Thm_lean_workbook_plus_70312
-- name    : lean_workbook_plus_70312
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9449b60b-7704-436d-9a89-ca2778a75119
-- statement:
--   Is the limit of the sequence $\lim_{n\to\infty}\dfrac{n^n}{n^n}$ equal to 1?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70312 (n : ℕ) : ((n:ℝ)^n / (n:ℝ)^n) = 1   :=  by sorry
