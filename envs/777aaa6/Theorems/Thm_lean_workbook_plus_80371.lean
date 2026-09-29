-- Prove2me | Theorems.Thm_lean_workbook_plus_80371
-- name    : lean_workbook_plus_80371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/0d1214b9-09ca-47b4-9c9c-c4122d905e12
-- statement:
--   c): $x_{n+1}=x^{2}_{n}+\frac{3}{16}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80371 : ∃ (x : ℕ → ℝ), x 0 = 1 ∧ ∀ n, x (n + 1) = x n ^ 2 + 3 / 16   :=  by sorry
