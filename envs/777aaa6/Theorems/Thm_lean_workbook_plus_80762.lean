-- Prove2me | Theorems.Thm_lean_workbook_plus_80762
-- name    : lean_workbook_plus_80762
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/ccbf1fa3-6fb3-4342-bfc6-fb2f772fc2a3
-- statement:
--   How can you show that $n^a \cdot n^b=n^{a+b}$, $\frac{n^a}{n^b}=n^{a-b}$, and $(n^a)^b=n^{ab}$ are true for any fractional (and more generally any real) $a$ and $b$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80762 (n a b : ℝ) (hn : n > 0) : n^a * n^b = n^(a + b)   :=  by sorry
