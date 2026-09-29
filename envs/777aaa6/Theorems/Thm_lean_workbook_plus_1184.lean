-- Prove2me | Theorems.Thm_lean_workbook_plus_1184
-- name    : lean_workbook_plus_1184
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5b7b0609-b1be-4e73-8950-dfada3758f7d
-- statement:
--   Prove that $\sum_{k=1}^{n}\frac{2k^4-k^3+2k^2+1}{k+2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1184 (n : ℕ) : ∑ k in Finset.Icc 1 n, (2 * k ^ 4 - k ^ 3 + 2 * k ^ 2 + 1) / (k + 2) ≥ 0   :=  by sorry
