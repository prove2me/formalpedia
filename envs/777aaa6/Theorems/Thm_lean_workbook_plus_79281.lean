-- Prove2me | Theorems.Thm_lean_workbook_plus_79281
-- name    : lean_workbook_plus_79281
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b066c86a-177d-4cc2-9aab-bf76bf7abe39
-- statement:
--   Prove or disprove $(1-\frac{1}{7})(1-\frac{1}{7^2})(1-\frac{1}{7^3}).....(1-\frac{1}{7^n})=\frac{7}{6}(1-\frac{1}{7^{n+1}})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79281 (n : ℕ) : (∏ k in Finset.range (n+1), (1-(1/7)^k)) = (7/6)*(1-(1/7)^(n+1))   :=  by sorry
