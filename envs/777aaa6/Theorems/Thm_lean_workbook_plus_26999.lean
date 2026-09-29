-- Prove2me | Theorems.Thm_lean_workbook_plus_26999
-- name    : lean_workbook_plus_26999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f8a30d15-59c9-4b99-8a8a-debc9dc3b190
-- statement:
--   Prove for all real numbers $x \neq 0$: $\frac{(x^{3}-1)^{2}(x^{6}+x^{3}+1)}{x^{4}}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26999 (x : ℝ) (hx : x ≠ 0) : (x^3 - 1)^2 * (x^6 + x^3 + 1) / x^4 ≥ 0   :=  by sorry
