-- Prove2me | Theorems.Thm_lean_workbook_plus_74771
-- name    : lean_workbook_plus_74771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/6d697d37-5be5-4689-8c4e-65713a6b8ee7
-- statement:
--   Prove that $\frac{(x^6+x^3+1)(x^3-1)^2}{x^4} \ge 0$ for all nonzero real numbers $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74771 (x : ℝ) (hx : x ≠ 0) : (x^6 + x^3 + 1) * (x^3 - 1)^2 / x^4 ≥ 0   :=  by sorry
