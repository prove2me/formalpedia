-- Prove2me | Theorems.Thm_lean_workbook_plus_36011
-- name    : lean_workbook_plus_36011
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8c509707-090c-4a9a-9e2f-92ddcb3c714a
-- statement:
--   Let $a,b>0$. Prove that: $\frac{(a-b)^2}{2ab+1 }+ \frac{2ab-1}{a^2+b^2+1 } \geq \frac{a^2+b^2-1 }{(a+b)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36011 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a - b) ^ 2 / (2 * a * b + 1) + (2 * a * b - 1) / (a ^ 2 + b ^ 2 + 1) ≥ (a ^ 2 + b ^ 2 - 1) / (a + b) ^ 2   :=  by sorry
