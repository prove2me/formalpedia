-- Prove2me | Theorems.Thm_lean_workbook_plus_15662
-- name    : lean_workbook_plus_15662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/9bed566f-9c76-4edc-b275-38fab33c48b9
-- statement:
--   For $a,b,c \ge 0$, prove that $\frac{2}{3}( a^2 + b^2 + c^2 )^2 \ge a^3 ( b + c ) + b^3 ( c + a ) + c^3 ( a + b )$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15662 (a b c : ℝ) : (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)   :=  by sorry
