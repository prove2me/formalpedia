-- Prove2me | Theorems.Thm_lean_workbook_plus_26537
-- name    : lean_workbook_plus_26537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2a1e5b95-b190-43d2-9277-2388eb078373
-- statement:
--   With $a,b,c>0$ and $ab+bc+ca=abc$ , prove: \n $$\left(3a+2b+c\right)\left(3b+2c+a\right)\left(3c+2a+b\right)\ge 24abc\left(a+b+c\right)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26537 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = a * b + b * c + c * a) : (3 * a + 2 * b + c) * (3 * b + 2 * c + a) * (3 * c + 2 * a + b) ≥ 24 * a * b * c * (a + b + c)   :=  by sorry
