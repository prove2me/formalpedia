-- Prove2me | Theorems.Thm_lean_workbook_plus_39026
-- name    : lean_workbook_plus_39026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c3de666a-2089-4cc5-a295-a54b94146098
-- statement:
--   For positive real numbers $a,b$ , prove that $\frac{1}{3a+b}+\frac{1}{a+3b} \leq \frac{1}{4}(\frac{1}{a} + \frac{1}{b}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39026 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (3 * a + b) + 1 / (a + 3 * b) ≤ (1 / 4) * (1 / a + 1 / b)   :=  by sorry
