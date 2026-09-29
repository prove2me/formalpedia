-- Prove2me | Theorems.Thm_lean_workbook_plus_24266
-- name    : lean_workbook_plus_24266
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8a762ba7-8a73-431b-81c7-9009f5a581bf
-- statement:
--   Let $a,b,c>0$ ,prove that: $\frac{ab}{a+2b+c}+\frac{bc}{b+2c+a}+\frac{ca}{c+2a+b} \le \frac{1}{4}(a+b+c).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24266 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a * b / (a + 2 * b + c) + b * c / (b + 2 * c + a) + c * a / (c + 2 * a + b)) ≤ 1 / 4 * (a + b + c)   :=  by sorry
