-- Prove2me | Theorems.Thm_lean_workbook_plus_38124
-- name    : lean_workbook_plus_38124
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/92e7819d-e6a4-4d37-b2d8-db609115be53
-- statement:
--   For $a,b,c >0$ we have: $\sum \frac{a}{2a+b+c} \le \frac{3}{4}$ because it is equivalent to: $\sum \frac{b+c}{2a+b+c} \ge \frac{3}{2}$ what is just Nesbitt's inequality using $a+b=x, \; a+c=y, \; b+c=z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38124 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (2 * a + b + c) + b / (2 * b + c + a) + c / (2 * c + a + b)) ≤ 3 / 4   :=  by sorry
