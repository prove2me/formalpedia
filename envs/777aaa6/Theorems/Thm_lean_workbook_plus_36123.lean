-- Prove2me | Theorems.Thm_lean_workbook_plus_36123
-- name    : lean_workbook_plus_36123
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3bd9d4f0-5f48-44ef-b742-c1c5bd836c8d
-- statement:
--   Let $a,b,c>0$ . Prove that $(a+b+c)(ab+bc+ca) \le \frac 89 (a+b)(b+c)(c+a)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36123 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (a * b + b * c + c * a) ≤ (8 / 9) * (a + b) * (b + c) * (c + a)   :=  by sorry
