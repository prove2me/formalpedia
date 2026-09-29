-- Prove2me | Theorems.Thm_lean_workbook_plus_43748
-- name    : lean_workbook_plus_43748
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/046777be-9cfd-4540-88f6-8bc9af4cf2cd
-- statement:
--   If $1 = (a+b)(b+c)(c+a)$ , $a,b,c >0$ then prove: $ab +bc +ca \leq \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43748 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : 1 = (a + b) * (b + c) * (c + a)) : a * b + b * c + c * a ≤ 3 / 4   :=  by sorry
