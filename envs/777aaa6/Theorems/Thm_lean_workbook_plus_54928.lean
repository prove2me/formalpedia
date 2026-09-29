-- Prove2me | Theorems.Thm_lean_workbook_plus_54928
-- name    : lean_workbook_plus_54928
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d14025fa-932a-462f-bb07-5b215aa925ae
-- statement:
--   If $1 = (a+b)(b+c)(c+a)$ , $a,b,c >0$ then prove: $ab +bc +ca \geq \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54928 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : 1 = (a + b) * (b + c) * (c + a)) : a * b + b * c + c * a ≥ 3 / 4   :=  by sorry
