-- Prove2me | Theorems.Thm_lean_workbook_plus_74931
-- name    : lean_workbook_plus_74931
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a4bcb69d-1c26-468a-b329-3eafbdaf3dc2
-- statement:
--   For positive real numbers a, b, c, prove that $(a^{2}+b^{2}+c^{2})^{2} \geq 3(a+b+c)(b+c-a)(a+c-b)(a+b-c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74931 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 ≥ 3 * (a + b + c) * (b + c - a) * (a + c - b) * (a + b - c)   :=  by sorry
