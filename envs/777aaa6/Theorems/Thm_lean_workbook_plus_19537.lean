-- Prove2me | Theorems.Thm_lean_workbook_plus_19537
-- name    : lean_workbook_plus_19537
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/316b1eef-b5f2-417a-918b-cce83b770041
-- statement:
--   Let $a, b, c > 0$ . Prove, that $8(a^3+b^3+c^3)^2\geq9(a^2+bc)(b^2+ca)(c^2+ab)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19537 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≥ 9 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)   :=  by sorry
