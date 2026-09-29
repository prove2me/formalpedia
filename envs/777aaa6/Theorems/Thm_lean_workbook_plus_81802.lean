-- Prove2me | Theorems.Thm_lean_workbook_plus_81802
-- name    : lean_workbook_plus_81802
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/74edd28e-aa1d-4de8-8b59-fb3f03d93a96
-- statement:
--   Let $a$ , $b$ and $c$ $>0$ . Prove that: \n $ \frac{3a+c}{a+b} + \frac{3b+a}{b+c} +\frac{3c+b}{c+a} \geq 6$ \n(a special case: <http://www.artofproblemsolving.com/community/c6h1250196_inequality_with_positive_real_numbers>)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81802 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (3 * a + c) / (a + b) + (3 * b + a) / (b + c) + (3 * c + b) / (c + a) ≥ 6   :=  by sorry
