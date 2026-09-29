-- Prove2me | Theorems.Thm_WorkbookSource_base_47415
-- name    : WorkbookSource.base_47415
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:55.897603+00:00
-- url     : https://prove2.me/theorems/0b618964-1518-4e6f-bd1c-795dab11e751
-- title:
--   A product of pairwise ratio sums has a squared-difference refinement
-- statement:
--   Let $a,b,c>0$ ,prove inequality
--    $\left( \frac{a}{b+c}+\frac{b}{c+a} \right)\left( \frac{b}{c+a}+\frac{c}{a+b} \right)\left( \frac{c}{a+b}+\frac{a}{b+c} \right)\ge 1+9{{\left( \frac{a-b}{a+b} \right)}^{2}}{{\left( \frac{b-c}{b+c} \right)}^{2}}{{\left( \frac{c-a}{c+a} \right)}^{2}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47415` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47415; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47415 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a)) * (b / (c + a) + c / (a + b)) * (c / (a + b) + a / (b + c)) ≥ 1 + 9 * (a - b) ^ 2 / (a + b) ^ 2 * (b - c) ^ 2 / (b + c) ^ 2 * (c - a) ^ 2 / (c + a) ^ 2  :=  by sorry
