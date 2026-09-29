-- Prove2me | Theorems.Thm_WorkbookSource_base_37591
-- name    : WorkbookSource.base_37591
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:31:17.744458+00:00
-- url     : https://prove2.me/theorems/22c936b8-4bba-4fdc-9055-b1785e9c239a
-- title:
--   A product of shifted ratios with a cubic reciprocal correction
-- statement:
--   Let $a, b, c>0$ . Prove that $\left( \frac{a}{b+c}+\frac{1}{2} \right)\left( \frac{b}{c+a}+\frac{1}{2} \right)\left( \frac{c}{a+b}+\frac{1}{2} \right)+\frac{abc}{6(a^3+b^3+c^3)} \geq\frac{19}{18}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37591` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37591; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37591 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) + a * b * c / (6 * (a ^ 3 + b ^ 3 + c ^ 3)) ≥ 19 / 18  :=  by sorry
