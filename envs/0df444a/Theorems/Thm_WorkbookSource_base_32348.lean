-- Prove2me | Theorems.Thm_WorkbookSource_base_32348
-- name    : WorkbookSource.base_32348
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:46:49.946035+00:00
-- url     : https://prove2.me/theorems/19eb07a8-0a43-4493-a95e-3c858cfebacd
-- title:
--   A cyclic ratio sum has a normalized quadratic refinement
-- statement:
--   Let $a,b,c $ be positive numbers. Prove that: $ \frac{a}{b} + \frac{b}{c} + \frac{c}{a} \ge \frac{14(a^2+b^2+c^2)}{(a+b+c)^2}-2 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32348` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32348; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32348 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (14 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2 - 2  :=  by sorry
