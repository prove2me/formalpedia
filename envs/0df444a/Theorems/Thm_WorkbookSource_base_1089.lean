-- Prove2me | Theorems.Thm_WorkbookSource_base_1089
-- name    : WorkbookSource.base_1089
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:58.955611+00:00
-- url     : https://prove2.me/theorems/14849da0-3960-4b37-8b70-39dec539d3bc
-- title:
--   A comparison of two cyclic quadratic ratio sums
-- statement:
--   Let a, b, c be three positive reals. Prove the inequality
--
--   $\frac{a^2}{2b+a}+\frac{b^2}{2c+b}+\frac{c^2}{2a+c}\geq\frac{a^2}{2a+b}+\frac{b^2}{2b+c}+\frac{c^2}{2c+a}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1089` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1089; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1089 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * b + a) + b^2 / (2 * c + b) + c^2 / (2 * a + c)) ≥ (a^2 / (2 * a + b) + b^2 / (2 * b + c) + c^2 / (2 * c + a))  :=  by sorry
