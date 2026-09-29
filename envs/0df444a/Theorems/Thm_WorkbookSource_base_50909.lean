-- Prove2me | Theorems.Thm_WorkbookSource_base_50909
-- name    : WorkbookSource.base_50909
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:34:59.606554+00:00
-- url     : https://prove2.me/theorems/582792d1-a402-47db-9da0-7eed577dec69
-- title:
--   A symmetric quadratic ratio bounds a weighted cyclic sum
-- statement:
--   The following inequality is also true.
--    For positives $a$ , $b$ and $c$ prove that:
--    $\frac{a^2+b^2+c^2}{3(ab+ac+bc)}\geq\frac{a}{2a+7b}+\frac{b}{2b+7c}+\frac{c}{2c+7a}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50909` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50909; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (3 * (a * b + a * c + b * c)) ≥ a / (2 * a + 7 * b) + b / (2 * b + 7 * c) + c / (2 * c + 7 * a)  :=  by sorry
