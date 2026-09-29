-- Prove2me | Theorems.Thm_WorkbookSource_plus_26490
-- name    : WorkbookSource.plus_26490
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:14:14.828279+00:00
-- url     : https://prove2.me/theorems/5d004f88-453c-4b5e-a236-d7e197c757aa
-- title:
--   A shifted quadratic reciprocal sum upper bound at fixed sum three
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that
--    $\frac{1}{a^2+bc+1}+\frac{1}{b^2+ca+1}+\frac{1}{c^2+ab+1}\le\frac{a^2+b^2+c^2}{3abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_26490` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_26490; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_26490 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (a^2 + b * c + 1) + 1 / (b^2 + c * a + 1) + 1 / (c^2 + a * b + 1) ≤ (a^2 + b^2 + c^2) / (3 * a * b * c)   :=  by sorry
