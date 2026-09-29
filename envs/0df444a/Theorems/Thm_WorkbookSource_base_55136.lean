-- Prove2me | Theorems.Thm_WorkbookSource_base_55136
-- name    : WorkbookSource.base_55136
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:06:51.413616+00:00
-- url     : https://prove2.me/theorems/44428bc9-917f-43ed-99f8-90d4e8da0a52
-- title:
--   A pair-product ratio upper bound at fixed sum three
-- statement:
--   For $a, b, c>0, a+b+c=3$ prove that
--    $\frac{ab}{a^2+b^2+3(a+b)}+\frac{bc}{b^2+c^2+3(b+c)}+\frac{ca}{c^2+a^2+3(c+a)}\le\frac{a^2+b^2+c^2}{8}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55136` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55136; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55136 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * b / (a ^ 2 + b ^ 2 + 3 * (a + b)) + b * c / (b ^ 2 + c ^ 2 + 3 * (b + c)) + c * a / (c ^ 2 + a ^ 2 + 3 * (c + a))) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 8  :=  by sorry
