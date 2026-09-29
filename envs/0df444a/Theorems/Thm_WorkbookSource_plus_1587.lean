-- Prove2me | Theorems.Thm_WorkbookSource_plus_1587
-- name    : WorkbookSource.plus_1587
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:52:17.616094+00:00
-- url     : https://prove2.me/theorems/0ada04b5-a9d0-4452-8e77-bb533e935de7
-- title:
--   A normalized product correction bounds a quadratic ratio
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{27abc}{(a+b+c)^3}+2\geq\frac{3(ab+bc+ca)}{a^2+b^2+c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_1587` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_1587; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_1587 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (27 * a * b * c) / (a + b + c) ^ 3 + 2 ≥ (3 * (a * b + b * c + a * c)) / (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
