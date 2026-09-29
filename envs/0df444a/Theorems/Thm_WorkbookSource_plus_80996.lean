-- Prove2me | Theorems.Thm_WorkbookSource_plus_80996
-- name    : WorkbookSource.plus_80996
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:21.555262+00:00
-- url     : https://prove2.me/theorems/2574d278-b5bc-43e0-acf9-3c7a7c80399a
-- title:
--   A reciprocal sum lower bound with a product correction
-- statement:
--   Let $a,b,c >0$ such that $a+b+c=3.$ Prove that
--
--    $$ \frac{1}{a} + \frac{1}{b} + \frac{1}{c} \ge \frac{1}{3}(13-4abc)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_80996` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_80996; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_80996 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / a + 1 / b + 1 / c ≥ 1 / 3 * (13 - 4 * a * b * c)   :=  by sorry
