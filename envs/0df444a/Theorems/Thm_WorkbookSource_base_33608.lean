-- Prove2me | Theorems.Thm_WorkbookSource_base_33608
-- name    : WorkbookSource.base_33608
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:29:47.905189+00:00
-- url     : https://prove2.me/theorems/3ed07271-d358-4bd0-a3fd-549caefeb08e
-- title:
--   A cubic ratio sum with a triple-product correction
-- statement:
--   For any three positive reals a, b, c, we have $\frac{a^3+3abc}{b+c}+\frac{b^3+3abc}{c+a}+\frac{c^3+3abc}{a+b} \ge 2(ab+bc+ca)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33608` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33608; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33608 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 3 * a * b * c) / (b + c) + (b^3 + 3 * a * b * c) / (c + a) + (c^3 + 3 * a * b * c) / (a + b) ≥ 2 * (a * b + b * c + c * a)  :=  by sorry
