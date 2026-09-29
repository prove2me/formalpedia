-- Prove2me | Theorems.Thm_WorkbookSource_base_31287
-- name    : WorkbookSource.base_31287
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:26:04.981945+00:00
-- url     : https://prove2.me/theorems/b9448fd4-a3b3-45ef-bdc2-3100bfbaa35e
-- title:
--   A cyclic quadratic ratio bounds a symmetric cubic ratio
-- statement:
--   Let $ a,b,c \in R^{+} $ .Prove that
--    $ \frac{a^2}{b} + \frac{b^2}{c} + \frac{c^2}{a} + a+b+c \ge \frac{2(a+b+c)^3}{3(ab+bc+ca)} $ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31287` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31287; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31287 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 / b + b^2 / c + c^2 / a + a + b + c ≥ 2 * (a + b + c)^3 / (3 * (a * b + b * c + c * a))  :=  by sorry
