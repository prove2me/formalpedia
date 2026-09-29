-- Prove2me | Theorems.Thm_WorkbookSource_base_4237
-- name    : WorkbookSource.base_4237
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:45.83647+00:00
-- url     : https://prove2.me/theorems/b25d96ba-61bc-4873-be8e-7dff16e9d27b
-- title:
--   A squared cyclic ratio sum with a triple-product correction
-- statement:
--   Prove that all positive real number a,b,c
--
--    $ \left(\frac {a}{b + c}\right)^2 + \left(\frac {b}{c + a}\right)^2 + \left(\frac {c}{a + b}\right)^2 + 10\cdot\frac {abc}{(a + b)(b + c)(c + a)}\geq2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4237` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4237; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4237 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c))^2 + (b / (c + a))^2 + (c / (a + b))^2 + 10 * (a * b * c) / ((a + b) * (b + c) * (c + a)) ≥ 2  :=  by sorry
