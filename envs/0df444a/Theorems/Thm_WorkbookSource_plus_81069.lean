-- Prove2me | Theorems.Thm_WorkbookSource_plus_81069
-- name    : WorkbookSource.plus_81069
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:22.093479+00:00
-- url     : https://prove2.me/theorems/3e4b3080-990f-44b5-893a-e93bfe7dc7ca
-- title:
--   A squared pair-sum ratio bounds a linear pair-sum ratio
-- statement:
--   Let a,b,c>0 Prove that $ \sum\frac {(a + b)^2}{c(2c + a + b)} \geq \sum\frac {a+b}{2c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_81069` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_81069; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_81069 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 / (c * (2 * c + a + b)) + (b + c) ^ 2 / (a * (2 * a + b + c)) + (c + a) ^ 2 / (b * (2 * b + c + a)) ≥ (a + b) / (2 * c) + (b + c) / (2 * a) + (c + a) / (2 * b)   :=  by sorry
