-- Prove2me | Theorems.Thm_WorkbookSource_base_52965
-- name    : WorkbookSource.base_52965
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:57:51.257366+00:00
-- url     : https://prove2.me/theorems/a4ff87de-9d80-4e51-8d83-77b30133cca9
-- title:
--   A weighted cyclic linear ratio sum is at least nine quarters
-- statement:
--   Let $ a,$ $ b$ and $ c$ are positive numbers. Prove that:
--    $ \frac {2a + b}{a + c + 2b} + \frac {2b + c}{b + a + 2c} + \frac {2c + a}{c + b + 2a}\geq\frac {9}{4}
--    There is a nice proof.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52965` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52965; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52965 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a + b) / (a + c + 2 * b) + (2 * b + c) / (b + a + 2 * c) + (2 * c + a) / (c + b + 2 * a) ≥ 9 / 4  :=  by sorry
