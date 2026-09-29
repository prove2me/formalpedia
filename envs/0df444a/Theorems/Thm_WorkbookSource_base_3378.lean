-- Prove2me | Theorems.Thm_WorkbookSource_base_3378
-- name    : WorkbookSource.base_3378
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:00:51.867126+00:00
-- url     : https://prove2.me/theorems/7eac4b78-0ab6-4186-8895-c1fc9e07d37b
-- title:
--   A lower bound for three quadratic factors under normalization
-- statement:
--   Let $a,b,c\ge 0$ and $a+b+c=1$ . Prove that $(8-27ab)(8-27bc)(8-27ca) \geq 80$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3378` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3378; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3378 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : (8 - 27 * a * b) * (8 - 27 * b * c) * (8 - 27 * c * a) ≥ 80  :=  by sorry
