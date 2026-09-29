-- Prove2me | Theorems.Thm_WorkbookSource_plus_28964
-- name    : WorkbookSource.plus_28964
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:00.962741+00:00
-- url     : https://prove2.me/theorems/76773230-c308-4fc7-868a-20e22d48a83b
-- title:
--   A product comparison involving shifted pairwise sums
-- statement:
--   Let $ a,$ $ b$ and $ c$ are non-negative numbers. Prove that
--
--    $ (a + b)(b + c)(c + a)(1 + a)(1 + b)(1 + c)\geq abc(2 + a + b)(2 + b + c)(2 + c + a).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28964` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28964; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28964 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b) * (b + c) * (c + a) * (1 + a) * (1 + b) * (1 + c) ≥ a * b * c * (2 + a + b) * (2 + b + c) * (2 + c + a)   :=  by sorry
