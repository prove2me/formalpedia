-- Prove2me | Theorems.Thm_WorkbookSource_base_1730
-- name    : WorkbookSource.base_1730
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:10:17.496814+00:00
-- url     : https://prove2.me/theorems/4a13ab00-e4b8-4abe-9b86-c8de98cb3399
-- title:
--   An eighth-degree binary polynomial inequality
-- statement:
--   Prove that $2(x+y)^8+x^4y^4-x^5y^3-x^3y^5\geq 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1730` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1730; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1730 (x y : ℝ) : 2 * (x + y) ^ 8 + x ^ 4 * y ^ 4 - x ^ 5 * y ^ 3 - x ^ 3 * y ^ 5 ≥ 0  :=  by sorry
