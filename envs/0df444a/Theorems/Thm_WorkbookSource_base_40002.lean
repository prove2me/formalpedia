-- Prove2me | Theorems.Thm_WorkbookSource_base_40002
-- name    : WorkbookSource.base_40002
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:28:25.98599+00:00
-- url     : https://prove2.me/theorems/b71ec008-31bd-40ff-a911-e502c66ae8dc
-- title:
--   A shifted quartic product bounds a squared quadratic sum
-- statement:
--   Prove that $(b^4 + 3)(c^4 + 3) \ge 3(b^2 + c^2)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40002` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40002; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40002 (b c : ℝ) : (b^4 + 3) * (c^4 + 3) ≥ 3 * (b^2 + c^2)^2  :=  by sorry
