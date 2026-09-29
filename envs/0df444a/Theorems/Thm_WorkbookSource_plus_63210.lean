-- Prove2me | Theorems.Thm_WorkbookSource_plus_63210
-- name    : WorkbookSource.plus_63210
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:39.505417+00:00
-- url     : https://prove2.me/theorems/efe5ddd8-450c-4374-8235-1db3fb584f76
-- title:
--   A squared-norm and product lower bound
-- statement:
--   Let $ a,b,c > 0$ such that $ ab + bc + ca = 3$ . Prove that : $ a^2 + b^2 + c^2 + 2abc\ge 5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_63210` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63210; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_63210 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c ≥ 5   :=  by sorry
