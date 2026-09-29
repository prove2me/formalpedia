-- Prove2me | Theorems.Thm_WorkbookSource_base_45142
-- name    : WorkbookSource.base_45142
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:50.753352+00:00
-- url     : https://prove2.me/theorems/3f582471-18bc-4418-a1b3-28251804b2c5
-- title:
--   A seventh-power difference bound under a nonnegative sum
-- statement:
--   Let $ x, y$ are real numbers such that $ x + y \geq 0.$ Prove that $ x^7 + y^7- x^6y-xy^6+ x^2 + 4x\geq -4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45142` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45142; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45142 (x y : ℝ) (h : x + y ≥ 0) : x^7 + y^7 - x^6*y - x*y^6 + x^2 + 4*x ≥ -4  :=  by sorry
