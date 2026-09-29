-- Prove2me | Theorems.Thm_WorkbookSource_base_5787
-- name    : WorkbookSource.base_5787
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:12.01638+00:00
-- url     : https://prove2.me/theorems/da4fd65c-0219-4bee-9fb9-1ff2eb4f4d85
-- title:
--   A two-variable rational product lower bound
-- statement:
--   Let $ x,y>0.$ Prove that $$\left(x+\frac{2}{y} \right) \left(\frac{y}{x}+2 \right)\geq 8$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5787` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5787; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5787 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x + 2/y) * (y/x + 2) ≥ 8  :=  by sorry
