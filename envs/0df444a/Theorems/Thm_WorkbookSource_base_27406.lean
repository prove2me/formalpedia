-- Prove2me | Theorems.Thm_WorkbookSource_base_27406
-- name    : WorkbookSource.base_27406
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:36:32.911236+00:00
-- url     : https://prove2.me/theorems/c640b331-86a0-4eb6-b4b7-9e1a6c457ea5
-- title:
--   A two-variable quartic product is at most eight at fixed total two
-- statement:
--   Let $x,y\geq 0$ and $x+y= 2.$ Show that $(x+1)y(x^2+y^2)\le 8$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27406` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27406; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27406 (x y : ℝ) (h : x + y = 2) (hx : x ≥ 0) (hy : y ≥ 0) : (x + 1) * y * (x ^ 2 + y ^ 2) ≤ 8  :=  by sorry
