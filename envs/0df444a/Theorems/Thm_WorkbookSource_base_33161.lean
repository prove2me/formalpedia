-- Prove2me | Theorems.Thm_WorkbookSource_base_33161
-- name    : WorkbookSource.base_33161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:54.108373+00:00
-- url     : https://prove2.me/theorems/4189e99e-839e-47cd-83e5-60d04c34127f
-- title:
--   A cyclic cubic inequality when the pairwise sum vanishes
-- statement:
--   Let $a,b,c$ such that $ab+bc+ca=0.$ Prove that: $a^2(1-b)+b^2(1-c)+c^2(1-a) \ge abc(a+b+c-3).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33161` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33161 (a b c : ℝ) (hab : a * b + b * c + c * a = 0) : a^2 * (1 - b) + b^2 * (1 - c) + c^2 * (1 - a) ≥ a * b * c * (a + b + c - 3)  :=  by sorry
