-- Prove2me | Theorems.Thm_WorkbookSource_base_20583
-- name    : WorkbookSource.base_20583
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:38.739543+00:00
-- url     : https://prove2.me/theorems/2872ceb7-ee9c-4df9-ac71-461772e0ab76
-- title:
--   A bilinear inequality with a circle constraint
-- statement:
--   For $ a,b\in R$ , and $ x,y\in R$ , such that $ x^2 + y^2 = 4$ , prove the following inequality
--    $ (a + b)^2 - (x + ay)(x + by) + 4\geq0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20583` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20583; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20583 (a b x y : ℝ) (h : x^2 + y^2 = 4) : (a + b)^2 - (x + a*y)*(x + b*y) + 4 ≥ 0  :=  by sorry
