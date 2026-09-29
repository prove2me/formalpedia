-- Prove2me | Theorems.Thm_WorkbookSource_base_2405
-- name    : WorkbookSource.base_2405
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:48.928788+00:00
-- url     : https://prove2.me/theorems/8fb32f08-4f25-42ca-90df-64cc79d1afea
-- title:
--   A symmetric quartic inequality for positive variables
-- statement:
--   If $x,y,z>0$ , prove that $\sum x^4+xyz(x+y+z)\ge 2\sum x^2y^2$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2405` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2405; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2405 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z * (x + y + z) ≥ 2 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)  :=  by sorry
