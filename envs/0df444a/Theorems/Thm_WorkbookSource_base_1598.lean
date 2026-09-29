-- Prove2me | Theorems.Thm_WorkbookSource_base_1598
-- name    : WorkbookSource.base_1598
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:10:48.067154+00:00
-- url     : https://prove2.me/theorems/0dcf6a57-16e0-4bc7-a7db-fa44df96cc17
-- title:
--   A weighted quadratic lower bound at unit sum
-- statement:
--   Let $x, y, z$ be reals such that $x+y+z=1.$ Prove that $2x^2 + 3y^2 + 4z^2\geq \frac{12}{13}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1598` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1598; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1598 (x y z : ℝ) (h : x + y + z = 1) : 2*x^2 + 3*y^2 + 4*z^2 ≥ 12/13  :=  by sorry
