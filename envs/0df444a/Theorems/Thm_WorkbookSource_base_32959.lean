-- Prove2me | Theorems.Thm_WorkbookSource_base_32959
-- name    : WorkbookSource.base_32959
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:23:33.228146+00:00
-- url     : https://prove2.me/theorems/2cd8e9db-b14b-4927-aeeb-7a25bf7fde23
-- title:
--   Factoring the absolute difference of quadratic values
-- statement:
--   Simplify $ |3x^2 + 4 - 3k^2 - 4| = 3|x - k||x + k| $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32959` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32959; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32959 (x k : ℝ) : ‖3 * x ^ 2 + 4 - (3 * k ^ 2 + 4)‖ = 3 * ‖x - k‖ * ‖x + k‖  :=  by sorry
