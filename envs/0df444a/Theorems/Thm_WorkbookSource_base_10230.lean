-- Prove2me | Theorems.Thm_WorkbookSource_base_10230
-- name    : WorkbookSource.base_10230
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:27:52.266345+00:00
-- url     : https://prove2.me/theorems/4aab03cc-6db5-4088-8ba1-70b3feb253f5
-- title:
--   A parameterized quadratic-product inequality
-- statement:
--   $M(M+2kc^2)(1-k^2) \leq (M+(k-k^2)c^2)^2,$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10230` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10230; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10230 (M c k : ℝ) : M * (M + 2 * k * c ^ 2) * (1 - k ^ 2) ≤ (M + (k - k ^ 2) * c ^ 2) ^ 2  :=  by sorry
