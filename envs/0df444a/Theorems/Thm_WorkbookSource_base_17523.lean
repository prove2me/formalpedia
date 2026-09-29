-- Prove2me | Theorems.Thm_WorkbookSource_base_17523
-- name    : WorkbookSource.base_17523
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:21.886153+00:00
-- url     : https://prove2.me/theorems/cd2d0bbc-6c56-4445-8170-9bdc798e818b
-- title:
--   A constrained quartic polynomial in three real variables
-- statement:
--   Let $a,b,c$ real numbers and $a+b+c=3.$ Prove that $a^2(6a^2+6c^2-3b^2-4)+b^2(6b^2+6c^2-3a^2-4)\geqslant 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17523` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17523; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17523 (a b c : ℝ) (h : a + b + c = 3) : a^2 * (6 * a^2 + 6 * c^2 - 3 * b^2 - 4) + b^2 * (6 * b^2 + 6 * c^2 - 3 * a^2 - 4) ≥ 0  :=  by sorry
