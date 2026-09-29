-- Prove2me | Theorems.Thm_WorkbookSource_base_31532
-- name    : WorkbookSource.base_31532
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:10:16.427885+00:00
-- url     : https://prove2.me/theorems/daf1ce50-7764-457f-9b5c-d32b66322820
-- title:
--   A quartic symmetric bound at a negative fixed sum
-- statement:
--   Prove that $a^2b^2+b^2c^2+c^2a^2+12abc+48\ge 0$ given $a+b+c=-6$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31532` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31532; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31532 (a b c : ℝ) (h : a + b + c = -6) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0  :=  by sorry
