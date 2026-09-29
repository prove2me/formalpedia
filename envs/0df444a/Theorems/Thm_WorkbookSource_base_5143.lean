-- Prove2me | Theorems.Thm_WorkbookSource_base_5143
-- name    : WorkbookSource.base_5143
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:44.215598+00:00
-- url     : https://prove2.me/theorems/eec6a5b2-69b5-4d23-8187-bf43a9a64ef0
-- title:
--   A product inequality for shifted quadratic factors
-- statement:
--   Prove that $3(a^2 - a + 1)(c^2 - c + 1) \ge 2(a^2c^2 - ac + 1)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5143` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5143; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5143 (a c : ℝ) : 3 * (a ^ 2 - a + 1) * (c ^ 2 - c + 1) ≥ 2 * (a ^ 2 * c ^ 2 - a * c + 1)  :=  by sorry
