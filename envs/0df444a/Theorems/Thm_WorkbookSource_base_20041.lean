-- Prove2me | Theorems.Thm_WorkbookSource_base_20041
-- name    : WorkbookSource.base_20041
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:23.945935+00:00
-- url     : https://prove2.me/theorems/8c91d8c0-795c-4b09-bf22-a6e23bc3883f
-- title:
--   A reciprocal sum with a nested reciprocal is at least five halves
-- statement:
--   For positive real $a$, prove that $a + \frac{1}{a} + \frac{1}{a + \frac{1}{a}} \geq \frac{5}{2}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20041` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20041; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20041 (a : ℝ) (ha : 0 < a) : a + (1/a) + (1/(a + (1/a))) ≥ 5/2  :=  by sorry
