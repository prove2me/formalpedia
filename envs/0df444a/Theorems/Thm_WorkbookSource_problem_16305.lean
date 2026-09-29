-- Prove2me | Theorems.Thm_WorkbookSource_problem_16305
-- name    : WorkbookSource.problem_16305
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:57.86408+00:00
-- url     : https://prove2.me/theorems/21c57628-247f-43cc-b559-73bedea42e26
-- title:
--   The average of three specified consecutive numbers
-- statement:
--   What is $(2021 + 2022 + 2023)/6$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16305` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16305; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16305 (a b c : ℝ) (h₁ : a = 2021) (h₂ : b = 2022) (h₃ : c = 2023) : (a + b + c)/6 = 1011  :=  by sorry
