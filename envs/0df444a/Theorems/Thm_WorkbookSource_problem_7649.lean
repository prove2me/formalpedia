-- Prove2me | Theorems.Thm_WorkbookSource_problem_7649
-- name    : WorkbookSource.problem_7649
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:47:43.446312+00:00
-- url     : https://prove2.me/theorems/035c7942-e8c3-4025-b41d-5dea24368bb2
-- title:
--   Counting integers avoiding multiples of four and seven
-- statement:
--   How many positive integers less than $100$ are not divisible by $4$ or $7$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7649` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Update legacy finite-sum notation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7649; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_7649 : ∑ k ∈ Finset.filter (λ x => ¬ (4 ∣ x ∨ 7 ∣ x)) (Finset.range 100), 1 = 64  :=  by sorry
