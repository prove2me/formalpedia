-- Prove2me | Theorems.Thm_WorkbookSource_problem_20899
-- name    : WorkbookSource.problem_20899
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:47:44.8993+00:00
-- url     : https://prove2.me/theorems/b7dee02a-f245-4f77-acab-5db9c9c8a044
-- title:
--   Counting numbers divisible by neither five nor seven
-- statement:
--   p4. How many whole numbers, from $1$ to $2006$ , are divisible neither by $5$ nor by $7$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20899` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Update legacy finite-sum notation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20899; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_20899 : ∑ i ∈ Finset.filter (λ x => ¬ (5∣x) ∧ ¬ (7∣x)) (Finset.Icc 1 2006), 1 = 1376  :=  by sorry
