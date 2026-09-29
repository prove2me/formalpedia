-- Prove2me | Theorems.Thm_WorkbookSource_problem_21029
-- name    : WorkbookSource.problem_21029
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:47.953982+00:00
-- url     : https://prove2.me/theorems/a40d950e-20fa-4bbc-830e-7e940460e210
-- title:
--   An exact geometric-series sum
-- statement:
--   Calculate the sum of the geometric series with $a_1 = 4096$, $r = -\frac{1}{2}$, and $n = 16$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21029` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Notation repair: Replaced legacy ∑ i in s binder notation with current ∑ i ∈ s; no binder/domain/proposition change.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21029; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_21029 (a : ℕ) (r : ℚ) (n : ℕ) (h₁ : a = 4096) (h₂ : r = -1/2) (h₃ : n = 16) : ∑ i ∈ Finset.range n, a * r^i = 2730.625  :=  by sorry
