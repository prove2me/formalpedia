-- Prove2me | Theorems.Thm_WorkbookSource_problem_3474
-- name    : WorkbookSource.problem_3474
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:38.653256+00:00
-- url     : https://prove2.me/theorems/b4e8bece-5bbb-402b-a09b-7e667de28ee9
-- title:
--   A product of nonnegative linear factors
-- statement:
--   prove that $3(5s_1-3)(s_1-3)\ge 0$ given $s_3\ge 1$ and $s_1\ge 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3474` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3474; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3474 (s₁ : ℝ) (s₃ : ℝ) : s₃ ≥ 1 ∧ s₁ ≥ 3 → 3 * (5 * s₁ - 3) * (s₁ - 3) ≥ 0  :=  by sorry
