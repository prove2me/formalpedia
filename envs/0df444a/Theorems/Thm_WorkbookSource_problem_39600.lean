-- Prove2me | Theorems.Thm_WorkbookSource_problem_39600
-- name    : WorkbookSource.problem_39600
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:44.532349+00:00
-- url     : https://prove2.me/theorems/6f6df081-bdd7-410b-9261-a7dd749633ec
-- title:
--   The closed form of a halving recurrence
-- statement:
--   Prove by induction that $y_n=\frac{3}{2^{n+1}}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39600` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39600; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39600 (y : ℕ → ℝ) (n : ℕ) (h₁ : y 0 = 3/2) (h₂ : ∀ n, y (n+1) = (y n)/2) : y n = 3 / 2 ^ (n + 1)  :=  by sorry
