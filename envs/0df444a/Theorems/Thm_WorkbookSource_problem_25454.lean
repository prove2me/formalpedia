-- Prove2me | Theorems.Thm_WorkbookSource_problem_25454
-- name    : WorkbookSource.problem_25454
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:22.771568+00:00
-- url     : https://prove2.me/theorems/f22425ff-8f68-417c-b1ce-783bedf8ef4b
-- title:
--   Evaluating a shifted cubic function
-- statement:
--   Given the function $f: \mathbb{R\rightarrow\mathbb{R}}$ defined by $f(x-2) = x^{3}$, find the value of $f(3)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25454` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25454; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_25454 (f : ℝ → ℝ) (h₁ : ∀ x, f (x - 2) = x^3) : f 3 = 125  :=  by sorry
