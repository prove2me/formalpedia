-- Prove2me | Theorems.Thm_WorkbookSource_problem_56440
-- name    : WorkbookSource.problem_56440
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:49.857079+00:00
-- url     : https://prove2.me/theorems/c88aab44-5db1-4ba5-8176-53da037f1f8a
-- title:
--   Both double-angle values from sine and cosine
-- statement:
--   Find $\cos(2\alpha)$ and $\sin(2\alpha)$ if $\cos\alpha = \frac{4}{5}$ and $\sin\alpha = \frac{3}{5}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56440` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56440; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_56440 (α : ℝ) (h₁ : cos α = 4/5) (h₂ : sin α = 3/5) : cos (2*α) = 7/25 ∧ sin (2*α) = 24/25  :=  by sorry
