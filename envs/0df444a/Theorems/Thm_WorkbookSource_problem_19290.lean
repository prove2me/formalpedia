-- Prove2me | Theorems.Thm_WorkbookSource_problem_19290
-- name    : WorkbookSource.problem_19290
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:05:12.700929+00:00
-- url     : https://prove2.me/theorems/3df683e7-2f31-4b86-97bf-bdf7a5192b38
-- title:
--   Preserving squares forces nonnegative values
-- statement:
--   For $f(1) = 1$ , $f(x^2) = [f(x)]^2$ . This implies that $f(x)$ is nonnegative whenever $x$ is nonnegative.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19290` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19290; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_19290  (f : ℝ → ℝ)
  (h₀ : f 1 = 1)
  (h₁ : ∀ x, f (x^2) = (f x)^2) :
  ∀ x ≥ 0, 0 ≤ f x  :=  by sorry
