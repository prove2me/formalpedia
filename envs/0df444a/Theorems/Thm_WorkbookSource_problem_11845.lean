-- Prove2me | Theorems.Thm_WorkbookSource_problem_11845
-- name    : WorkbookSource.problem_11845
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:37.752481+00:00
-- url     : https://prove2.me/theorems/631c08c6-7d42-4968-9cdf-d69ef7ef12a2
-- title:
--   Bounds for twice the sine-cosine product
-- statement:
--   Given $0<x<\pi/2$ ; we see that $ 0 \le \sin (2x) \le 1 \implies 0 \le 2 \sin x \ \cos x \le 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11845` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11845; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_11845 : ∀ x : ℝ, 0 < x ∧ x < π/2 → 0 ≤ 2 * Real.sin x * Real.cos x ∧ 2 * Real.sin x * Real.cos x ≤ 1  :=  by sorry
