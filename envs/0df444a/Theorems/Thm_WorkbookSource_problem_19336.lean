-- Prove2me | Theorems.Thm_WorkbookSource_problem_19336
-- name    : WorkbookSource.problem_19336
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:05:11.242312+00:00
-- url     : https://prove2.me/theorems/f5d23478-7b5d-4f08-a7d4-da8f84fed4de
-- title:
--   A trigonometric identity using the angle pi over three
-- statement:
--   Prove that $ \cos\theta + \sqrt{3}\sin\theta = 2\left(\cos\theta\cos\frac{\pi}{3} + \sin\theta\sin\frac{\pi}{3}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19336` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19336; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_19336 : ∀ θ : ℝ, ∃ h : 0 < 3, ∃ h2 : 0 < 2, ∃ h3 : 0 < π, ∃ h4 : 0 < 6, cos θ + Real.sqrt 3 * sin θ = 2 * (cos θ * cos (π / 3) + sin θ * sin (π / 3))  :=  by sorry
