-- Prove2me | Theorems.Thm_WorkbookSource_problem_13333
-- name    : WorkbookSource.problem_13333
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:22.907895+00:00
-- url     : https://prove2.me/theorems/484a7ec1-ed5c-4d8f-92fb-d6215d6531af
-- title:
--   A cubic bound on the unit interval
-- statement:
--   If $f(y)=y^2-{{2y^3}\over 3}$ then $f'(y)=2y(1-y)\ge 0$ on $[0,1]$ hence $f(y)\le f(1)=1/3$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13333` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13333; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13333  (y : ℝ)
  (h₀ : 0 ≤ y)
  (h₁ : y ≤ 1) :
  y^2 - (2 * y^3) / 3 ≤ 1 / 3  :=  by sorry
