-- Prove2me | Theorems.Thm_WorkbookSource_problem_15814
-- name    : WorkbookSource.problem_15814
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:38.900533+00:00
-- url     : https://prove2.me/theorems/0a7177a1-1c44-4671-948f-0dce78e7555c
-- title:
--   The other root of a quadratic
-- statement:
--   Then $ 12x^2-17x+5=0$ . You can see pretty quickly that $ 1$ is a root, so synthetic division or whatever will get you $ (x-1)(12x-5)=0$ . Obviously $ x
--   e 1$ , so $ x=\frac{5}{12}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15814` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15814; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_15814  (x : ℝ)
  (h₀ : 12 * x^2 - 17 * x + 5 = 0)
  (h₁ : x ≠ 1) :
  x = 5 / 12  :=  by sorry
