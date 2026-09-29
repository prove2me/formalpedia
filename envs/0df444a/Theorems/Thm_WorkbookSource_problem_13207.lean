-- Prove2me | Theorems.Thm_WorkbookSource_problem_13207
-- name    : WorkbookSource.problem_13207
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:17.816913+00:00
-- url     : https://prove2.me/theorems/765911d0-fce6-4268-abc4-cd512216fa76
-- title:
--   Adding two cubic constraints
-- statement:
--   Another solution: Again, we suppose that $AD$ is a diameter of the semicircle. Let $e = CE$ and $f = CA$ . From a result of the previous post, $a^2 + b^2 + e^2 + abe = 4$ and $f^2 + c^2 + d^2 + fcd = 4$ . Adding these gives $a^2 + b^2 + c^2 + d^2 + e^2 + f^2 + abe + fcd = 8$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13207` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13207; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13207  (a b c d e f : ℝ)
  (h₀ : a^2 + b^2 + e^2 + a * b * e = 4)
  (h₁ : f^2 + c^2 + d^2 + f * c * d = 4) :
  a^2 + b^2 + c^2 + d^2 + e^2 + f^2 + a * b * e + f * c * d = 8  :=  by sorry
