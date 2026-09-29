-- Prove2me | Theorems.Thm_lean_workbook_plus_2328
-- name    : lean_workbook_plus_2328
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/00852ce4-d682-4b26-8645-c5453dd41450
-- statement:
--   If $b+c+d+e=0$ , we're done. Otherwise, as the required inequality is homogeneous, we may assume $b+c+d+e = 1$ . Then $b^2+c^2+d^2+e^2 \ge 1/4$ by Cauchy-Schwarz, and it is enough to prove $a^2-a+1/4 = (a-1/2)^2 \ge 0$ , which is true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2328  (b c d e a : ℝ)
  (h₀ : b + c + d + e = 0)
  (h₁ : a + b + c + d + e = 1) :
  a^2 + b^2 + c^2 + d^2 + e^2 ≥ 1 / 4   :=  by sorry
