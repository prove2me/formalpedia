-- Prove2me | Theorems.Thm_lean_workbook_plus_30760
-- name    : lean_workbook_plus_30760
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c48e2651-b6a2-4839-bc6b-6ff610ba4b2f
-- statement:
--   We have $x \heartsuit y = |x-y|$ . Thus the LHS of the second equation is just $2 \cdot |x-y|$ . Similarly, the RHS is $|(2x)-(2y)| = |2 \cdot (x-y)| = 2|x-y|$ . Hope this clears things up!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30760  (x y : ℝ)
  (h₀ : x ≠ y)
  (h₁ : 0 < abs (x - y))
  (h₂ : 0 < abs (2 * (x - y))) :
  abs (2 * (x - y)) = 2 * abs (x - y)   :=  by sorry
