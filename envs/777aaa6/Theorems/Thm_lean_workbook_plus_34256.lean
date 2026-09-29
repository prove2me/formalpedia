-- Prove2me | Theorems.Thm_lean_workbook_plus_34256
-- name    : lean_workbook_plus_34256
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/39551ccd-6c62-4e55-a5e2-20bef86c702d
-- statement:
--   For $a,b,c,d \in \mathbb R$ , show that:\n\n$ \left(a^2+b^2+c^2+d^2\right)^2\ge \frac{(a+b)^4+(a+c)^4+(a+d)^4+(b+c)^4+(b+d)^4+(c+d)^4}6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34256 (a b c d : ℝ) :
  (a^2 + b^2 + c^2 + d^2)^2 ≥
   ((a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4) / 6   :=  by sorry
