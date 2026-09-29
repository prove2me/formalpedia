-- Prove2me | Theorems.Thm_lean_workbook_plus_52334
-- name    : lean_workbook_plus_52334
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9686a54f-e028-4c76-ba8d-f6b25406a54c
-- statement:
--   My SolutionWe have the equations $4s + c + 10b = 16.90$ , $3s + c + 7b = 12.60$ , and we are trying to find $2s + 2c + 2b$ . Subtracting the first two equations, we obtain $s + 3b = 4.30$ . Adding the first two equations, we obtain $7s + 2c + 17b = 29.50$ . Multiplying the first equation ( $s + 3b = 4.30$ ) by $5$ , we obtain $5s + 15b = 21.50$ . Subtracting $5 + 15b = 21.50$ from $7s + 2c + 17b = 29.50$ , we obtain the answer. $2s + 2c + 2b = \boxed{8.00}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52334  (s c b : ℝ)
  (h₀ : 4 * s + c + 10 * b = 16.9)
  (h₁ : 3 * s + c + 7 * b = 12.6) :
  2 * s + 2 * c + 2 * b = 8   :=  by sorry
