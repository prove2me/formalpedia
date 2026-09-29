-- Prove2me | Theorems.Thm_WorkbookSource_problem_12336
-- name    : WorkbookSource.problem_12336
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:46.695369+00:00
-- url     : https://prove2.me/theorems/fe354544-b73e-4646-bf6f-edc89a20f980
-- title:
--   Three equal evaluations determine quadratic coefficients
-- statement:
--   Let Bob's quadratic be $ax^2+bx+c$ and Alice's be $dx^2+ex+f$ . We know that,
--
--    $a+b+c=d+e+f$ ,
--
--    $4a+2b+c=4d+2e+f$ ,
--
--    $9a+3b+c=9d+3e+f$ .
--
--   Then by subtracting the 2nd equation from the 3rd one we have $5a+b=5d+e$ .
--
--   By subtracting the first equation from the second we have $3a+b=3d+3$ .
--
--   Now we subtract $3a+b=3d+3$ from $5a+b=5d+e$ to find $2a=2d$ or $a=d$ .
--
--   By substituting $a=d$ into our original 3 equations we have,
--
--    $a+b+c=a+e+f$ or $b+c=e+f$ ,
--
--    $4a+2b+c=4a+2e+f$ or $2b+c=2e+f$ ,
--
--    $9a+3b+c=9a+3e+f$ or $3b+c=3e+f$ .
--
--   By subtracting the second equation from the first one we obtain $b=e$ so then $c$ must equal $f$ .
--
--   Therefore, the quadratics are the same.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12336` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12336; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_12336  (a b c d e f : ℝ)
  (h₀ : a + b + c = d + e + f)
  (h₁ : 4 * a + 2 * b + c = 4 * d + 2 * e + f)
  (h₂ : 9 * a + 3 * b + c = 9 * d + 3 * e + f) :
  a = d ∧ b = e ∧ c = f  :=  by sorry
