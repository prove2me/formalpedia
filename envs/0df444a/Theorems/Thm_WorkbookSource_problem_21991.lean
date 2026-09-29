-- Prove2me | Theorems.Thm_WorkbookSource_problem_21991
-- name    : WorkbookSource.problem_21991
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:36.693826+00:00
-- url     : https://prove2.me/theorems/17a891df-5586-427a-8458-14ebba65b2bc
-- title:
--   A product bound from three symmetric bounds
-- statement:
--   From the condition, we get: $a+b+c \geq 6$ , $ab+bc+ca \geq 12$ and $abc \geq 8$ . Therefore:
--
--    $$\prod_{cyc}(1+a^2) = 1+(a^2+b^2+c^2)+(a^2b^2+b^2c^2+c^2a^2)+(abc)^2 \geq 1+12+48+64=125$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21991` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21991; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_21991  (a b c : ℝ) (h₀ : a + b + c ≥ 6) (h₁ : a * b + b * c + c * a ≥ 12) (h₂ : a * b * c ≥ 8) :
  (1 + a^2) * (1 + b^2) * (1 + c^2) ≥ 125  :=  by sorry
