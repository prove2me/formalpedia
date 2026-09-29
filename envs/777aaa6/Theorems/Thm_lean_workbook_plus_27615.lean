-- Prove2me | Theorems.Thm_lean_workbook_plus_27615
-- name    : lean_workbook_plus_27615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/af9cc746-3d8c-4d4d-afd1-828618bd9629
-- statement:
--   Let $S$ be the sum of the squares of the numbers on the board. Note that after each successive operation, $S$ always increases and never decreases since: $a^2+b^2 > 0 \implies 2a^2+2b^2 > a^2+b^2 \implies (a-b)^2+(a+b)^2 > a^2+b^2$. Equality would hold if $a=b=0$ but that is impossible under the problem statement.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27615 :
  ∀ a b : ℤ, a ≠ 0 ∧ b ≠ 0 → (a - b) ^ 2 + (a + b) ^ 2 > a ^ 2 + b ^ 2   :=  by sorry
