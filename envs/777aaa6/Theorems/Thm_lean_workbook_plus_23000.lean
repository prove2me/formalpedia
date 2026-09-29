-- Prove2me | Theorems.Thm_lean_workbook_plus_23000
-- name    : lean_workbook_plus_23000
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c0aa9e57-c624-4e6b-8078-d129aef584f9
-- statement:
--   For $a=b$ and $c=-2a+3$ we got the following ineauality \n $$\frac{3}{64}(4 a - 3)^2 (48 a^2 - 104 a + 57)\geq 0$$ , which is true for all reals. Equality occurs for $(a.b,c)=(\frac{3}{4}, \frac{3}{4}, \frac{3}{2})$ and it's permutations.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23000 :  ∀ a b c : ℝ, a = b ∧ c = -2 * a + 3 → (3 / 64) * (4 * a - 3) ^ 2 * (48 * a ^ 2 - 104 * a + 57) ≥ 0   :=  by sorry
