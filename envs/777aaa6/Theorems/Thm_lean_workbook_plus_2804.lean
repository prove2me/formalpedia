-- Prove2me | Theorems.Thm_lean_workbook_plus_2804
-- name    : lean_workbook_plus_2804
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8b6dd8f1-b8d0-4a15-88b3-2a2c41dd8a49
-- statement:
--   Case 2. $x \ge 2$ . We now cannot set $y=x$ , as $z=3-2x \le -1$ . We need to set $y=4-x$ and $z=-1$ to get $y$ as large as possible. This gives $x^2+y^2+z^2=x^2+(4-x)^2+1 = 2x^2-8x+17$ , which has maximum at $x=3$ , ( $2 \le x \le 3$ ) so $x^2+y^2+z^2 \le 11$ in this case.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2804 (x y z : ℝ) (h₀ : 2 ≤ x ∧ x ≤ 3) (h₁ : y = 4 - x) (h₂ : z = -1) : x^2 + y^2 + z^2 ≤ 11   :=  by sorry
