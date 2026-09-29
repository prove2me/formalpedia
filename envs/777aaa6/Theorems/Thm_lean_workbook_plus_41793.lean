-- Prove2me | Theorems.Thm_lean_workbook_plus_41793
-- name    : lean_workbook_plus_41793
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3868a9f4-240a-45c0-8ac8-8fa036d3cd29
-- statement:
--   WLOG, let $a, b, c, \in \mathbb{R^+}$ s.t. $a \le b \le c$ . Then, $a = u, b = u+v, c = u+v+w$ , for some $u, v, w \ge 0$ . \n\nThen, if $ab(a+b)+bc(b+c)+ca(c+a)\leq 2(a^3+b^3+c^3)$ we have \n\n \begin{align*}ab(a+b)+bc(b+c)+ca(c+a) &\leq 2(a^3+b^3+c^3) \\\n\implies u*(u+v)*(u+u+v)+(u+v)*(u+v+w)*(u+v+u+v+w)+(u+v+w)*u*(u+v+w+u) & \leq 2*(u^3+(u+v)^3+(u+v+w)^3) \\\n\implies 6 u^3+12 u^2 v+6 u^2 w+8 u v^2+8 u v w+2 u w^2+2 v^3+3 v^2 w+v w^2 & \leq 6 u^3+12 u^2 v+6 u^2 w+12 u v^2+12 u v w+6 u w^2+4 v^3+6 v^2 w+6 v w^2+2 w^3 \\\n\implies 0 & \leq 4 u v^2+4 u v w+4 u w^2+2 v^3+3 v^2 w+5 v w^2+2 w^3 \\\n\end{align*} which is true, so we're done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41793  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a ≤ b ∧ b ≤ c) :
  a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≤ 2 * (a^3 + b^3 + c^3)   :=  by sorry
