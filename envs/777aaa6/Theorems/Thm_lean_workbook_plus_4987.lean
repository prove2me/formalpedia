-- Prove2me | Theorems.Thm_lean_workbook_plus_4987
-- name    : lean_workbook_plus_4987
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5d13649c-9da1-4724-a16b-3d4d0a02eedf
-- statement:
--   1a) WLOG, let $a, b, c, \in \mathbb{R^+}$ s.t. $a \le b \le c$ . Then, $a = u, b = u+v, c = u+v+w$ , for some $u, v, w \ge 0$ . Then, if $a^4+b^4+c^4 \ge abc(a+b+c)$ , we have \n \n$3 u^4+8 u^3 v+4 u^3 w+12 u^2 v^2+12 u^2 v w+6 u^2 w^2+8 u v^3+12 u v^2 w+12 u v w^2+4 u w^3+2 v^4+4 v^3 w+6 v^2 w^2+4 v w^3+w^4 \ge 3 u^4+8 u^3 v+4 u^3 w+7 u^2 v^2+7 u^2 v w+u^2 w^2+2 u v^3+3 u v^2 w+u v w^2$ \n$\implies 5 u^2 v^2+5 u^2 v w+5 u^2 w^2+6 u v^3+9 u v^2 w+11 u v w^2+4 u w^3+2 v^4+4 v^3 w+6 v^2 w^2+4 v w^3+w^4 \ge 0$ \nwhich is true, since $u, v, w \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4987  (u v w a b c : ℝ)
  (h₀ : 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w)
  (h₁ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
  (h₂ : a = u)
  (h₃ : b = u + v)
  (h₄ : c = u + v + w)
  (h₅ : 3 * u^4 + 8 * u^3 * v + 4 * u^3 * w + 12 * u^2 * v^2 + 12 * u^2 * v * w + 6 * u^2 * w^2 + 8 * u * v^3 + 12 * u * v^2 * w + 12 * u * v * w^2 + 4 * u * w^3 + 2 * v^4 + 4 * v^3 * w + 6 * v^2 * w^2 + 4 * v * w^3 + w^4 ≥ 3 * u^4 + 8 * u^3 * v + 4 * u^3 * w + 7 * u^2 * v^2 + 7 * u^2 * v * w + u^2 * w^2 + 2 * u * v^3 + 3 * u * v^2 * w + u * v * w^2) :
  u^2 * v^2 + u^2 * v * w + u^2 * w^2 + 6 * u * v^3 + 9 * u * v^2 * w + 11 * u * v * w^2 + 4 * u * w^3 + 2 * v^4 + 4 * v^3 * w + 6 * v^2 * w^2 + 4 * v * w^3 + w^4 ≥ 0   :=  by sorry
