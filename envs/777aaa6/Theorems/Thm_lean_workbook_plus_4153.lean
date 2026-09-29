-- Prove2me | Theorems.Thm_lean_workbook_plus_4153
-- name    : lean_workbook_plus_4153
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/2e6ca6a3-4294-4587-9a2b-85e87d1da152
-- statement:
--   Notice that $a^2 + b^2 + c^2 = 2(ab + bc + ca)$ , and therefore \n \n \begin{align*}(a + b + c)^2 &= a^2 + b^2 + c^2 + 2(ab + bc + ca) \\\ &= 4(ab + bc + ca) \\\end{align*} Notice that $ab + bc + ca = \left( \frac{a + b + c}{2} \right)^2$ , and since $LHS \in \mathbb{N}$ , then $\frac{a + b + c}{2} \in \mathbb{N}$ as well, and therefore $ab + bc + ca$ is a square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4153  (a b c : ℕ)
  (h₀ : a^2 + b^2 + c^2 = 2 * (a * b + b * c + c * a)) :
  (a + b + c)^2 = 4 * (a * b + b * c + c * a)   :=  by sorry
