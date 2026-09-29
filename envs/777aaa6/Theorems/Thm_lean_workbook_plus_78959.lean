-- Prove2me | Theorems.Thm_lean_workbook_plus_78959
-- name    : lean_workbook_plus_78959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0ec99be5-2c3d-47b5-ae7b-e70ff0347610
-- statement:
--   Let $k=a+b+c$. Then $3(a^2 + b^2 + c^2) - 2(ab + bc + ca + a + b + c) = 4(a^2 + b^2 + c^2) - k(k+2)$ But, by power means, this is greater than or equal to $\tfrac{4}{3}(a+b+c)^2 -k(k+2) \,=\, \tfrac{1}{3}(k-3)^2-3 \,\ge\, {\bf -3}$ and that bound is attained for $a=b=c=\tfrac{k}{3}=1\quad\blacksquare$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78959  (a b c : ℝ)
  (k : ℝ)
  (h₀ : k = a + b + c) :
  3 * (a^2 + b^2 + c^2) - 2 * (a * b + b * c + c * a + a + b + c) ≥ -3   :=  by sorry
