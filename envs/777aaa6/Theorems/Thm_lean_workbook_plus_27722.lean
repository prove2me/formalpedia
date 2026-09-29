-- Prove2me | Theorems.Thm_lean_workbook_plus_27722
-- name    : lean_workbook_plus_27722
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/0ce8b71a-f3e8-451c-bbae-1e271ee86a67
-- statement:
--   Let $ x=\frac{b}{a},y=\frac{c}{b},z=\frac{a}{c}.$ \n the inequality is equivalent now to: \n $ \frac{1}{x^2+x+1}+\frac{1}{y^2+y+1}+\frac{1}{z^2+z+1} \ge 1$ with $ xyz=1$ , \n which is equivalent after expansion to: \n $ x^2+y^2+z^2 \ge xy+yz+zx$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27722  (x y z : ℝ)
  (h₀ : x * y * z = 1)
  (h₁ : 0 < x ∧ 0 < y ∧ 0 < z) :
  x^2 + y^2 + z^2 ≥ x * y + y * z + z * x   :=  by sorry
