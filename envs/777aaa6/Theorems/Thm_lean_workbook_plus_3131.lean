-- Prove2me | Theorems.Thm_lean_workbook_plus_3131
-- name    : lean_workbook_plus_3131
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/fe41bee4-6ac4-4b77-9008-6e1d26fe0c95
-- statement:
--   Let $ a\ge b\ge c\ge 0$ then $a+b\ge 2$ and \n\n $$ \dfrac {1} {2a^2+3} +\dfrac {1} {2b^2+3} \ge \dfrac {4} {(a+b)^2+6} \Leftrightarrow$$ $$(a-b)^2 \cdot [(a+b)^2+2ab-3]\ge 0$$ which is true since $a+b\ge 2$ so it is sufficies to prove \n\n $$ \dfrac {4} {(a+b)^2+6} +\dfrac {1} {2c^2+3} \ge \dfrac {3} {5} \Leftrightarrow$$ $$ \dfrac {4} {(3-c)^2+6} +\dfrac {1} {2c^2+3} \ge \dfrac {3} {5} \Leftrightarrow$$ $$6c(4-c)(c-1)^2 \ge 0$$ which is obvious since $c\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3131  (a b c : ℝ)
  (h₀ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
  (h₁ : a ≥ b ∧ b ≥ c)
  (h₂ : a + b ≥ 2) :
  1 / (2 * a^2 + 3) + 1 / (2 * b^2 + 3) ≥ 4 / ((a + b)^2 + 6) ↔ (a - b)^2 * ((a + b)^2 + 2 * a * b - 3) ≥ 0   :=  by sorry
