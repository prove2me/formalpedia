-- Prove2me | Theorems.Thm_lean_workbook_plus_26590
-- name    : lean_workbook_plus_26590
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8a3ffbe8-0dd1-46e8-9182-3f2067d33260
-- statement:
--   For positive fractions $\dfrac {a} {b} < \dfrac {c} {d}$ that is called the mediant (the name comes from the Farey sequence(s)), and we have $\dfrac {a} {b} < \dfrac {a+c} {b+d} < \dfrac {c} {d}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26590 (a b c d : ℕ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h₂ : a * d < b * c) : (a * d < b * c ∧ b * c < (a + c) * (b + d))   :=  by sorry
