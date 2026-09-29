-- Prove2me | Theorems.Thm_lean_workbook_plus_58926
-- name    : lean_workbook_plus_58926
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3143869d-9a52-4a14-abcf-3fa90c3a1ee3
-- statement:
--   Let $2>a\geq 0$ . Prove that \n $$\frac{a}{2-a}+ \frac{2}{a+1}\geq \frac{5}{3}$$ Equality holds when $a=\frac{1}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58926 (a : ℝ) (ha : 2 > a ∧ a >= 0) : a / (2 - a) + 2 / (a + 1) ≥ 5 / 3 ∧ (a = 1 / 2 → a / (2 - a) + 2 / (a + 1) = 5 / 3)   :=  by sorry
