-- Prove2me | Theorems.Thm_lean_workbook_plus_63717
-- name    : lean_workbook_plus_63717
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/3047ecc1-2bc7-409d-88b1-c96dee56b523
-- statement:
--   Let $ a,b,c\geq 0$ and $a+b+c>0 .$ Prove that \n $$ \frac{b}{a+2b+c}+\frac{ c}{a+b+2c} \leq \frac{2}{3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63717 :  ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c > 0 → b / (a + 2 * b + c) + c / (a + b + 2 * c) ≤ 2 / 3   :=  by sorry
