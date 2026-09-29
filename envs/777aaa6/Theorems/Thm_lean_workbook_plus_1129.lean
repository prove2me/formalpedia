-- Prove2me | Theorems.Thm_lean_workbook_plus_1129
-- name    : lean_workbook_plus_1129
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/68b32e23-cbeb-40f4-97c6-32ab08949f5b
-- statement:
--   Let $a,b,c$ be non negative real numbers satisfying $a+b+c=1$ . Prove that $ (1+a)(1+b^2)(1+c)\geq \frac{50}{27} $ Equality holds when $a=0,b=\frac{1}{3},c=\frac{2}{3}$ or $a=\frac{2}{3},b=\frac{1}{3},c=0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1129 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : (1 + a) * (1 + b^2) * (1 + c) ≥ 50 / 27 ∧ (a = 0 ∧ b = 1 / 3 ∧ c = 2 / 3 ∨ a = 2 / 3 ∧ b = 1 / 3 ∧ c = 0) ↔ a = 0 ∧ b = 1 / 3 ∧ c = 2 / 3 ∨ a = 2 / 3 ∧ b = 1 / 3 ∧ c = 0   :=  by sorry
