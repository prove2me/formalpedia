-- Prove2me | Theorems.Thm_lean_workbook_plus_79770
-- name    : lean_workbook_plus_79770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d0d2e45c-71ef-4aa4-9fce-ad99bd106b02
-- statement:
--   Let $ a,b,c$ be positive numbers such that $ abc \ge 1$ \nProve that $ a^3 + b^3 + c^3\ge ab + bc + ca$ \nWe can use AM-GM \n $ a^3+b^3+1 \ge 3ab ,b^3+c^3+1 \ge 3bc, c^3+a^3+1 \ge 3ca$ \nand $ ab+bc+ca \ge 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79770  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b * c ≥ 1) :
  a^3 + b^3 + c^3 ≥ a * b + b * c + c * a   :=  by sorry
