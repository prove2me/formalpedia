-- Prove2me | Theorems.Thm_lean_workbook_plus_17121
-- name    : lean_workbook_plus_17121
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/16de531b-a9b8-4eba-acbd-fc2779ef9922
-- statement:
--   Prove that for $a,b,c>0$ from $\mathbb R $ and $abc=1$ , we have $$(a^2+1)(b^2+1)(c^2+1)\ge \frac{1}{2}(abc+1)(a+1)(b+1)(c+1).$$ $$(a^3+1)(b^3+1)(c^3+1) \ge \frac{1}{2}(abc+1)(a^2+1)(b^2+1)(c^2+1).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17121 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 1 / 2 * (a * b * c + 1) * (a + 1) * (b + 1) * (c + 1)   :=  by sorry
