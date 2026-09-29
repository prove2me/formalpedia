-- Prove2me | Theorems.Thm_lean_workbook_plus_19557
-- name    : lean_workbook_plus_19557
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d54db039-070e-41b8-b6d8-e5729415448f
-- statement:
--   Let $a,b,c>0$ , $a,b,c\in (0,\frac{1}{2}]$ ,prove that:\n\n $a(1-a)+b(1-b)+c(1-c) \le2/3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19557 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ∈ Set.Icc 0 (1 / 2) ∧ b ∈ Set.Icc 0 (1 / 2) ∧ c ∈ Set.Icc 0 (1 / 2) → a * (1 - a) + b * (1 - b) + c * (1 - c) ≤ 2 / 3   :=  by sorry
