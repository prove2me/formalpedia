-- Prove2me | Theorems.Thm_lean_workbook_plus_23104
-- name    : lean_workbook_plus_23104
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0b4e1c80-639a-49ba-bb3c-aac01b7da79e
-- statement:
--   i think what the problem means is that if $c|b$ and $a|\frac{b}{c}$ , then $a|b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23104 (a b c : ℕ) (h₁ : c ∣ b) (h₂ : a ∣ b / c) : a ∣ b   :=  by sorry
