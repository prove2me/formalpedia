-- Prove2me | Theorems.Thm_lean_workbook_plus_71909
-- name    : lean_workbook_plus_71909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b4bef74f-999d-438b-b28f-5c70d22b6401
-- statement:
--   Let $a,b,c,d\in \mathbb{R}$ such that $ab=1$ and $ac+bd=2$ . Prove: $1-cd\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71909 : ∀ a b c d : ℝ, a * b = 1 ∧ a * c + b * d = 2 → 1 - c * d ≥ 0   :=  by sorry
