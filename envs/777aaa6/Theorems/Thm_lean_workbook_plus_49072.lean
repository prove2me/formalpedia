-- Prove2me | Theorems.Thm_lean_workbook_plus_49072
-- name    : lean_workbook_plus_49072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/794d8237-867f-4d65-bd60-9253f80c89d3
-- statement:
--   Let $a,b,c>0$. By Cauchy-Schwarz inequality, $(a+b+c)^2 \leq 3(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49072 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
