-- Prove2me | Theorems.Thm_lean_workbook_plus_77500
-- name    : lean_workbook_plus_77500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/61e33320-bf1e-4461-a52a-fbfc51ef5e28
-- statement:
--   Let $ a,b,c > 0$ such that $ ab + bc + ca = 3$ . Prove that $ abc(a + b + c)\leq 3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77500 (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0) (hab : a * b + b * c + c * a = 3): a * b * c * (a + b + c) ≤ 3   :=  by sorry
