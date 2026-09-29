-- Prove2me | Theorems.Thm_lean_workbook_plus_30063
-- name    : lean_workbook_plus_30063
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5de93d12-095b-4e3c-a540-61d5abee965f
-- statement:
--   Let $ a,b,c > 0$ such that $ ab + bc + ca = 3$ . Prove that $ abc(a + b + c)\leq 3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30063 (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c + c * a = 3): a * b * c * (a + b + c) ≤ 3   :=  by sorry
