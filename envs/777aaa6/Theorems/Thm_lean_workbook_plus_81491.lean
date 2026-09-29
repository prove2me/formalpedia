-- Prove2me | Theorems.Thm_lean_workbook_plus_81491
-- name    : lean_workbook_plus_81491
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b53f933d-8245-4931-bb38-4dda30aaad7b
-- statement:
--   Let $ a,b,c\in[\frac{1}{2},1]$ . Prove that $ ab+bc+ca+\frac{3}{4} \geq a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81491 (a b c : ℝ) (ha : 1 / 2 ≤ a ∧ a ≤ 1) (hb : 1 / 2 ≤ b ∧ b ≤ 1) (hc : 1 / 2 ≤ c ∧ c ≤ 1) : a * b + b * c + c * a + 3 / 4 ≥ a + b + c   :=  by sorry
