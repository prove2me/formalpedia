-- Prove2me | Theorems.Thm_lean_workbook_plus_6172
-- name    : lean_workbook_plus_6172
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/14a89328-d548-4fc1-9ae6-878b103307fc
-- statement:
--   Sum to product gives $\sin(20)+\sin(40)=2\sin(30)\cos(10)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6172 : ∀ a b c d : ℝ, a = 20 ∧ b = 40 → c = 30 ∧ d = 10 → sin a + sin b = 2 * sin c * cos d   :=  by sorry
