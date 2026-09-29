-- Prove2me | Theorems.Thm_lean_workbook_plus_77826
-- name    : lean_workbook_plus_77826
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/bb72ce99-9072-4bb0-a57e-4ab7aebb4f85
-- statement:
--   Prove that for positive reals $a, b, c$ with $ab + bc + ac = 3$, $a + b + c \geq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77826 (a b c: ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c + a * c = 3): a + b + c >= 3   :=  by sorry
