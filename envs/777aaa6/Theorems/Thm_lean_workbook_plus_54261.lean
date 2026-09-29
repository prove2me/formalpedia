-- Prove2me | Theorems.Thm_lean_workbook_plus_54261
-- name    : lean_workbook_plus_54261
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/faf99b36-f4d9-47c4-a3b5-8d1122b84006
-- statement:
--   Prove that if $a, b, c$ are real numbers such that $a + b + c > 0, ab + bc + ca > 0, abc > 0$, then the numbers $a, b, c$ are positive.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54261 (a b c : ℝ) (ha : a + b + c > 0) (hb : a * b + b * c + c * a > 0) (hc : a * b * c > 0) : a > 0 ∧ b > 0 ∧ c > 0   :=  by sorry
