-- Prove2me | Theorems.Thm_lean_workbook_plus_54232
-- name    : lean_workbook_plus_54232
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/660eaf92-d79b-4ac5-84b7-484dc697e94f
-- statement:
--   Find the maximum and minimum values of the function $\sin(x+a) \cos(2x+b)$, where $a$ and $b$ are fixed constants.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54232 (a b : ℝ) : ∀ x : ℝ, (-1 ≤ sin (x + a) * cos (2 * x + b) ∧ sin (x + a) * cos (2 * x + b) ≤ 1)   :=  by sorry
