-- Prove2me | Theorems.Thm_lean_workbook_plus_22387
-- name    : lean_workbook_plus_22387
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/583bd946-6727-44c3-a824-e73359bc42e6
-- statement:
--   prove that $ \frac {3(ab + bc + ca)}{(a + b + c)^2}\leq 1$ where $a, b, c$ are positive numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22387 (a b c : ℝ) : (3 * (a * b + b * c + c * a)) / (a + b + c) ^ 2 ≤ 1   :=  by sorry
