-- Prove2me | Theorems.Thm_lean_workbook_plus_48545
-- name    : lean_workbook_plus_48545
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3b891653-50bc-4152-a6ce-4bd635b7a037
-- statement:
--   Let $a, b, c$ be integers satisfying $ab + bc + ca = 1.$ Prove that $(1+ a^2 )(1+ b^2 )(1+ c^2 )$ is a perfect square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48545 (a b c : ℤ) (hab : a * b + b * c + c * a = 1) : ∃ k : ℤ, k ^ 2 = (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2)   :=  by sorry
