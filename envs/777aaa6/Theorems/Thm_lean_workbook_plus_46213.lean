-- Prove2me | Theorems.Thm_lean_workbook_plus_46213
-- name    : lean_workbook_plus_46213
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1cc1cd32-492a-4a7a-b308-5550f9391e77
-- statement:
--   Find the number of real roots of the equation $x^2-x.\sin x-\cos x = 0$ for all $x \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46213 : ∀ x : ℝ, (x^2 - x * Real.sin x - Real.cos x = 0) ↔ (x = Real.pi / 2 + Real.pi * ↑(Int.ofNat 0)) ∨ (x = Real.pi / 2 + Real.pi * ↑(Int.ofNat 1))   :=  by sorry
