-- Prove2me | Theorems.Thm_lean_workbook_plus_74363
-- name    : lean_workbook_plus_74363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/17579831-e0e6-4c47-af21-d5bc2c33c9ed
-- statement:
--   Can we use such function: $f(x) = 0$ for $x \in [0, \frac{1}{8}]$ and $f(x) = \frac{8x - 1}{14}$ for $x \geq \frac{1}{8}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74363 : ∃ f : ℝ → ℝ, ∀ x ∈ Set.Icc 0 (1 / 8), f x = 0 ∧ ∀ x ≥ 1 / 8, f x = (8 * x - 1) / 14   :=  by sorry
