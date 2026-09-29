-- Prove2me | Theorems.Thm_lean_workbook_plus_65553
-- name    : lean_workbook_plus_65553
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b2a7a8aa-c0a5-4f27-9e93-cce897d638e5
-- statement:
--   Find the closed form of the sequence $ a_n=\frac{\sqrt{2}}{2}((3+2\sqrt{2})^{n}-(3-2\sqrt{2})^{n})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65553 (a : ℕ → ℝ) (a_n : ∀ n, a n = (Real.sqrt 2 / 2) * ((3 + 2 * Real.sqrt 2)^n - (3 - 2 * Real.sqrt 2)^n)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
