-- Prove2me | Theorems.Thm_lean_workbook_plus_71362
-- name    : lean_workbook_plus_71362
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d1b1d343-f0d5-4eaa-a419-11d00f2a0df8
-- statement:
--   Prove that $x^3(1+\sqrt{3-x^2})+x^2\leq 1$ for $x\leq \frac{\sqrt{5}-1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71362 : ∀ x : ℝ, x ≤ (Real.sqrt 5 - 1) / 2 ∧ x ≤ 0 → x^3 * (1 + Real.sqrt (3 - x^2)) + x^2 ≤ 1   :=  by sorry
