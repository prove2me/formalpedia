-- Prove2me | Theorems.Thm_lean_workbook_plus_44014
-- name    : lean_workbook_plus_44014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6d070904-1e57-45a4-9868-96490d33220d
-- statement:
--   If the equation $x^{3}+(a-1)\sqrt{3}x^{2}-6ax+b=0$ has three real roots, prove that $|b|\leq |a+1|^{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44014 (a b : ℝ) : ∃ x y z : ℝ, x^3 + (a - 1) * Real.sqrt 3 * x^2 - 6 * a * x + b = 0 ∧ y^3 + (a - 1) * Real.sqrt 3 * y^2 - 6 * a * y + b = 0 ∧ z^3 + (a - 1) * Real.sqrt 3 * z^2 - 6 * a * z + b = 0 → |b| ≤ |a + 1|^3   :=  by sorry
