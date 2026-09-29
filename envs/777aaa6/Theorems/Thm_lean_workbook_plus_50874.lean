-- Prove2me | Theorems.Thm_lean_workbook_plus_50874
-- name    : lean_workbook_plus_50874
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/7a106a4d-9287-4357-9fb8-864e86b62cd7
-- statement:
--   For $P(x) = x^2-ax+2$ to have real roots we need $P(a/2) \leq 0$ , whence $a^2 \geq 8$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50874 : ∀ a : ℝ, (∃ x, x^2 - a*x + 2 = 0) → a^2 ≥ 8   :=  by sorry
