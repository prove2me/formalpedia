-- Prove2me | Theorems.Thm_lean_workbook_plus_61738
-- name    : lean_workbook_plus_61738
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ba6864f4-67cf-4322-a578-76a9c793db36
-- statement:
--   Prove that $\frac{1}{27} \geq \frac{abc}{(a+b+c)^3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61738 : ∀ a b c : ℝ, (1 / 27) ≥ (a * b * c) / (a + b + c) ^ 3   :=  by sorry
