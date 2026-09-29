-- Prove2me | Theorems.Thm_lean_workbook_plus_62136
-- name    : lean_workbook_plus_62136
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cf90d4b0-b5f2-4374-9643-fe7013654729
-- statement:
--   $ m \le g\left( {1 - {x^2}} \right) \le M \Leftrightarrow \frac{m}{4} \le \frac{1}{4}g\left( {1 - {x^2}} \right) \le \frac{M}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62136 (m M : ℝ) (x : ℝ) (g : ℝ → ℝ): m ≤ g (1 - x^2) ∧ g (1 - x^2) ≤ M ↔ m/4 ≤ (1/4) * g (1 - x^2) ∧ (1/4) * g (1 - x^2) ≤ M/4   :=  by sorry
