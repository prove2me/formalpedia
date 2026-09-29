-- Prove2me | Theorems.Thm_lean_workbook_plus_46444
-- name    : lean_workbook_plus_46444
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/887b90ee-3f26-405f-bd45-6fa5f4a23d86
-- statement:
--   Calculate the closed form for the integral $\int_{0}^{t} e^{x} (x - t)^{n} (x - s)^{m} \ dx, \quad s, t > 0, \quad n, m\in \mathbb{N} ?$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46444 (s t : ℝ) (n m : ℕ) : ∃ (f : ℝ → ℝ), ∀ x ∈ Set.Icc 0 t, f x = exp x * (x - t) ^ n * (x - s) ^ m   :=  by sorry
